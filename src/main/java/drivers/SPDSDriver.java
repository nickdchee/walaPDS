/*
 * Copyright (c) 2002 - 2006 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 */
package drivers;

import static com.ibm.wala.util.config.AnalysisScopeReader.addClassPathToScope;
import static com.ibm.wala.util.config.AnalysisScopeReader.makeJavaBinaryAnalysisScope;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.ibm.wala.cast.ir.ssa.AstIRFactory;
import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.classLoader.Language;
import com.ibm.wala.classLoader.ShrikeCTMethod;
import com.ibm.wala.classLoader.ShrikeIRFactory;
import com.ibm.wala.core.tests.callGraph.CallGraphTestUtil;
import com.ibm.wala.examples.drivers.PDFTypeHierarchy;
import com.ibm.wala.examples.properties.WalaExamplesProperties;
import com.ibm.wala.ipa.callgraph.AnalysisCacheImpl;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilder;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.ipa.slicer.HeapStatement;
import com.ibm.wala.ipa.slicer.MethodEntryStatement;
import com.ibm.wala.ipa.slicer.MethodExitStatement;
import com.ibm.wala.ipa.slicer.SDG;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.properties.WalaProperties;
import com.ibm.wala.shrikeBT.IInstruction;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.IRFactory;
import com.ibm.wala.ssa.SSAOptions;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.NullProgressMonitor;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.collections.MultiMap;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.GraphIntegrity;
import com.ibm.wala.util.graph.GraphIntegrity.UnsoundGraphException;
import com.ibm.wala.util.graph.GraphSlicer;
import com.ibm.wala.util.io.CommandLine;
import com.ibm.wala.util.io.FileProvider;
import com.ibm.wala.viz.DotUtil;
import com.ibm.wala.viz.NodeDecorator;
import com.ibm.wala.viz.PDFViewUtil;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Properties;
import java.util.function.Predicate;

import sync.pds.solver.nodes.Node;
import translator.WALAIRtoNodeTranslator;
import wpds.interfaces.Location;
import wpds.interfaces.State;
import wpds.wildcard.ExclusionWildcard;
import wpds.wildcard.Wildcard;


public class SPDSDriver {

    private static final String PDF_FILE = "sdg.pdf";
    private static final ShrikeIRFactory irFactory = new ShrikeIRFactory();
    /**
     * Usage: GVSDG -appJar [jar file name] -mainClass [main class]
     *
     * <p>The "jar file name" should be something like "c:/temp/testdata/java_cup.jar"
     */
    public static void main(String[] args)
            throws IllegalArgumentException, CancelException, IOException {
        run(args);
    }

    public static Process run(String[] args)
            throws IllegalArgumentException, CancelException, IOException {

        Properties p = CommandLine.parse(args);
        validateCommandLine(p);
        return run(
                p.getProperty("appJar"),
                p.getProperty("mainClass"),
                getDataDependenceOptions(p),
                getControlDependenceOptions(p));
    }

    public static DataDependenceOptions getDataDependenceOptions(Properties p) {
        String d = p.getProperty("dd", "full");
        for (DataDependenceOptions result : DataDependenceOptions.values()) {
            if (d.equals(result.getName())) {
                return result;
            }
        }
        Assertions.UNREACHABLE("unknown data datapendence option: " + d);
        return null;
    }

    public static ControlDependenceOptions getControlDependenceOptions(Properties p) {
        String d = p.getProperty("cd", "full");
        for (ControlDependenceOptions result : ControlDependenceOptions.values()) {
            if (d.equals(result.getName())) {
                return result;
            }
        }
        Assertions.UNREACHABLE("unknown control datapendence option: " + d);
        return null;
    }

    /** @param appJar something like "c:/temp/testdata/java_cup.jar" */
    public static Process run(
            String appJar,
            String mainClass,
            DataDependenceOptions dOptions,
            ControlDependenceOptions cOptions)
            throws IllegalArgumentException, CancelException, IOException {
        try {
//      AnalysisScope scope =
//          AnalysisScope.createJavaAnalysisScope();
//      ClassLoaderReference loader = scope.getLoader(AnalysisScope.APPLICATION);
//
//      addClassPathToScope(appJar, scope, loader);
//            File file = new File("C:/walaPDS/src/main/resources/Java60RegressionExclusions.txt");
            AnalysisScope scope = makeJavaBinaryAnalysisScope(appJar, new FileProvider().getFile(CallGraphTestUtil.REGRESSION_EXCLUSIONS));

            // generate a WALA-consumable wrapper around the incoming scope object

            ClassHierarchy cha = ClassHierarchyFactory.make(scope);
            Iterable<Entrypoint> entrypoints =
                    com.ibm.wala.ipa.callgraph.impl.Util.makeMainEntrypoints(scope, cha, mainClass);
            AnalysisOptions options = CallGraphTestUtil.makeAnalysisOptions(scope, entrypoints);
            SSAOptions ssaOptions = new SSAOptions();

            CallGraphBuilder<InstanceKey> builder =
                    Util.makeZeroOneCFABuilder(Language.JAVA, options, new AnalysisCacheImpl(), cha, scope);
            CallGraph cg = builder.makeCallGraph(options, new NullProgressMonitor());
            final PointerAnalysis<InstanceKey> pointerAnalysis = builder.getPointerAnalysis();
//            SDG<?> sdg = new SDG<>(cg, pointerAnalysis, dOptions, cOptions);
//            try {
//                GraphIntegrity.check(sdg);
//            } catch (UnsoundGraphException e1) {
//                e1.printStackTrace();
//                Assertions.UNREACHABLE();
//            }
//
//            System.err.println(sdg);

            ArrayList<IR> ir = new ArrayList();

            // Create IR from each instruction.
            for (IClass c: cha) {
                for (IMethod m: c.getDeclaredMethods()) {
                    try {
                        if (!m.getDeclaringClass().getClassLoader().toString().equals("Primordial")
                        && !m.getDeclaringClass().getClass().toString().equals("LFieldsExample")) {
                            System.out.println(m.getDeclaringClass().toString());
                            ir.add(irFactory.makeIR((ShrikeCTMethod) m, Everywhere.EVERYWHERE, options.getSSAOptions()));
                        }
                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                }
            }

            // Convert WALA IR to SPDS nodes.
            Multimap<Node<WALAIRtoNodeTranslator.Stmt, WALAIRtoNodeTranslator.Variable>, State> successorMap = new WALAIRtoNodeTranslator().createSuccessorMapFromIR(ir);

            Properties p = null;
            try {
                p = WalaExamplesProperties.loadProperties();
                p.putAll(WalaProperties.loadProperties());
            } catch (WalaException e) {
                e.printStackTrace();
                Assertions.UNREACHABLE();
            }
            String psFile = p.getProperty(WalaProperties.OUTPUT_DIR) + File.separatorChar + PDF_FILE;

            String dotExe = p.getProperty(WalaExamplesProperties.DOT_EXE);
//            Graph<Statement> g = pruneSDG(sdg);
//            DotUtil.dotify(g, makeNodeDecorator(), PDFTypeHierarchy.DOT_FILE, psFile, dotExe);

            String gvExe = p.getProperty(WalaExamplesProperties.PDFVIEW_EXE);
            return PDFViewUtil.launchPDFView(psFile, gvExe);

        } catch (WalaException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            return null;
        }
    }

    private static Graph<Statement> pruneSDG(final SDG<?> sdg) {
        Predicate<Statement> f =
                s -> {
                    if (s.getNode().equals(sdg.getCallGraph().getFakeRootNode())) {
                        return false;
                    } else if (s instanceof MethodExitStatement || s instanceof MethodEntryStatement) {
                        return false;
                    } else {
                        return true;
                    }
                };
        return GraphSlicer.prune(sdg, f);
    }

    private static NodeDecorator<Statement> makeNodeDecorator() {
        return s -> {
            switch (s.getKind()) {
                case HEAP_PARAM_CALLEE:
                case HEAP_PARAM_CALLER:
                case HEAP_RET_CALLEE:
                case HEAP_RET_CALLER:
                    HeapStatement h = (HeapStatement) s;
                    return s.getKind() + "\\n" + h.getNode() + "\\n" + h.getLocation();
                case EXC_RET_CALLEE:
                case EXC_RET_CALLER:
                case NORMAL:
                case NORMAL_RET_CALLEE:
                case NORMAL_RET_CALLER:
                case PARAM_CALLEE:
                case PARAM_CALLER:
                case PHI:
                default:
                    return s.toString();
            }
        };
    }

    static void validateCommandLine(Properties p) {
        if (p.get("appJar") == null) {
            throw new UnsupportedOperationException("expected command-line to include -appJar");
        }
        if (p.get("mainClass") == null) {
            throw new UnsupportedOperationException("expected command-line to include -appJar");
        }
    }
}
