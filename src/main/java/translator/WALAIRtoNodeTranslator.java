package translator;


import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

import com.ibm.wala.cast.ir.ssa.AstPropertyRead;
import com.ibm.wala.cast.ir.ssa.AstPropertyWrite;
import com.ibm.wala.cast.ir.ssa.SSAConversion;
import com.ibm.wala.cast.js.ssa.*;
import com.ibm.wala.dalvik.dex.instructions.Instruction;
import com.ibm.wala.dalvik.dex.instructions.PutField;
import com.ibm.wala.ssa.*;
import sync.pds.solver.OneWeightFunctions;
import sync.pds.solver.SyncPDSSolver;
import sync.pds.solver.WeightFunctions;
import sync.pds.solver.nodes.*;
import wpds.impl.SummaryNestedWeightedPAutomatons;
import wpds.impl.Weight;
import wpds.interfaces.Location;
import wpds.interfaces.State;
import wpds.wildcard.ExclusionWildcard;
import wpds.wildcard.Wildcard;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;

public class WALAIRtoNodeTranslator extends Instruction.Visitor implements JSInstructionVisitor {


    public static final Multimap<Node<Stmt, Variable>, State> successorMap = HashMultimap.create();
    public static final HashSet<String> parameters = new HashSet<>(); // For adding parameters invoked by call
    public static final HashSet<String> inSet = new HashSet<>();
    public static Boolean conditioned = false;  // Check if the statement we're visiting is conditioned
    public static String targetMethod = "foo"; // TODO: Handle this programmatically

    // Creates successor map similar to SPDS example.
    public Multimap<Node<Stmt, Variable>, State> createSuccessorMapFromIR(ArrayList<IR> irArrayList) {
        for (IR ir: irArrayList) {
            SSAInstruction[] ssaInstructions = ir.getInstructions();
            int recentIndex = 0;
            for (SSAInstruction ssaInstruction: ssaInstructions) {
                try {
                    // Don't know which visit method is for static gets and puts
                    // TODO: Fix this
                    if (ssaInstruction.toString().contains("static")) {
                        for (String var : parameters) {
                            if (successorMap.containsKey(node(recentIndex, var))) {
                                visitInstruction(node(recentIndex+1, var));
                            }
                        }
                        recentIndex++;
                        continue;
                    }

                    System.out.println("Inst index: " + ssaInstruction.iIndex());
                    System.out.println(ssaInstruction.toString());
                    ssaInstruction.visit(this);
                    recentIndex = ssaInstruction.iIndex();

                } catch (Exception e) {
                    System.out.println(recentIndex+1);
                    for (String var : parameters) {
                        if (successorMap.containsKey(node(recentIndex, var))) {
                            visitInstruction(node(recentIndex+1, var));
                        }
                    }
                    recentIndex++;
                }
            }
        }

        // DEBUG
        solver.solve(node(1, "1"));
        System.out.println(solver.getReachedStates());
        solver.debugOutput();



        return successorMap;
    }

    // Method for normals; propogate facts down
    // TODO: make this more efficient by passing in parameters
    public void visitInstruction(Node node1) {
        Node<Stmt, Variable> currNode = node1;

        // Add initial rule if empty
        if (successorMap.isEmpty()) {
            int node2stmt = Integer.parseInt(node1.stmt().toString()) + 1;
            String node2var = node1.fact().toString();
            Node<Stmt, Variable> node2 = node(node2stmt, node2var);
            addNormal(node1, node2);

            System.out.println("INIT NORMAL: (" + node1.fact().toString() + "@" + node1.stmt() + ", " + "*) ->"
                    + "(" + node2var + "@" + node2stmt + ", " + "*)");

            currNode = node2;
        }

        int node3stmt = Integer.parseInt(currNode.stmt().toString()) + 1;
        String node3var = currNode.fact().toString();
        Node<Stmt, Variable> node3 = node(node3stmt, node3var);
        addNormal(currNode, node3);
        System.out.println("NORMAL: (" + currNode.fact().toString() + "@" + currNode.stmt() + ", " + "*) ->"
                + "(" + node3var + "@" + node3stmt + ", " + "*)");
    }

    public void visitCondInstruction(Node node1, int target) {
        Node<Stmt, Variable> currNode = node1;

        int node3stmt = Integer.parseInt(currNode.stmt().toString()) + 1;
        String node3var = currNode.fact().toString();
        Node<Stmt, Variable> node3 = node(node3stmt, node3var);
        Node<Stmt, Variable> targNode = node(target, node3var);
//        addNormal(currNode, node3);

        // add target
        addNormal(currNode, targNode);

//        System.out.println("NORMAL: (" + currNode.fact().toString() + "@" + currNode.stmt() + ", " + "*) ->"
//                + "(" + node3var + "@" + node3stmt + ", " + "*)");
        System.out.println("NORMAL: (" + currNode.fact().toString() + "@" + currNode.stmt() + ", " + "*) ->"
                + "(" + node3var + "@" + target + ", " + "*)");
    }

    @Override
    public void visitPut(SSAPutInstruction instruction) {
        // e.g) a.g = c
        // a.g
        String var1 = Integer.toString(instruction.getRef());
        int line1 = instruction.iIndex();
        Node<Stmt, Variable> node1 = node(line1, var1);

        // field ref
        FieldRef field = f(instruction.getDeclaredField().getName().toString());

        // c
        String var2 = Integer.toString(instruction.getVal());
        Node<Stmt, Variable> node2 = node(line1 - 1, var2);

        visitInstruction(node2);
        visitInstruction(node1);

        for (String var : parameters) {
            if (successorMap.containsKey(node(instruction.iIndex()-1, var))) {
                visitInstruction(node(instruction.iIndex(), var));
            }
        }

        // TODO: Handle static variables
        if (Integer.parseInt(var1) == -1 || Integer.parseInt(var2) == -1) {
            return;
        }

        addFieldPush(node2, field, node1);

        System.out.println("Field PUSH: (" + var2 + "@" + Integer.toString(line1-1) + ", " + "*) ->"
                + "(" + var1 + "@" + Integer.toString(line1) + ", " + field.toString() + ".*)");
    }

    @Override
    public void visitGet(SSAGetInstruction instruction) {
        // If got to here, means we have a statement involving fields.
        // e.g) e = a.f

        // a.f
        String var1 = Integer.toString(instruction.getDef());
        int line1 = instruction.iIndex();
        Node<Stmt, Variable> node1 = node(line1+1, var1);

        // field ref
        FieldRef field = f(instruction.getDeclaredField().getName().toString());

        // c
        String var2 = Integer.toString(instruction.getRef());
        Node<Stmt, Variable> node2 = node(line1-1, var2);

        // TODO: Handle static variables; need to resolve methods.
        if (Integer.parseInt(var1) == -1 || Integer.parseInt(var2) == -1) {
            return;
        }

        // Check if any normals need to be added
        for (String var : parameters) {
            if (successorMap.containsKey(node(instruction.iIndex()-1, var))) {
                visitInstruction(node(instruction.iIndex(), var));
            }
        }

        addFieldPop(node2 ,field, node1);
        System.out.println("Field POP: (" + var2 + "@" + Integer.toString(line1-1) + ", " + field.toString() + ") ->"
                + "(" + var1 + "@" + Integer.toString(line1) + ", eps)");

    }

    @Override
    public void visitGoto(SSAGotoInstruction instruction) {
        int target = instruction.getTarget();
        for (String var : parameters) {
            if (successorMap.containsKey(node(instruction.iIndex()-1, var))) {
                visitCondInstruction(node(instruction.iIndex(), var), target);
            }
        }
    }

    @Override
    public void visitArrayLoad(SSAArrayLoadInstruction instruction) {
        System.out.println("VISITED ARRAYLOAD INSTRUCTION");

    }

    @Override
    public void visitArrayStore(SSAArrayStoreInstruction instruction) {
        System.out.println("VISITED ARRAYSTORE INSTRUCTION");

    }

    @Override
    public void visitBinaryOp(SSABinaryOpInstruction instruction) {
        System.out.println("VISITED BINARYOP INSTRUCTION");

    }

    @Override
    public void visitUnaryOp(SSAUnaryOpInstruction instruction) {
        System.out.println("VISITED UNARYOP INSTRUCTION");

    }

    @Override
    public void visitConversion(SSAConversionInstruction instruction) {
        System.out.println("VISITED CONVERSION INSTRUCTION");

    }

    @Override
    public void visitComparison(SSAComparisonInstruction instruction) {
        System.out.println("VISITED COMP INSTRUCTION");

    }

    @Override
    public void visitConditionalBranch(SSAConditionalBranchInstruction instruction) {
        for (String var : parameters) {
            if (successorMap.containsKey(node(instruction.iIndex()-1, var))) {
                Node<Stmt, Variable> node = node(instruction.iIndex(), var);
                visitInstruction(node);
                int target = instruction.getTarget();
                visitCondInstruction(node, target);
            }
        }

    }

    @Override
    public void visitSwitch(SSASwitchInstruction instruction) {
        System.out.println("VISITED SWITCH INSTRUCTION");

    }

    @Override
    public void visitReturn(SSAReturnInstruction instruction) {
//        System.out.println("VISITED RET INSTRUCTION");

    }

    @Override
    public void visitInvoke(SSAInvokeInstruction instruction) {
        for (String var : parameters) {
            if (successorMap.containsKey(node(instruction.iIndex()-1, var))) {
                visitInstruction(node(instruction.iIndex(), var));
            }
        }
    }

    @Override
    public void visitNew(SSANewInstruction instruction) {
//        System.out.println("VISITED INVKE INSTRUCTION");

    }

    @Override
    public void visitArrayLength(SSAArrayLengthInstruction instruction) {
        System.out.println("VISITED ARRLENGTH INSTRUCTION");

    }

    @Override
    public void visitThrow(SSAThrowInstruction instruction) {
        System.out.println("VISITED THROW INSTRUCTION");

    }

    @Override
    public void visitMonitor(SSAMonitorInstruction instruction) {
        System.out.println("VISITED MON INSTRUCTION");

    }


    @Override
    public void visitJavaScriptInvoke(JavaScriptInvoke javaScriptInvoke) {
    }

    @Override
    public void visitTypeOf(JavaScriptTypeOfInstruction javaScriptTypeOfInstruction) {
    }

    @Override
    public void visitJavaScriptInstanceOf(JavaScriptInstanceOf javaScriptInstanceOf) {
    }

    @Override
    public void visitWithRegion(JavaScriptWithRegion javaScriptWithRegion) {

    }

    @Override
    public void visitCheckRef(com.ibm.wala.cast.js.ssa.JavaScriptCheckReference javaScriptCheckReference) {
    }

    @Override
    public void visitSetPrototype(com.ibm.wala.cast.js.ssa.SetPrototype setPrototype) {

    }

    @Override
    public void visitPrototypeLookup(com.ibm.wala.cast.js.ssa.PrototypeLookup prototypeLookup) {

    }

    private void addFieldPop(Node<Stmt, Variable> curr, FieldRef ref, Node<Stmt, Variable> succ) {
        addSucc(curr, new PopNode<NodeWithLocation<Stmt, Variable, FieldRef>>(
                new NodeWithLocation<Stmt, Variable, FieldRef>(succ.stmt(), succ.fact(), ref), SyncPDSSolver.PDSSystem.FIELDS));
    }

    private void addFieldPush(Node<Stmt, Variable> curr, FieldRef push, Node<Stmt, Variable> succ) {
        addSucc(curr, new PushNode<Stmt, Variable, FieldRef>(succ.stmt(), succ.fact(), push, SyncPDSSolver.PDSSystem.FIELDS));
    }

    private void addNormal(Node<Stmt, Variable> curr, Node<Stmt, Variable> succ) {
        parameters.add(curr.fact().toString());
        parameters.add(succ.fact().toString());
        addSucc(curr, succ);
    }

    private void addReturnFlow(Node<Stmt, Variable> curr, Variable returns, Stmt returnSite) {
        addSucc(curr, new CallPopNode<Variable, Stmt>(returns, SyncPDSSolver.PDSSystem.CALLS, returnSite));
    }

    private void addCallFlow(Node<Stmt, Variable> curr, Node<Stmt, Variable> succ, Stmt returnSite) {
        addSucc(curr,
                new PushNode<Stmt, Variable, Stmt>(succ.stmt(), succ.fact(), returnSite, SyncPDSSolver.PDSSystem.CALLS));
    }

    private void addSucc(Node<Stmt, Variable> curr, State succ) {
        successorMap.put(curr, succ);
    }

    private void addExcludeField(Node<Stmt, Variable> curr, FieldRef push, Node<Stmt, Variable> succ) {
        addSucc(curr, new ExclusionNode<Stmt, Variable, FieldRef>(succ.stmt(), succ.fact(), push));
    }

    private FieldRef epsilonField = new FieldRef("eps_f");
    private Stmt epsilonCallSite = new Stmt(-1);

    private SyncPDSSolver<Stmt, Variable, FieldRef, Weight.NoWeight> solver = new SyncPDSSolver<Stmt, Variable, FieldRef, Weight.NoWeight>(
            new SingleNode<Variable>(new Variable("u")), new SingleNode<Node<Stmt, Variable>>(node(1, "u")), false,
            new SummaryNestedWeightedPAutomatons<Stmt, INode<Variable>, Weight.NoWeight>(), false,
            new SummaryNestedWeightedPAutomatons<FieldRef, INode<Node<Stmt, Variable>>, Weight.NoWeight>()) {

        @Override
        public void computeSuccessor(Node<Stmt, Variable> node) {
            Collection<State> states = successorMap.get(node);
            for (State s : states) {
                propagate(node, s);
            }
        }

        @Override
        public FieldRef epsilonField() {
            return epsilonField;
        }

        @Override
        public Stmt epsilonStmt() {
            return epsilonCallSite;
        }

        @Override
        public FieldRef emptyField() {
            return new FieldRef("EMPTY_F");
        }

        @Override
        public FieldRef fieldWildCard() {
            return new FieldWildCard();
        }

        @Override
        public FieldRef exclusionFieldWildCard(FieldRef exclusion) {
            return new ExclusionWildcardField(exclusion);
        }

        @Override
        protected WeightFunctions<Stmt, Variable, FieldRef, Weight.NoWeight> getFieldWeights() {
            return new OneWeightFunctions<Stmt, Variable, FieldRef, Weight.NoWeight>(Weight.NoWeight.NO_WEIGHT_ZERO,
                    Weight.NoWeight.NO_WEIGHT_ONE);
        }

        @Override
        protected WeightFunctions<Stmt, Variable, Stmt, Weight.NoWeight> getCallWeights() {
            return new OneWeightFunctions<Stmt, Variable, Stmt, Weight.NoWeight>(Weight.NoWeight.NO_WEIGHT_ZERO,
                    Weight.NoWeight.NO_WEIGHT_ONE);
        }

    };

    // Types defined by SPDS files.
    public Variable var(String v) {
        return new Variable(v);
    }

    public static Stmt returnSite(int call) {
        return new Stmt(call);
    }

    public static FieldRef f(String f) {
        return new FieldRef(f);
    }

    public static Node<Stmt, Variable> node(int stmt, String var) {
        return new Node<Stmt, Variable>(new Stmt(stmt), new Variable(var));
    }

    public static class Stmt extends StringBasedObj implements Location {
        public Stmt(int name) {
            super(Integer.toString(name));
        }
    }

    public static class Variable extends StringBasedObj {
        public Variable(String name) {
            super(name);
        }
    }

    public static class FieldWildCard extends FieldRef implements Wildcard {
        public FieldWildCard() {
            super("*");
        }
    }

    private static class ExclusionWildcardField extends FieldRef implements ExclusionWildcard<FieldRef> {
        private final FieldRef excludes;

        public ExclusionWildcardField(FieldRef excl) {
            super(excl.name);
            this.excludes = excl;
        }

        @Override
        public FieldRef excludes() {
            return (FieldRef) excludes;
        }

        @Override
        public String toString() {
            return "not " + super.toString();
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = super.hashCode();
            result = prime * result + ((excludes == null) ? 0 : excludes.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (!super.equals(obj))
                return false;
            if (getClass() != obj.getClass())
                return false;
            ExclusionWildcardField other = (ExclusionWildcardField) obj;
            if (excludes == null) {
                if (other.excludes != null)
                    return false;
            } else if (!excludes.equals(other.excludes))
                return false;
            return true;
        }

    }

    private static class FieldRef extends StringBasedObj implements Location {
        public FieldRef(String name) {
            super(name);
        }
    }

    private static class StringBasedObj {
        final String name;

        public StringBasedObj(String name) {
            this.name = name;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((name == null) ? 0 : name.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            StringBasedObj other = (StringBasedObj) obj;
            if (name == null) {
                if (other.name != null)
                    return false;
            } else if (!name.equals(other.name))
                return false;
            return true;
        }

        @Override
        public String toString() {
            return name;
        }
    }

    // For readability.
    enum Operations {
        PUT,
        GET
    }
}
