/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.listener;

import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.MONITORENTER;
import gov.nasa.jpf.jvm.bytecode.MONITOREXIT;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.util.DeepClone;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;
import gov.nasa.jpf.vm.bytecode.FieldInstruction;
import gov.nasa.jpf.vm.choice.ThreadChoiceFromSet;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

public class MyListener3 extends PropertyListenerAdapter {

    Node root = null;
    Node current = null;
    volatile private int depth = 0;
    volatile private int id = 0;
    HashMap<Long, Integer> parentLockRemovals = null;
    Set<String> allowDepth = null;
    Set<String> allowChild = null;
    Set<String> allowThreads = null;
    HashMap<String, ArrayList<String>> threadsDepMap = null;
    HashMap<Integer, ArrayList<Integer>> allowedPaths = null;
    int previousId = -1;
    ArrayList<Integer> statesHistory = new ArrayList<Integer>();
    ArrayList<String> statesAction = new ArrayList<String>();
    StateNode rootNode = new StateNode();
    HashMap<Integer, StateNode> stateMap = new HashMap<>();
    ArrayList<Integer> statesExcluded = new ArrayList<Integer>();
    ArrayList<Integer> statesIncluded = new ArrayList<Integer>();
    HashMap<Integer, Node> nodesIncluded = new HashMap<>();
    HashMap<Integer,Boolean> isEndState = new HashMap<>();
    HashMap<Integer,Integer> stateGroups = new HashMap<>();
    HashMap<String,Integer> stateGroupMap = new HashMap<>();
    int endNodes = 0;



    public MyListener3() {
        root = new Node();
        current = new Node();
        current.parent = root;
        root.children.add(current);
        allowedPaths = new HashMap<>();

        if (allowThreads == null && VM.getVM().getConfig().get("vm.allowed.threads") != null) {
            String[] tids = VM.getVM().getConfig().get("vm.allowed.threads").toString().split(",");
            if (tids != null) {
                allowThreads = new HashSet<String>(Arrays.asList(tids));
            }

            if (threadsDepMap == null && VM.getVM().getConfig().get("vm.allowed.threads.seqdeps") != null) {
                String[] deps = VM.getVM().getConfig().get("vm.allowed.threads.seqdeps").toString().split(";");
                if (deps != null) {
                    threadsDepMap = new HashMap<>();
                    for (String s : deps) {
                        String d = s.split(":")[0];
                        String[] depList = s.split(":")[1].split(",");
                        for (String s2 : depList) {
                            if (threadsDepMap.get(s2) == null) {
                                ArrayList<String> d2 = new ArrayList();
                                d2.add(d);
                                threadsDepMap.put(s2, d2);
                            } else {
                                threadsDepMap.get(s2).add(d);
                            }
                        }

                    }
                }
            }
        }

        if (allowedPaths.size() == 0) {
            String[] allowedDepths = null;
            String[] allowedChildren = null;
            if (allowDepth == null && VM.getVM().getConfig().get("vm.parallel.allowed.depth") != null) {
                allowedDepths = VM.getVM().getConfig().get("vm.parallel.allowed.depth").toString().split(",");
                if (allowedDepths != null) {
                    allowDepth = new HashSet<String>(Arrays.asList(allowedDepths));
                }
            }
            if (allowChild == null && VM.getVM().getConfig().get("vm.parallel.allowed.child") != null) {
                allowedChildren = VM.getVM().getConfig().get("vm.parallel.allowed.child").toString().split(",\\[");
                if (allowedChildren != null) {
                    allowChild = new HashSet<String>(Arrays.asList(allowedChildren));
                }
            }

            if (allowDepth != null && allowChild != null) {

                if (allowedDepths.length == allowedChildren.length) {
                    for (int i = 0; i < allowedDepths.length; i++) {
                        String[] depthSeq = allowedDepths[i].split("-");
                        String[] childrenSeq = allowedChildren[i].replaceAll("\\[", "").replaceAll("\\]", "").split(",");

                        ArrayList<Integer> allowedChildrenArray = new ArrayList<>();
                        for (int j = 0; j < childrenSeq.length; j++) {
                            String[] childSeqRange = childrenSeq[j].split("-");
                            for (int k = Integer.parseInt(childSeqRange[0]); k <= Integer.parseInt(childSeqRange[childSeqRange.length - 1]); k++) {
                                allowedChildrenArray.add(k);
                            }
                        }
                        for (int j = Integer.parseInt(depthSeq[0]); j <= Integer.parseInt(depthSeq[depthSeq.length - 1]); j++) {
                            allowedPaths.put(j, allowedChildrenArray);
                            //        System.out.println("j " + j);
                        }
                    }
                } else {
                    System.err.println("Parameters allowed.depth and allowed.child should have the same length.");
                }
            }
        }
       
    }

  
    @Override
    public synchronized void choiceGeneratorSet(VM vm, ChoiceGenerator<?> cg) {
        Search search = vm.getSearch();

        id = search.getStateId();
        depth = search.getDepth();

  

        boolean found = current.findNode(id, depth);
    

        if (!found) {

            Node newN = new Node();
            newN.parent = current;
         
            newN.depth = depth;
            newN.id = id;
            newN.threadAccessed = (ArrayList<String>) current.threadAccessed.clone();

            if (cg instanceof ThreadChoiceFromSet) {

                ThreadInfo[] threads = ((ThreadChoiceFromSet) cg).getAllThreadChoices();
                for (int i = 0; i < threads.length; i++) {
                    ThreadInfo ti = threads[i];
                    if (!ti.hasChanged() && (threadsDepMap == null || threadsDepMap.get(search.getVM().getCurrentThread().getName()) == null)) {
                       continue;
                    }
                    if (allowThreads != null && !allowThreads.contains(ti.getName()) && (threadsDepMap == null || threadsDepMap.get(search.getVM().getCurrentThread().getName()) == null)) {
                        continue;
                    }

                    if (allowDepth != null && allowChild != null && allowedPaths.size() != 0) {
                        if (allowedPaths.containsKey(depth)) {
                            //       System.out.println("allowDepth " + allowedPaths.containsKey(depth) + " " + depth + " " + current.children.size() + " " + allowedPaths.get(depth).contains(current.children.size()) + " " + id + " " + ti.getName());
                            if (!allowedPaths.get(depth).contains(current.children.size())) {
                                ti.breakTransition(true);
            
                                continue;
                            }

                        }
                    }

                    Instruction insn = ti.getPC();

               /*     if (insn instanceof MONITORENTER) {
                        Data newD = new Data();
                        newD.locks = newN.getParentLockInfo(ti.getName(), current);
                        newD.lockRemovals = parentLockRemovals;

                        newD.fileLocation = insn.getFileLocation();
                        newD.lineNumber = insn.getLineNumber();
                        newD.methodName = insn.getMethodInfo().getName();
                        newD.className = insn.getMethodInfo().getClassName();
                        newD.packageName = insn.getMethodInfo().getClassInfo().getPackageName();
                        newD.isSynchronized = insn.getMethodInfo().isSynchronized();
                        newD.threadName = ti.getName();
                        if (!newN.threadAccessed.contains(ti.getName())) {
                            newN.threadAccessed.add(ti.getName());
                        }
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();

                        MONITORENTER mentsinsn = (MONITORENTER) insn;
                        newD.isMonitorEnter = true;
                        newD.lockRef = mentsinsn.getLastLockRef();
                        newD.sourceLine = mentsinsn.getSourceLine();

                        newN.addThreadLock(newD, newD.threadName, newD.lockRef);
                        newN.data.add(newD);
                    }

                    if (insn instanceof MONITOREXIT) {
                        Data newD = new Data();
                        newD.locks = newN.getParentLockInfo(ti.getName(), current);
                        newD.lockRemovals = parentLockRemovals;

                        newD.fileLocation = insn.getFileLocation();
                        newD.lineNumber = insn.getLineNumber();
                        newD.methodName = insn.getMethodInfo().getName();
                        newD.className = insn.getMethodInfo().getClassName();
                        newD.packageName = insn.getMethodInfo().getClassInfo().getPackageName();
                        newD.isSynchronized = insn.getMethodInfo().isSynchronized();
                        newD.threadName = ti.getName();
                        if (!newN.threadAccessed.contains(ti.getName())) {
                            newN.threadAccessed.add(ti.getName());
                        }
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();

                        MONITOREXIT mexinsn = (MONITOREXIT) insn;
                        newD.isMonitorExit = true;
                        newD.lockRef = mexinsn.getLastLockRef();
                        newD.sourceLine = mexinsn.getSourceLine();

                        newN.removeThreadLock(newD, newD.threadName, newD.lockRef);
                        newN.data.add(newD);
                    }

                    /*    if (insn instanceof InvokeInstruction) {
                        System.out.println("!!!!!!!!!!! InvokeInstruction : " + ((InvokeInstruction) insn).getInvokedMethodName());
                    }*/
                //    if (insn instanceof ReadOrWriteInstruction) {
                   //     System.out.println("ReadOrWriteInstruction " + id);
               //     }
                    if (insn instanceof FieldInstruction) { // Ok, its a get/putfield

                        Data newD = new Data();
                        newD.locks = newN.getParentLockInfo(ti.getName(), current);
                        newD.lockRemovals = parentLockRemovals;

                        newD.fileLocation = insn.getFileLocation();
                        newD.lineNumber = insn.getLineNumber();
                        newD.methodName = insn.getMethodInfo().getName();
                        newD.isSynchronized = insn.getMethodInfo().isSynchronized();
                        newD.threadName = ti.getName();
                        if (!newN.threadAccessed.contains(ti.getName())) {
                            newN.threadAccessed.add(ti.getName());
                        }
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();

                        FieldInstruction finsn = (FieldInstruction) insn;

                        if (finsn.isRead()) {
                            newD.readOperation = true;
                        } else {
                            newD.writeOperation = true;
                        }
                        FieldInfo fi = finsn.getFieldInfo();

                        newD.threadName = ti.getName();
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();
                        newD.className = fi.getClassInfo().getSimpleName();
                        newD.packageName = fi.getClassInfo().getPackageName();
                        newD.fieldName = fi.getFullName();
                        newD.value = String.valueOf(finsn.getLastValue());
                        newD.type = finsn.getFieldInfo().getType();
                        newD.sourceLine = finsn.getSourceLine();

                        if (newD.fieldName.compareTo("gr.uop.gr.javamethodsjpf.ReentrantLock.num") == 0 && newD.writeOperation) {
                            if (newD.methodName.compareTo("lock") == 0) {
                                newN.addThreadLock(newD, newD.threadName, newD.instance);
                                //    System.out.println("-------- : " + newD.instance);
                            } else if (newD.methodName.compareTo("unlock") == 0) {
                                if (newN.removeThreadLock(newD, newD.threadName, newD.instance)) {
                                    if (newD.lockRemovals.get(newD.instance) != null) {
                                        newD.lockRemovals.put(newD.instance, (int) newD.lockRemovals.get(newD.instance) + 1);
                                    } else {
                                        newD.lockRemovals.put(newD.instance, 1);
                                    }
                                }

                            }
                        }

                   
                        newN.data.add(newD);
                    }

                }
                if (newN.data != null && newN.data.size() != 0) {
                current.children.add(newN);
                current = newN;
                statesIncluded.add(cg.getStateId());
                String nodeMap = newN.data.get(0).threadName + " " + newN.data.get(0).fieldName;
                if(!stateGroupMap.containsKey(nodeMap)){
                    stateGroupMap.put(nodeMap, cg.getStateId());
                    stateGroups.put(cg.getStateId(), cg.getStateId());
                }else {
                    if (!stateGroups.containsKey(cg.getStateId())) {
                        int keyNode = stateGroupMap.get(nodeMap);
                        stateGroups.put(cg.getStateId(), keyNode);
                    }
                }
                nodesIncluded.put(cg.getStateId(), newN);
            } else {
                current.children.add(newN);
                current = newN;
                statesExcluded.add(cg.getStateId());
            }
            }
       
            
            previousId = id;
        }
    }

   

    //--- the ones we are interested in
    @Override
    public synchronized void searchStarted(Search search) {
        System.out.println("----------------------------------- search started");
    }

    @Override
    public synchronized void stateAdvanced(Search search) {



        synchronized (this) {
            statesHistory.add(search.getVM().getStateId());
            statesAction.add("advanced " + search.getVM().isEndState());
        }

        if (allowThreads != null) {
            if (!allowThreads.contains(search.getVM().getCurrentThread().getName()) && (threadsDepMap == null || threadsDepMap.get(search.getVM().getCurrentThread().getName()) == null)) {

                search.getVM().ignoreState();
            } else if (!allowThreads.contains(search.getVM().getCurrentThread().getName())) {
                if (threadsDepMap != null && threadsDepMap.get(search.getVM().getCurrentThread().getName()) != null) {
                    current.findNode(search.getStateId(), search.getDepth());
                    boolean canBeTerminated = true;
                    for (String t : threadsDepMap.get(search.getVM().getCurrentThread().getName())) {
                        //        System.out.println("t " + t);
                        if (!current.threadAccessed.contains(t)) {
                            canBeTerminated = false;
                            break;
                        }
                    }
                    if (canBeTerminated) {
                        search.getVM().ignoreState();

                    }
                }
            }
        }
    }

    @Override
    public synchronized void stateBacktracked(Search search) {
        synchronized (this) {
            statesHistory.add(search.getVM().getStateId());
            statesAction.add("backtracked " + search.getVM().isEndState());
        }


    }

    @Override
    public synchronized void searchFinished(Search search) {
        System.out.println("----------------------------------- search finished");

        rootNode.stateId = 0;
        stateMap.put(0, rootNode);
        HashMap<Integer,HashMap<Integer,Boolean>> stateGraph = new HashMap();
        HashMap<Integer,Boolean> isUsed = new HashMap<>();
        
        HashMap<Integer,Boolean> isRootParent = new HashMap<>();
        HashMap<Integer,ArrayList<Integer>> reUsed = new HashMap<>();
        
        int parentId = -100;

        int x = 0;
        for (int state : statesHistory) {
            System.out.println("state : " + state + " parentId : " + parentId);
            String action = statesAction.get(x);
            
            if (state >= 0) {
                if (action.contains("advanced") && state > parentId) {
                    if (stateGraph.get(state)==null)
                        stateGraph.put(state, new HashMap<>());
                    
                        if(parentId>=0) {
                            stateGraph.get(parentId).put(state, statesIncluded.contains(state));
                            isRootParent.put(state, Boolean.FALSE);
                        }else{
                            isRootParent.put(state, Boolean.TRUE);
                        }
                        
                        if (statesIncluded.contains(state)) {
                            isUsed.put(state, Boolean.TRUE);
                        }else{
                            isUsed.put(state, Boolean.FALSE);
                        }

                        if (action.contains("true")) {
                            isEndState.put(state, Boolean.TRUE);
                            endNodes=endNodes+1;
                        }else {
                            isEndState.put(state, Boolean.FALSE);
                        }

                        parentId = state;

                        
                    } else if (action.contains("advanced") && state <= parentId) {
                        if(reUsed.get(state)==null) {
                            reUsed.put(state, new ArrayList<>());
                        }
                        reUsed.get(state).add(parentId);
                        
                    
                        if (statesIncluded.contains(state) && !statesIncluded.contains(parentId)) {
                            for(int k : stateGraph.get(state).keySet()){
                                if (!stateGraph.get(parentId).keySet().contains(k)) {
                                    stateGraph.get(parentId).put(k, stateGraph.get(state).get(k));
                                }
                            }
                            System.out.println("state matching 1");
                        }else if(!statesIncluded.contains(state) && statesIncluded.contains(parentId)) {
                            stateGraph.get(parentId).put(state, statesIncluded.contains(state));
                            System.out.println("state matching 2");
                        }else {
            
                            for(int k : stateGraph.get(state).keySet()){
                                if (!stateGraph.get(parentId).keySet().contains(k)) {
                                    stateGraph.get(parentId).put(k, stateGraph.get(state).get(k));
                                }
                            }
                        }
                        
                        
                        System.out.println("state matching : " + parentId + " " + state );
                        parentId = state;

                    }

                    if (action.contains("backtracked")) {
                        System.out.println("backtrack... ");
                        
      
                        parentId = state;

                    }

                    
                    
            }
            x++;
        }
        
       
        HashMap<Integer,HashMap<Integer,Boolean>> stateGraph2 = new HashMap();
        stateGraph2 = stateGraph;
        
        ArrayList<ArrayList<Integer>> paths = new ArrayList();
        
        for (Integer key : stateGraph2.keySet()) {
            if(isRootParent.get(key)) {
                ArrayList<Integer> path = new ArrayList();
                if(isUsed.get(key))
                    path.add(key);
                calculatePaths(stateGraph2,path,paths,key);
            }
        }
        

        ArrayList<ArrayList<Node>> nodePaths = new ArrayList();
        int ss = paths.size();
        System.out.println("ss : " + ss);
        for (int n=0; n < ss; n++) {
            ArrayList<Integer> pathI = paths.get(n);
            
                
                    ArrayList<Node> nodePath = new ArrayList<>();
                    for(int i=0; i<pathI.size(); i++) {
                        nodePath.add(nodesIncluded.get(pathI.get(i)));
                    }
                    
                    int snp = nodePaths.size();
                    boolean exclude = false;
                    for(int m=0; m<snp; m++) {
                        if(!exclude && nodePaths.get(m).size()==nodePath.size()) {
                            int nps = nodePath.size();
                            int exclNum = 0;
                            for(int nn=0; nn<nps; nn++) {
                                if(nodePaths.get(m).get(nn).data.get(0).threadName.compareTo(nodePath.get(nn).data.get(0).threadName)==0 &&
                                   nodePaths.get(m).get(nn).data.get(0).fieldName.compareTo(nodePath.get(nn).data.get(0).fieldName)==0 ){
                                   exclNum++;
                                }
                                if(exclNum==nps) {
                                   exclude = true;
                                   break;
                                }
                            }
                            
                        }
                    }
                    
                    if(!exclude) {
                        nodePaths.add(nodePath);
                    }

            
        }
        
        System.out.println("@@@@@@ Paths Size : " + paths.size() + " " + nodePaths.size());
        
  
        int snp = nodePaths.size();
        for(int m=0; m<snp; m++) {
            int nps = nodePaths.get(m).size();
            for(int nn=0; nn<nps; nn++) {
                System.out.print(nodePaths.get(m).get(nn).data.get(0).threadName + "," + nodePaths.get(m).get(nn).data.get(0).fieldName + " ");
            }
            System.out.println();
        }

        
        
        System.out.println("used vs unused : " + stateMap.size() + " " + statesExcluded.size());
        

        
        rootNode.depth=0;

        System.out.println(rootNode.stateId + " root children : " + rootNode.children.size());
        
        
        
        System.out.println("End Node Num : " + endNodes);
        
        
        rootNode.currentSubpathNodes=0;
        
        
        System.out.println("Path Num : " + rootNode.currentSubpathNodes);



        try {
            printTree(root);
         //   Thread.sleep(10000);
            //      printGraph();

        checkFieldRule2(root,new HashMap<String,FieldState>());
//

        } catch (Exception ex) {
            Logger.getLogger(MyListener3.class.getName()).log(Level.SEVERE, null, ex);
        }

    }
    

    private void calculatePaths(HashMap<Integer,HashMap<Integer,Boolean>> stateGraph2, ArrayList<Integer> path, ArrayList<ArrayList<Integer>> paths,int key) {
           
        ArrayList<Integer> path2 = new ArrayList();
        for(int x : path){
            path2.add(x);
        }

        HashMap<Integer,Boolean> neighbours = stateGraph2.get(key);
        
        if(!neighbours.keySet().isEmpty()) {
            for(int x:neighbours.keySet()) {
                path2.add(x);
                if(!isEndState.get(x)) {
                    calculatePaths(stateGraph2,path2,paths,x);
                
                    path2.remove(path2.get(path2.size()-1));
                }else if(isEndState.get(x)){
                    int s = path2.size();
            
                    for(int ii = 0; ii < s; ii++ ) {
                            int value = path2.get(ii);
                            if(!statesIncluded.contains(value)) {
                                path2.remove(ii);
                                ii--;
                                s--;

                            }else{
                                int node = path2.remove(ii);
                                path2.add(ii, stateGroups.get(node));

                            }
                        }

                    s = path2.size();
                        
                        boolean exists = false;
                        for(int m=0; m<paths.size(); m++) {
                            if(paths.get(m).equals(path2)) {
                                exists=true;
                                break;
                            }
                        }
                        if(!exists && path2.size()!=0) {
                            paths.add(path2);
                        }
            
                }
            }
        }
        
    }
        

    
  

    public void printTree(Node myNode) {

        List<Data> ld = myNode.data;

        System.out.println();
        System.out.print("id : " + myNode.id);
        System.out.print(" depth : " + myNode.depth);

        for (Data d : ld) {

            System.out.print(" fieldName : " + d.fieldName);
            System.out.print(" lineNumber : " + d.lineNumber);
            System.out.print(" methodName : " + d.methodName);
            System.out.print(" className : " + d.className);
            System.out.print(" instance : " + d.instance);
            System.out.print(" writeOperation : " + d.writeOperation);
            System.out.print(" readOperation : " + d.readOperation);
            System.out.print(" threadName : " + d.threadName);
            System.out.print(" isSynchronized : " + d.isSynchronized);
            System.out.print(" packageName : " + d.packageName);
            System.out.print(" fileLocation : " + d.fileLocation);
            System.out.print(" isMonitorEnter : " + d.isMonitorEnter);
            System.out.print(" isMonitorExit : " + d.isMonitorExit);
            System.out.print(" lockRef : " + d.lockRef);
            System.out.print(" value : " + d.value);
            System.out.print(" type : " + d.type);
            System.out.print(" sourceLine : " + d.sourceLine);
            System.out.print(" locks : " + (d.locks != null ? d.locks.toString() : null));
            System.out.print(" lockRemovals : " + (d.lockRemovals != null ? Arrays.asList(d.lockRemovals) : null));
        }

        for (Node nd : myNode.children) {
            printTree(nd);
        }
    }

    public void printData(Data d) {
        System.out.println();
        System.out.print(" fieldName : " + d.fieldName);
        System.out.print(" lineNumber : " + d.lineNumber);
        System.out.print(" methodName : " + d.methodName);
        System.out.print(" className : " + d.className);
        System.out.print(" instance : " + d.instance);
        System.out.print(" writeOperation : " + d.writeOperation);
        System.out.print(" readOperation : " + d.readOperation);
        System.out.print(" threadName : " + d.threadName);
        System.out.print(" isSynchronized : " + d.isSynchronized);
        System.out.print(" packageName : " + d.packageName);
        System.out.print(" fileLocation : " + d.fileLocation);
        System.out.print(" isMonitorEnter : " + d.isMonitorEnter);
        System.out.print(" isMonitorExit : " + d.isMonitorExit);
        System.out.print(" lockRef : " + d.lockRef);
        System.out.print(" value : " + d.value);
        System.out.print(" type : " + d.type);
        System.out.print(" sourceLine : " + d.sourceLine);
        System.out.print(" locks : " + (d.locks != null ? d.locks.toString() : null));
        System.out.print(" lockRemovals : " + (d.lockRemovals != null ? Arrays.asList(d.lockRemovals) : null));
    }


    public void checkRule(Node myNode, Rule checkRule, HashMap<String, Rule> states) {

        List<Data> ld = myNode.data;
        Rule state;

        for (Data d : ld) {
            if (states.containsKey(d.threadName)) {
                state = states.get(d.threadName);
            } else {
                states.put(d.threadName, new Rule());
                state = states.get(d.threadName);
                state.accessSeq = (ArrayList<String>) checkRule.accessSeq.clone();
            }

            if (d.fieldName != null && d.fieldName.compareTo(checkRule.field) == 0 && state.isIfIncluded == false && d.sourceLine.contains("if")) {
                state.field = d.fieldName;
                state.isIfIncluded = true;
            }

            if (state.isIfIncluded) {
                if (d.fieldName != null && d.fieldName.compareTo(checkRule.field) == 0) {
                    if (state.accessSeq.isEmpty() == false && state.accessSeq.get(0).compareTo("r") == 0 && d.readOperation == true) {
                        state.accessSeq.remove(0);
                    } else if (state.accessSeq.isEmpty() == false && state.accessSeq.get(0).compareTo("w") == 0 && d.writeOperation == true) {
                        state.accessSeq.remove(0);
                    } else if (state.accessSeq.isEmpty() == false && state.accessSeq.get(0).compareTo("r") == 0 && d.writeOperation == true) {
                        state = new Rule();
                        state.accessSeq = (ArrayList<String>) checkRule.accessSeq.clone();
                        continue;
                    }
                }

                if (d.fieldName != null && d.fieldName.compareTo(checkRule.lock) == 0) {
                    if (state.accessSeq.isEmpty() == false && state.accessSeq.get(0).compareTo("u") == 0 && d.sourceLine.contains("unlock")) {
                        state.accessSeq.remove(0);
                    } else if (state.accessSeq.isEmpty() == false && state.accessSeq.get(0).compareTo("l") == 0 && d.sourceLine.contains("lock")) {
                        state.accessSeq.remove(0);
                    }
                }
            }

            if (state.accessSeq.isEmpty() && state.isIfIncluded == checkRule.isIfIncluded && state.field.compareTo(checkRule.field) == 0) {
                System.out.println("Error pattern detected... " + d.lineNumber + " " + d.className);
                System.exit(-1);
            }
        }

        for (Node nd : myNode.children) {
            checkRule(nd, checkRule, states);
        }
    }

    class Rule {

        String threadName = null;
        String field = null;
        String lock = null;
        boolean isIfIncluded = false;
        ArrayList<String> accessSeq = new ArrayList<>();

        public void check() {

        }
    }

    class StateNode {

        int stateId = -1;
        int depth=-1;
        int currentSubpathNodes = 0;
        boolean visited = false;
        boolean isEndState = false;
        boolean isStateMatch = false;
        int realParent = -1;
        ArrayList<Integer> parrents = new ArrayList<>();
        ArrayList<Integer> children = new ArrayList<>();
    }
    
    private StateNode deepCloneStateNode(StateNode origin) {
        StateNode clone = new StateNode();
        clone.stateId = origin.stateId;
        clone.depth = origin.depth;
        clone.currentSubpathNodes = origin.currentSubpathNodes;
        clone.visited = origin.visited;
        clone.isEndState = origin.isEndState;
        clone.parrents = DeepClone.deepClone(origin.parrents);
        clone.children = DeepClone.deepClone(origin.children);
        
        return clone;
    }

    class Node {

        protected List<Data> data = new ArrayList<Data>();
        protected ArrayList<String> threadAccessed = new ArrayList<>();
        protected Node parent = null;
        protected List<Node> children = new ArrayList<Node>();
        protected int id = 0;
        protected int depth = 0;
        protected boolean locksSearched = false;

        public ArrayList<Long> getParentLockInfo(String thread, Node parent) {
            ArrayList<Long> parentLocks = null;

            if (parent != null) {
                Node nd = parent;

                for (Data d : nd.data) {
                    if (d.threadName.compareTo(thread) == 0 && d.locks != null) {
                        parentLocks = (ArrayList<Long>) d.locks.clone();
                        parentLockRemovals = new HashMap<>();
                        if (d.lockRemovals != null) {
                            parentLockRemovals.putAll(d.lockRemovals);
                        }
                        //    System.out.println("parentLocks : " + parentLocks.toString());
                        break;
                    }
                }

                if (parentLocks == null && nd.parent != null && !locksSearched) {
                    locksSearched = true;
                    parentLocks = getParentLockInfo(thread, nd.parent);
                    locksSearched = false;
                }
            }

            return parentLocks;
        }

        public void addThreadLock(Data d, String thread, long lockInstance) {
            ArrayList<Long> locks = d.locks;
            if (locks == null) {
                locks = new ArrayList<>();
                d.locks = locks;
            }

            if (!locks.contains(lockInstance)) {
                locks.add(lockInstance);
            }
        }

        public boolean removeThreadLock(Data d, String thread, long lockInstance) {
            boolean removal = false;
            ArrayList<Long> locks = d.locks;
            if (locks != null) {
                if (locks.remove(lockInstance)) {
                    removal = true;
                }
            }

            return removal;

        }

        public boolean findNode(int id, int depth) {
            boolean found = false;

            while (current.depth >= depth && current.depth != 0) {
                current = current.parent;
            }

            if (current.id != id) {
                for (Node nd : current.children) {
                    if (nd.id == id) {
                        current = nd;
                        found = true;
                        break;
                    }
                }
            } else {
                found = true;
            }

            return found;
        }

        public Node findNode(int id, int depth, Node parentNode) {
            Node found = parentNode;

            if (found.id != id) {
                for (Node nd : found.children) {
                    if (nd.id == id) {
                        found = nd;
                        //    System.out.println("Found .....");
                        break;
                    } else {
                        if (nd.depth > depth) {
                            break;
                        }
                        found = findNode(id, depth, nd);
                    }
                }
            }

            return found;
        }
    }

    class Data {

        String fieldName = null;
        String className = null;
        long instance = 0;
        boolean writeOperation = false;
        boolean readOperation = false;
        String threadName = null;
        String methodName = null;
        int threadId = -1;
        boolean isSynchronized = false;
        String fileLocation = null;
        int lineNumber = -1;
        String packageName = null;
        String value = null;
        String type = null;
        boolean isMonitorEnter = false;
        boolean isMonitorExit = false;
        int lockRef = -1;
        String sourceLine = null;
        ArrayList<Long> locks = new ArrayList<>();
        HashMap<Long, Integer> lockRemovals = new HashMap<>();
    }

    public void checkFieldRule(Node myNode, HashMap<String, FieldState> fieldStates) {
        // Set the field rule to check
        ArrayList<String> checkFieldRule = new ArrayList<>();
        checkFieldRule.add("readField");
        checkFieldRule.add("threadChange");
        checkFieldRule.add("writeField");
        checkFieldRule.add("threadBack");
        checkFieldRule.add("writeField");

        List<Data> ld = myNode.data;
        FieldState state = null;

        for (Data d : ld) {
            if (d.fieldName != null) {
                if (fieldStates.containsKey(d.fieldName)) {
                    state = fieldStates.get(d.fieldName);
                } else {
                    fieldStates.put(d.fieldName, new FieldState());
                    state = fieldStates.get(d.fieldName);
                    state.resetFieldRule(checkFieldRule);
        

                }

                if (d.readOperation && state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("readField") == 0) {
                    state.threadSeq.add(d.threadName);
                    state.checkFieldRule.remove(0);
                    state.lineNumberSeq.add(d.lineNumber);
                    state.allThreadSeq.add(d.threadName);
                    state.parentId = myNode.id;
                    state.parentDepth = myNode.depth;
                    fieldStates.replace(d.fieldName, state);
              
                } else if (state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadChange") == 0 && state.checkFieldRule.get(1).compareTo("writeField") == 0) {
                    if (!state.threadSeq.contains(d.threadName) && d.writeOperation) {
                        for (Node nd : myNode.children) {
                            checkFieldRule(nd, deepCloneStates(fieldStates));
                        }
                        state.checkFieldRule.remove(0);
                        state.checkFieldRule.remove(0);
                        state.lineNumberSeq.add(d.lineNumber);
                        state.allThreadSeq.add(d.threadName);
          
                    } else if (state.threadSeq.contains(d.threadName) && d.writeOperation) {
                        state.resetFieldRule(checkFieldRule);
                        if (state.parentId != -1) {
                            Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                            for (Node nd : parentNd.children) {
                                checkFieldRule(nd, deepCloneStates(fieldStates));
                            }
                        }
                        state.parentId = -1;
                        
                    }
                } else if (state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadBack") == 0 && state.checkFieldRule.get(1).compareTo("writeField") == 0) {
                    if (state.threadSeq.get(0).compareTo(d.threadName) == 0 && d.writeOperation) {
                        state.checkFieldRule.remove(0);
                        state.checkFieldRule.remove(0);
                        state.lineNumberSeq.add(d.lineNumber);
                        state.allThreadSeq.add(d.threadName);
                 
                    }
                }

                if (state != null && state.checkFieldRule.isEmpty()) {
                    //    if(d.fieldName.compareTo("gr.uop.intermittent.faults.symbiosistest.TestClass.filled")==0) 
                    System.out.println("Error pattern detected... " + d.lineNumber + " " + d.className + " " + d.fieldName + state.lineNumberSeq.toString() + " " + state.allThreadSeq.toString() + " " + state.log);
                    state.resetFieldRule(checkFieldRule);
                    //  System.out.println("========= : " + state.parentId);
                    if (state.parentId != -1) {
                        Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                        for (Node nd : parentNd.children) {
                            checkFieldRule(nd, deepCloneStates(fieldStates));
                        }
                    }
                    state.parentId = -1;

                }
            }
        }

        for (Node nd : myNode.children) {
            checkFieldRule(nd, deepCloneStates(fieldStates));
        }

    }

    public void checkFieldRule2(Node myNode, HashMap<String, FieldState> fieldStates) {
        // Set the field rule to check
        ArrayList<String> checkFieldRule = new ArrayList<>();
        checkFieldRule.add("readField");
        checkFieldRule.add("threadChange");
        checkFieldRule.add("writeField");
        checkFieldRule.add("threadBack");
        checkFieldRule.add("readField");

        List<Data> ld = myNode.data;
        FieldState state = null;

        for (Data d : ld) {
            if (d.fieldName != null) {
                if (fieldStates.containsKey(d.fieldName)) {
                    state = fieldStates.get(d.fieldName);
                } else {
                    fieldStates.put(d.fieldName, new FieldState());
                    state = fieldStates.get(d.fieldName);
                    state.resetFieldRule(checkFieldRule);
           

                }

                if (d.readOperation && state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("readField") == 0) {
                    state.threadSeq.add(d.threadName);
                    state.checkFieldRule.remove(0);
                    state.lineNumberSeq.add(d.lineNumber);
                    state.allThreadSeq.add(d.threadName);
                    state.parentId = myNode.id;
                    state.parentDepth = myNode.depth;
                    fieldStates.replace(d.fieldName, state);
     
                } else if (state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadChange") == 0 && state.checkFieldRule.get(1).compareTo("writeField") == 0) {
                    if (!state.threadSeq.contains(d.threadName) && d.writeOperation) {
                        for (Node nd : myNode.children) {
                            checkFieldRule(nd, deepCloneStates(fieldStates));
                        }
                        state.checkFieldRule.remove(0);
                        state.checkFieldRule.remove(0);
                        state.lineNumberSeq.add(d.lineNumber);
                        state.allThreadSeq.add(d.threadName);
                        state.threadSeq.add(d.threadName);
                
                    } else if (state.threadSeq.contains(d.threadName) && d.writeOperation) {
                        state.resetFieldRule(checkFieldRule);
                        //     System.out.println("========= : " + state.parentId);
                        if (state.parentId != -1) {
                            Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                            for (Node nd : parentNd.children) {
                                checkFieldRule(nd, deepCloneStates(fieldStates));
                            }
                        }
                        state.parentId = -1;
                 
                    }
                } else if (state.checkFieldRule.size() != 0 && state.checkFieldRule.get(0).compareTo("threadBack") == 0 && state.checkFieldRule.get(1).compareTo("readField") == 0) {
                    if (state.threadSeq.get(0).compareTo(d.threadName) == 0 && d.readOperation) {
                        state.checkFieldRule.remove(0);
                        state.checkFieldRule.remove(0);
                        state.lineNumberSeq.add(d.lineNumber);
                        state.allThreadSeq.add(d.threadName);
          
                    } else if (state.threadSeq.get(0).compareTo(d.threadName) == 0 && d.writeOperation) {
                        state.resetFieldRule(checkFieldRule);

                        if (state.parentId != -1) {
                            Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                            for (Node nd : parentNd.children) {
                                checkFieldRule(nd, deepCloneStates(fieldStates));
                            }
                        }
                        state.parentId = -1;
                   
                    }
                }

                if (state != null && state.checkFieldRule.isEmpty()) {
                    //    if(d.fieldName.compareTo("gr.uop.intermittent.faults.symbiosistest.TestClass.filled")==0) 
                    System.out.println("Error pattern detected... " + d.lineNumber + " " + d.className + " " + d.fieldName + state.lineNumberSeq.toString() + " " + state.allThreadSeq.toString() + " " + state.log);
                    state.resetFieldRule(checkFieldRule);
                    //  System.out.println("========= : " + state.parentId);
                    if (state.parentId != -1) {
                        Node parentNd = myNode.findNode(state.parentId, state.parentDepth, root);
                        for (Node nd : parentNd.children) {
                            checkFieldRule(nd, deepCloneStates(fieldStates));
                        }
                    }
                    state.parentId = -1;

                }
            }
        }

        for (Node nd : myNode.children) {
            checkFieldRule(nd, deepCloneStates(fieldStates));
        }

    }

    private HashMap<String, FieldState> deepCloneStates(HashMap<String, FieldState> fieldStates) {
        HashMap<String, FieldState> fieldStatesCloned = new HashMap<>();

        for (HashMap.Entry<String, FieldState> entry : fieldStates.entrySet()) {
            FieldState fieldStateCloned = new FieldState();
            String key = entry.getKey();
            FieldState value = entry.getValue();
            fieldStateCloned.allThreadSeq = DeepClone.deepClone(value.allThreadSeq);
            fieldStateCloned.checkFieldRule = DeepClone.deepClone(value.checkFieldRule);
            fieldStateCloned.threadSeq = DeepClone.deepClone(value.threadSeq);
            fieldStateCloned.lineNumberSeq = DeepClone.deepClone(value.lineNumberSeq);
            fieldStateCloned.log = value.log;
            fieldStateCloned.parentId = value.parentId;
            fieldStateCloned.parentDepth = value.parentDepth;
            fieldStatesCloned.put(key, fieldStateCloned);
        }

        return fieldStatesCloned;
    }

    class FieldState {

        public int parentId = -1;
        public int parentDepth = -1;
        ArrayList<String> checkFieldRule = new ArrayList<String>();
        ArrayList<String> threadSeq = new ArrayList<String>();
        ArrayList<Integer> lineNumberSeq = new ArrayList<Integer>();
        ArrayList<String> allThreadSeq = new ArrayList<String>();
        String log = "";

        public void resetFieldRule(ArrayList<String> fieldRule) {
            checkFieldRule = DeepClone.deepClone(fieldRule);
            threadSeq = new ArrayList<String>();
            lineNumberSeq = new ArrayList<Integer>();
            allThreadSeq = new ArrayList<String>();
        }

        public void initializeFieldRule() {
            checkFieldRule = new ArrayList<String>();
            threadSeq = new ArrayList<String>();
            lineNumberSeq = new ArrayList<Integer>();
            allThreadSeq = new ArrayList<String>();
        }

        public FieldState deepClone() {
            FieldState fs = new FieldState();
            fs.checkFieldRule = (ArrayList<String>) DeepClone.deepClone(checkFieldRule);
            fs.threadSeq = (ArrayList<String>) DeepClone.deepClone(threadSeq);
            fs.lineNumberSeq = (ArrayList<Integer>) DeepClone.deepClone(lineNumberSeq);
            fs.allThreadSeq = (ArrayList<String>) DeepClone.deepClone(allThreadSeq);
            fs.log = this.log;

            return fs;
        }
    }

}
