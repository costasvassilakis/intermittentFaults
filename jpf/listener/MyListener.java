/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.listener;
import com.mongodb.client.model.Filters;
import com.mongodb.client.MongoCursor;
import com.mongodb.client.MongoCollection;
import com.mongodb.client.MongoDatabase;
import com.mongodb.BasicDBObject;
import com.mongodb.DB;
import com.mongodb.DBCollection;
import com.mongodb.DBObject;
import com.mongodb.MongoClient;
import com.mongodb.MongoClientURI;
import org.bson.Document;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.util.DeepClone;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.LocalVarInfo;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;
import gov.nasa.jpf.vm.bytecode.FieldInstruction;
import gov.nasa.jpf.vm.bytecode.LocalVariableInstruction;
import gov.nasa.jpf.vm.choice.ThreadChoiceFromSet;
import java.io.BufferedWriter;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

public class MyListener extends PropertyListenerAdapter {

    Node2 root = null;
    Node2 current2 = null;
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
    StateNode rootNode = new StateNode();
    HashMap<Integer, StateNode> stateMap = new HashMap<>();
    HashMap<Integer, Node> nodesIncluded = new HashMap<>();
    HashMap<Integer, Boolean> isEndState = new HashMap<>();
    HashMap<Integer, Integer> stateGroups = new HashMap<>();
    HashMap<String, Integer> stateGroupMap = new HashMap<>();
    HashMap<Integer, String> stateGroupMap2 = new HashMap<>();
    HashSet<Integer> firstElements = new HashSet<>();
    HashSet<String> finalSequences = new HashSet<>();
    HashSet<String> errors = new HashSet<>();
    HashMap<String, HashSet<String>> threadNames = new HashMap<>();
    int endNodes = 0;
    HashSet<String> fieldNames = new HashSet<>();
    HashMap<String, ArrayList<String>> functions = new HashMap<>();
    HashMap<String,String> paramFields = new  HashMap<>();
    HashMap<String, ArrayList<String>> functionsMapping = new HashMap<>();
    Set<String> functionNames = new HashSet<>();
    BufferedWriter bw;
    DBCollection collection;
    DBCollection collection2;
    DBCollection collection3;
    DBCollection collection4;
    MongoCollection<Document> collection11;
    MongoCollection<Document> collection22;
    MongoCollection<Document> collection33;

    public MyListener() {
        MongoClient mongoClient = new MongoClient(new MongoClientURI("mongodb://localhost:27017"));
            DB database = mongoClient.getDB("jpf");
            MongoDatabase database2 = mongoClient.getDatabase("jpf");
            collection = database.getCollection("jpfdata"); 
            collection2 = database.getCollection("varfieldrelations"); 
            collection3 = database.getCollection("varfieldgroups"); 
            collection4 = database.getCollection("ids"); 
            collection11 = database2.getCollection("jpfdata"); 
            collection22 = database2.getCollection("varfieldrelations"); 
            collection33 = database2.getCollection("varfieldgroups"); 
        root = new Node2();
        current2 = new Node2();
        current = new Node();
        current2.parent = root;
        root.children.add(current2);
        allowedPaths = new HashMap<>();

        if (VM.getVM().getConfig().get("fieldNames") != null) {
            String[] fields = VM.getVM().getConfig().get("fieldNames").toString().split(",");
            if (fields != null) {
                fieldNames = new HashSet<String>(Arrays.asList(fields));
            }
        }
        if (VM.getVM().getConfig().get("vm.functions") != null) {
            String[] functions = VM.getVM().getConfig().get("vm.functions").toString().split(";");
            if (functions != null) {
                for(String f:functions) {
                    String fname = f.substring(0, f.indexOf("("));
                    String fparams =f.substring(f.indexOf("(")+1, f.indexOf(")"));
                    ArrayList<String> pa = new ArrayList<>();
                    if(fparams!=null) {
                        String[] params = fparams.split(",");
                        for(String s:params) {
                            pa.add(s);
                        }
                    }
                    this.functions.put(fname, pa);
                }
            }
            this.functionNames = this.functions.keySet();
        }

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
    public void methodEntered (VM vm, ThreadInfo currentThread, MethodInfo enteredMethod) {
    }
    
    @Override
    public void instructionExecuted(VM vm, ThreadInfo ti, Instruction nextInsn, Instruction insn) {
        
      Search search = vm.getSearch();

        id = search.getStateId();
        depth = search.getDepth();

        boolean found = current2.findNode(id, depth);
        boolean continuerun = true;
        if (allowDepth != null && allowChild != null && allowedPaths.size() != 0) {
                        if (allowedPaths.containsKey(depth)) {
                            //       System.out.println("allowDepth " + allowedPaths.containsKey(depth) + " " + depth + " " + current.children.size() + " " + allowedPaths.get(depth).contains(current.children.size()) + " " + id + " " + ti.getName());
                            if (!allowedPaths.get(depth).contains(current2.children.size())) {
                                ti.breakTransition(true);
                                continuerun  = false;
                            }

                        }
                    }
                    
                    if (!ti.hasChanged() && (threadsDepMap == null || threadsDepMap.get(search.getVM().getCurrentThread().getName()) == null)) {
                        continuerun  = false;
                    }
                    if (allowThreads != null && !allowThreads.contains(ti.getName()) && (threadsDepMap == null || threadsDepMap.get(search.getVM().getCurrentThread().getName()) == null)) {
                        continuerun  = false;
                    }
    //       System.out.println("id  vs current id : " + id + " " + current.id);
   /*        if(!found) {
           try {
                collection4.remove(new BasicDBObject("id", id));
            } catch (Exception me) {
                System.err.println("IDs: Unable to delete due to an error: " + me);
            }
            
            BasicDBObject bo = new BasicDBObject();  

            bo.append("id", Integer.toString(id)).append("previousid", Integer.toString(current2.previousid));
            
                         
            collection4.insert(bo);
           }*/
            Node newN = current;
            
            if(continuerun && insn instanceof LocalVariableInstruction) {
                LocalVariableInstruction lvinsn = (LocalVariableInstruction) insn;
                        
                    LocalVarInfo vi = lvinsn.getLocalVarInfo();
                    String name = null;
                    if(vi!=null){
                     name = vi.getName();
                            if (name.contains(".")) {
                                name = name.substring(name.lastIndexOf(".") + 1);
                            }}
                    if(vi!=null)
                        
                   /* if (functionNames!=null)
                    for(String f : functionNames) {
                        if (lvinsn.getSourceLine()!=null && lvinsn.getSourceLine().contains(f)) {
                            String func = lvinsn.getSourceLine().substring(lvinsn.getSourceLine().indexOf(f), lvinsn.getSourceLine().indexOf(")"));
                            func = func.substring(func.indexOf("(")+1);
                            String[] pars = func.split(",");
                            ArrayList<String> params = new ArrayList<>();
                            for (String p : pars) {
                                params.add(p);               
                            }
                            if (functionsMapping!=null)
                            functionsMapping.put(f, params);
                            break;
                        }
                    }
*/                   
                //    if(vi!=null && (!newN.relationOfFieldsAndVarsMap.keySet().isEmpty()  && newN.relationOfFieldsAndVarsMap.containsKey(vi.getName())) || (functionsMapping.get(lvinsn.getMethodInfo().getName())!=null  &&  newN.relationOfFieldsAndVarsMap.containsKey(functionsMapping.get(lvinsn.getMethodInfo().getName()).get(functions.get(lvinsn.getMethodInfo().getName()).indexOf(vi.getName())))) || (functionsMapping.get(lvinsn.getMethodInfo().getName())!=null  &&  fieldNames.contains(functionsMapping.get(lvinsn.getMethodInfo().getName()).get(functions.get(lvinsn.getMethodInfo().getName()).indexOf(vi.getName())))) ) {
                 if(paramFields.keySet().contains(name))    {
                        VariableData newD = new VariableData();

                        if(lvinsn.getSourceLine()!=null) {
                        newD.sourceLine = lvinsn.getSourceLine();
                        System.out.println("++++++++"+newD.sourceLine);
                        newD.fileLocation = lvinsn.getFileLocation();
                        newD.lineNumber = lvinsn.getLineNumber();
                        newD.methodName = lvinsn.getMethodInfo().getName();
                        newD.isSynchronized = lvinsn.getMethodInfo().isSynchronized();
                        newD.threadName = ti.getName();
             //           if (!newN.threadAccessed.contains(ti.getName())) {
              //              newN.threadAccessed.add(ti.getName());
             //           }
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();

                        

                        newD.threadName = ti.getName();
                        newD.threadId = ti.getId();
                        newD.instance = lvinsn.getMethodInfo().getClassInfo().getUniqueId();
                        newD.className = lvinsn.getMethodInfo().getClassInfo().getSimpleName();
                        newD.packageName = lvinsn.getMethodInfo().getClassInfo().getPackageName();
                        if(vi!=null)
                        newD.variableName = vi.getName();
                        System.out.println(vi.getName());
                        newD.value = lvinsn.getVariableId();
                        
                        if(vi!=null)
                        newD.type = vi.getType();
                        

                        if(newD.sourceLine!=null) {
                            if(newD.sourceLine.contains("=")) {
                                String part1 = newD.sourceLine.split("=")[0].trim();
                             //   System.out.println("p1 " + part1);
                                if(newD.sourceLine.split("=").length>=2) {
                                    String part2 = newD.sourceLine.split("=")[1].trim();
                                //    System.out.println("p2 " + part2);
                                    if (part2.contains(newD.variableName)) {
                                        newD.readOperation = true;
                                    }
                                    if(part1.contains(newD.variableName) && (part1.lastIndexOf(newD.variableName)+newD.variableName.length()==part1.length())) {
                                        newD.writeOperation = true;
                                        
                                    /*    boolean fieldrel = false;
                                        for(String fld:newN.fieldVarGroups.keySet()) {
                                        //    System.out.println("fld " + fld.substring(fld.lastIndexOf(".")+1));
                                            if(part2.contains(fld.substring(fld.lastIndexOf(".")+1))) {
                                            //    System.out.println("par " + newD.sourceLine);
                                                fieldrel=true;
                                                break;
                                            }
                                        }*/
                                     //   if(!fieldrel && !newD.readOperation) {
                                        if(newD.writeOperation) {
                                            if(paramFields.containsKey(newD.className+newD.lineNumber)){
                                               paramFields.put(name+newD.className, paramFields.get(newD.className+newD.lineNumber));
                                               paramFields.remove(newD.className+newD.lineNumber);
                                            }
                                     /*       RelationOfFieldsAndVars rfvrem = null;
                                            boolean loop = true;
                                            
                                            if (newN.relationOfFieldsAndVarsMap!=null)
                           //     System.out.println("relationOfFieldsAndVarsMap ... " + newN.relationOfFieldsAndVarsMap.size());
                                            
                                            while(loop) {
                                                loop = false;
                                                for(RelationOfFieldsAndVars rfv:newN.relationOfFieldsAndVarsMap.get(vi.getName())) {
                                                    if(rfv.variableName.compareTo(vi.getName())==0 && rfv.threadName.compareTo(newD.threadName)==0) {
                                                        newN.fieldVarGroups.get(rfv.fieldName).remove(newD.threadName+"#"+newD.className+"."+newD.methodName+"."+vi.getName());
                                                        rfvrem = rfv;
                                                        loop = true;
                                                        break;
                                                    }
                                                }
                                                newN.relationOfFieldsAndVarsMap.get(vi.getName()).remove(rfvrem);
                                                rfvrem=null;
                                            }
                                            */
                                        /*    FieldVarGroups fvgs = new FieldVarGroups();
                                            fvgs.toDBObject(newN.id, newN.fieldVarGroups);
                                            int count = 0;
                                             try {
                                                    collection2.remove(new BasicDBObject("id", id));
                                                } catch (Exception me) {
                                                    System.err.println("RelationOfFiledsAndVars: Unable to delete due to an error: " + me);
                                                }
                                            for(String k:newN.relationOfFieldsAndVarsMap.keySet()) {
                                                for(RelationOfFieldsAndVars rf:newN.relationOfFieldsAndVarsMap.get(k)) {
                                                    rf.toDBObject(newN.id, count++);
                                                }
                                            }*/
                                        }
                                    }
                                    
                                    
                                    if(newD.readOperation && !newD.writeOperation) {
                                        if (part1.split(" ").length >= 2) {
                                            String fn = null;
                                            String var = part1.split(" ")[1].trim();
                                            if(!paramFields.containsKey(newD.className+newD.lineNumber) && paramFields.get(name+newD.className)!=null){
                                               paramFields.put(newD.className+newD.lineNumber, paramFields.get(name+newD.className));
                                            }
                                       //     System.out.println("var " + var);
                                         //   ArrayList<RelationOfFieldsAndVars> fvs = newN.relationOfFieldsAndVarsMap.get(vi.getName());
                                         /*   for(RelationOfFieldsAndVars rfv:fvs) {
                                                if(rfv.threadName.compareTo(newD.threadName)==0) {
                                                    fn = rfv.fieldName;
                                               //     System.out.println("fn " + fn + " " + rfv.variableName + " " + rfv.sourceLine);
                                                    RelationOfFieldsAndVars nrfv = rfv.copy();
                                                    nrfv.variableName=var;
                                                    if(newN.relationOfFieldsAndVarsMap.get(var)!=null) {
                                                        newN.relationOfFieldsAndVarsMap.get(var).add(nrfv);
                                                    }else{
                                                        ArrayList<RelationOfFieldsAndVars> relArr = new ArrayList<>();
                                                        relArr.add(nrfv);
                                                //        System.out.println("nrfv.variableName " + nrfv.variableName + " " + newD.lineNumber + " " + newN.id + " " + newN.depth);
                                                        newN.relationOfFieldsAndVarsMap.put(var, relArr);
                                                    }
                                                    
                                                }
                                            }*/
                                            
                                    /*        if (newN.fieldVarGroups!=null)
                        //        System.out.println("relationOfFieldsAndVarsMap ... " + newN.fieldVarGroups.size());
                                            
                                            if(newN.fieldVarGroups.get(fn)==null) {
                                                HashSet hs = new HashSet();
                                                hs.add(newD.threadName+"#"+newD.className+"."+newD.methodName+"."+var);
                                        //        System.out.println("fieldVarGroups " + fn);
                                                newN.fieldVarGroups.put(var, hs);
                                            }else {
                                       //         System.out.println("fieldVarGroups2 " + fn);
                                                newN.fieldVarGroups.get(fn).add(newD.threadName+"#"+newD.className+"."+newD.methodName+"."+var);
                                            }
                                            */
                                        /*    FieldVarGroups fvgs = new FieldVarGroups();
                                            fvgs.toDBObject(newN.id, newN.fieldVarGroups);
                                            int count = 0;
                                             try {
                                                    collection2.remove(new BasicDBObject("id", id));
                                                } catch (Exception me) {
                                                    System.err.println("RelationOfFiledsAndVars: Unable to delete due to an error: " + me);
                                                }
                                            for(String k:newN.relationOfFieldsAndVarsMap.keySet()) {
                                                for(RelationOfFieldsAndVars rf:newN.relationOfFieldsAndVarsMap.get(k)) {
                                                    rf.toDBObject(newN.id, count++);
                                                }
                                            }*/
                                        }
                                        
                                    }
                                }
                            }else if(newD.sourceLine.contains("++") || newD.sourceLine.contains("--")) {
                                newD.writeOperation = true;
                            }else
                                newD.readOperation = true;
                        }

                        if (newD.variableName != null) {
                            if (newN.varData.get(newD.threadName)==null) {
                                newN.varData.put(newD.threadName, new HashMap<>());
                                newN.varData.get(newD.threadName).put(newD.variableName, new ArrayList<>());
                            }else if (newN.varData.get(newD.threadName).get(newD.variableName)==null) {
                                newN.varData.get(newD.threadName).put(newD.variableName, new ArrayList<>()); 
                            }
                            newN.varData.get(newD.threadName).get(newD.variableName).add(newD);
                            addData(newN);
                            
                        }
     
                        }
                    }
                }
        
     
    }

    @Override
    public synchronized void choiceGeneratorSet(VM vm, ChoiceGenerator<?> cg) {
        Search search = vm.getSearch();

        id = search.getStateId();
        depth = search.getDepth();

        boolean found = current2.findNode(id, depth);
        System.out.println("id found : " + id + " " + found);
        if (!found) {
            
            System.out.println("id not found : " + id + " " + found);
           // addData(current);
            
            Node newN = new Node();
            Node2 newN2 = new Node2();
            newN2.parent = current2;
            newN2.depth = depth;
            newN2.id = id;
            newN2.objectCount = current2.objectCount+1;
            newN.depth = depth;
            newN.id = id;
       //     newN.threadAccessed = (ArrayList<String>) current.threadAccessed.clone();
      //      newN.getParentThreadLocks();
        ///    newN.getFieldVarGroups();
        ////    newN.getRelationOfFieldsAndVarsMap();

            if(current!=null) {
                newN.objectCount = current2.objectCount; 
                newN.objectPerThreadCount = DeepClone.deepClone(current.objectPerThreadCount);
            }
        
            if (cg instanceof ThreadChoiceFromSet) {

                ThreadInfo[] threads = ((ThreadChoiceFromSet) cg).getAllThreadChoices();
                for (int i = 0; i < threads.length; i++) {
                    ThreadInfo ti = threads[i];
                    
                    if (allowDepth != null && allowChild != null && allowedPaths.size() != 0) {
                        if (allowedPaths.containsKey(depth)) {
                            //       System.out.println("allowDepth " + allowedPaths.containsKey(depth) + " " + depth + " " + current.children.size() + " " + allowedPaths.get(depth).contains(current.children.size()) + " " + id + " " + ti.getName());
                            if (!allowedPaths.get(depth).contains(current2.children.size())) {
                                ti.breakTransition(true);

                                continue;
                            }

                        }
                    }
                    
                    if (!ti.hasChanged() && (threadsDepMap == null || threadsDepMap.get(search.getVM().getCurrentThread().getName()) == null)) {
                        continue;
                    }
                    if (allowThreads != null && !allowThreads.contains(ti.getName()) && (threadsDepMap == null || threadsDepMap.get(search.getVM().getCurrentThread().getName()) == null)) {
                        continue;
                    }

                    

                    Instruction insn = ti.getPC();
                    
           
                if (insn instanceof FieldInstruction) { // Ok, its a get/putfield
                    FieldInstruction finsn = (FieldInstruction) insn;
                       String fname = null;
                        Data newD = new Data();


                        newD.fileLocation = insn.getFileLocation();
                        newD.lineNumber = insn.getLineNumber();
                        newD.methodName = insn.getMethodInfo().getName();
                        newD.isSynchronized = insn.getMethodInfo().isSynchronized();
                        newD.threadName = ti.getName();
                    //    if (!newN.threadAccessed.contains(ti.getName())) {
                    //        newN.threadAccessed.add(ti.getName());
                     //   }
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();
                
                        if(current2!=null) {
                            newN.objectCount = current2.objectCount + 1; 
                        }
                        if(newN.objectPerThreadCount.get(newD.threadName)==null){
                            newN.objectPerThreadCount.put(newD.threadName, 1);
                        }else {
                            newN.objectPerThreadCount.put(newD.threadName, newN.objectPerThreadCount.get(newD.threadName)+1);
                        }
                        
                        

                        if (finsn.isRead()) {
                            newD.readOperation = true;
                        } else {
                            newD.writeOperation = true;
                        }
                        FieldInfo fi = finsn.getFieldInfo();

                        newD.fieldName = fi.getFullName();
                        System.out.println("===="+fi.getFullName());
                        newD.threadName = ti.getName();
                        newD.threadId = ti.getId();
                        newD.instance = insn.getMethodInfo().getClassInfo().getUniqueId();
                        newD.className = fi.getClassInfo().getSimpleName();
                        newD.packageName = fi.getClassInfo().getPackageName();
                        if (fieldNames != null) {
                            String name = fi.getFullName();
                            if (name.contains(".")) {
                                name = name.substring(name.lastIndexOf(".") + 1);
                            }
                            fname=name;
                            fieldNames.add(name);
                        //    System.out.println("wwwwww" + fieldNames.toString());
                            if (fieldNames.contains(name)) {
                                newD.fieldName = fi.getFullName();
                            } else {
                                newD.fieldName = null;
                            }
                        } else {
                            newD.fieldName = fi.getFullName();
                        }
                        newD.value = String.valueOf(finsn.getLastValue());
                        newD.type = finsn.getFieldInfo().getType();
                        newD.sourceLine = finsn.getSourceLine();
                        
                        if(newD.readOperation) {
                         //   System.out.println("readOperation2 : " + newD.readOperation);
                            if(newD.sourceLine!=null) {
                            //    System.out.println("newD.sourceLine : " + newD.sourceLine);
                                String part1 = newD.sourceLine.split("=")[0].trim();
                                if (newD.sourceLine.split("=").length >= 2) {
                                    String var = null;
                                    RelationOfFieldsAndVars rel = new RelationOfFieldsAndVars();
                                    if (part1.split(" ").length >= 2) {
                                        var = part1.split(" ")[1].trim();
                                        rel.variableName=var;
                                        rel.type=part1.split(" ")[0].trim();
                                     //   System.out.println("var2 : " + var);
                                    } else {
                                        var = part1.trim();
                                        rel.variableName=var;
                                    //    System.out.println("var2 : " + var);
                                    }
                                    String v  = rel.variableName + newD.className;
                                    
                                    if(!paramFields.keySet().contains(v))
                                        paramFields.put(v, fname);
                                    
                           /*         rel.fieldName=newD.fieldName;
                                    rel.className=newD.className;
                                    rel.methodName=newD.methodName;
                                    rel.packageName=newD.packageName;
                                    rel.threadName=newD.threadName;
                                    rel.sourceLine=newD.sourceLine;
                                    rel.lineNumber=newD.lineNumber;
                              */                           //   System.out.println("LocalVariableInstruction3 " + ((LocalVariableInstruction) insn).getVariableId() + " linenumber " + insn.getLineNumber() + " " + insn.getSourceLine() + " " + insn.getSourceLocation());

                          /*          if(newN.relationOfFieldsAndVarsMap.get(var)==null) {
                                    //    System.out.println("var3 : " + var);
                                        ArrayList<RelationOfFieldsAndVars> relArr = new ArrayList<>();
                                        relArr.add(rel);
                                        newN.relationOfFieldsAndVarsMap.put(var, relArr);
                                    } else {
                                    //    System.out.println("var3 : " + var);
                                        newN.relationOfFieldsAndVarsMap.get(var).add(rel);
                                    }
                                    
                                    if(newN.fieldVarGroups.get(newD.fieldName)==null) {
                                        HashSet hs = new HashSet();
                                        hs.add(newD.threadName+"#"+newD.className+"."+newD.methodName+"."+var);
                                        newN.fieldVarGroups.put(newD.fieldName, hs);
                                    }else {
                                        newN.fieldVarGroups.get(newD.fieldName).add(newD.threadName+"#"+newD.className+"."+newD.methodName+"."+var);
                                    }
                                    */
                                /*    FieldVarGroups fvgs = new FieldVarGroups();
                                    fvgs.toDBObject(newN.id, newN.fieldVarGroups);
                                    int count = 0;
                                    for(String k:newN.relationOfFieldsAndVarsMap.keySet()) {
                                        for(RelationOfFieldsAndVars rf:newN.relationOfFieldsAndVarsMap.get(k)) {
                                            rf.toDBObject(newN.id, count++);
                                        }
                                    }*/
                                }    
                                
                            }
                        }else if(newD.writeOperation){
                            if(newD.sourceLine!=null) {
                            //    System.out.println("newD.sourceLine : " + newD.sourceLine);
                                String part2 = newD.sourceLine.split("=")[1].trim();
                                if (newD.sourceLine.split("=").length >= 2) {
                                    String var = null;
                                    if (part2.split(" ").length >= 2) {
                                        
                                        for(String s:part2.split(" "))  {
                                            s=s.replaceAll(";", "");
                                            String v  = s + newD.className;
                                    System.out.println("paramFields.keySet() v " + paramFields.keySet() + " " + v + " "  +  paramFields.get(v));
                                           if(paramFields.keySet().contains(v))
                                                newD.relatedField=paramFields.get(v);
                                    
                                        }
                                     //   System.out.println("var2 : " + var);
                                    } else {
                                        var = part2.trim();
                                        var=var.replaceAll(";", "");
                                        String v  = var + newD.className;
                                    System.out.println("paramFields.keySet() v " + paramFields.keySet() + " " + v + " "  +  paramFields.get(v));
                                           if(paramFields.keySet().contains(v))
                                                newD.relatedField=paramFields.get(v);
                                    //    System.out.println("var2 : " + var);
                                    }
                                
                                }
                            }
                        }

                        if(paramFields.keySet()!=null)
                        System.out.println("paramFields.keySet() : " + paramFields.keySet().toString());
                        
                        if (newD.fieldName != null) {
                            newN.data.add(newD);
                        //    printData(newD);
                        }
               //     }
                   newN.previousid=newN2.parent.id;
                   addData(newN);
                }
                    
           

                }
        

                current2.children.add(newN2);
                current2 = newN2;
                newN.parentid = current2.parent.id;
                current = newN;
        ///        FieldVarGroups fvgs = new FieldVarGroups();
        //        fvgs.toDBObject(newN.id, newN.fieldVarGroups);
        //        int count = 0;
       //          try {
        ///        collection2.remove(new BasicDBObject("id", id));
       //             } catch (Exception me) {
        /////                System.err.println("RelationOfFiledsAndVars: Unable to delete due to an error: " + me);
        ///            }
        ///        for(String k:newN.relationOfFieldsAndVarsMap.keySet()) {
         //           for(RelationOfFieldsAndVars rf:newN.relationOfFieldsAndVarsMap.get(k)) {
         ///               rf.toDBObject(newN.id, count++);
          //          }
           ///     }
                
            }

            
        }
    }

    //--- the ones we are interested in
    @Override
    public synchronized void searchStarted(Search search) {
        System.out.println("----------------------------------- search started");
    }


    int rootId = -100;

    @Override
    public synchronized void searchFinished(Search search) {
        System.out.println("----------------------------------- search finished");
       

    }

    
    public DBObject toDBObject(Node myNode, Data d) {
       
            try {
                collection.remove(new BasicDBObject("id", myNode.id));
            } catch (Exception me) {
                System.err.println("Data: Unable to delete due to an error: " + me);
            }
            
        BasicDBObject bo = new BasicDBObject();  
        
        bo.append("objectCount",myNode.objectCount);
        
        bo.append("objectPerThreadCountKeys", Arrays.toString(myNode.objectPerThreadCount.keySet().toArray()));
        for(String k : myNode.objectPerThreadCount.keySet())
            bo.append(k, myNode.objectPerThreadCount.get(k));
        
        bo.append("id", myNode.id)
                     .append("previousId", myNode.previousid)
                     .append("depth", myNode.depth)
                     .append("data", new BasicDBObject("fieldName", d.fieldName)
                                                  .append("lineNumber", d.lineNumber)
                                                  .append("methodName", d.methodName)
                                                  .append("className", d.className)
                                                  .append("packageName", d.packageName)
                                                  .append("readOperation", d.readOperation)
                                                  .append("writeOperation", d.writeOperation)
                                                  .append("sourceLine", d.sourceLine)
                                                  .append("threadId", d.threadId)
                                                  .append("threadName", d.threadName)
                                                  .append("relatedField", d.relatedField)
                                                  .append("value", d.value));
                     
        
        if(myNode.fieldVarGroups.get(d.fieldName)!=null) {
            bo.append("fieldVarGroups", Arrays.toString(myNode.fieldVarGroups.get(d.fieldName).toArray()));
        }
        
        if(d.fieldName!=null && myNode.relationOfFieldsAndVarsMap!=null && myNode.relationOfFieldsAndVarsMap.get(d.fieldName)!=null) {  
                                    int i=0;
                                    for(RelationOfFieldsAndVars rofv:myNode.relationOfFieldsAndVarsMap.get(d.fieldName)) {
                                        bo.append("relationOfFieldsAndVarsMap" + i, new BasicDBObject("fieldName", rofv.fieldName)
                                                  .append("lineNumber", rofv.lineNumber)
                                                  .append("methodName", rofv.methodName)
                                                  .append("className", rofv.className)
                                                  .append("packageName", rofv.packageName)
                                                  .append("sourceLine", rofv.sourceLine)
                                                  .append("threadName", rofv.threadName));
                                        i++;
                                    }
                                
                            }
             
            HashMap<String,ArrayList<VariableData>> vdt = myNode.varData.get(d.threadName);
            
            if(vdt!=null) {
                for(String vdv : vdt.keySet()) {
                    if(vdt.get(vdv)!=null) {
                        for(VariableData vd:vdt.get(vdv)) {  
                            if(vd!=null) {
                                bo.append("variableData"+vd.hashCode(), new BasicDBObject("variableName", vd.variableName)
                                                  .append("lineNumber", vd.lineNumber)
                                                  .append("methodName", vd.methodName)
                                                  .append("className", vd.className)
                                                  .append("packageName", vd.packageName)
                                                  .append("readOperation", vd.readOperation)
                                                  .append("writeOperation", vd.writeOperation)
                                                  .append("sourceLine", vd.sourceLine)
                                                  .append("threadId", vd.threadId)
                                                  .append("threadName", vd.threadName)
                                                  .append("value", vd.value));
                            }

                                
                        }
                    }
                }
            }
            
            if(myNode.prevDBObject!=null) {
        //        bo.append("prevDBObject",myNode.prevDBObject);
            }
                    
        return bo;
    }
   
    public void addData(Node myNode)  {
        try {
        List<Data> ld = myNode.data;

     //   String store="";
        
        System.out.println();
        System.out.print("id : " + myNode.id);
 //       store += "id : " + myNode.id;
        System.out.print(" depth : " + myNode.depth);
 //       store += " depth : " + myNode.depth;

        for (Data d : ld) {
            if(d.fieldName!=null) {

            System.out.print(" fieldName : " + d.fieldName);
   //         store += " fieldName : " + d.fieldName;
            System.out.print(" lineNumber : " + d.lineNumber);
  //          store += " lineNumber : " + d.lineNumber;
            System.out.print(" methodName : " + d.methodName);
   //         store += " methodName : " + d.methodName;
            System.out.print(" className : " + d.className);
    //        store += " className : " + d.className;
            System.out.print(" instance : " + d.instance);
   //         store += " instance : " + d.instance;
            System.out.print(" writeOperation : " + d.writeOperation);
    //        store += " writeOperation : " + d.writeOperation;
            System.out.print(" readOperation : " + d.readOperation);
    //        store += " readOperation : " + d.readOperation;
            System.out.print(" threadName : " + d.threadName);
    //        store += " threadName : " + d.threadName;
            System.out.print(" isSynchronized : " + d.isSynchronized);
    //        store += " isSynchronized : " + d.isSynchronized;
            System.out.print(" packageName : " + d.packageName);
     //       store += " packageName : " + d.packageName;
            System.out.print(" fileLocation : " + d.fileLocation);
     //       store += " fileLocation : " + d.fileLocation;
            System.out.print(" isMonitorEnter : " + d.isMonitorEnter);
     //       store += " isMonitorEnter : " + d.isMonitorEnter;
            System.out.print(" isMonitorExit : " + d.isMonitorExit);
     //       store += " isMonitorExit : " + d.isMonitorExit;
            System.out.print(" lockRef : " + d.lockRef);
     //       store += " lockRef : " + d.lockRef;
            System.out.print(" value : " + d.value);
     //       store += " value : " + d.value;
            System.out.print(" type : " + d.type);
     //       store += " type : " + d.type;
            System.out.print(" sourceLine : " + d.sourceLine);
            System.out.print(" relatedField : " + d.relatedField);
    //        store += " sourceLine : " + d.sourceLine;
    //        System.out.print(" threadLocks : " + Arrays.toString(myNode.threadLocks.get(d.threadName).toArray()));
    //        store += " threadLocks : " + Arrays.toString(myNode.threadLocks.get(d.threadName).toArray());
            if(myNode.fieldVarGroups.get(d.fieldName)!=null) {
                System.out.print(" fieldVarGroups : " + Arrays.toString(myNode.fieldVarGroups.get(d.fieldName).toArray()));
    //            store += " fieldVarGroups : " + Arrays.toString(myNode.fieldVarGroups.get(d.fieldName).toArray());
            }
            
            HashMap<String,ArrayList<VariableData>> vdt = myNode.varData.get(d.threadName);
            HashSet<String> rvars = new HashSet();
            if(vdt!=null) {
                for(String vdv : vdt.keySet()) {
                    for(VariableData vd:vdt.get(vdv)) {  
                        if(d.lineNumber==vd.lineNumber) {
                            rvars.add(vd.variableName);
                        }
                    }
                }
            }
            for(String vd : myNode.relationOfFieldsAndVarsMap.keySet())
            if(rvars.contains(vd) && myNode.relationOfFieldsAndVarsMap.get(vd)!=null) {  
                                    System.out.print(" 111111111 : " + vd + " " + myNode.relationOfFieldsAndVarsMap.get(vd).size());
                                    ArrayList<RelationOfFieldsAndVars> rvs = null;
                                    if(myNode.relationOfFieldsAndVarsMap.get(d.fieldName)==null)
                                        rvs = new ArrayList<>();
                                    else
                                        rvs = myNode.relationOfFieldsAndVarsMap.get(d.fieldName);
                                    
                                    for(RelationOfFieldsAndVars rofv:myNode.relationOfFieldsAndVarsMap.get(vd)) {
                                       rvs.add(rofv);
                                        System.out.print(" relationOfFieldsAndVarsMap : " + rofv.fieldName + " " + rofv.variableName + " " + rofv.threadName + " " + rofv.sourceLine + " " + rofv.lineNumber);
           //                             store += " relationOfFieldsAndVarsMap : " + rofv.fieldName + " " + rofv.variableName + " " + rofv.threadName + " " + rofv.sourceLine + " " + rofv.lineNumber;
                                    }   
                                    myNode.relationOfFieldsAndVarsMap.put(d.fieldName, rvs);
                                }
            System.out.print(" locks : " + (d.locks != null ? d.locks.toString() : null));
            System.out.print(" lockRemovals : " + (d.lockRemovals != null ? Arrays.asList(d.lockRemovals) : null));
            
            vdt = myNode.varData.get(d.threadName);
            
            if(vdt!=null) {
                for(String vdv : vdt.keySet()) {
                    if(vdt.get(vdv)!=null) {
                        for(VariableData vd:vdt.get(vdv)) {  
                            if(vd!=null) {
                                System.out.println(" Variable data : ");
           //                     store += " Variable data : ";
                                System.out.print(" variableName : " + vd.variableName);
         //                       store += " variableName : " + vd.variableName;
                                System.out.print(" lineNumber : " + vd.lineNumber);
          //                      store += " lineNumber : " + vd.lineNumber;
                                System.out.print(" methodName : " + vd.methodName);
          //                      store += " methodName : " + vd.methodName;
                                System.out.print(" className : " + vd.className);
          //                      store += " className : " + vd.className;
                                System.out.print(" writeOperation : " + vd.writeOperation);
          //                      store += " writeOperation : " + vd.writeOperation;
                                System.out.print(" readOperation : " + vd.readOperation);
         //                       store += " readOperation : " + vd.readOperation;
                                System.out.print(" isSynchronized : " + vd.isSynchronized);
          //                      store += " isSynchronized : " + vd.isSynchronized;
                                System.out.print(" fileLocation : " + vd.fileLocation);
          //                      store += " fileLocation : " + vd.fileLocation;
                                System.out.print(" packageName : " + vd.packageName);
          //                      store += " packageName : " + vd.packageName;
                                System.out.print(" sourceLine : " + vd.sourceLine);
          //                      store += " sourceLine : " + vd.sourceLine;
                                System.out.print(" threadName : " + vd.threadName);
           //                     store += " threadName : " + vd.threadName;
           //                     System.out.print(" threadLocks : " + Arrays.toString(myNode.threadLocks.get(vd.threadName).toArray()));
            //                    store += " threadLocks : " + Arrays.toString(myNode.threadLocks.get(vd.threadName).toArray());
                                if(myNode.relationOfFieldsAndVarsMap.get(vd.variableName)!=null) {  
                                    System.out.print(" 111111111 : " + vd.variableName + " " + myNode.relationOfFieldsAndVarsMap.get(vd.variableName).size());
                                    for(RelationOfFieldsAndVars rofv:myNode.relationOfFieldsAndVarsMap.get(vd.variableName)) {
                                        System.out.print(" relationOfFieldsAndVarsMap : " + rofv.fieldName + " " + rofv.variableName + " " + rofv.threadName + " " + rofv.sourceLine + " " + rofv.lineNumber);
           //                             store += " relationOfFieldsAndVarsMap : " + rofv.fieldName + " " + rofv.variableName + " " + rofv.threadName + " " + rofv.sourceLine + " " + rofv.lineNumber;
                                    }    
                                }
                                    
                                    
                                System.out.print(" type : " + vd.type);
          //                      store += " type : " + vd.type;
                                System.out.print(" value : " + vd.value);
          //                      store += " value : " + vd.value;
                            }
                        }
                    }
                }
            }
            
      //      bw.write(store);
      //      bw.newLine();
      try {
            DBObject prevDBObject = toDBObject(myNode,d);
       //     myNode.prevDBObject = prevDBObject;
      //      System.out.println("out..." + prevDBObject);
            collection.insert(prevDBObject);
            prevDBObject = null;
      }catch(Exception e){
          e.printStackTrace();
      }
            }
        }
        

   //     for (Node nd : myNode.children) {
    //        nd.previousid=myNode.id;
         //   nd.prevDBObject=myNode.prevDBObject;
         //   System.out.println("DBObjects .... ");
     //       printTree(nd);
    //    }
        }catch(Exception e){
            e.printStackTrace();
            
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
    
    public void printVarData(VariableData d) {

        System.out.println();
        System.out.print(" varName : " + d.variableName);
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
        System.out.print(" value : " + d.value);
        System.out.print(" type : " + d.type);
        System.out.print(" sourceLine : " + d.sourceLine);

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

    //    for (Node nd : myNode.children) {
    //        checkRule(nd, checkRule, states);
    //    }
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
        int depth = -1;
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

    class Node2 {
        protected int id = 0;
        protected int depth = 0;
        protected int previousid = -100;
        protected int objectCount = 0;
        protected Node2 parent = null;
        protected List<Node2> children = new ArrayList<Node2>();
        
        public boolean findNode(int id, int depth) {
            boolean found = false;

            while (current2.id > id && current2.depth != 0) {
                current2 = current2.parent;
            }

            if (current2.id != id) {
                for (Node2 nd : current2.children) {
                    if (nd.id == id) {
                        current2 = nd;
                        found = true;
                        break;
                    }
                }
            } else {
                found = true;
            }

            return found;
        }

        public Node2 findNode(int id, int depth, Node2 parentNode) {
            Node2 found = parentNode;

            if (found.id != id) {
                for (Node2 nd : found.children) {
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
    
    class Node {

        protected List<Data> data = new ArrayList<Data>();
    //    protected ArrayList<String> threadAccessed = new ArrayList<>();
        protected int parentid = 0;
        protected int id = 0;
        protected int previousid = -100;
        protected int depth = 0;
        protected boolean locksSearched = false;
        protected DBObject prevDBObject = null;
        protected int objectCount = 0;
        protected HashMap<String,Integer> objectPerThreadCount = new HashMap<>();
     //   HashMap<String, HashSet<String>> threadLocks = new HashMap<>();
        HashMap<String, HashMap<String,ArrayList<VariableData>>> varData = new HashMap<>();
        ConcurrentHashMap<String,ArrayList<RelationOfFieldsAndVars>> relationOfFieldsAndVarsMap = new ConcurrentHashMap<>();
        HashMap<String,HashSet<String>> fieldVarGroups = new HashMap<>();
        
       
        
        public HashMap<String, HashSet<String>> getFieldVarGroups() {   
            FieldVarGroups fvgs = new FieldVarGroups();
            fieldVarGroups = fvgs.getDBObject(parentid);
            
            return fieldVarGroups;
        }
        
        public ConcurrentHashMap<String,ArrayList<RelationOfFieldsAndVars>> getRelationOfFieldsAndVarsMap() {    
            int count = 0;
            RelationOfFieldsAndVars rfv = new RelationOfFieldsAndVars();
            boolean r;
            do {
                r = rfv.getDBObject(parentid, count++);
                if(r) {
                    relationOfFieldsAndVarsMap.put(rfv.fieldName,new ArrayList<>());
                    relationOfFieldsAndVarsMap.get(rfv.fieldName).add(rfv.copy());
                }
            } while(r);
            
            return relationOfFieldsAndVarsMap;
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
        String relatedField = null;
        int relatedLinenum = -1;
        ArrayList<Long> locks = new ArrayList<>();
        HashMap<Long, Integer> lockRemovals = new HashMap<>();
    }
    
    class VariableData {

        String variableName = null;
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
        String sourceLine = null;
    }
    
    class FieldVarGroups {
                
        public DBObject toDBObject(int id, HashMap<String,HashSet<String>> fieldVarGroups) {
       
            try {
                collection3.remove(new BasicDBObject("id", id));
            } catch (Exception me) {
                System.err.println("FieldVarGroups: Unable to delete due to an error: " + me);
            }
            
            BasicDBObject bo = new BasicDBObject();  

            bo.append("id", Integer.toString(id));
            
            for(String k:fieldVarGroups.keySet()) {
                bo.append("var", k)
                         .append("fields", fieldVarGroups.get(k).toArray().toString());
            }
                         
            collection3.insert(bo);
            return bo;
        }
        
        public HashMap<String,HashSet<String>> getDBObject(int id) {
            HashMap<String,HashSet<String>> fieldVarGroups = null;
            fieldVarGroups = new HashMap<>();
            Document query = new Document("id", id);
            
            MongoCursor<Document> cursor = collection33.find(query).iterator();
            
            try {
              while(cursor.hasNext()) {
                
                Document next = cursor.next();
                String var = next.get("var").toString();
                String fields = next.get("fields").toString();
                String[] split_string = fields.split(",");
                
                HashSet<String> hs = new HashSet<>();
                for(String s:split_string)
                    hs.add(s);
                
                fieldVarGroups.put(var, hs);
              } 
            } finally {
                cursor.close();
            }
            
            return fieldVarGroups;
        }
    }
    
    class RelationOfFieldsAndVars {

        String fieldName = null;
        String variableName = null;
        String className = null;
        String threadName = null;
        String methodName = null;
        String packageName = null;
        String type = null;
        String sourceLine = null;
        int lineNumber = -1;
        
        public RelationOfFieldsAndVars copy() {
            RelationOfFieldsAndVars cp = new RelationOfFieldsAndVars();
            
            cp.fieldName=this.fieldName;
            cp.variableName=this.variableName;
            cp.className=this.className;
            cp.threadName=this.threadName;
            cp.methodName=this.methodName;
            cp.packageName=this.packageName;
            cp.type=this.type;
            cp.sourceLine=this.sourceLine;
            cp.lineNumber=this.lineNumber;
            
            return cp;
        }
        
        public DBObject toDBObject(int id, int count) {
        
            BasicDBObject bo = new BasicDBObject();  

            bo.append("id", Integer.toString(id))
                         .append("count", count)
                         .append("fieldName", this.fieldName)
                         .append("variableName", this.variableName)
                         .append("className", this.className)
                    .append("threadName", this.threadName)
                    .append("methodName", this.methodName)
                    .append("packageName", this.packageName)
                    .append("type", this.type)
                    .append("sourceLine", this.sourceLine)
                    .append("lineNumber", this.lineNumber);

            collection2.insert(bo);
            return bo;
        }
        
        public boolean getDBObject(int id, int count) {
            Document query = new Document("id", id);
            Document query2 = new Document("count", count);
            
            MongoCursor<Document> cursor = collection22.find(Filters.and(query,query2)).iterator();
            
            try {
              if(cursor.hasNext()) {
                Document next = cursor.next();
                fieldName = next.get("fieldName").toString();
                variableName = next.get("variableName").toString();
                className = next.get("className").toString();
                threadName = next.get("threadName").toString();
                methodName = next.get("methodName").toString();
                packageName = next.get("packageName").toString();
                type = next.get("type").toString();
                sourceLine = next.get("sourceLine").toString();
                lineNumber = (int)next.get("lineNumber");
                cursor.close();
                return true;
              } else {
                  cursor.close();
                  return false;
              }
            } finally {
                cursor.close();
            }
        }
    }


}
