// Evaluator for Lego formulas
package lego;

import java.util.Objects;
import lego.parser.*;
import java.util.Stack;

// Data structure to store values of each quantification
class Quantifier {
    Var var;
    Domain dom;
    String qunatifier;
    int currentValue;
    public Quantifier(Var var, Domain dom, String quantifier){
        this.var = var;
        this.dom = dom;
        this.qunatifier = quantifier;
        this.currentValue = dom.from.n;
    }
}

// Data structure to store values of free variables
class Env {
    private Stack<Quantifier> stack;
    
    public Env(){
        stack = new Stack<>();
    }
    public void push(Quantifier q){
        stack.push(q);
    }
    public Quantifier pop(){
        return stack.pop();
    }
    public boolean isEmpty(){
        return stack.isEmpty();
    }
}

public class Eval {
    public static boolean eval(Formula f) {
	return eval(f, new Env());
    }
    // Figures out what type of formula we have and calls the appropriate method for that type of formula
    public static boolean eval(Formula f, Env e) {
        if (f instanceof Atomic)
            return atomicEval(f,e);
        else if (f instanceof Unary)
            return unaryEval(f,e);
        else if (f instanceof Binary)
            return binaryEval(f,e);
        else if (f instanceof Quantified)
            return quantifiedEval(f,e);
	return false;
    }
    
    // Takes a formula that is known to be of type Atomic and evaluates it
    public static boolean atomicEval(Formula f, Env e){
        Atomic a = (Atomic)f;
        Exp e1 = a.e1;
        Exp e2 = a.e2;
        int i1 = simplify(e1,e);
        int i2 = simplify(e2,e);
        
        if (Objects.equals(a.rel_op, ">"))
            return i1 > i2;
        else if (Objects.equals(a.rel_op, ">="))
            return i1 >= i2;
        else if (Objects.equals(a.rel_op, "="))
            return i1 == i2;
        else
            return false;
    }
    
    // Takes a formula that is known to be of type Unary and evaluates it
    public static boolean unaryEval(Formula f, Env e){
        Unary u = (Unary)f;
        String conn = u.unary_conn;
        if (Objects.equals(conn, "!"))
            return !eval(u.f, e);
        else
            return false;
    }
    
    // Takes a formula that is known to be of type Binary and evaluates it
    public static boolean binaryEval(Formula f, Env e){
        Binary b = (Binary)f;
        String conn = b.bin_conn;
        Formula f1 = b.f1;
        Formula f2 = b.f2;
        boolean evalF1 = eval(f1,e);
        boolean evalF2 = eval(f2,e);

        if (Objects.equals(conn, "&&"))
            return evalF1 && evalF2;
        else if (Objects.equals(conn, "||"))
            return evalF1 || evalF2;
        else if (Objects.equals(conn, "->"))
            return !evalF1 || evalF2;
        else if (Objects.equals(conn, "<->")){
            if (evalF1)
                return evalF2;
            else
                return !evalF2;
        }
        else
            return false;
    }
    
    // Takes a formula that is known to be of type Quantified and evaluates it
    public static boolean quantifiedEval(Formula f, Env e){
        Quantified q = (Quantified)f;
        Domain dom = q.dom;
        String quant = q.quant;
        Var v = q.var;
        Quantifier current = new Quantifier(v, dom, quant);
        e.push(current);

        if (Objects.equals(quant, "forall")){
            for (int i = dom.from.n; i <= dom.to.n; i++){
                // Change the current value of variable v so that the variable can evaluate to an int
                current.currentValue = i;
                
                // If we find a number in the domain where the formula evaluates to false, we can return false
                if (!eval(q.f, e)){
                    e.pop();
                    return false;
                }
            }
            // If we leave the for loop, all of the numbers in the domain made the formula evaluate to true so we can return true
            e.pop();
            return true;
        }
        else if (Objects.equals(quant, "exists")){
            for (int i = dom.from.n; i <= dom.to.n; i++){
                // Change the current value of variable v so that the variable can evaluate to an int
                current.currentValue = i;

                // If we find a number in the domain where the formula evaluates to true, we can return true
                if (eval(q.f, e)){
                    e.pop();
                    return true;
                }
            }
            // If we leave the for loop, none of the numbers in the domain made the formula evaluate to true so we can return false
            e.pop();
            return false;
        }
        e.pop();
        return false;
    }
    
    // Simplifies expressions until we are left with an integer
    public static int simplify(Exp exp, Env e){
        if (exp instanceof Int){
            Int i = (Int)exp;
            return i.n;
        }
        else if (exp instanceof Var){
            Var v = (Var)exp;
            Stack<Quantifier> temp = new Stack<>();
            Quantifier current;
            
            if (e.isEmpty()){
                System.out.println("Error. Variable is not bound.");
                System.exit(1);
            }
            
            // Find the most recent quantification of variable v
            do {
                current = e.pop();
                temp.push(current);
            }
            while (!Objects.equals(current.var.s, v.s) && !e.isEmpty());
            
            // If we have gone through the stack and still haven't found v, v must be unbound
            if (!Objects.equals(current.var.s, v.s)){
                System.out.println("Error. Variable is not bound.");
                System.exit(1);
            }
            // Get the current value of variable v
            int num = current.currentValue;
            
            // Puts all the quantifications back onto the stack
            while (!temp.isEmpty()){
                e.push(temp.pop());
            }
            // Return the current value of variable v
            return num;
        }
        else if (exp instanceof BinExp){
            BinExp b = (BinExp)exp;
            int simplifyE1 = simplify(b.e1,e);
            int simplifyE2 = simplify(b.e2,e);

            if (Objects.equals(b.bin_op, "+"))
                return simplifyE1 + simplifyE2;
            else if (Objects.equals(b.bin_op, "-"))
                return simplifyE1 - simplifyE2;
            else if (Objects.equals(b.bin_op, "*"))
                return simplifyE1 * simplifyE2;
            else if (Objects.equals(b.bin_op, "/")){
                // Check for division by 0
                if (simplifyE2 == 0){
                    System.out.println("Error. Division by zero.");
                    System.exit(1);
                }
                else
                    return simplifyE1 / simplifyE2;
            }
            else if (Objects.equals(b.bin_op, "mod")){
                // Check for modulo by 0
                if (simplifyE2 == 0){
                    System.out.println("Error. Modulo by zero.");
                    System.exit(1);
                }
                else
                    return simplifyE1 % simplifyE2;
            }
            else{
                System.out.println("Error. Not a valid operator.");
                System.exit(1);
            }
        }
        return 0;
    }
}