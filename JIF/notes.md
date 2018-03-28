# This is an introduction to Jif
Jif is a security-typed programming language that extends Java
with support for information flow control and access control,
enforced at both compile time and run time.
You can find Jif here https://www.cs.cornell.edu/jif/

Static information flow control can protect the confidentiality and integrity
of information manipulated by computing systems. The compiler tracks the correspondence
between information and the policies that restrict its use,
enforcing security properties end-to-end within the system.
After checking information flow within Jif programs, the Jif compiler translates them to Java programs
and uses an ordinary Java compiler to produce secure executable programs.

Jif extends Java by adding labels that express restrictions on how information may be used.
For example, the following variable declaration declares not only that the variable `x` is an `int`,
but also that the information in `x` is governed by a security policy:

```Java
int {*→Bob} x;
```

In this case, the security policy says that the information in `x` can be
seen by the principal `Bob` (the meaning of `*` will be
explained later). The policy `{*←Bob}` means
that the information can be affected by `Bob`. Based on label annotations
like these, the Jif compiler analyzes information flows within programs, to determine whether
they enforce the confidentiality and integrity of information. 



# Introduction
Lot of this material has been copied from https://www.cs.cornell.edu/jif/doc/jif-3.3.0/manual.html

Jif is an extension to the Java programming language that adds static analysis of information flow for improved security assurance.
The primary goal is to prevent confidential and/or untrusted information from being used improperly.

This document describes Jif 3.5.0 Jif is based on the JFlow language described in the Practical Mostly-Static Information Flow Control, published in the Proceedings of the 26th ACM Symposium on Principles of Programming Languages (POPL), pp. 228-241, January 1999, by Andrew C. Myers.

Jif extends Java by adding labels that express restrictions on how information may be used. For example, the following variable declaration declares not only that the variable `x` is an `int`, but also that the information in `x` is governed by a security policy:

```Java
int {*->Bob} x;
```
In this case, the security policy says that the information in x can be seen by the principal Bob.

Using label annotations like this one, the Jif compiler analyses how information flows within programs and determines whether security policies for the confidentiality or integrity of information are enforced by the program. For example, consider the following variable declaration and assignments:
(See DirectFlow01.jif)

```Java
int {*->Bob, Chuck} y;
x = y; // OK: policy on x is stronger
y = x; // BAD: policy on y is not as strong as x
```

The variable `y` is declared to be an `int`, and the information in `y` can be seen by both `Bob` and `Chuck`. The first assignment is secure because it does not make the information in `y` visible to any additional principals. The second assignment is insecure, because it allows  `Chuck` to see the information that was in `x`, and the policy on `x` forbids this (unless Bob happen to trust Chuck, as seen later). The Jif compiler makes these determinations at compile time, as part of type checking.


If a Jif program type-checks, the compiler translates it into Java code that can be compiled with a standard Java compiler. The program can then be executed with a standard Java virtual machine. Although enforcement is mostly done at compile time, Jif does also allow some enforcement to take place at run time. Therefore, Jif programs in general require the Jif run-time library.

# Decentralized label model (1)
Jif allows mutually distrusting entities to express information-flow security policies for confidentiality and integrity. Security policies are expressed using the decentralized label model (DLM).
In this section, we introduce the core concepts of the DLM: principals, policies, and labels, and present the syntax used to write labels in Jif programs.
Later we will refine these definition to cover more complex policies.

## Principals
A principal is an entity with some power to observe and change certain aspects of the system. 
A principal `p` may delegate authority to another principal `q`, in which case `q` is said to act for `p`, written `q≽p`.
If the principal `q` acts for the principal `p`, any action taken by `q` is implicitly assumed to be authorized by `p`.
Thus, the `acts-for` relation expresses trust relationships between principals. The `acts-for` relation is reflexive and transitive.

The `acts-for` relation can be used to model groups and roles conveniently. A group principal, such as students, is modeled by authorizing all of the principals representing members of the group to act for the group principal. That is, the group principal delegates its authority to all of the group members. A role, a restricted form of a user's authority, is modeled by authorizing the user's principal to act for the role principal.

Jif supports a top principal `⊤` (or `*`) able to act for all principals, and a bottom principal `⊥` (or `_`) that allows all principals to act for it.

Jif allows principals to be composed together to form conjunctive and disjunctive principals. A conjunctive principal, written `p&q`, is able to act for both the principals `p` and `q`. A disjunctive principal, written `p,q` delegates its authority to `p` and `q`, that is, `p` can act for `p,q`, and `q` can act for `p,q`. Conjunctions and disjunctions are associative, commutative and idempotent.

## Confidentiality policies
A reader policy allows to specify which principals can read a given piece of information.
A reader policy is written `o -> r`, where the principal `o` is the owner of the policy, and the principal `r` is the specified reader.
For now we will use ony `*` as owner. More complex policies will be discussed later.
A reader policy `* -> r` says that a principal `q` is allowed to read information only if `q` can act for the specified reader `r`.
As a formal semantics for reader policies, we define the function `readers(*, c)` to be the set of principals that should be allowed to read information according to reader policy `c`:
```
readers(*, *->r) = {q  | q ≽ r}
```
(These definitions will be refined later for policies whose owner is not `*`).

Let assume `Alice`, `Bob`, `Chuck` and `Dolores` are four principals (the only ones in the system), with `Dolores` acting for both `Alice` and `Chuck` (i.e. `Dolores ≽ Alice` and `Dolores ≽ Chuck`).

 * `readers(*, *->Alice)` is `{Alice, Dolores, *}`: The participants that can act for Alice are `Alice, Dolores, *`.
 * `readers(*, *->Alice&Chuck)` is `{Dolores, *}`: The participants that can act for `Alice&Chuck` are `Dolores, *`
 * `readers(*, *->Alice,Bob)` is `{Alice,Bob,Dolores, *}`
 * `readers(*, *->_)` is `{Bob,Alice,Chuck,Dolores, *}`
 * `readers(*, *->*)` is `{*}`

### Ordering confidentiality policies (simplified since owner is always `*`). 
Using the `readers(*, ∙)` function, we can define a "no more restrictive than" relation `⊑C` on confidentiality policies. For two confidentiality policies `c` and `d`, we have `c ⊑C d` if and only if `readers(*, c) ⊇ readers(*, d)`. If `c ⊑C d` then `c` permits at least as many readers as `d` does. The confidentiality policy `c` is thus of lower (or equal) confidentiality than `d`, and so information labeled `c` can be used in at least as many places as information labeled `d`: policy `c` is no more restrictive than policy `d`.

* `*->_ ⊑C *->Bob ⊑C *->*`
* `*->_ ⊑C *->Alice ⊑C *->Dolores ⊑C *->*`
* `*->Alice,Chuck ⊑C *->Alice`
* `*->Bob ⋢C *->Alice,Bob`
* `*->Alice,Dolores ⊑C *->Alice`
* `*->Alice ⊑C *->Alice&Bob`

### Conjunction and disjunction.
Greater expressiveness is achieved by allowing conjunctions and disjunctions of reader policies. We define confidentiality policies to be the smallest set containing all reader policies and closed under the binary operators `⊔` and `⊓`. That is, if `c` and `d` are confidentiality policies, then both `c⊓d` and `c⊔d` are too.

The operator `⊔` (or `;`) is conjunction for confidentiality policies: `c⊔d` is the policy that enforces both `c` and `d`. The policy `c⊔d` permits a principal to read information only if both `c` and `d` allow it. Thus, `c⊔d` is at least as restrictive as both `c` and `d`. The operator `⊓` is disjunction for confidentiality policies: `c⊓d` (or `c meet d`) allows a principal to read information if either `c` or `d` allows it. Thus, `c⊓d` is no more restrictive than either `c` or `d`.

We extend `readers(*, c)` for confidentiality policies. Since `c⊔d` enforces both `c` and `d`, the reader sets for `c` and `d` are intersected; for `c⊓d` the reader sets are combined.
`readers(*, c ⊔ d) ≜ readers(*, c) ∩ readers(*, d)`
`readers(*, c ⊓ d) ≜ readers(*, c) ∪ readers(*, d) `

* `Readers(*, *->Alice meet *->Bob) = {Alice,Bob,Dolores,*} = Readers(*, *->Alice,Bob)`
* `Readers(Alice, *->Alice,*->Bob) = {*} = Readers(*, *->Alice&Bob)` 
* `*->Bob ⊑C *->Bob,*->Chuck`
* `*->Bob ⋢C *->Bob;*->Bob,Chuck`

## Integrity policies
For now we skip them, since we will never use them. If you see something like `T <- T` in the compiler log, this is an integrity policy and you can just ignore it for now.


# Direct flows
## Labeled types
In Jif, every value has a labeled type that consists of two parts: an ordinary Java type such as `int`, and a label that describes how the value can be used. Any type expression `t` may be labeled with any label expression `l`. This labeled type expression is written `t{l}`; for example, the labeled type `int{*->p}` represents an integer that only principal `p`  can read (plus participants that can act for `p`, see next section). A variable may be declared with this labeled type:
```Java
int{*→p} x = 2;
```

This labeled type may also be written as `int{*->p}` or `int{*:p}`. The syntax of labels is described [here](https://www.cs.cornell.edu/jif/doc/jif-3.3.0/dlm.html#dlm_syntax)

The compiler permits information to flow between locations with different labels only if that information flow does not lose policy restrictions. In particular, if information is able to flow from a location with label `L1` to a location with label `L2`, the label `L2` must be more restrictive than `L1`, or equally restrictive. In other words, the compiler checks that `L1 ⊑ L2`.

[DirectFlow01.jif](../Tutorial/src-jif/DirectFlow01.jif) provides a small example of this rule:
```Java
int {* -> Bob} x;
int {* -> Bob, Chuck} y = 5;
x = y;
//y = x;
```
Here, information in `x` can be accessed by `Bob` and information in `y` can be accessed by both `Bob` and `Chuck`.
That is: `{* -> Bob, Chuck} ⊑ {* -> Bob}`, `y` is governed by a label that is less restrictive than the  label of `x`.
For this reason `y` can be assigned to `x`. The opposite does not hold: if the statement
``y=x`` is uncommented then the compiler produces the following error:
```
01       [apply] /home/guancio/Sources/dd2460/jif/Tutorial/src-jif/DirectFlow01.jif:6: 
02       [apply]     Unsatisfiable constraint
03       [apply]     	general constraint:
04       [apply]     		rhs.nv ⊑ label of var y
05       [apply]     	in this context:
06       [apply]     		{caller_pc ⊔ ⊤→Bob; ⊥←⊥} ⊑ {caller_pc ⊔ ⊤→Bob,Chuck; ⊥←⊥}
07       [apply]     	cannot satisfy equation:
08       [apply]     		{caller_pc ⊔ ⊤→Bob; ⊥←⊥} ⊑ {caller_pc ⊔ ⊤→Bob,Chuck; ⊥←⊥}
09       [apply]     	in environment:
10       [apply]     		[]
11       [apply]     Label Descriptions
12       [apply]     ------------------
13       [apply]      - rhs.nv = label of successful evaluation of right hand of assignment
14       [apply]      - rhs.nv = {caller_pc ⊔ ⊤→Bob; ⊥←⊥}
15       [apply]      - label of var y = {caller_pc ⊔ ⊤→Bob,Chuck; ⊥←⊥}
16       [apply]      - caller_pc = pc label
17       [apply]     More information is revealed by the successful evaluation of the right 
18       [apply]     hand side of the assignment than is allowed to flow to the local variable
19       [apply]      y.
20       [apply] 		y = x;
21       [apply] 		^
22       [apply] 1 error.
```
The compiler output can be read as follows:
 * 01: the error is at line 6
 * 04: the line contains an assignment, therefore the label of the right expression must be not more restrictive than the label of `y`
 * 06: the label of the expression it is just the label of `x`. In this context the label of `x` is `{caller_pc ⊔ ⊤→Bob; ⊥←⊥}`.
       `⊥←⊥` is an integrity policy. We will not cover them in this course and they are basically the converse of the confidential one.
       We will also see later what `caller_pc` is. Finally, `⊤→Bob` is the policy explicitly annotated on `x`.
The check fails due to  `{* -> Bob} ⋢ {* -> Bob,Chuck}`.




When computation combines several input values to produce a result, the result may reveal information about any of the inputs.
For example, when two variables x and y are added, the sum x+y may reveal information about both x and y. Conservatively, the label of the result is the union of the policies in the labels of the inputs. This union is the join or least upper bound of the input labels. For example, if the label of x is `{*→q}` and the label of y is `{*→b; *→q,r}`, the label of the result is `{*→q; *→b; *→q,b}`, which is equivalent to `{*→q; *→b}`.
See [DirectFlow02.jif](../Tutorial/src-jif/DirectFlow02.jif)


In a program, the policy component of a label may take a few additional forms. One such form is a variable name, which denotes the set of policies in the label of the variable named.
For example, suppose that `a` is a variable and hence has a labeled type. The label expression `{a}` contains a single component expression; this label means that it is as restricted as the contents of `a` are. The more complex label expression `{a; *→r}` contains two policy components, indicating that the labeled value should be as restricted as `a` is, and also that the value can be read by at most the principal `r`. This is a further example:
```Java
int {*->Alice} x = 1;
int (*->Bob} y = 2;
int {x;y;*->Chuck} z = x+y
```

The type and label parts of a labeled type act largely independently.

## Label inference

A labeled type may occur in a Jif program almost anywhere a type may occur in a Java program. If the label is omitted from a type, the Jif compiler automatically generates a label for that type according to certain rules. In particular, labels on local variables are automatically inferred by the Jif compiler in a way that satisfies the constraints on information flow, if possible. Not all omitted labels are inferred; other labels, such as on method arguments, are generated automatically using defaults (see [Default labels](https://www.cs.cornell.edu/jif/doc/jif-3.3.0/language.html#default-labels)).

For example, in the following code the label on the variable y is inferred automatically as `{*→Alice}`:
```Java
  int{*→Alice} x;
  int{*→Alice} z;
  int y = x;
  z = y;
```
Usually, it is not necessary to annotate local variables with labels. The labels appearing in method signatures are enough to infer their labels.
**However, I strongly suggest you to annotate every variable, since it make easier to debug the compiler errors**.

## Implicit flows and program-counter labels

The label of an expression's value varies depending on the evaluation context. This is needed to prevent leaks through implicit flows: channels created by the control flow structure itself. To prevent information leaks through implicit flows, the compiler associates a program-counter label (`pc`) with every statement and expression, representing the information that might be learned from the knowledge that the statement or expression was evaluated.

For example, consider the following program, which is obviously equivalent to the statement `l = h`, assuming `h` and `l` are boolean variables:
```Java
l = false;
if (h) {
    l = true;
}
```

If `l` contains public (low confidentiality) information and `h` contains secret (high confidentiality) information, this program is not secure. The solution is that by conditioning on the variable `h`, the if statement makes the `pc` of the assignment to `l` at least as restrictive as `{h}` (the same policy governing `h`). Assume no information can be learned from the fact that the program is executed, and that the program executes with the highest possible integrity (that is, initially pc = `{*←*}`). In this case, the value of `pc` during the consequent clause is `{h}`. After the if statement, it is again true that `pc = {*←*}`, because no information about `h` can be deduced from the fact that the statement after the if statement is executed.  The label of a literal expression (e.g., `true`) is the same as its `pc`, or `{h}` in this case. So the assignment is permitted only if the label `{l}` is at least as restrictive as the label `{h}`. This would not be true if `l` was public and `h` was secret.

One way to think about the program-counter label is that there is a distinct pc for every basic block in the program. In general, the flow of control within a program depends on the values of certain expressions. At any given point during execution, various values have been observed in order to decide to arrive at the current basic block; therefore, the labels of these values affect the current pc. The Jif type system ensures that the pc label is at least as restrictive as the labels of all the variables on which the program counter depends.

An example is provided in 
[ImplicitFlow01.jif](../Tutorial/src-jif/ImplicitFlow01.jif)
. If you decomment the line `// l = true;` the Jif compile raises the following error:
```
       [apply] /home/guancio/Sources/dd2460/jif/Tutorial/src-jif/ImplicitFlow01.jif:11: 
       [apply]     Unsatisfiable constraint
       [apply]     	general constraint:
       [apply]     		rhs.nv ⊑ label of var l
       [apply]     	in this context:
       [apply]     		{caller_pc ⊔ ⊤→Bob; ⊥←⊥} ⊑ {caller_pc ⊔ ⊤→Bob,Chuck; ⊥←⊥}
       [apply]     	cannot satisfy equation:
       [apply]     		{caller_pc ⊔ ⊤→Bob; ⊥←⊥} ⊑ {caller_pc ⊔ ⊤→Bob,Chuck; ⊥←⊥}
       [apply]     	in environment:
       [apply]     		[]
       [apply]     Label Descriptions
       [apply]     ------------------
       [apply]      - rhs.nv = label of successful evaluation of right hand of assignment
       [apply]      - rhs.nv = {caller_pc ⊔ ⊤→Bob; ⊥←⊥}
       [apply]      - label of var l = {caller_pc ⊔ ⊤→Bob,Chuck; ⊥←⊥}
       [apply]      - caller_pc = pc label
       [apply]     More information is revealed by the successful evaluation of the right 
       [apply]     hand side of the assignment than is allowed to flow to the local variable
       [apply]      l.
       [apply]     		l = true;
       [apply]     		^
       [apply] 1 error.
```
The right hand of assignment (`true`) has label `{caller_pc ⊔ *→Bob; ⊥←⊥}`:
* `⊥←⊥` is an integrity policy, we can ignore it
* `*→Bob` is the policy of `h`. This policy has been attached to the program counter, since we reach this assignment only if `h` holds.
* Intuitively, `caller_pc` informs us which policy a caller wants to be respected by this method. The fact that someone invoked our main function can also leak information, we will see this
  in *Caller Pc` section`.

Thus the assignment cannot be allowed, since this leaks information that should be accessed only by `Bob` to a variable (`l`) that can also be accessed by `Chuck`.

Sometime can be difficult to debug these problems. Take [ImplicitFlow02.jif](../Example02/src-jif/ImplicitFlow02.jif).
```Java
		boolean {* -> Bob,Chuck} l = false;
		boolean {* -> Bob} h = true;
		if (h) {
			boolean {* -> Bob,Chuck} v = true;
   	 		l = v;
		}
```
The compiler does not raise an error for the assignment `boolean {* -> Bob,Chuck} v = true;`, but fails on the assignment `l = v;`. Intuitively:
* The label of a constant is always the same as the label of the `pc`
* The real label of a variable `T{L} v` is `{L;pc_label}`. That is: the label of a variable is always restrictive at least as the label of the `pc`.

Thus, the actual label of `v` is `{* -> Bob,Chuck; h; caller_pc} = {* -> Bob; caller_pc}`.
Obviously, the label of a program counter can depends on multiple variables, for example when the branch condition depends on complex expressions
(see [ImplicitFlow03.jif](../Example02/src-jif/ImplicitFlow03.jif)
```Java
		int {* -> Bob} v1 = 1;
		int {* -> Bob} v2 = 2;
		int {* -> Chuck} v3 = 3;
		if (v2 == v3) {
	    		v1 = 10;
		}
```
or due to nested branches
(see [ImplicitFlow04.jif](../Example02/src-jif/ImplicitFlow04.jif)
```Java
		int {* -> Bob} v1 = 1;
		int {* -> Bob} v2 = 2;
		int {* -> Chuck} v3 = 3;
		if (v2 > 0) {
			if (v3 > 0) {
    				v1 = 10;
    			}
		}
```

A related issue is the transmission of information through the termination or non-termination of a program.
Consider the execution of a while statement `while (h != 0) { ... }`. According to the Jif type system, assuming that initially `pc={*←*}`, then after the statement terminates, `pc={*←*}`, using the same reasoning as for the `if` statement. This labeling might seem strange, because we know the value of `h` when we arrive at the final basic block. However, arriving at the final block gives no information about the value of `h` before the code started. Therefore, Jif does not attempt to control information transfers through termination channels.
This is exemplified by [TerminationInsensitive01.jif](../Example02/src-jif/TerminationInsensitive01.jif).
Jif also ignores timing channels, which are an issue for concurrent programming languages. Jif does not support the Java thread model for concurrent programming. 


## Methods
### Method invocation
Take the example in [Methods01.jif](../Example02/src-jif/Methods01.jif) and uncomment the assignment `a=true`
```Java
	static boolean {*->Bob} a;

	public static void hello() {
		a = true;
	}
```
The compiler yields the following error
```
       [apply] /home/guancio/Sources/dd2460/jif/Tutorial/src-jif/Methods01.jif:9: 
       [apply]     Unsatisfiable constraint
       [apply]     	general constraint:
       [apply]     		rhs.nv ⊑ label of field a
       [apply]     	in this context:
       [apply]     		{caller_pc} ⊑ {⊤→Bob}
       [apply]     	cannot satisfy equation:
       [apply]     		{caller_pc} ⊑ {⊤→Bob}
       [apply]     	in environment:
       [apply]     		[]
       [apply]     Label Descriptions
       [apply]     ------------------
       [apply]      - rhs.nv = label of successful evaluation of right hand of assignment
       [apply]      - rhs.nv = {caller_pc}
       [apply]      - label of field a = {⊤→Bob}
       [apply]      - caller_pc = pc label
       [apply]     More information is revealed by the successful evaluation of the right 
       [apply]     hand side of the assignment than is allowed to flow to the field a.
       [apply] 		a = true;
       [apply] 		^
       [apply] 1 error.
```
Why this program fail? Why the compilation successes if we remove the static field `a` and we declare `a` inside the method body with the label `*->Bob`?

Regarding the first question. When we compile this class (and method) we do not know the code of all the possible callers. In particular we do not know the control
flow of the caller and if this depends on same strong confidential policy. For example, the caller can be the following code
```Java
boolean {*->Alice} cnd = true;
if (cnd) {
	Methods01.hello();
}
```
The caller invokes `hello` only if `cnd` holds: that is, the label of the program counter at the point of invocation is the same as the one of `cnd` (`*->Alice`).
If we do not put any restriction, the fact that the static field `a` is updated (information that is accessible by `Bob`) disclose information about the value of the variable `cnd`, which should accessible only by `Alice`.

To allow a modular compilation (i.e. prevent the compiler to retype all classes when one single class is changed),
we cannot assume to know all the caller of the method `hello`, thus we do not know the label of the program counter at the point of invocation.
For this reason, the compiler uses a metavariable to represent this information (`caller_pc`) and uses it as label of the initial program counter of the method.
Without any further restriction, we cannot guarantee that `{caller_pc} ⊑ {*→Bob}`, thus the assignment fails.

Regarding the second question, the following code can be compiled successfully:
```Java
	public static void hello() {
		boolean {*->Bob} a;
		a = true;
	}
```
Also in this case we do not know the label of the program counter of the caller, thus the initial program counter has label `caller_pc`. However, like discussed in 
*Implicit flows and program-counter labels*, the real label of the local variable `a` is `{*->Bob;caller_pc}`, thus the assignment succeeds.


Intuitively, we must restrict the possible labels of the caller's program counter if we want to update any field of a class.
This can be done via the `begin-label` annotation. This is written between the method name and the list of arguments.
A begin-label `{L}` ensures that the method can be called only if the `pc` of the caller is *no more restrictive* than `{L}`;
the `begin-label` also ensures that the method can only update locations with a label at least as restrictive as `{L}`.
These two restrictions combined ensure that there will not be implicit information flow via invocation of the method.
```Java
	static boolean {*->Bob} a;

	public static void hello{*->Bob,Chuck}() {
		a = true;
	}
```
In this example, we allow to invoke the method `hello` only from program locations that depends on information that can be known by both `Bob` and `Chuck`.
Since we update only information accessible by `Bob`, we do not leak any information.

The method `hello` can be invoked by the following caller
```Java
	public static void main{*->_}(String [] params) {
		hello();
	}
```
Notice that the main method `begin-label` is `{*->_}`: that is the invocation of the main method cannot depend on any classified data, thus it is secure to invoke
the method `hello` from `main`. If we remove the `begin-label` from `main` we get the following error
```
       [apply] /home/guancio/Sources/dd2460/jif/Tutorial/src-jif/Methods01.jif:15: 
       [apply]     Unsatisfiable constraint
       [apply]     	general constraint:
       [apply]     		pc ⊑ callee_PC_bound
       [apply]     	in this context:
       [apply]     		{caller_pc} ⊑ {⊤→Bob,Chuck}
       [apply]     	cannot satisfy equation:
       [apply]     		{caller_pc} ⊑ {⊤→Bob,Chuck}
       [apply]     	in environment:
       [apply]     		[]
       [apply]     Label Descriptions
       [apply]     ------------------
       [apply]      - pc = label of the program counter at this call site
       [apply]      - pc = {caller_pc}
       [apply]      - callee_PC_bound = lower bound on the side effects of the method public
       [apply]      static void hello()
       [apply]      - callee_PC_bound = {⊤→Bob,Chuck}
       [apply]      - caller_pc = pc label
       [apply]     Calling the method at this program point may reveal too much information 
       [apply]     to the receiver of the method call. public static void hello() can only 
       [apply]     be invoked if the invocation will reveal no more information than the 
       [apply]     callee's begin label, callee_PC_bound. However, execution reaching this 
       [apply]     program point may depend on information up to the PC at this program 
       [apply]     point: pc.
       [apply] 		hello();
       [apply] 		^-----^
       [apply] 1 error.
```
Since we do not know anything about the caller of `main`, its initial program counter has label `caller_pc` which is unbounded.
This does not guarantee that the label of the caller's pc is less restrictive of the `hello` begin-label, therefore there can be an informatino leackage.

A further example of caller of the method `hello` is the following code
```Java
	public static void main{}(String [] params) {
		boolean {*->Alice,Bob,Chuck} cnd = true;
		if (cnd) {
			hello();
		}
	}
```
In this case, the invocation of `hello` depends on the value of the variable of `cnd`: that is the label of the caller's pc is
the same of the label of `cnd`: `{*->Alice,Bob,Chuck}`. Informally, `Alice`, `Bob`, and `Chuck` all know that `hello` will be invoked.
Thus the method call succeeds. On the other hand, if we change the policy of `cnd` to `{*->Alice,Chuck}` we get the following error:
```
       [apply] /home/guancio/Sources/dd2460/jif/Tutorial/src-jif/Methods01.jif:17: 
       [apply]     Unsatisfiable constraint
       [apply]     	general constraint:
       [apply]     		pc ⊑ callee_PC_bound
       [apply]     	in this context:
       [apply]     		{⊤→Alice,Chuck; ⊥←⊥ ⊔ caller_pc} ⊑ {⊤→Bob,Chuck}
       [apply]     	cannot satisfy equation:
       [apply]     		{⊤→Alice,Chuck} ⊑ {⊤→Bob,Chuck}
       [apply]     	in environment:
       [apply]     		[]
       [apply]     Label Descriptions
       [apply]     ------------------
       [apply]      - pc = label of the program counter at this call site
       [apply]      - pc = {⊤→Alice,Chuck; ⊥←⊥ ⊔ caller_pc}
       [apply]      - callee_PC_bound = lower bound on the side effects of the method public
       [apply]      static void hello()
       [apply]      - callee_PC_bound = {⊤→Bob,Chuck}
       [apply]      - caller_pc = pc label
       [apply]     Calling the method at this program point may reveal too much information 
       [apply]     to the receiver of the method call. public static void hello() can only 
       [apply]     be invoked if the invocation will reveal no more information than the 
       [apply]     callee's begin label, callee_PC_bound. However, execution reaching this 
       [apply]     program point may depend on information up to the PC at this program 
       [apply]     point: pc.
       [apply] 			hello();
       [apply] 			^-----^
       [apply] 1 error.
```
Since `{*→Alice,Chuck} ⋢ {*→Bob,Chuck}`.

#### Restricriveness of begin-label
To summarize, let `L` be the begin-label of a method:
 * The initial pc-label of the method is `L`. Therefore, all expressions in the method
   and it's local variables have label at least as restrictive as `L`
 * The caller cannot have a pc-label that is more restrictive than the begin-label
 * Side effects cannot modify fields that have labels less restrictive than `L`.
 * If methods `a` and `b` have labels `L1` and `L2` respectively, with `L1 ⊑ L2`, then the method `b` can be
   invoked from everywhere the method `a` can be invoked


### Parameters of methods
Methods can receive parameters. In Jif, a parameter is always `final`
and can be annotated with a label `{L}`, which identify an upper bound on the label of any actual arguments.
 * All expressions involving the formal argument have at least at least as restrictive as `L`
 * The caller cannot provide an actual argument whose that is more restrictive than `L`
 * If we change the label of an argument from `L1` to `L2`, with `L1 ⊑ L2`, then the method can be
   invoked with all arguments that can be used with`L1`
 
By default the argument label is `*->*`, which is the most restrictive policy label. Thus the following code
```Java
	static boolean {*->Bob} a;

	public static void hello{*->Bob,Chuck}(boolean v) {
		a = v;
	}
```
produces the following compiler error
```Java
       [apply] /home/guancio/Sources/dd2460/jif/Tutorial/src-jif/Methods02.jif:7: 
       [apply]     Unsatisfiable constraint
       [apply]     	general constraint:
       [apply]     		rhs.nv ⊑ label of field a
       [apply]     	in this context:
       [apply]     		{v ⊔ caller_pc} ⊑ {⊤→Bob}
       [apply]     	cannot satisfy equation:
       [apply]     		{v} ⊑ {⊤→Bob}
       [apply]     	in environment:
       [apply]     		[]
       [apply]     Label Descriptions
       [apply]     ------------------
       [apply]      - rhs.nv = label of successful evaluation of right hand of assignment
       [apply]      - rhs.nv = {v ⊔ caller_pc}
       [apply]      - label of field a = {⊤→Bob}
       [apply]      - v = polymorphic label of formal argument v of method hello (bounded 
       [apply]     above by {⊤→})
       [apply]      - caller_pc = pc label
       [apply]     More information is revealed by the successful evaluation of the right 
       [apply]     hand side of the assignment than is allowed to flow to the field a.
       [apply] 		a = v;
       [apply] 		^
       [apply] 1 error.
```
Since the label of `v` (which is only bounded by `T->T`) is not less restrictive that `*->Bob`.
The parameter's labels are specified like variable labels, as follows
```Java
	public static void hello{*->Bob,Chuck}(boolean {*->Bob,Alice}v) {
		a = v;
	}
```
The formal parameter label is an upper bound on the label of any actual arguments. Thus the following code is
correct
```Java
	public static void main{}(String [] params) {
		boolean {*->Alice,Bob,Chuck} cnd = true;
		hello(cnd);
	}
```
while the following one no, since the `hello` method expect a parameter that is accessible to both `Bob` and `Chuck`.
```Java
	public static void main{}(String [] params) {
		boolean {*->Alice,Chuck} cnd = true;
		hello(cnd);
	}
```
and produces the following error
```
       [apply] /home/guancio/Sources/dd2460/jif/Tutorial/src-jif/Methods01.jif:17: 
       [apply]     Unsatisfiable constraint
       [apply]     	general constraint:
       [apply]     		pc ⊑ callee_PC_bound
       [apply]     	in this context:
       [apply]     		{⊤→Alice,Chuck; ⊥←⊥ ⊔ caller_pc} ⊑ {⊤→Bob,Chuck}
       [apply]     	cannot satisfy equation:
       [apply]     		{⊤→Alice,Chuck} ⊑ {⊤→Bob,Chuck}
       [apply]     	in environment:
       [apply]     		[]
       [apply]     Label Descriptions
       [apply]     ------------------
       [apply]      - pc = label of the program counter at this call site
       [apply]      - pc = {⊤→Alice,Chuck; ⊥←⊥ ⊔ caller_pc}
       [apply]      - callee_PC_bound = lower bound on the side effects of the method public
       [apply]      static void hello()
       [apply]      - callee_PC_bound = {⊤→Bob,Chuck}
       [apply]      - caller_pc = pc label
       [apply]     Calling the method at this program point may reveal too much information 
       [apply]     to the receiver of the method call. public static void hello() can only 
       [apply]     be invoked if the invocation will reveal no more information than the 
       [apply]     callee's begin label, callee_PC_bound. However, execution reaching this 
       [apply]     program point may depend on information up to the PC at this program 
       [apply]     point: pc.
       [apply] 			hello();
       [apply] 			^-----^
       [apply] 1 error.
```

### Method returns
Return label `{L}` is an upper bound on the label of the information returned by the method.
 * Ensures that label of the returned expression is no more
   restrictive then `{L}`
 * Ensures that label of the receiving expression is at least restrictive as `{L}`
 * If we change the return-label of a method from `L2` to `L1`, with `L1 ⊑ L2`, then the method invocation can
   be part of any expression that can use the method with return-label `L2`

The following is a program that can be correctly compiled.
```Java
	public static int hello {*->Bob,Chuck}  (int {*->Bob,Chuck} v) : {*->Bob} {
		return v + 10;
	}
	
	public static void main{}(String [] params) {
		int {*->Alice,Bob,Chuck} val = 1;
		int {*->Bob&Chuck} val2 = hello(val);
	}
```

# Object references
Similarly to variables containing primitive values, object references can have labels likewise.
The following program cannot be compiled:
```Java
		References {*->Bob,Alice}x = new References();
		References {*->Bob,Alice}y = new References();
		boolean {*->Bob,Chuck}z;
		z = (x == y);
```
and produce the following error
```
       [apply] /home/guancio/Sources/dd2460/jif/Tutorial/src-jif/References.jif:11: 
       [apply]     Unsatisfiable constraint
       [apply]     	general constraint:
       [apply]     		rhs.nv ⊑ label of var z
       [apply]     	in this context:
       [apply]     		{caller_pc ⊔ ⊤→Bob,Alice; ⊥←⊥} ⊑ {caller_pc ⊔ ⊤→Bob,Chuck; ⊥←⊥}
       [apply]     	cannot satisfy equation:
       [apply]     		{caller_pc ⊔ ⊤→Bob,Alice; ⊥←⊥} ⊑ {caller_pc ⊔ ⊤→Bob,Chuck; ⊥←⊥}
       [apply]     	in environment:
       [apply]     		[]
       [apply]     Label Descriptions
       [apply]     ------------------
       [apply]      - rhs.nv = label of successful evaluation of right hand of assignment
       [apply]      - rhs.nv = {caller_pc ⊔ ⊤→Bob,Alice; ⊥←⊥}
       [apply]      - label of var z = {caller_pc ⊔ ⊤→Bob,Chuck; ⊥←⊥}
       [apply]      - caller_pc = pc label
       [apply]     More information is revealed by the successful evaluation of the right 
       [apply]     hand side of the assignment than is allowed to flow to the local variable
       [apply]      z.
       [apply] 		z = (x == y);
       [apply] 		^
       [apply] 1 error.
```
In fact, Chuck should not be able to discover anything about the two references `x` and `y`, like if they point to the same object.

Labels of object fields is always restrictive at least as the label of the object reference. For example the expression
`x.c == 10` has label `{x;c}`: i.e. the label of `x` conjunct the label of the field `c`. For this reason the following
fragment cannot be compiled:
```Java
public class References {
	public int {*->Bob,Alice,Chuck} c;

	public static void hello() {
		References {*->Bob,Alice}x = new References();
		boolean {*->Bob,Chuck}z;
		z = (x.c == 10);
	}
}
```
When we type a class in isolation, we do not know how much secret will be the reference to the corresponding objects. For this
reason, non-static methods are typed under the assumption that the label attached to `this` is not more restrictive than
the begin-label. For this reason the following program cannot be compiled:
```Java
public class References02 {
	public static int {*->Bob,Alice,Chuck} a;
	public int {*->Bob,Alice,Chuck} b;

	public void hello() {
		a = b;
	}
}
```
Here, the expression `b` is equivalent to `this.b`, therefore its label is equal to `{*->Bob,Alice,Chuck};{this}`. Since there
is not bound for `begin-label` we cannot guarantee that `{this}` is not more restrictive than the label of `a`.

# Exceptions
Sometime programs fail, for example the following method can fail if `y` is `0`, throwing
an `ArithmeticException` exception.
```Java
	static int {*->Bob} a;

	public static void hello{*->Bob,Chuck}(int {*->Bob}x, int {*->Bob}y) {
		a = x/y;
	}
```
Differently from Java, `RuntimeException` (such as `NullPointerException`, `ClassCastException`, and `ArrayIndexOutOfBoundsException`) must be checked.
Intuitively, a failing program can lead information to be leaked.
In the previous example, both `Bob` and `Chuck` know that this method is invoked. However, if the method fails (due to `y` being `0`),
part of information that should be known only by `Bob` is leaked to `Chuck`.
We have two options:
(1) We intercept the exception, making the method to succeed:
```Java
	public static void hello{*->Bob,Chuck}(int {*->Bob}x, int {*->Bob}y) {
		try {
			a = x/y;
		}
		catch (ArithmeticException ex) {
		}
	}
```
(2) We throw the exception
```Java
	public static void hello1{*->Bob,Chuck}(int {*->Bob}x, int {*->Bob}y) throws ArithmeticException {
		a = x/y;
	}
```
Notice that in the latter case, the Jif compiler produces the following error:
```
       [apply] /home/guancio/Sources/dd2460/jif/Tutorial/src-jif/Exception01.jif:12: 
       [apply]     Unsatisfiable constraint
       [apply]     	general constraint:
       [apply]     		X.n join X.r join Li ⊑ Lr
       [apply]     	in this context:
       [apply]     		{y ⊔ caller_pc} ⊑ {caller_pc}
       [apply]     	cannot satisfy equation:
       [apply]     		{y} ⊑ {caller_pc}
       [apply]     	in environment:
       [apply]     		[]
       [apply]     Label Descriptions
       [apply]     ------------------
       [apply]      - X.n = information that may be gained by the body terminating normally
       [apply]      - X.n = {y ⊔ caller_pc}
       [apply]      - X.r = information that may be gained by exiting the body with a return
       [apply]      statement
       [apply]      - X.r = 0
       [apply]      - Li = Lower bound for method output
       [apply]      - Li = Exception01.provider
       [apply]      - Lr = return label of the method
       [apply]      - Lr = {caller_pc}
       [apply]      - y = polymorphic label of formal argument y of method hello1 (bounded 
       [apply]     above by {⊤→Bob})
       [apply]      - caller_pc = pc label
       [apply]      - 0 = pseudo-label representing a path that cannot be taken
       [apply]     The method return label, Lr, is an upper bound on how much information 
       [apply]     can be gained by observing that this method terminates normally (i.e., 
       [apply]     terminates without throwing an exception). The method body may reveal 
       [apply]     more information than this. The return label of a method is declared 
       [apply]     after the variables, e.g. "void m(int i):{Lr}".
```
The compiler inform us that by observing the correct termination of the program,
an adversary can learn information about `y` (i.e. that `y` is not `0`).
We can fix the problem, by defining the method return label as `{*->Bob}` (Notice
that the return label is the label after `:` after the parameters and before the exceptions):
```Java
	public static void hello1{*->Bob,Chuck}(int {*->Bob}x, int {*->Bob}y) : {*->Bob} throws ArithmeticException {
		a = x/y;
	}
```
Notice that the return label `{*->Bob,Chuck}` does not allow to compile the program.
Formally, the normal termination label for the method body must be no more restrictive than the return-label of the method joined with the `caller_pc` label. 
Similarly, the information that is gained by knowing the method terminates via a return statement must be no more restrictive than the `end-label` of the method joined with the `caller_pc` label.

In addition, the label associated with any exception thrown by the method body must be no more restrictive than the labels for the appropriate exceptions declared in the throws clause of the method, joined with the `caller_pc` label. More precisely, if label checking the method body determines that the method body may throw an exception of class `C` with label `LC`, and the method declaration says that the method may throw an exception of class `D` with label `LD`, where `C` is a subclass of `D`, then we must have `LC ⊑ LD ⊔ caller_pc`.

The method `hello1` can be invoked by the following caller
```Java
	public static void main{}(String [] args) {
		int {*->Bob} x = 1;
		int {*->Bob,Chuck} y = 1;
		int {*->Bob} z;
		try {
			hello1(x,y);
			z = 1;
		} catch (ArithmeticException ex) {
		}
	}
```
However, if we change the label of `z` to `*->Alice`, the compiler produces the following error
```
       [apply] /home/guancio/Sources/dd2460/jif/Tutorial/src-jif/Exception01.jif:22: 
       [apply]     Unsatisfiable constraint
       [apply]     	general constraint:
       [apply]     		rhs.nv ⊑ label of var z
       [apply]     	in this context:
       [apply]     		{⊤→Bob} ⊑ {⊤→Alice}
       [apply]     	cannot satisfy equation:
       [apply]     		{⊤→Bob} ⊑ {⊤→Alice}
       [apply]     	in environment:
       [apply]     		[]
       [apply]     Label Descriptions
       [apply]     ------------------
       [apply]      - rhs.nv = label of successful evaluation of right hand of assignment
       [apply]      - rhs.nv = {⊤→Bob}
       [apply]      - label of var z = {⊤→Alice}
       [apply]      - ⊤→Bob; ⊥←⊥ = pc label
       [apply]     More information is revealed by the successful evaluation of the right 
       [apply]     hand side of the assignment than is allowed to flow to the local variable
       [apply]      z.
       [apply] 			z = 1;
       [apply] 			^
       [apply] 1 error.
```
In fact, after the invocation of `hello1`, the program counter of the caller is joined with the return
label of `hello1`, since the caller can discover that the method succeeded. In this case the label of `pc`
became `{*→Bob}`, thus modifying something that is accessible from `Alice` can leak information.

## Accessing objects
Among other `RuntimeException` that must be checked, all `NullPointerException` must be explicitly handled.
For example the following program has a compilation problem:
```Java
public class Exception02 {
	public Exception02 {*->Bob,Chuck} next;
	public int {*->Bob,Chuck} value;

	public void hello() {
		int {*->Bob} tot = 0;
		tot += this.value;
		tot += this.next.value;
	}
}
```
since `this.next` can be `null`, accessing `this.next.value` can raise a `NullPointerException`.
First option is to annotate the method with the throws clause, however this also requires
to change the return label, since correct termination of the program depends on information
accessible only by `Bob` and `Chuck`.
```Java
public class Exception02 {
	public Exception02 {*->Bob,Chuck} next;
	public int {*->Bob,Chuck} value;

	public void hello() : {*→Bob,Chuck} throws NullPointerException {
		int {*->Bob} tot = 0;
		tot += this.value;
		tot += this.next.value;
	}
}
```
Another option is to catch the exception, which does no requires to specify the return-label:
```Java
	public void hello1() {
		int {*->Bob} tot = 0;
		tot += this.value;
		try {
			tot += this.next.value;
		} catch (NullPointerException ex) {
		}
	}
```
Finally, we can rely on a primitive constant propagation mechanism available in Jif:
```Java
	public void hello2() {
		int {*->Bob} tot = 0;
		tot += this.value;
		Exception02 localNext = this.next; 
		if (localNext != null) {
			tot += localNext.value;
		}
	}
```
Jif discovers that `localNext` cannot be `null` when the `if-body` is executed, thus there is no need
of checking the exception.
Notice that the following program cannot be compiled:
```Java
	public void hello3() {
		int {*->Bob} tot = 0;
		tot += this.value;
		if (this.next != null) {
			tot += this.next.value;
		}
	}
```
There are two reasons for this: (i) the Jif procedure for constant propagation is quite simple and (ii) there
can be another thread that changes this.next after that the `if` condition has been tested.


------------------------------------------------------------------------------------------

# Second Lecture
## Final remarks on OO
References can be annotated with security policies. 
Label of expressions that access fields is `pc ; L-ref ; L-field`, for example
```Java
class A {
   int {T1} f;
}
...
A {T2} x = new A();
```
Label of `x.f` is `pc;T1;T2`, where `pc` is the label of the program counter where
the expression `x.f` is used.

Labels for methods are designed for modular verification,
enabling to check  type of a method without looking at
the implementation of the other methods and of
the code of the callers.
```Java
int {return-label} foo {begin-label}
   (int {parameter1-label}x, int {parameter2-label} y) : {end-label} {
   ...
}
```
 * Begin-label:
   * upper bound on the secrecy of the caller `PC` (it is
     the initial label of PC when the method is typed)
   * {* → _} means that the caller PC must be public
   * {* → Alice, Bob} means that the caller PC can depend on
	information accessible by both Alice
	and Bob
   * The method cannot have side effects to variables that
     have label less restrictive than Begin-label
 * Parameter-label:
   * upper bound on the secrecy of the arguments
   * {* → _} means that the actual argument must be public
   * {* → Alice, Bob} means that the argument can depend
     on information accessible by both
     Alice and Bob
   * The method must respects the argument policy
 * Return-label: policy of the return value
   * {* → _} means that the return value does no contain classified information
   * The expression returned by the method (e.g. x) can not have
      a label more restrictive than the return-label
   * The method requires the caller to respect the return policy
 * End-label: information that can be learned by observing
	whether the method terminates normally
   * The `PC` when the method returns or throws an exception cannot have a label
     more restrictive then the `end-label`
   * The `PC` of the caller becomes restrictive at least as the method `end-label`
     after the invocation.
```Java
line 10: x.method(y)
line 11: z = 1
```
 * Method invocation. Assume:
   * `pc-label` at line 10 ⊔ label of `x` cannot be more restrictive that `pc-label` of `method`
   * `pc-label` at line 10 ⊔ label of `x` ⊔ label of `y` cannot be more restrictive that `parameter-label` of `method`
	(notice ⊔ label of `x` ⊔. In fact the argument is passed only if `x` is not null)
   * Label of `z` can not be less restrictive that the return-label of `method`
   * `pc-label` at line 11 is `pc-label` at line 10 ⊔ `end-label` of `method`
   * Constructors can be seen as static-methods.


# Decentralized label model (2)
Jif allows mutually distrusting entities to express information-flow security policies for confidentiality and integrity. Security policies are expressed using the decentralized label model (DLM).
In this section, we describe the core concepts of the DLM: principals, policies, and labels, and present the syntax used to write labels in Jif programs.

## Principals
A principal is an entity with some power to observe and change certain aspects of the system. The goal of Jif is to permit principals to express security requirements and to enforce them. 

## Confidentiality policies
Until now we used `*` in all policies. Jif permits a more fine grade control on the
principals that express their security concerns about information.

A reader policy allows the owner of the policy to specify which principals the owner permits to read a given piece of information.
A reader policy is written `o -> r`, where the principal `o` is the owner of the policy, and the principal `r` is the specified reader.
(until now, we always used `o=*`).
A reader policy `o -> r` says that `o` permits a principal `q` to read information only if `q` can act for either the owner of the policy or the specified reader `r`.
As a formal semantics for reader policies, we define the function `readers(p, c)` to be the set of principals that principal `p` believes should be allowed to read information according to reader policy `c`:
```
readers(p, o->r) = {q  |  if o ≽ p then (q ≽ o or q ≽ r)}
```
A principal `p` believes that a reader policy `c` should restrict the readers of information only if the owner of the policy can act for `p`. The parameterization on `p` is important in the presence of mutual distrust, because it allows the significance of the policy to be expressed for every principal independently. If principal `o` owns a policy that restricts the readers of information, it does not necessarily mean that another principal `p` also believes those restrictions should apply. Thus, if `o` does not act for `p`, then `readers(p, o->r)` is the set of all principals; in other words, `p` does not credit the policy with any significance.

Let assume `Alice`, `Bob`, `Chuck` and `Dolores` are four principals (the only ones in the system), with `Dolores` acting for both `Alice` and `Chuck` (i.e. `Dolores ≽ Alice` and `Dolores ≽ Chuck`).

 * `readers(Alice, Alice->*)` is `{Alice, Dolores, *}`: `Alice` act for herself, so she believe that the policy is in place (`o ≽ p` holds). The participants that can act for Alice are `Alice, Dolores, *`.
 * `readers(Bob, Alice->*)` is `{Alice, Bob, Chuck, Dolores, *, _}`: `Alice` does not act for `Bob`, so he does not believe that the policy is in place (`o ≽ p` does not hold).
   Similarly, `readers(Chuck, Alice->*)` is `{Alice, Bob, Chuck, Dolores, *, _}` and `readers(*, Alice->*)` is `{Alice, Bob, Chuck, *, _}`.
 * `readers(_, Alice->*)` is `{Alice, Dolores, *}`. Every participant can act-for `_`, so `_` believes that the policy is in place.
 * `readers(Alice, Alice->Bob)` is `{Alice, Bob, Dolores, *}`. These are the participants that can act for either `Alice` or `Bob`.
 * `readers(Bob, Bob->Alice&Chuck)` is `{Bob, Dolores, *}`: `Bob` acts for himself, so he believes that the policy is in place (`o ≽ p` holds). The participants that can act for `Bob` are `Bob, *`, while
   the participants that can act for `Alice&Chuck` are `Dolores, *`
 * `readers(Bob, Alice&Bob->Alice&Chuck)` is `{Dolores, *}`, since `Alice&Bob` acts for `Bob`
 * `readers(Alice, Alice&Bob->Alice&Chuck)` is `{Dolores, *}`, since `Alice&Bob` acts for `Alice`
 * `readers(Dolores, Alice&Bob->Alice&Chuck)` is `{Alice, Bob, Chuck, Dolores, *, _}`, since `Alice&Bob` does not act for `Dolores`
 * `readers(Dolores, Alice&Bob&Chuck->Alice&Chuck)` is `{Dolores, *}`, since `Alice&Bob&Chuck` acts for `Dolores`
 * `readers(Dolores, *->Alice&Chuck)` is `{Dolores, *}`, since `*` acts for `Dolores`
 * `readers(_, *->Alice&Chuck)` is `{Dolores, *}`, since `*` acts for `_`
 * `readers(_, *->Bob,Dolores)` is `{Bob,Dolores, *}`

### Ordering confidentiality policies. 
Using the `readers(∙, ∙)` function, we can define a "no more restrictive than" relation `⊑` on confidentiality policies. For two confidentiality policies `c` and `d`, we have `c ⊑ d` if and only if for every principal `p`, `readers(p, c) ⊇ readers(p, d)`. If `c ⊑ d` then every principal `p` believes that `c` permits at least as many readers as `d` does. The confidentiality policy `c` is thus of lower (or equal) confidentiality than `d`, and so information labeled `c` can be used in at least as many places as information labeled `d`: policy `c` is no more restrictive than policy `d`.

* `Alice->_ ⊑ Alice->Bob ⊑ Alice->*`
* `Alice->_ ⊑ Alice->Alice ⊑ Alice->Dolores ⊑ Alice->*`
* `Alice->Chuck ⊑ Alice->Alice`
* `Bob->Alice ⋢ Alice->Dolores`
* `Bob->Alice ⊑ Bob&Alice->Dolores`
* `ALice->Alice ⊑ Bob&Alice->Dolores`
* `ALice->Alice ⊑ Dolores->Dolores`
* `Bob->Alice ⋢ Dolores->Dolores`
* `Bob->Bob ⋢ Alice->Alice,Bob`
* `Bob->Bob ⊑ Bob->Alice,Bob`


The relation `⊑` forms a pre-order over confidentiality policies, and its equivalence classes form a lattice. The operators `⊔` and `⊓` are the join and meet operators of this lattice. The least restrictive confidentiality policy is the reader policy `⊥->⊥` (or `_ -> _`), where `⊥` is a principal that all principals can act for, since all principals believe that information labeled `⊥→⊥` is allowed to be read by any principal. The most restrictive expressible confidentiality policy is `⊤→⊤`, where `⊤` is a principal that can act for all principals; information labeled `⊤→⊤` is allowed to be read only by principal `⊤`.

## Declassification
Few useful programs respect noninterference. Hereafter there are four examples of programs that do not respect perfect noninterference.
The first example is a password-checker
```Java
	public static void login() {
		String {*->_} input = "Hello";
		String {Alice->Alice} password = "PWD";
		boolean {*->_} logged = input.equals(password);
	}
```
By allowing a user to type a password and attempt a login in a system, we disclose some information
about the admin password (i.e. `PWD`): the quality between the password and the user's input.

The second example is a "statistical" program
```Java
	public static void average() {
		int {Alice->Alice} v1 = 10;
		int {Bob->Bob} v2 = 20;
		int {Chuck->Chuck} v3 = 17;
		int {*->_} average = (v1+v2+v3)/3;
	}
```
We cannot leak the average salary of several users, since this depends on private information.
Actually, we can not leak this information to any user, i.e. `int {*->Bob} average = ...` is also
not ok.

The third example is the implementation of One Time Pad.
```Java
	public static void otp() {
		int {Alice->Alice} secret = 62;
		int {Alice->Alice} random = 12345;
		int {*->_} output = secret ^ random;
	}
```
Even if one-time pads is information-theoretically secure (i.e. the encrypted message provides no information about the original message to a cryptanalyst),
the program cannot be typed, since `output` depends on information that should be accessible only by `Alice`.

The last example is the encryption of a message
```Java
	public static void RSA() {
		int {Alice->Alice,Bob} message = 62;
		int {*->_} bobPublicKey = 12345;
		int {*->_} output = message ^ bobPublicKey; // Super complex operation implements RSA encryption
	}
```
Here, `Alice` sends a message to `Bob` (therefore both of them can access the content of the message).
The message is encrypted using the public key of `Bob`, therefore only the owner of the private key (`Bob`) can
decrypt the message. In general, mechanisms to guarantee noninterference have no support for this kind of reasoning, which
requires to argue about computational complexity of operations.

To handle this cases we use declassification, which is dangerous because violate noninterference.
Notice that in these examples we always specified the principal that owns the information.
This allows us to express who cares about the compliance with the policy.
To declassify information (i.e. make its policy weaker) the program (i.e. class and method) must
have the `Authority` of the policy owner.
For example:
```Java
public class A authority (Alice & Bob) {
  public void hello() where authority (Alice) {...}
  public void hello2() where authority (Bob) {...}
  public void hello3() where authority (Alice&Bob) {...}
}
```
 * Class `A` has authority of both `Alice` and `Bob`, therefore we know that this class can potentially
   declassify information (i.e. violate security policies expressed by) `Alice` and `Bob`, and that
   this class will never declassify information owned by `Chuck`.
 * Method `hello` has authority of `Alice`, therefore it can declassify only information owned by `Alice`
 * Method `hello2` has authority of `Bob`, therefore it can declassify only information owned by `Bob`
 * Method `hello3` has authority of both `Alice` and `Bob`, therefore we know that this class can potentially
   declassify information  `Alice` and `Bob`
In general, the authority of a class must always `act-for` the authority of every method of the class.
The mechanism of Authority allows us to clearly identify where information is leaked and the owner of
the policies that can be violated.


The password checker can be implemented by declassifying the result of string comparison:
```Java
class Declassification authority (Alice) {
	public static void  login1 {*->_} () where authority (Alice) {
		String {*->_} input = "Hello";
		String {Alice->Alice} password = "PWD";
		boolean {*->_} logged = declassify(
			input.equals(password),
			{Alice->Alice} to {*->_}
		);
	}
}
```
The expression `declassify(exp, p1 to p2)` is correctly typed is:
 1. `exp` is an expression having policy `p3` that is less restrictive than `p1` (in this example `Alice->Alice`)
 2. the method has Authority a principal that act-for the owner of the policy `p1` (here `Alice`)
 3. the resulting expression has policy `p2` (here `*->_`).

Another examples are the following (here we assume that the input is owned by `Bob`):
```Java
	public static void  login2 {Bob->Bob} () where authority (Alice) {
		String {Bob->Bob} input = "Hello";
		String {Alice->Alice} password = "PWD";
		boolean {Bob->Bob} logged = declassify(
			input.equals(password),
			{Bob->Bob;Alice->Alice} to {Bob->Bob}
		);
	}
	public static void  login3 {Bob->Bob} () where authority (Alice) {
		String {Bob->Bob} input = "Hello";
		String {Alice->Alice} password = "PWD";
		boolean {Bob->Bob} logged = declassify(
			input.equals(password),
			{Bob->Bob;Alice->Alice&Bob} to {Bob->Bob}
		);
	}
```
Notice that in `login3` the policy `{Bob->Bob;Alice->Alice&Bob}` is relaxed, even if the expression has label `input.equals(password)`.
Notice also that we specified the begin-label of the method (`Bob->Bob`). In fact, if we do not know an upper bound on the confidentiality
of the program counter, then the expression `input.equals(password)` has label `Bob->Bob;Alice->Alice;caller_pc`. Therefore, we can not guarantee
that the label of the expression is less restrictive than the declassified policy (i.e. `{Bob->Bob;Alice->Alice}`). For this reason
the following program cannot be compiled:
```Java
	public static void  login4 () where authority (Alice) {
		String {Bob->Bob} input = "Hello";
		String {Alice->Alice} password = "PWD";
		boolean {Bob->Bob} logged = declassify(
			input.equals(password),
			{Bob->Bob;Alice->Alice} to {Bob->Bob}
		);
	}
```
and produces the following errof
```
       [apply]     Unsatisfiable constraint
       [apply]     	general constraint:
       [apply]     		l ⊑ from
       [apply]     	in this context:
       [apply]     		{Bob→Bob; Alice→Alice; ⊥←⊥ ⊔ caller_pc} ⊑ {Bob→Bob; Alice→Alice}
       [apply]     	cannot satisfy equation:
       [apply]     		{Bob→Bob; Alice→Alice; ⊥←⊥ ⊔ caller_pc} ⊑ {Bob→Bob; Alice→Alice}
       [apply]     	in environment:
       [apply]     		[]
       [apply]     Label Descriptions
       [apply]     ------------------
       [apply]      - l = {Bob→Bob; Alice→Alice; ⊥←⊥ ⊔ caller_pc}
       [apply]      - from = {Bob→Bob; Alice→Alice}
       [apply]      - caller_pc = pc label
       [apply]     This declassify expression is allowed to declassify information labeled 
       [apply]     up to from. However, the label of the expression to declassify is l, 
       [apply]     which is more restrictive than is allowed.
       [apply] 		boolean {Bob->Bob} logged = declassify(
       [apply] 		                            ^----------
       [apply] 		...
       [apply] 		);
       [apply] 		^
       [apply] 1 error.
```
An alternative well-typed login program is the following
```Java
	public static void  login5 {*->_}() where authority (Alice) {
		String {*->_} input = "Hello";
		String {Alice->Alice} password = "PWD";
		String {*->_} publicPwd = declassify(
			password,
			{Alice->Alice} to {*->_}
		);
		boolean {*->_} logged = input.equals(publicPwd);
	}	
```
Even if `login5` is equivalent to `login1` it makes use of a *bad practice*:
it declassifies too much information. In fact declassification is dangerous, since
it permits to violate non-interference. `login5` declassifies the whole password of `Alice`, therefore
the whole password can be leaked due to a programming error outside the point of declassification, like in the following example:
```Java
	static String {*->_} publicString;
	public static void  login6 {*->_}() where authority (Alice) {
		String {*->_} input = "Hello";
		String {Alice->Alice} password = "PWD";
		String {*->_} publicPwd = declassify(
			password,
			{Alice->Alice} to {*->_}
		);
		boolean {*->_} logged = input.equals(publicPwd);
		publicString = publicPwd;
	}
```
This cannot happen when we declassify only the result of the equality test.

The `average` program can be fixed using the following annotations
```Java
	public static void average1 {*->_} () where authority (Alice,Bob,Chuck) {
		int {Alice->Alice} v1 = 10;
		int {Bob->Bob} v2 = 20;
		int {Chuck->Chuck} v3 = 17;
		int {*->_} average = declassify(
			(v1+v2+v3)/3,
			{Alice&Bob&Chuck->Alice&Bob&Chuck} to {*->_}
		);
	}
```
Notice that the method needs the authority of all the three participants, and that the policy that
is relaxed (i.e. `Alice&Bob&Chuck->Alice&Bob&Chuck`) is not less restrictive than the label of the expression
that is declassified (i.e. `Alice->Alice; Bob->Bob; Chuck->Chuck`).
An alternative implementation is the following:
```Java
	public static void average2 {*->_} () where authority (Alice,Bob,Chuck) {
		int {Alice->Alice} v1 = 10;
		int {Bob->Bob} v2 = 20;
		int {Chuck->Chuck} v3 = 17;
		int {*->_} p1 = declassify(v1, {Alice->Alice} to {*->_});
		int {*->_} p2 = declassify(v2, {Bob->Bob} to {*->_});
		int {*->_} p3 = declassify(v3, {Chuck->Chuck} to {*->_});
		int {*->_} average = (p1+p2+p3)/3;
	}
```
However, this implementation is discouraged, since it declassifies all private data instead of the average.

Clearly, we do not need the authority of `Bob` if the average remains under his authority:
```Java
	public static void average3 {Bob->Bob} () where authority (Alice,Chuck) {
		int {Alice->Alice} v1 = 10;
		int {Bob->Bob} v2 = 20;
		int {Chuck->Chuck} v3 = 17;
		int {Bob->Bob} average = declassify(
			(v1+v2+v3)/3,
			{Alice&Bob&Chuck->Alice&Bob&Chuck} to {Bob->Bob}
		);
```

Finally, we can also declassify the program counter when the control flow depends on information that are controlled
by a security policy. For instance, an alternative implementation of the login function is the following:
```Java
	public static void  login7 {*->_} () where authority (Alice) {
		String {*->_} input = "Hello";
		String {Alice->Alice} password = "PWD";
		boolean {*->_} logged = false;
		if (input.equals(password)) {
			declassify({Alice->Alice} to {*->_}) {
				logged = true;
			}
		}
	}
```

## Dynamic labels and principals
To make code more flexible and reusable, can be useful to allow dynamic check of labels and principals, which are resolved
at run-time. In the following example, principals are used as parameters
```Java
  public static int add(principal P, int {*->P} value1, int {*->P} value2) : {*->P} {
  	return value1+value2;
  }

  public static int add1(principal P1, principal P2, int {*->P1} value1, int {*->P2} value2) : {*->(P1&P2)} {
  	return value1+value2;
  }

  public static void test {*->_} () {
  	int {*->Bob} v1 = 10;
  	int {*->Bob} v2 = 11;
  	v1 = add(Bob, v1, v2);

  	int {*->Alice} x1 = 10;
  	int {*->Alice} x2 = 11;
  	x1 = add(Alice, x1, x2);
  	
  	int {*->(Alice&Bob&Chuck)} res = add1(Bob, Alice, v1, x1);
  }
```
When principals are provided dynamically, we can constraint them to ensure that they act for someone else. For example:
* Example on act-for in definng principals *
* Also I've no idea how to specify p = Alice&Bob *
```Java
  public static int add2(principal P, int {*->P} value1, int {*->Bob} value2) : {*->P} 
  	where P actsfor Bob {
  	return value1+value2;
  }
  public static int add3(principal P, int {*->P} value1, int {*->Bob} value2) : {*->Bob} 
  	where Bob actsfor P {
  	return value1+value2;
  }
  public static void test1 {*->_} () {
  	int {*->Alice} v1 = 10;
  	int {*->Bob} v2 = 11;
  	if (Alice actsfor Bob) {
  		v1 = add2(Alice, v1, v2);
  	} else if (Bob actsfor Alice) {
  		v2 = add3(Alice, v1, v2);
  	} else {
  		v2 = add2(Bob, v2, v2);
  	}
  }
```

Similarly, labels are can be used as arguments.
```Java
  public static int add(label L, int {*L} value1, int {*L} value2) : {*L} {
  	return value1+value2;
  }

  public static int add1(label L1, label L2, int {*L1} value1, int {*L2} value2) : {*L1;*L2} {
  	return value1+value2;
  }

  public static void test {*->_} () {
  	int {*->Bob} v1 = 10;
  	int {*->Bob} v2 = 11;
  	v1 = add(new label{*->Bob}, v1, v2);

  	int {*->Alice} x1 = 10;
  	int {*->Alice} x2 = 11;
  	x1 = add(new label{*->Alice}, x1, x2);
  	
  	int {*->(Alice&Bob&Chuck)} res = add1(new label {*->Bob}, new label {*->Alice}, v1, x1);
  }
```
Notice the usage of `*` in `{*L}`. In fact, Jif interprets `{L}` as the label of the variable `L`, that in this case is public.
Similarly to principals, we can add constraints over labels
* TODO *

## Parametrized classes
Parametrized classes
enable building reusable data structures (i.e. Lists).
```Java
class Parametrized01 [label L1, label L2] where L1 <= L2 {
	public void hello{L1}(int {L2} x) {
	}
	
	public static void test{*->_}() {
		int {*->Alice,Bob} value = 10;
		Parametrized01[{*->Alice,Bob}, {*->Bob}] a = new Parametrized01[{*->Alice,Bob}, {*->Bob}]();
		a.hello(value);
		Parametrized01[{*->_}, {*->Bob,Chuck}] b = new Parametrized01[{*->_}, {*->Bob,Chuck}]();
		//b.hello(value);
		//b = a;
		//a = b;
	}
}
```
There is no subtyping relation among parametrized classes instantiated with different arguments. That is both `a=b` and
`b=a` are not correct, even if `{*->Bob,Chuck}` is less restrictive that `{*->Bob}`.
Like for dynamic labels, `where` clause can be used to constraint parameters.


