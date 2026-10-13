## What changed
Added the fixed-degree intermediate theorem module and imported it privately. The original theorem now assembles the degreewise results into the required universal statement.

## Proved and sorry left
The original declaration `ModuleCat.localizedTensorComparison_inheritance` is proved by applying the fixed-degree theorem for each degree. The new declaration `ModuleCat.localizedTensorComparison_inheritance_fixed_degree` remains `sorry`; it is the genuine fixed-degree localizing-subcategory argument and has a new DAG node.

## No longer needed
No imports were removed. The existing proof dependencies remain part of the statement's route.

## Where the brief, the DAG or earlier work was wrong
The original DAG had only the global quantified statement, while the natural proof is degreewise. The fixed-degree component was split out as a separately sourced obligation.

## New nodes
`lem-pc-localized-tensor-comparison-inheritance-fixed-degree` in `dag/nodes/sec-picard-framework/`.

## Earlier second reading (a previous round; superseded)
The fixed-degree declaration is a strict degreewise component of the quantified target. Its node now records the associator, model, and free-generation proof route rather than depending circularly on the global theorem. The global proof compiles and applies the fixed-degree statement for each degree.

## Second reading by E2

1. I compared the delivered global module with the repository version. The theorem
   signature, hypotheses, local instances, and conclusion are byte-for-byte unchanged;
   only a private import and its proof body were added. The new fixed-degree module is
   a separate declaration and does not alter an existing interface.

2. I compiled both delivered modules with `lcompile.py --all`. They compile without
   errors or warnings. The global theorem has no `sorry`; the only remaining `sorry` is
   the named fixed-degree theorem, which is listed with its new node above. No
   forbidden `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition was added.

3. The fixed-degree statement is a strict, true decomposition of the quantified
   conclusion: it fixes the degree and takes exactly the corresponding hypothesis.
   Its docstring records the Stacks source and the localizing-subcategory,
   associator, and flat-extension argument. The new DAG node matches its declaration,
   records the three proof dependencies, and records the source and searches. No
   duplicate declaration was found in the library or Mathlib.

4. The global proof follows the planned route by applying the fixed-degree result for
   each degree; the fixed-degree node records the associator and free-generation route
   from the original proof. The original public imports remain needed by the statement
   and fixed-degree module. The unit is still the same `sk-thm-picard-semicon` route;
   no unit statement or step was bypassed.

5. I checked the DAG and Lean declarations together: the target node still names the
   original global theorem, while the new split node names exactly the fixed-degree
   theorem and its module. The proof dependency list is the union of the route's
   dependencies, and the target's quantified conclusion is assembled without changing
   its strength.

I changed only the report for this second reading. No Lean proof or statement required
   repair after compilation.
