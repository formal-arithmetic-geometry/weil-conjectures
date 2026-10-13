## What changed

Reduced Algebra.popescu_special_chart_map_injective using one new proof-only import,
Sheaf.RingTheory.PopescuSpecialChartSubstitution. Its statement constructs a
C0-algebra substitution on the unlocalized quotient D0 and specifies its values
on free auxiliary generators. The target proof extends this map through
localization and proves the composite identity using two extensionality steps.
Existing signatures and public imports are unchanged. Both files compile.
The new substitution module publicly imports only PopescuLiftPresentation,
which supplies the types in its statement.

## Proved and sorry left

Closed the hole in Algebra.popescu_special_chart_map_injective
(lem-weil-pbc-popescu-special-chart-map-injective). Added one hole in
Algebra.popescu_special_chart_substitution
(lem-weil-pbc-popescu-special-chart-substitution), exactly `:= by sorry`.
This is a decomposition: one upper hole closed, one lower hole added; net zero.
The localization extension, coefficient extensionality, polynomial extensionality,
and deduction of injectivity are proved. The elimination and quotient descent
remain to be proved. No sorry remains in the original module.

## No longer needed

No existing import is removed and no module is pruned from the closure.
The original direct proof dependency lem-weil-pbc-popescu-lift-preparation
is replaced by lem-weil-pbc-popescu-special-chart-substitution in the target
node; preparation and conormal comparison remain transitive dependencies
through that new node. Localization and polynomial extensionality remain used.
Second reading replaced the new module's unnecessarily broad public import
PopescuSpecialChartMap with PopescuLiftPresentation and removed the unused
chart-map dependency from the new node.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy found. The original three-step plan did not have a
separate declaration for its substantial elimination and quotient-descent step.
The new node exposes this step without merely restating injectivity or a left
inverse: its domain is the unlocalized quotient, and it only specifies free
variable values together with scalar compatibility. The original proof carries
out the localization extension and the two extensionality arguments.
Edge cases include the zero coefficient ring, localization at zero, and an empty
free-variable index set; the statement and proof require no nontriviality.

## New nodes

lem-weil-pbc-popescu-special-chart-substitution, in
lean/Sheaf/RingTheory/PopescuSpecialChartSubstitution.lean, isolates the Tag 07CP
substitution killing the defining equations and descent through the unlocalized
quotients. It preserves the prepared conormal comparison from the planned route.
No unit statement or realized unit proof step is bypassed; no change record is
needed because all existing signatures remain unchanged.

## Second reading by M1

1. Compared the existing Lean module against the repository by diff and
   checked its theorem signature byte for byte: unchanged. The only existing
   Lean edits are the proof and a proof-only import. Compared the existing
   JSON structurally: only proof, proof_deps and proof_origin changed. No
   definition, target statement or externally visible existing import changed.
2. Compiled both modules in import order using lcompile.py. There is exactly
   one sorry, the named substitution theorem listed above, and no forbidden
   declaration or hollow definition. The substitution witness is eliminated
   locally in a proposition proof; no data definition chooses an arbitrary
   witness. Scratch #print axioms checks for both declarations give only
   propext, Classical.choice, Quot.sound and sorryAx. This remains a
   decomposition with net zero holes, not a completed axiom-free proof.
3. Read the new statement against Prepared.relation, normalized_h, conormal,
   surjective and kernel, and checked the coefficient calculation against
   https://stacks.math.columbia.edu/tag/07CP. Multiplying the two chart
   relations and using the k-basis makes the indicated comparison
   coefficients vanish; substitution therefore kills every chart relation.
   The zero ring and localization at zero give a zero polynomial ring; an
   empty E gives the coefficient ring and the empty sums vanish. Empty chart
   index gives no k and hence no obligation. Coefficient compatibility is
   determined by hc, surjectivity and hcmod, so the statement is valid for
   the given cmod, rather than a separately chosen coefficient map.
   Searched again with quotient-descent queries via leanfinder and loogle,
   a toCotangent/sum/smul grep, and relevant local and upstream source
   searches. Found general quotient lifts but no existing prepared-chart
   descent theorem. The hole isolates quotient descent; localization,
   scalar extensionality, polynomial extensionality and injectivity are
   proved explicitly, so it does not merely rename the target conclusion.
4. Read the proof top down: Away.liftAlgHom constructs the extension,
   localization ringHom_ext handles coefficients, and polynomial ringHom_ext
   handles variables. No shorter existing prepared-chart result was found.
   Inspected sk-thm-p1 realized: neither changed node realizes a unit step,
   and this decomposition preserves the existing route. No closure module
   is pruned. Narrowed the new public import as recorded above.
5. Checked the new node's signature against Lean, its required fields and
   its stated proof route. The existing node now describes precisely the
   localization/extensionality reduction, and its old preparation dependency
   remains below the new descent node. Removed the new node's unused
   special-chart-map statement/proof dependency along with its import.

Second reading changed imports, corresponding new-node dependencies, and
report accuracy. The checked proof and existing signature needed no repair.
