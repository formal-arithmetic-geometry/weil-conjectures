## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.singletonTensorSections_span` by
composition of the existing indexed product-ring equivalence and normalized affine
sections equivalence, followed by a proved private additive-generation lemma.
Added proof-only imports of `Sheaf.AlgebraicGeometry.EtaleAffineSingletonProductRing`
and `Sheaf.AlgebraicGeometry.EtaleAffineTensorSectionsEquiv`.
Updated the item's node proof and proof dependencies to match this composition.
The public statement and its hypotheses are unchanged.

## Proved and sorry left

Closed the one local hole (all three sandbox modules compile): `AlgebraicGeometry.Scheme.singletonTensorSections_span`
(node `new-etale-affine-singleton-tensor-sections-span`).
The private `tensor_generators_span` is proved by two tensor inductions;
`tensor_generators_span_of_equivs` composes the geometric equivalences in generic
types. Both helper axiom checks contain only propext, Classical.choice and Quot.sound.
No local sorry remains and no new sorry is added. The proof uses the existing
holed declarations `AlgebraicGeometry.Scheme.singletonProduct_affine_ring` and
`AlgebraicGeometry.Scheme.exists_etaleAffineTensorSectionsEquiv`; it does not
claim to close their geometric arguments or all transitive axioms.
Zero modules, zero rings and n=0 are included: the private helper has no
nonzero assumptions and the indexed product still has one factor for n=0.

## No longer needed

No existing import was removed. The original five direct proof dependencies are
now handled through the two existing geometric comparison nodes; they are not
pruned from the transitive argument:
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-quasi-coherent`,
`lem-pc-module-pullback-adjunction`,
`lem-weil-pbc-module-pullback-affine-sections`, and
`lem-sc-etale-qcoherent-presheaf-functorial`.
No node or module is made globally unnecessary by this proof. Pruned: none.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The geometric comparison nodes added for the kernel
argument already provide the first two steps of this item's plan, so they can be
reused without introducing any new statements. The unit record has no realized
statement or proof steps attached to this node; the affine tensor calculation
itself is retained. The dependency modules are present in the sandbox and compile successfully.

Validation: sandbox compilation of the two dependency modules and this module succeeds. The required `deliver3.py C1 Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorSectionsSpan --no-push` dry run prints OK (commit 3b7f9edf6c); no delivery was pushed. The scratch assembly also compiles without transparency options.

## Second reading by C1

1. PASS: diffed every sandbox module against the repository. The existing public
   signature of `AlgebraicGeometry.Scheme.singletonTensorSections_span` is byte
   for byte unchanged; its docstring and public import are unchanged. The two
   dependency modules are byte-identical copies for local compilation, not adaptations.
   No definitions or other existing declarations changed.
2. PASS: compiled all three files locally in import order with `lcompile.py`.
   The item contains no sorry and no prohibited declaration or attribute. In a
   scratch copy, `#print axioms` reports only propext, Classical.choice and
   Quot.sound for both private helpers; the public theorem additionally uses
   sorryAx through existing open geometric dependencies. No data definition is
   introduced; the existential equivalences are eliminated inside a proof only.
3. PASS: no statement or hole is split off and no new node is introduced. Read
   both existing comparison statements and their docstring arguments. The ring
   comparison and normalized affine sections comparison are strictly distinct
   geometric parts of the argument, not restatements of additive generation.
   The proof includes n=0 (one factor), zero coefficient modules, and zero rings.
4. PASS: searched the library and Mathlib for tensor closure and pure-tensor span
   results. Mathlib's `PiTensorProduct.span_tprod_eq_top` is a linear-span result;
   the current short induction supplies the required additive closure by moving
   scalars to the coefficient factor. No shorter matching section theorem was
   found. Both added imports are proof-only and used. The five former direct DAG
   dependencies are all listed under No longer needed and retained transitively
   through the comparison nodes; no module is pruned. Read sk-prop-h2's realized
   record: no realized statement or step is bypassed, and its route is unchanged.
5. PASS: compared the node JSONs: only proof, proof_deps and proof_origin change.
   The two dependencies match the Lean applications; the elementary tensor
   induction and composition steps match both proved private helpers. The Lean
   statement recorded in the node matches the unchanged public signature.

Changes made by the second reader: corrected the stale pending-compilation wording
in Proved and sorry left and appended this independent review. No Lean or DAG
repair was needed. One local hole closed, zero holes added, zero split-off
statements, and no pruning; the remaining geometric holes are pre-existing.
