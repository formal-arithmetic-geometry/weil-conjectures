## What changed

Proved `CategoryTheory.homTensorDegreewiseMap_iteratedDifferential_summand` with its
existing signature unchanged. Its proof-only imports include
`Sheaf.Algebra.Homology.HomTensorSummandPureExt` and
`Sheaf.Algebra.Homology.HomTensorPureDifferentials`. The calculation evaluates on
localized pure tensors, expands the two Hom differentials, applies the currying
specification, and matches the two tensor differential contributions. The final
sign calculation uses `Int.negOnePow_add` and additive-group identities.

Added two modules. `HomTensorSummandPureExt` proves single-tensor extensionality
from the existing `homTensorLocalized_ext`, using constant zero-differential
complexes and their degree-zero codiagonal. `HomTensorPureDifferentials` proves the
two summand formulas from Mathlib's `mapBifunctor.d₁_eq` and `d₂_eq`, together with
`CategoryTheory.homTensorSectionMap_natural` imported from the existing
`Sheaf.Algebra.Homology.HomTensorSectionNaturality`. That naturality theorem's
proof remains `sorry`; this delivery reuses it without modifying it.
No existing statement, definition, visibility or target changed. All helper
definitions are explicit constructions; all private lemmas are proved.

Updated the original node's proof, proof dependencies and proof origin to match
the Lean proof. New-node records contain the exact Lean signatures and the
recorded Mathlib searches. Leansearch was unavailable; no mathematical verdict
was inferred from its failure.

## Proved and sorry left

Closed the original module's one hole:
`CategoryTheory.homTensorDegreewiseMap_iteratedDifferential_summand`
(node `lem-sc-hom-tensor-iterated-differential-summand`). No sorry remains in that
module.

Also proved the new declarations `CategoryTheory.homTensorSummandPure_ext`
(node `lem-sc-hom-tensor-summand-pure-ext`) and
`CategoryTheory.homTensor_pure_differentials`
(node `lem-sc-hom-tensor-pure-differentials`).

Added zero holes. No sorry remains in any delivered module. The original
module had one hole and now has none. Existing imported holes, including
`CategoryTheory.homTensorSectionMap_natural`
(node `lem-sc-hom-tensor-section-natural`) and `homTensorDegreewise_exists`,
are reused without changes. `homTensorLocalized_ext` is already proved in the
current repository source, although its compiled axiom closure still includes
`sorryAx`. The imported proof obligations remain open; this delivery does not close the complete target import closure. Closure
progress is determined by the pinned-baseline sorry ledger.

## No longer needed

Removed the duplicate new module
`Sheaf.Algebra.Homology.HomTensorSectionMapNaturality` and its node
`lem-sc-hom-tensor-section-map-natural` from the delivery. Replaced its proof-only
import in `HomTensorPureDifferentials` by the existing
`Sheaf.Algebra.Homology.HomTensorSectionNaturality` and replaced the corresponding
node references by `lem-sc-hom-tensor-section-natural`.

No original import was removed and no existing module is claimed globally pruned.
The old direct proof dependencies `def-pc-tensor-complex-sheaves` and
`lem-pc-sheaf-modules-tensor-closed` are no longer direct dependencies of the
original node's proof. They remain transitively available or used by supporting
lemmas; their statement dependencies remain unchanged. The new direct proof
dependencies are recorded in the original node.

## Where the brief, the DAG or earlier work was wrong

Return C5/H9 identified that the previous delivery duplicated
`CategoryTheory.homTensorSectionMap_natural`, already declared in
`Sheaf.Algebra.Homology.HomTensorSectionNaturality` with the same statement after
binder renaming. Importing both modules caused an environment name collision.
The repair removes the duplicate module and node and reuses the existing theorem,
whose proof remains sorry. The earlier claim that this delivery proved naturality
is withdrawn. The previous second-reading results concern the returned four-file
version and have been removed pending a fresh independent reading.

No false statement was found, and no existing interface needed correction.
Local irreducibility attributes avoid repeatedly unfolding the chosen Hom
complexes and projections; they do not change any exported interface. The unit's
prescribed route is retained.

## New nodes

`lem-sc-hom-tensor-summand-pure-ext`, module
`Sheaf.Algebra.Homology.HomTensorSummandPureExt`: proved localized extensionality
for the internal Hom from a single sheaf tensor. Its actual proof reduces to the
existing total-tensor extensionality theorem, not a new generation assumption.

`lem-sc-hom-tensor-pure-differentials`, module
`Sheaf.Algebra.Homology.HomTensorPureDifferentials`: proved the first and signed
second summand differential formulas, using the existing naturality theorem
`CategoryTheory.homTensorSectionMap_natural`
(node `lem-sc-hom-tensor-section-natural`). Integer signs cover negative degrees.

The static checker requires a change record for the added module-local
irreducibility commands, despite the unchanged signatures and exported
attributes. See `coord/changes/hom-tensor-summand-local-reducibility.md`.
No existing definition or statement changed.


## Second reading by Q2

1. **Interfaces: pass.** Diffed the existing module against the repository and
   checked the theorem signature byte for byte, including all hypotheses,
   conclusions, visibility and degree equalities. Only its proof, private
   helpers, proof-only imports and local elaboration controls change. Both
   added public statements live in new modules with new nodes. No target or
   existing definition changes. The change record accurately describes the
   local irreducibility commands; these do not export an attribute change.
2. **Proofs and axioms: pass with existing open dependencies.** Compiled all
   three modules through `lcompile.py --all`: no errors or warnings. Scratch
   copies with `#print axioms` for all three public theorems report exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. No delivered
   declaration contains `sorry`, and no forbidden trust mechanism occurs.
   Constant complexes, codiagonal and evaluation homomorphisms are explicit
   constructions, with no arbitrary witness chosen from an unproved existence
   theorem in this delivery. One original hole is closed; zero holes are added.
3. **New statements: pass.** There are no split-off unproved statements.
   Single-tensor extensionality follows by the explicitly constructed
   codiagonal and its (0,0) section. The two differential formulas are precisely
   Mathlib's summand formulas evaluated after the section map. Checked zero
   tensors, zero differentials, zero factors, negative degrees (including odd
   negative p), and the vacuous empty-site case. The second sign is (-1)^p;
   combining it with (-1)^n gives (-1)^(p+n) for all integers. Independent
   LeanFinder search for equality via local tensor generators, Loogle search
   for `mapBifunctor.d₂_eq`, and grep for `tensor_ext`,
   `sheafificationHomEquiv`, and `ι_mapBifunctorDesc` found the general tools
   already used, but no duplicate of either new statement. Repository searches
   also confirmed that the existing section-map naturality theorem is reused,
   rather than redeclared. Docstrings and nodes explain each complete proof.
4. **Route and pruning: pass.** Read the proof from the summand theorem down:
   localized pure-tensor extensionality, two Hom differential expansions,
   currying, Mathlib tensor differentials, and integer sign rearrangement.
   The new helpers contain actual reductions and do not restate the item.
   All imports are needed; helper imports used only by proofs are plain
   imports. `No longer needed` lists both old direct proof dependencies removed
   from the route, without claiming their transitive modules globally pruned.
   The unit `sk-thm-picard-duality` and its `realized` fields remain unchanged;
   these changes are below its prescribed route and bypass no realized step.
5. **DAG: pass.** Read all three node records alongside their modules. Their
   recorded Lean signatures agree, each `proof_deps` is exactly the union of
   step `uses`, and proof origins identify this Q2 calculation. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`. Both new nodes
   contain source, searches, creation/blueprint metadata and Lean records.

Second reading changed only this report: corrected the stale claim that
`homTensorLocalized_ext` itself remains an open theorem hole, and added this
independent review. Its current source has a proof; the axiom probe still shows
an unresolved imported `sorryAx` dependency. No Lean repair was necessary.
