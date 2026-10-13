## What changed

The original instance `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`
is reduced to the proper factor of the chosen compactification. Its proof obtains the
left-adjoint instance for the exact derived extension by zero from the already implemented
`Adjunction.mapDerivedCategoryRightDerivedAdjunction` and
`Etale.openImmersionLowerShriekAdjunction`, obtains the proper-factor instance from the new
proof-only import `Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint`, unfolds
`Rf_! = D(i_!) ⋙ Rg_*`, and composes the left adjoints. All existing signatures, universes,
definitions, and public imports are preserved. No object is chosen from a new mere-existence
statement; only the Prop-valued adjoint instance is used.

The new theorem is strictly the proper-direct-image part of the compactification argument:
it mentions neither extension by zero nor lower shriek nor a compactification. The original
proof genuinely supplies the open-immersion factor and composes the two adjoints.

The second original instance is marked STATEMENT-DISPUTED, with its original signature and
hole preserved. The new root DAG record describes the first original instance exactly;
no existing node statement is changed.

## Proved and sorry left

One of the two original holes is closed by a decomposition:
`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`, recorded by
`lem-etale-lower-shriek-adjoint-from-compactification`. This is a reduction, not an
axiom-free proof: its proper factor remains open, and C1 makes its Brown input
a separate new open theorem (two added holes in total).

Added hole: `AlgebraicGeometry.Etale.isLeftAdjoint_proper_rightDerivedLowerStar`, node
`lem-etale-proper-derived-direct-image-adjoint`, in the new module
`Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint`.

Added hole for C1: `CategoryTheory.grothendieckDerived_hasRightAdjoint`, node
`lem-grothendieck-derived-brown-right-adjoint`, in
`Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint`. Its exact, coproduct-preserving
hypotheses are the Brown step only, strictly independent of the geometric coproduct argument.
The zero category, identity functor and zero functor satisfy the expected conclusion.

Unchanged hole: `AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`. There was no primary
DAG record for this declaration in the supplied checkout. Its existing docstring contains
the intended finite-amplitude argument, but that argument has no global uniform bound under
the stated hypotheses; see the counterexample below. No new bounded-below theorem is asserted.

The first-instance proof compiles. Both new theorems have exactly `:= by sorry` as their proof;
there are no new holes inside a definition or a partial proof. Edge cases checked in words:
a scheme isomorphism and the empty proper map have right adjoints; a disconnected base with
unbounded fibre dimensions requires only local amplitude for coproduct preservation and
Brown representability, so does not contradict the proper-factor statement.

## No longer needed

No original import is removed, and no formerly reached module is claimed as pruned.
The second reader removed the redundant new public import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB` from the helper module: its
required instances are already available through `Derived.UpperLowerStar`. The route for
this particular adjoint-existence instance does not need compactification independence or
`lem-amb-etale-compact-comparisons`: it uses the actual chosen compactification only.
The proper-coproduct and Brown inputs remain needed inside the new proper-factor item.
The current second reader also removed redundant direct public imports
`Mathlib.CategoryTheory.Triangulated.Functor` and `Mathlib.CategoryTheory.Adjunction.Basic`
from the new Brown module; both interfaces already arrive through its required
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory` import.

## Where the brief, the DAG or earlier work was wrong

The interface checker treats an instance proof replacement as an interface change;
a change record is supplied for that conservative classification. It is not an actual
change of the theorem's type or any consumer-facing definition.

The primary `lean.module` search yields no node for this source module. The hit in
`thm-fd-fourier-perverse` is merely its historical `lean_audit.open` list. The docstring's
`thm-amb-etale-exceptional-adjoint` node assumes Noetherian schemes, unlike the source instance.
The new nodes document the exact existing source signature and the local-amplitude argument,
without broadening that blueprint node or mapping its different statement to this signature.
The unit `sk-prop-sf-cbc` has no realized statement or proof-step entries; no unit step is
removed or replaced. Mathlib's compactly-generated Brown theorem in the current Sheaf library
cannot be applied by assuming that arbitrary étale derived categories are compactly generated.
The needed version is Stacks Tag 0F5Y for a Grothendieck abelian source; its statement and proof
were read at https://stacks.math.columbia.edu/tag/0F5Y.

STATEMENT-DISPUTED: `AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek` is missing a
uniform global dimension/amplitude bound. Take Λ = F₂, Y the countable disjoint union of
Spec(C), X the disjoint union of P^n_C, and f the componentwise structural morphism.
The map is proper: properness is local on the target, and every quasi-compact part of Y
meets finitely many components. Choose its identity-open compactification. The constant
Λ-sheaf on Y in degree zero is globally bounded below. On component n its exceptional
inverse image is Λ(n)[2n] by smooth purity (equivalently by the projective-space duality
calculation). This has nonzero cohomology in degree -2n. Hence its exceptional inverse image
has no global lower bound. The class uses the global standard `t.plus`, not a locally bounded
condition. Existence of the right adjoint is consistent with this example; preservation of
D⁺ is not. This is a mathematical counterexample, not a newly formalized Lean refutation.
The statement is preserved and flagged for repair by the maintainer.

## New nodes

`lem-grothendieck-derived-brown-right-adjoint` repairs reviewer C1. It records the exact
Grothendieck derived Brown criterion of Stacks Tag 0F5Y, label
`injectives-proposition-brown`, with source/proof/search records and the corresponding
public Lean theorem in `Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint`.
Step 3 of the proper-factor node now names this id in `uses` and `proof_deps`.
The proper-factor module imports the Brown module as a proof dependency. The original
source declarations and their signatures are unchanged by this repair. LeanSearch was
unavailable; leanfinder, loogle and grep found no applicable existing declaration.


`lem-etale-proper-derived-direct-image-adjoint` records the new proper-factor theorem, its
local finite-amplitude/coproduct argument, and the Grothendieck Brown input. It is in
`dag/nodes/sec-smooth-purity/lem-etale-proper-derived-direct-image-adjoint.json`.

`lem-etale-lower-shriek-adjoint-from-compactification` records the actual first source
instance, previously without a primary node, and the compiling composition proof. It is in
`dag/nodes/sec-smooth-purity/lem-etale-lower-shriek-adjoint-from-compactification.json`.
Change record: `coord/changes/isLeftAdjoint_rightDerivedLowerShriek-proof.md`.
The preflight classifies the changed Prop-valued instance proof as an interface change,
because it stores the entire body of instances. The record documents identical signatures
and unchanged instance registration, with all transitive users and no adaptations.

## Earlier second reading (a previous round; superseded)

1. Checked the full diff against the repository module. Every existing declaration
   signature, section variable, universe, definition, public import and instance
   registration is unchanged. The changes are the first instance's proof, one proof-only
   import, a blueprint comment, and the disputed-statement comments. The helper is new.
   Verdict: no accidental interface or mathematical change. The change record's Old and
   New blocks now reproduce the declarations' actual line breaks.
2. Compiled both delivered modules in dependency order through lcompile.py. Scratch
   copies with `#print axioms` confirm that the two adjoint-existence declarations and
   the unchanged disputed instance use only propext, Classical.choice, Quot.sound and
   sorryAx. The existing exceptional-functor and adjunction definitions use only the
   three standard axioms. No forbidden declaration or new sorry inside data is present.
   Verdict: one original hole is genuinely reduced, with one strictly smaller open
   proper-factor theorem; this is a decomposition with net zero holes, not an axiom-free
   proof. The other original hole is unchanged and disputed.
3. Read the new theorem and its entire natural-language proof. Properness is local on
   the base, and finite type gives a fibre-dimension bound over each quasi-compact affine
   open. Proper base change and finite torsion cohomological dimension supply local
   finite amplitude; filtered-colimit compatibility gives coproduct compatibility.
   Exact open restriction preserves injectives by its exact extension-by-zero left
   adjoint, so the local unbounded comparisons detect the global comparison.
   [Stacks Tag 0F5Y](https://stacks.math.columbia.edu/tag/0F5Y) was independently read
   and supplies precisely the final Grothendieck Brown implication. The identity map,
   empty source, zero coefficient ring and disconnected unbounded-dimension base do
   not contradict adjoint existence. Independent leanfinder search for a
   coproduct-preserving triangulated functor from a Grothendieck derived category,
   loogle query `"rightDerivedFunctor", "IsLeftAdjoint"`, and local rg/msearch grep
   for Grothendieck Brown and proper-derived adjoints found no usable exact theorem.
   The existing BrownRepresentabilityRightAdjoint requires compact generation, which
   is not available here. Verdict: the split-off statement is true, strictly one
   geometric factor of the original argument, and cannot be closed in a few minutes
   from the available declarations. The bounded-below counterexample also checks:
   choosing the identity-open compactification makes the proper projective-space
   example independent of any unproved compactification-independence comparison.
4. Read the proof from the target downward: it uses the existing exact-open derived
   adjunction, unfolds the actual compactification, and composes the two adjoints.
   No shorter available route was found. Removed the redundant newly added public
   ModuleCat.AB import from the helper and recompiled it successfully. All original
   imports remain required by existing signatures or definitions; there was no primary
   existing node for this module whose proof_deps needed pruning. The cited blueprint
   node has a different Noetherian statement and was not altered or falsely remapped.
   The unit sk-prop-sf-cbc has empty realized statement and step lists. Verdict: the
   available unit route is preserved; no formerly reached module is claimed pruned.
5. Read both new nodes, checked their exact Lean signatures, sources, creation/search
   fields, chapter and unit, and verified that each proof_deps list is the union of
   its proof steps' uses. The root node matches the implemented composition proof;
   the proper-factor node records the still-open geometric/Brown argument rather
   than claiming it formalized. Verdict: the records agree with the Lean and report.

Second reading changed: removed one redundant new public import, corrected the change
record's verbatim declaration formatting, and added this independent review. No existing
statement, definition or proof argument was changed.

## Second reading by B2

1. Compared the delivered source module with the repository version using diff.
   The only edits are a proof-only helper import, the first instance's proof and
   explanatory comments. All existing signatures, universes, definitions and public
   imports are unchanged. Read the change record: its Old/New blocks match the actual
   declarations, and its instance-body classification does not assert a type change.
   Verdict: no accidental visible change; no target or definition is weakened.
2. Compiled all three modules with lcompile.py in dependency order, without warnings.
   Temporary axiom probes give only propext, Classical.choice, Quot.sound and sorryAx
   for the two new theorems, the reduced instance and the disputed instance. The
   exceptional functor and its adjunction definitions use only the three standard
   axioms. Inspected all delivered Lean text: no forbidden declaration or data hole.
   Verdict: one of two original holes closed by decomposition, two new named holes
   added; net minus one hole closed, not an axiom-free proof. The Brown hole is the
   explicit repair required by return C1, not an additional proved step.
3. Independently read Stacks Tags 0F5Y and 0F5X. The Brown statement has exactly the
   exactness and coproduct hypotheses, with indexing large enough for both source
   and target Hom universes; it does not assume compact generation of the sheaf
   derived category. Its Gabriel-Popescu/direct-summand argument agrees with 0F5X.
   Checked proper-factor steps against the fibre, torsion-dimension, filtered-colimit,
   conservative-stalk and finite-amplitude coproduct node statements. Properness gives
   quasi-compact/quasi-separated inverse images of affine opens and a local finite
   fibre-dimension bound; no global bound is required for adjoint existence.
   Empty source, identity map, zero coefficient ring and a disjoint union with
   unbounded dimensions do not contradict either split statement. Brown's zero and
   identity functor cases also check. Fresh leanfinder searches for Grothendieck
   derived adjoints and exceptional proper pushforward, loogle searches involving
   IsTriangulated/IsLeftAdjoint and rightDerivedFunctor/IsLeftAdjoint, and local rg
   searches found no applicable replacement. Existing BrownRepresentabilityRightAdjoint
   requires compact generation; the remaining formalizations exceed a few-minute
   repair. Verdict: the two split statements are true and strictly smaller inputs;
   neither is a renamed version of the whole compactification argument. The original
   bounded-below statement's disconnected projective-space counterexample remains
   valid, so its unchanged hole and dispute flag are retained.
4. Read downward from the reduced instance: mapDerivedCategoryRightDerivedAdjunction
   applied to openImmersionLowerShriekAdjunction gives the open factor; the proper
   helper gives the other factor; change unfolds the actual chosen compactification;
   the composition instance finishes. No independence-of-compactification theorem is
   needed. No original proof-dependency node is attached to this source declaration;
   the distinct Noetherian blueprint node is preserved. Unit sk-prop-sf-cbc has empty
   realized.statement and realized.steps lists. Verdict: the unit route is kept and
   no original module is pruned. Removed two redundant public imports from the new
   Brown helper and verified that its one remaining import supplies its signature.
5. Read all three new DAG records. Their Lean signatures match their modules, and
   proof_deps is exactly the union of step uses. The root describes the composition
   proof; the proper node explicitly cites the new Brown node in step 3 and
   proof_deps, repairing the sole recorded C1 return. Sources, natural-language
   proofs, searches, creation records, chapter and unit are present. Verdict: DAG
   and Lean agree; the open geometric and Brown arguments are reported as open.

Second reading changed: removed two redundant direct public imports from the new
Brown module and updated the pruning inventory and this review. Existing statements,
definitions and the compactification proof were preserved.
