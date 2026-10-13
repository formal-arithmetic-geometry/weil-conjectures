## What changed

The existing theorem `AlgebraicGeometry.perfect_hom_mayerVietoris_triangle_cocone`
keeps its signature and all three public imports. Its proof now constructs the
triangle functor and cocone explicitly from a natural Mayer--Vietoris family.
The original stage and apex distinguishedness, central equivalences, and both
transport equations are assembled in Lean without a hole in this module.

Three new modules support this construction:

- `Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone` constructs the representing
  derived objects as `Rpi_* Lpi* Q`. It proves their coherent diagram and cocone
  using adjunction, natural transport, evaluation at identities (Yoneda), and
  quasi-coherence preservation. Its equivalences are natural in EVERY testing
  object, so the representing arrows are pinned, including their restrictions.
- `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisDiagram` constructs the actual
  geometric triangle from the units, restriction maps and boundary. Its map is
  uniquely determined by the three prescribed components. Componentwise proofs
  establish identity, composition and cocone laws; there is no sorry in a definition.
- `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisColumns` leaves only the
  geometric outer-column recognition step open. Its statement applies to the
  explicit family construction and the universally natural representing cocone,
  not arbitrary distinguished triangle cocones.

The parent node's proof and dependencies now follow this implementation. No
existing statement, definition or visibility was changed; no forced adaptation
or change record is needed. The unit `sk-thm-picard-semicon` was read: its realized
statement and step lists are empty, and no unit statement or step is bypassed.

## Proved and sorry left

Original holes closed: 1 of 1,
`AlgebraicGeometry.perfect_hom_mayerVietoris_triangle_cocone`
(node `lem-pc-perfect-hom-mayer-vietoris-triangle-cocone`).

New holes added: 1,
`AlgebraicGeometry.perfect_hom_mayerVietoris_geometric_columns`
(node `lem-pc-perfect-hom-mayer-vietoris-geometric-columns`). Its entire proof
is exactly `:= by sorry`; its docstring and node give the source and the full
geometric argument. This is a one-to-one decomposition, not a net hole reduction
or a proof of the final target without dependencies.

`AlgebraicGeometry.perfect_hom_pushPull_cocone` is proved with no new hole.
The naturality helpers, triangle component lemmas, identity/composition lemmas,
diagram and cocone constructors are also complete. No other delivered declaration
contains sorry. Existing imported declarations may still depend on sorry, as
stage 3 permits.

Validation: all four delivery modules compile cleanly with lcompile.py --all.
The axiom probe shows only `propext`, `Classical.choice`, `Quot.sound` for
`perfect_hom_pushPull_cocone`, `PerfectHomMVFamily.diagram`, and
`PerfectHomMVFamily.cocone`: these constructions are proved without any sorry
even in their dependency closure. The named geometric-columns hole and the
parent theorem have those three axioms plus `sorryAx`. The scratch axiom probe
is outside the delivery set. The first dry run identified two unscoped elaboration
options as an interface change; they are now scoped to the existing theorem.
The second-reader section is deliberately absent, as required by the worker brief.
The final deliver3.py --no-push result is given in the worker final status.

## No longer needed

Removed these six direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.PerfectThickClosure`
- `Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel`
- `Sheaf.AlgebraicGeometry.PerfectImpliesQCoh`
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`
- `Sheaf.AlgebraicGeometry.DerivedAdjoint`
- `Sheaf.AlgebraicGeometry.PerfectHomStageColimit`

`DerivedAdjoint`, `PerfectImpliesQCoh` and `PerfectHomStageColimit` are used
privately by the proved representing-cocone module. The parent no longer needs
to prove perfectness of all stage pullbacks or their shifts: quasi-coherence of
Q, pullback preservation and affine direct-image preservation suffice for its
representing objects. The local perfect restrictions and shifts are still steps
of the remaining geometric-columns node, so this delivery does not claim that
those geometric lemmas can be deleted from the whole target DAG.

The old parent dependencies are either used through the new constructions or
remain in the proof plan of the geometric-columns node. No claim is made that
a library node is globally pruned from all targets. The following modules leave
this item's *present source import closure* (other target routes and future imports
for the open geometric step can still need them):

- `Mathlib.Algebra.Category.ModuleCat.Biproducts`
- `Mathlib.Algebra.Category.ModuleCat.Free`
- `Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle`
- `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`
- `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects`
- `Mathlib.CategoryTheory.Monoidal.Closed.Braided`
- `Mathlib.LinearAlgebra.Basis.Prod`
- `Mathlib.RingTheory.Finiteness.Cardinality`
- `Mathlib.RingTheory.Finiteness.Prod`
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`
- `Sheaf.Algebra.Homology.BoundedFlatKFlat`
- `Sheaf.Algebra.Homology.PreciseVanishing`
- `Sheaf.Algebra.Homology.PreciseVanishingCore`
- `Sheaf.Algebra.Homology.RingPseudoCoherentSummand`
- `Sheaf.Algebra.Homology.TorAmplitudeFlatModel`
- `Sheaf.AlgebraicGeometry.AffineDerivedSummandModels`
- `Sheaf.AlgebraicGeometry.AffineLocalSheafificationTorAmplitude`
- `Sheaf.AlgebraicGeometry.AffineLocalizedDerivedSheafification`
- `Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport`
- `Sheaf.AlgebraicGeometry.AffinePerfectModuleModel`
- `Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion`
- `Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes`
- `Sheaf.AlgebraicGeometry.DerivedTensorVanishingRetract`
- `Sheaf.AlgebraicGeometry.FiniteTorDimension`
- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`
- `Sheaf.AlgebraicGeometry.FlatSheafStalk`
- `Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel`
- `Sheaf.AlgebraicGeometry.LocallyFiniteTorDimension`
- `Sheaf.AlgebraicGeometry.OpenImmersionTensorVanishingTest`
- `Sheaf.AlgebraicGeometry.PerfectOfPseudoCoherentLocallyFiniteTor`
- `Sheaf.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor`
- `Sheaf.AlgebraicGeometry.PerfectSummand`
- `Sheaf.AlgebraicGeometry.PerfectThickClosure`
- `Sheaf.AlgebraicGeometry.PseudoCoherentSummand`
- `Sheaf.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect`
- `Sheaf.RingTheory.DerivedMapLift`
- `Sheaf.RingTheory.FiniteConeCycleAttachment`
- `Sheaf.RingTheory.FiniteConeFreeExtension`
- `Sheaf.RingTheory.FiniteConeFreeModel`
- `Sheaf.RingTheory.FiniteHomologyOfMPseudoCoherent`
- `Sheaf.RingTheory.MPseudoCoherent`
- `Sheaf.RingTheory.MPseudoCoherentShift`
- `Sheaf.RingTheory.MPseudoCoherentVanishingBase`
- `Sheaf.RingTheory.PseudoCoherentApproximationTriangle`
- `Sheaf.RingTheory.PseudoCoherentDistinguishedTriangle`
- `Sheaf.RingTheory.PseudoCoherentIffAllM`
- `Sheaf.RingTheory.RingPseudoCoherent`
- `Sheaf.RingTheory.StabilizingConeTower`
- `WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat`
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective`

## Where the brief, the DAG or earlier work was wrong

The rejected first attempt asserted outer local comparisons from central Hom
transport for arbitrary triangle cocones. Its singleton-field counterexample is
valid: a zero stage triangle can map to the split triangle `0 -> O -> O -> 0`,
while the central groups remain zero. That conclusion is not used or restated.
The archived rejected modules and nodes stay outside the delivery set.

The repaired local statement requires `A.diagram` and `A.cocone`, whose outer
objects are explicitly the two-open biproduct and intersection direct image,
and whose maps are explicitly restrictions and direct images. The representing
equivalences are natural in every source object, not merely P. In the old
counterexample with Q = 0, these equivalences force the representing objects
and their restrictions to be zero, so the arbitrary split apex cannot satisfy
these geometric hypotheses.

Other edge cases checked mathematically: empty Y and empty opens give zero
objects; U = V gives a genuine repeated binary product; the tail includes i;
Q = 0 is covered by the same construction. No nonemptiness, affine cover
uniqueness, or continuity hypothesis was added. The ring-colimit witness hc is
not needed to construct comparison presentations, but its existing binder is
retained unchanged and explicitly referenced to keep compilation warning-free.

The new nodes have no dependency on the parent or its downstream stage-row
lemmas. No dependency cycle passes through a delivered node. A broad traversal
also encountered older cycles in unrelated sheaf-algebraic-structure, delta-functor,
flat-base-change, invert-section, higher-image and truncation nodes; those are
outside this delivery and were not modified.
The source pages for Stacks Tags 09RE, 08BW and 079W were read online.
Searches are logged in searches.jsonl; LeanSearch returned an internal server
error and is recorded as unavailable, not as a negative match.

## New nodes

`lem-pc-perfect-hom-push-pull-cocone`: coherent representing derived-object
cocone, universally natural Hom equivalences and pinning; fully proved from
existing adjunction, transport, stage-colimit and quasi-coherence declarations.
This is independent of triangles, covers and group colimits.

`lem-pc-perfect-hom-mayer-vietoris-diagram`: explicit natural-family triangle,
its uniquely specified maps, and the proved diagram/cocone constructions. The
field construction and component proofs are real Lean and have no new holes.

`lem-pc-perfect-hom-mayer-vietoris-geometric-columns`: only the four outer-column
comparison presentations for these specified geometric constructions. This is
strictly the final local recognition step; it asserts no existence of a triangle
cocone, no distinguishedness, and no central transport equations. Its stagewise
geometric identification and colimit/product argument are recorded in full.

## Second reading by A4

1. I compared the delivered parent module with the repository version. The theorem
   signature is unchanged byte for byte; the proof-only import pruning and the
   scoped elaboration options are recorded in the diff and do not alter any public
   declaration. The three supporting modules are new declarations with DAG nodes.
   Verdict: pass.

2. I compiled the three supporting modules and the parent with `lcompile.py`.
   There are no `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`
   declarations, and no `sorry` occurs in a definition. The only remaining sorry
   is the named theorem
   `AlgebraicGeometry.perfect_hom_mayerVietoris_geometric_columns`, exactly the
   split-off hole listed above and matched by its node. Verdict: pass.

3. The split-off geometric-columns statement is a genuine outer-column recognition
   lemma for the explicitly constructed geometric family and universally natural
   representing cocone. It does not restate the parent target or quantify over
   arbitrary triangle cocones. Its docstring gives the source and a complete
   geometric proof plan, and its node records the same statement and dependencies.
   The diagram and push-pull declarations are proved constructions, not witness data
   selected from an undetermined existence theorem. Verdict: pass.

4. The parent proof follows the shortened route through the representing cocone,
   the natural Mayer--Vietoris family, and the local geometric-columns lemma. The
   unit route remains represented by the parent and supporting nodes; removed direct
   proof imports are listed under `## No longer needed`. No shorter existing library
   theorem was found by the recorded searches. Verdict: pass.

5. The parent node proof steps, proof dependencies, origin, and the three new nodes'
   Lean declarations agree with the delivered source. The unit record is unchanged,
   and no dependency cycle is introduced by these nodes. Verdict: pass.

I changed only this report section. No Lean source, statement, definition, or DAG
content required repair during second reading.
