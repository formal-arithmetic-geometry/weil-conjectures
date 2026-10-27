## Worker report

Item: `lem-sfb-flat-trait-group-affinization`, Q05, stage 2, 2026-10-24.
Module: `Sheaf.AlgebraicGeometry.GroupScheme.FlatTraitAffinization`.
Declaration: `AlgebraicGeometry.exists_group_affinization_of_flat_trait`.
There is one theorem, with `sorry`; there are no new definitions, helper theorems,
dependency repairs, or statement corrections. Only the item's `lean` record changes.

Source read: Prasad--Yu, *On quasi-reductive group schemes*, Proposition 3.1,
printed p.5, https://math.stanford.edu/~conrad/papers/qrg.pdf, especially the
paragraph introducing A and its natural group scheme before finite generation.
The PDF and the text of that page were read in the sandbox scratchpad. The paper
uses that construction within its generic-affine argument; the present node
isolates the more general construction justified by its five recorded proof steps.
No generic-affine or smoothness hypothesis is needed for that construction.
The docstring reproduces all five steps, including the three-factor injectivity
needed to descend associativity, rather than inferring the group diagrams without it.

Hypotheses and objects, matched individually:

- The commutative DVR is `(R : CommRingCat.{u}) [IsDomain R]
  [IsDiscreteValuationRing R]`. The Mathlib DVR class adds localness, principal
  ideals and a nonzero maximal ideal to the explicit integral-domain hypothesis.
- `S = Spec R` is literally the base of `G : Over (Spec R)`.
- An arbitrary, potentially noncommutative group scheme is `[GrpObj G]`.
  `GrpObj` extends `MonObj`, with multiplication, identity, associativity,
  both unit laws, inverse, and both inverse laws in the category over the base.
  Its cartesian product is the scheme fibre product, as prescribed by the node.
- Flatness is `[Flat G.hom]`, separatedness is `[IsSeparated G.hom]`.
  Properness is not imposed. The recorded proper-morphism node also records
  the `IsSeparated` declaration; that is the clause needed here.
- Finite type is `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, exactly the
  two conditions recorded by `def-weil-finite-type-morphism`.
- The section ring A is the existing `Γ(G.left, ⊤)`, implicit in `G.hom.appTop`.
  The actual R-to-A map is `(Scheme.ΓSpecIso R).inv ≫ G.hom.appTop`, first
  identifying R with the sections of `Spec R`, then pulling back along G's
  structure morphism. No arbitrary R-algebra structure is quantified over.
- H is literally `Spec Γ(G.left, ⊤)` with structure morphism `Spec.map` of
  that map. This is the target of the displayed `Over.mk`.
- The existential over-arrow `u` has the condition `u.left = G.left.toSpecΓ`.
  Thus its underlying map is the canonical adjunction unit corresponding to
  `id_A`; it cannot be replaced by another map to the same affine scheme.
  Being an over-arrow includes its compatibility with the specified base map.

Conclusion clauses:

- The first conjunct is `IsPushout ρ ρ p₁.appTop p₂.appTop`, where ρ is the
  actual R-to-A map above and `p₁`, `p₂` are `pullback.fst G.hom G.hom` and
  `pullback.snd G.hom G.hom`. This expresses exactly the tensor comparison
  in the node, using its universal property. In commutative rings the pushout
  of `A ← R → A` is `A ⊗_R A` (Mathlib's `CommRingCat.pushoutCocone` and
  `CommRingCat.pushoutCoconeIsColimit`, Ring/Constructions.lean:47--124).
  The induced map sends `a ⊗ b` to `p₁.appTop a * p₂.appTop b`; its being an
  isomorphism is equivalent to the displayed square being a pushout. Thus
  neither an arbitrary equivalence of rings nor just abstract existence of
  an isomorphism is asserted. This is the same natural homomorphism, specified
  by its two actual legs, over R itself (not over a replacement base ring).
- The second conjunct gives a `GrpObj` structure on exactly H above and a
  homomorphism from G with that fixed canonical underlying map. The existential
  group structure is used by `IsMonHom u`, not an unrelated preexisting instance.
- `IsMonHom.one_hom` says `e_G ≫ u = e_H`, hence `e_H* = e_G*` under the
  spectrum section identifications. `IsMonHom.mul_hom` says
  `m_G ≫ u = (u × u) ≫ m_H`. On sections this says `β₂ ∘ Δ = m_G*` because
  pullback by the fixed `u` is `id_A`. With the first conjunct this is precisely
  `Δ = β₂⁻¹ ∘ m_G*`, so multiplication is the specified induced multiplication.
- `CategoryTheory.GrpObj.inv_hom` (Mathlib.CategoryTheory.Monoidal.Grp:326)
  gives `i_G ≫ u = u ≫ i_H` for a homomorphism of group objects. Its section
  equation is exactly `i_H* = i_G*` under the same identifications. Thus the
  inverse clause is included in the group-homomorphism assertion. There is no
  separate unproved helper theorem in this delivery.
- There is no `[IsAffine G.left]`, `[Algebra.FiniteType R A]`, smoothness,
  connectedness, reducedness, or restriction on residue characteristic.

Recorded statement dependencies read and reused:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  Mathlib.RingTheory.DiscreteValuationRing.Basic, lines 55--60.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme, lines 470--483.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  Mathlib.AlgebraicGeometry.Morphisms.Flat, lines 36--46, with the stalkwise
  characterization `Flat.iff_flat_stalkMap` described by its record.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated`, one of the
  node's recorded declarations, Mathlib.AlgebraicGeometry.Morphisms.Separated:44.
  Imported through the recorded module Mathlib.AlgebraicGeometry.Morphisms.Proper.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType:43, and
  `AlgebraicGeometry.QuasiCompact`, Morphisms.QuasiCompact:43.
- `def-pc-base-change`: WeilConjectures.AlgebraicGeometry.BaseChangeConventions,
  whose documentation explicitly specifies `Limits.pullback` and its projections
  for the scheme product. Read its `baseChange_morphism_projections` and the
  node's note; its module-base-change functor is not mistaken for a scheme product.
- `lem-weil-pbc-morphism-into-affine-scheme` is a Mathlib leaf with no `lean`
  record. Its `mathlib_match` is `AlgebraicGeometry.ΓSpec.adjunction`,
  Mathlib.AlgebraicGeometry.GammaSpecAdjunction:400. This is used through
  `Scheme.toSpecΓ`, defined as its unit at lines 435--440. The node's basic-open
  clause is `Scheme.preimage_basicOpen` (Scheme.lean:679), also read.

Proof dependencies remain available by plain imports: Flat supplies `flat_iff`
and `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`; Pullbacks supplies
`pullbackSpecIso` and its projection formulas; Flat.TorsionFree supplies
`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`; Flat.Stability supplies
`Module.Flat.baseChange`; RingHom.Flat supplies `RingHom.Flat.comp`; the recorded
WeilConjectures modules supply `Scheme.Modules.IsInvertible` and
`Scheme.Modules.injective_smul_sections_of_flat`. The qcqs-over-affine leaf is
`QuasiCompact.compactSpace_of_compactSpace` together with
`quasiSeparatedSpace_of_quasiSeparated`, available from the morphism imports.
The records and the source declarations/docstrings of these inputs were read.

Edge cases checked before writing: the trivial group has A = R and the
comparison reduces to `R ⊗_R R = R`; an elliptic scheme is allowed, with A = R
and a highly noninjective affinization map. The additive and multiplicative
groups give the usual polynomial/Laurent-polynomial comparisons. Non-smooth
groups such as μ_p in residue characteristic p are included; no smoothness
or geometric reducedness was smuggled into the statement. The group need
not be commutative or connected. An empty G cannot carry the required identity
section over a DVR, so it is already ruled out by the actual group hypothesis,
not by an added `Nonempty` condition. The universe u is declared explicitly,
and `autoImplicit` is false. No base change or test-object quantification is
made artificially small. No statement dispute was found.

Searches actually run with `msearch.py Q05 lem-sfb-flat-trait-group-affinization`:

- `leanfinder`: "The affinization of a flat separated finite type group scheme
  over a discrete valuation ring is a group scheme". Eight hits on affine
  schemes, affine space and finite morphisms; no match.
- `loogle`: `"GrpObj", "Γ"`. Zero hits.
- `grep`: `affinization|affinisation|[Hh]opf.*[Ss]ection|[Ss]ection.*[Hh]opf`.
  Five hits, three in Group/Affine.lean and two irrelevant Hopf quotients.
  Read the affine-group global-sections instance at lines 336--346: it
  requires `[IsAffine G]`, absent here, so it cannot be reused as this theorem.
- `leansearch`: "Global sections of a flat group scheme over a discrete
  valuation ring form a Hopf algebra". Eight hits: the Γ functors, ΓSpecIso,
  general Hopf-algebra structures, group-like elements; no comparison theorem.
- `rg` of `lean/WeilConjectures` for the item id found no declaration. `rg`
  of both `lean/WeilConjectures` and `lean/Sheaf` for affinization and group
  keywords found existing relative-affinization, open-image and equivariance
  results, but no flat-trait group-affinization theorem. Existing group
  statements use the same `GrpObj`/`IsMonHom` interface; no notion was copied.

Validation: `scompile.py Q05 lem-sfb-flat-trait-group-affinization` on the
delivered module succeeds against current server sources (1.9 seconds).
The wrapper's local attempt encountered ENOSPC and automatically confirmed
with the successful server compile; no compiler or wrapper was modified.
The module has no diagnostic commands, all lines are at most 100 characters,
and the recorded statement is extracted verbatim from the declaration.

## Second reading by Q05

The delivering worker reread the node alongside the complete signature and
the definitions of `GrpObj`, `IsMonHom`, `IsPushout`, `Scheme.toSpecΓ` and
`Scheme.ΓSpecIso`. This is a second pass, not a claim of independent review;
the dispatcher brief assigns independent review to the maintainer.
In particular, the first conjunct retains the canonical map (the two actual
projection pullbacks), and the second conjunct retains the induced R-structure
and the canonical map on G. The class-typed existential supplies the target
group structure for `IsMonHom`, and `GrpObj.inv_hom` verifies that this includes
the inverse clause. Finite type still has both its local and quasi-compact
parts. No generic-affine hypothesis from Proposition 3.1's surrounding argument
was added. No mismatch or change to the DAG statement was needed.
