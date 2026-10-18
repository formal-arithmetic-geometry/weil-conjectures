/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Localization.FractionRing
import Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import Sheaf.AlgebraicGeometry.FlatValuationLifting

/-!
# Fpqc descent of separatedness and full valuative lifting for algebraic spaces

Source: Bhatt–Scholze, The pro-étale topology for schemes, Lemma 7.3.9, p.67;
Stacks Project, Tags 0421 and 04P2
(blueprint: lem-a1-space-fpqc-separated-valuative-descent).

Separatedness is the project's `IsSeparatedPresheafMap` (every scheme test of the diagonal
is a closed immersion) of the structure map `terminal.from F`: the terminal presheaf on
`Over S` is represented by `Over.mk (𝟙 S)`, so this map is `q : F → S`. The predicate below
spells out the full valuative lifting property defined in this node. Restriction along
`Over.map f` is the functor of points of the actual base change: on a scheme `T → U` its
sections are precisely maps `T → E` over `S`, hence maps `T → E ×_S U` over `U`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The full valuative lifting property defined in this node, expressed on the functor of
points. A section on `Spec R` already lies over the specified `b`, and its restriction to
`Spec K` must be the specified generic section. Both existence and uniqueness are required.
Source: Bhatt–Scholze, Lemma 7.3.9, p.67, valuative criterion in the forward inclusion
(blueprint: lem-a1-space-fpqc-separated-valuative-descent). -/
def HasFullValuativeLifting {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (b : Spec (CommRingCat.of R) ⟶ S)
    (a : F.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b)))),
    ∃! e : F.obj (op (Over.mk b)),
      F.map (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        (Eq.refl _)).op e = a

/-- Fpqc descent of separatedness and the full valuative lifting property, without
quasi-compactness or finite-type assumptions on the algebraic space over its base.
Source: Bhatt–Scholze, Lemma 7.3.9, p.67; Stacks Project, Tags 0421 and 04P2
(blueprint: lem-a1-space-fpqc-separated-valuative-descent).

Proof: (1) Test the diagonal on a scheme. Its equality locus is a scheme by the
representable diagonal of `E`. After pulling the fpqc cover back to the test scheme,
it is a closed immersion locally, and hence globally by
`lem-pc-fpqc-descend-closed-immersion` and `lem-galois-fpqc-covering-base-change`.
(2) Two valuation lifts have a closed equalizer. Its ideal becomes zero in the fraction
field, so injectivity of the valuation ring into that field makes the ideal zero.
(3) Pull the cover back to `Spec R`, choose a point above its closed point, and use
`lem-a1-flat-valuation-lifting` to obtain an injective local extension `R → R'` of
valuation rings and a map to one covering member.
(4) By `lem-trf-valuation-torsionfree-flat`, both `R'` and its fraction field `K'` are
flat over `R`. The local flat extension is faithfully flat by
`lem-weil-pbc-flat-local-hom-faithfully-flat`; its spectrum and the field-extension
spectrum are fpqc covers, using `lem-weil-pbc-flat-ring-map-iff-flat-affine` and
`lem-weil-pbc-affine-scheme-qcqs`.
(5) Apply the lifting hypothesis on the chosen covering member to obtain a lift over `R'`.
(6) The map `R' ⊗[R] R' → K' ⊗[K] K'` is injective by two applications of
`lem-trf-flat-tensor-preserves-injection`; the tensor products describe the overlaps by
`lem-weil-pbc-algebra-tensor-pushout-universal-property` and `def-weil-affine-spectrum`.
The two lifts agree over the field overlap. Their closed equalizer over the ring overlap
is the whole overlap, since its ideal dies under that injective map.
(7) Descend the compatible lift using `lem-a1-algebraic-space-fpqc-sheaf`. Its generic
restriction equals the original generic section after the fpqc field extension, hence
before it by the same sheaf lemma. Uniqueness follows from (2). -/
theorem closedDiagonal_and_fullValuativeLifting_of_fpqc_cover
    {X : Scheme.{u}} (E : AlgebraicSpace X) {I : Type u}
    (U : I → Scheme.{u}) (f : ∀ i : I, U i ⟶ X)
    (hcover : Presieve.ofArrows U f ∈ Scheme.fpqcPrecoverage X)
    (hlocal : ∀ i : I,
      IsSeparatedPresheafMap (terminal.from ((Over.map (f i)).op ⋙ E.obj.obj)) ∧
      HasFullValuativeLifting ((Over.map (f i)).op ⋙ E.obj.obj)) :
    IsSeparatedPresheafMap (terminal.from E.obj.obj) ∧
      HasFullValuativeLifting E.obj.obj := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
