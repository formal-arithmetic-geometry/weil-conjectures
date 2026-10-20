/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.Paper.OrgogozoInductionData
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.TraceFormula.CurveNormalizationCompletion
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.ComplementaryPureSubcurveComponents
import Sheaf.TraceFormula.NodalSubcurveBoundary

/-! # Normalization branches of a nodal contraction

Source: Temkin, Stable modification of relative curves, Appendix B, Corollary B.2,
final normalization paragraph, printed p. 58; the ordinary-point reduced-fibre
calculation is expanded in the DAG proof.
(blueprint: lem-trf-nodal-contraction-normalization-branches).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Noncontracted component normalizations identify over the target, and the target's
normalization branches above the contraction point identify with the nonempty boundary.
At each boundary node precisely one branch belongs to the contracted subcurve. An ordinary
multiple target point has reduced scheme-theoretic fibre.

`B`, with `iB`, is the reduced induced closed subscheme on the fibre support: reducedness,
closed immersion and `hB` characterize it uniquely. The families `CX`, `CY` with closed
immersions `a`, `b` enumerate the reduced irreducible components without repetitions.
`N`, `ι`, `hN`, `ν`, `hν` present the normalization of the possibly reducible `X` as the
coproduct of the existing integral component normalizations. These are presentations of
objects in the statement, and impose no geometric restrictions. Over the algebraically
closed field a closed point is a rational point. All completion isomorphisms preserve
its specified ground-field scalars.

Source: Temkin, Appendix B, Corollary B.2 proof, final paragraph, printed p. 58.
(blueprint: lem-trf-nodal-contraction-normalization-branches).

Proof, following the nine steps of the DAG node:
1. Finite-type-over-noetherian gives Noetherianity. Complementary-pure-subcurve-components
   makes B a union of components and A, the reduced closure of its complement, the union
   of the others. Nodal-subcurve-boundary makes T = A intersect B finite and smooth on
   each subcurve. The two completed axes give one branch on each side.
2. The isomorphism off the fibre identifies all remaining generic points and hence the
   components and function fields. Reducedness makes their morphisms factor through
   the corresponding reduced target components.
3. Proper-fp-permanence gives proper component maps. Their fibres are finite, including
   the fibre inside T, so finite-iff-proper-finite-fibres makes them finite. The
   normalization-properties and smooth-normal lemmas give smooth proper normalizations;
   normalization-dominant-lift gives their comparison over the target.
4. On affine charts the comparison is finite: the source's finite module generators over
   the original target ring also generate over the intermediate normalized ring.
   Finite-birational-normal-iso makes it an isomorphism. Its inverses followed by the
   component inclusions give h on the coproduct N.
5. The image of the points over x is exactly T. A is smooth at T, so normalization is an
   isomorphism there (normalization-properties and smooth-normal), giving injectivity.
   A component through x and surjectivity of its normalization prove T nonempty.
6. For an ordinary target, curve-normalization-completion identifies the completed
   normalization with the product of the n power-series axes. Adjoining coordinate
   idempotents gives this integral closure; a negative valuation contradicts a monic
   integral equation. The maximal-ideal quotient is k to the n-th power.
7. Local-completion-faithfully-flat embeds the uncompleted quotient into that product.
   It is reduced; its local factors are finite-dimensional reduced local k-algebras,
   hence fields. Thus the target maximal ideal generates the parameter ideal on each
   exterior normalized branch, which is the smooth local ring of A at the boundary.
8. At a boundary node write the completed ambient ring as k[[u,v]]/(uv), with B the
   u=0 axis. Completion-exact-finite-modules identifies the component quotients.
   The fibre ideal lies in (u) and its restriction to A generates (u), hence it contains
   u times a unit and equals (u). The completed fibre ring is k[[v]], a domain.
   Faithful flatness descends reducedness to the uncompleted fibre local ring.
9. Away from A the reduced ambient scheme is an open of B, and the fibre ideal vanishes.
   Together with step 8 this proves reducedness everywhere on the actual fibre.
   Reduced-induced-closed-subscheme identifies that fibre with B over Y.
-/
theorem nodal_contraction_normalization_branches
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsProper pX] [IsProper pY] [IsReduced X] [IsReduced Y]
    (hX : X.IsPureDimension 1) (hY : Y.IsPureDimension 1)
    (f : Y ⟶ X) [IsProper f] [Surjective f] (hf : f ≫ pX = pY)
    (x : X) (hx : IsClosed ({x} : Set X))
    (B : Scheme.{u}) [IsReduced B] (iB : B ⟶ Y) [IsClosedImmersion iB]
    (hB : Set.range iB = f ⁻¹' {x}) [ConnectedSpace B] (hpureB : B.IsPureDimension 1)
    (hoff : IsIso (pullback.snd f
      (Scheme.Opens.ι (X := X) ⟨{x}ᶜ, hx.isOpen_compl⟩)))
    (hnodal : ∃ U : Y.Opens, Set.range iB ⊆ U ∧
      ∀ y : Y, y ∈ U → IsClosed ({y} : Set Y) →
        (¬ ∃ V : Y.Opens, y ∈ V ∧ Smooth (V.ι ≫ pY)) →
          Orgogozo.IsOrdinaryDoublePoint pY y)
    {I J : Type u} (CX : I → Scheme.{u}) (CY : J → Scheme.{u})
    [∀ i : I, IsIntegral (CX i)] [∀ j : J, IsIntegral (CY j)]
    (a : ∀ i : I, CX i ⟶ X) (b : ∀ j : J, CY j ⟶ Y)
    [∀ i : I, IsClosedImmersion (a i)] [∀ j : J, IsClosedImmersion (b j)]
    (ha : ∀ i : I, Set.range (a i) ∈ irreducibleComponents X)
    (hb : ∀ j : J, Set.range (b j) ∈ irreducibleComponents Y)
    (haindex : Function.Bijective
      (fun i : I ↦ (⟨Set.range (a i), ha i⟩ : irreducibleComponents X)))
    (hbindex : Function.Bijective
      (fun j : J ↦ (⟨Set.range (b j), hb j⟩ : irreducibleComponents Y)))
    (N : Scheme.{u}) (ι : ∀ i : I, (CX i).normalization ⟶ N)
    (hN : IsColimit (Cofan.mk N ι)) (ν : N ⟶ X)
    (hν : ∀ i : I, ι i ≫ ν = (CX i).fromNormalization ≫ a i) :
    (∃ e : {j : J // ¬ Set.range (b j) ⊆ Set.range iB} ≃ I,
      (∀ j : {j : J // ¬ Set.range (b j) ⊆ Set.range iB},
        closure (f '' Set.range (b j.1)) = Set.range (a (e j))) ∧
      ∃ c : ∀ j : {j : J // ¬ Set.range (b j) ⊆ Set.range iB},
        (CY j.1).normalization ≅ (CX (e j)).normalization,
        (∀ j : {j : J // ¬ Set.range (b j) ⊆ Set.range iB},
          (c j).hom ≫ (CX (e j)).fromNormalization ≫ a (e j) =
          (CY j.1).fromNormalization ≫ b j.1 ≫ f) ∧
        (∀ j : {j : J // ¬ Set.range (b j) ⊆ Set.range iB},
          Smooth ((CY j.1).fromNormalization ≫ b j.1 ≫ pY) ∧
          IsProper ((CY j.1).fromNormalization ≫ b j.1 ≫ pY) ∧
          Smooth ((CX (e j)).fromNormalization ≫ a (e j) ≫ pX) ∧
          IsProper ((CX (e j)).fromNormalization ≫ a (e j) ≫ pX)) ∧
        ∃ h : N ⟶ Y, h ≫ f = ν ∧
          (∀ j : {j : J // ¬ Set.range (b j) ⊆ Set.range iB},
            ι (e j) ≫ h = (c j).inv ≫ (CY j.1).fromNormalization ≫ b j.1) ∧
          Set.BijOn h (ν ⁻¹' {x}) (Set.range iB ∩ closure ((Set.range iB)ᶜ))) ∧
    (Set.range iB ∩ closure ((Set.range iB)ᶜ)).Nonempty ∧
    (∀ y : Y, y ∈ Set.range iB ∩ closure ((Set.range iB)ᶜ) →
      Orgogozo.IsOrdinaryDoublePoint pY y ∧
      (∃! j : J, y ∈ Set.range (b j) ∧ Set.range (b j) ⊆ Set.range iB) ∧
      (∃! j : J, y ∈ Set.range (b j) ∧ ¬ Set.range (b j) ⊆ Set.range iB) ∧
      ∀ j : J, y ∈ Set.range (b j) →
        ∃! z : (CY j).normalization, ((CY j).fromNormalization ≫ b j) z = y) ∧
    (∀ n : ℕ, 1 ≤ n →
      (∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
            (MvPowerSeries (Fin n) k ⧸ Ideal.span
              {g | ∃ i j : Fin n, i ≠ j ∧ g = MvPowerSeries.X i * MvPowerSeries.X j}),
        ∀ r : k, e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) (Orgogozo.localScalar pX x r)) =
            Ideal.Quotient.mk _ (MvPowerSeries.C r)) →
      IsReduced (f.fiber x) ∧
        ∃ eB : f.fiber x ≅ B, eB.hom ≫ iB = f.fiberι x) := by
  sorry

end AlgebraicGeometry
