/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.AffineSpace

public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude

import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceAmbientAdjunction
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionAbelianDirectImageVanishing
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.LowerShriek.Formalism.Compactification
import WeilConjectures.AlgebraicGeometry.Finite.Etale.FiniteEtaleOpenUniformTorImage
import WeilConjectures.AlgebraicGeometry.Etale.EtalePullbackLineFlatModel
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeDirectImageConstructibility
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceAmbientAdjunctionCore
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportAmplitude
public import WeilConjectures.AlgebraicGeometry.EtaleClosedSupportTorBound
public import WeilConjectures.AlgebraicGeometry.UnboundedCompactSupportProperComposition
public import WeilConjectures.ConstructibleSheaf.InternalHom
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

/-!
# Exceptional interval estimate on one affine closed/smooth chart

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/sk-lem-sf-kunneth-star/
sk-rem-sf-typing.md, Rf^! row, the single affine chart sub-step; and
literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-ctf-finite-geometric-restriction/sk-prop-sf-rf-shriek-preservation/
sk-prop-sf-rf-shriek-preservation.proof.md,
closed-support, affine-projection and composition paragraphs
(blueprint: lem-sf-finite-ring-affine-exceptional-window).

The two clauses concern ordinary unbounded derived categories of étale module sheaves.
The ring need not be a field or regular, and the coefficient zero ring is included.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem finiteWindow_bounded_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : DerivedCategoryModule A X) :
    DerivedCategory.isBoundedConstructible A X K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, hab, hz⟩
    exact ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).2
      (fun q hq ↦ hz q (.inl hq))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K b).2 (fun q hq ↦ hz q (.inr hq))⟩⟩,
      fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)⟩
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (hc q), min a b, max a b, min_le_max, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha q (lt_of_lt_of_le hq (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb q
        (lt_of_le_of_lt (le_max_right _ _) hq)

private theorem finiteWindow_bounded_of_interval
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : DerivedCategoryModule A X) (a b : ℤ) (hab : a ≤ b)
    (hc : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K))
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    DerivedCategory.isBoundedConstructible A X K := by
  refine ⟨hc, a, b, hab, fun q hq ↦ ?_⟩
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff K a).1 hK.1 q hq
  · exact (_root_.DerivedCategory.isLE_iff K b).1 hK.2 q hq

/-- The ordinary exceptional right adjoint on one affine chart carries constructible
cohomology and Tor intervals `[a,b]` to `[a-2r,b+2e+1]`.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/sk-lem-sf-kunneth-star/
sk-rem-sf-typing.md, Rf^! row, the single affine chart sub-step; and the closed-support,
affine-projection and composition paragraphs of
literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-ctf-finite-geometric-restriction/sk-prop-sf-rf-shriek-preservation/
sk-prop-sf-rf-shriek-preservation.proof.md
(blueprint: lem-sf-finite-ring-affine-exceptional-window).

Proof:
1. Put `P = A^r_V` and let `j` be the open complement of the image of `i`.
   The Noetherian polynomial dimension formula gives `dim P ≤ r+e`, and open
   monotonicity gives the same bound for the complement. Field extension does not
   increase this dimension. The relative torsion
   direct-image dimension bound therefore gives `cd(j) ≤ 2(r+e)`. The uniform open
   direct-image theorem gives vanishing for all coefficient module sheaves above this
   bound, and Tor amplitude `[a,b+2(r+e)]` for bounded constructible inputs of Tor
   amplitude `[a,b]`. Finite-type direct-image constructibility gives constructible
   higher images of every constructible sheaf, including sheaves without finite Tor
   amplitude. Thus both clauses of the open-complement condition hold.
2. The closed-support amplitude lemma gives constructible cohomology in
   `[a,b+2(r+e)+1]`. For Tor amplitude use the support triangle
   `i_* Ri^! K → K → Rj_* j^* K → (i_* Ri^! K)[1]` and the preceding open Tor bound.
   Exact closed pushforward and its restriction recover the same Tor interval for
   `Ri^! K`. The proper-input comparison used in step 3 identifies closed
   pushforward with compact support while composing the functors.
3. The ordinary affine-space adjunction identifies the right adjoint of the projection
   with `pi^*(-)(r)[2r]`. Exact pullback preserves constructibility, and the Tate twist
   is locally free of rank one. Cohomology therefore has interval `[a-2r,b-2r]`.
   For the Tor assertion, represent the input by flat constructible sheaves supported
   in `[a,b]`; pullback, flat rank-one tensor, and shift give the interval
   `[a-2r,b-2r]` as well. The compact-support composition comparison and uniqueness of
   composed right adjoints identify `G` with the closed right adjoint composed with
   this projection right adjoint, for every supplied compactification. Apply step 2
   to get `[a-2r,b-2r+2(r+e)+1] = [a-2r,b+2e+1]`. Empty schemes and the zero
   coefficient ring give zero objects; the same formulas apply when `r=0` or `e=0`.
-/
theorem finiteRingAffineExceptionalWindow
    (ell p : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hk : Finite k ∨ IsAlgClosed k)
    (_hne : p ≠ ell)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 1 ≤ n ∧ (ell : A) ^ n = 0)
    {U V : Scheme.{u}}
    [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [IsAffine U] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsAffine V] [IsSeparated (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    (r e : ℕ) (he : topologicalKrullDim V ≤ (e : WithBot ℕ∞))
    (i : U ⟶ AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) V)
    [IsClosedImmersion i]
    (π : AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) V ⟶ V)
    (hπ : π = (AlgebraicGeometry.AffineSpace.over (ULift.{u} (Fin r)) V).hom)
    (c : Compactification (i ≫ π))
    (G : DerivedCategoryModule A V ⥤ DerivedCategoryModule A U)
    (hG : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (a b : ℤ) (hab : a ≤ b) :
    (∀ L : DerivedCategoryModule A V,
      AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A V L ∧
        DerivedCategory.homologyConcentratedIn a b L →
      AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A U (G.obj L) ∧
        DerivedCategory.homologyConcentratedIn (a - 2 * r) (b + 2 * e + 1) (G.obj L)) ∧
    (∀ K : DerivedCategoryModule A V,
      AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A V K ∧
        AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn A V a b K →
      AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A U (G.obj K) ∧
        AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn A U
          (a - 2 * r) (b + 2 * e + 1) (G.obj K)) := by
  classical
  subst π
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian
    (V ↘ Spec (.of k))
  have : IsNoetherian V := {}
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian
    (U ↘ Spec (.of k))
  have : IsNoetherian U := {}
  let P := AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) V
  let π : P ⟶ V := P ↘ V
  let aP : P ⟶ Spec (.of k) := π ≫ (V ↘ Spec (.of k))
  let pOver : P.Over (Spec (.of k)) := ⟨aP⟩
  have : LocallyOfFiniteType aP := inferInstance
  have : QuasiCompact aP := inferInstance
  have : IsSeparated aP := inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian aP
  have : IsNoetherian P := {}
  let W : P.Opens := ⟨(Set.range i.base)ᶜ,
    i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let j := W.ι
  let aW : W.toScheme ⟶ Spec (.of k) := j ≫ aP
  let wOver : W.toScheme.Over (Spec (.of k)) := ⟨aW⟩
  have : TopologicalSpace.NoetherianSpace W :=
    j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : LocallyOfFiniteType aW := inferInstance
  have : QuasiCompact aW := inferInstance
  have : IsSeparated aW := inferInstance
  have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have : IsNoetherianRing Γ(V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V⟩
  have hdimP : topologicalKrullDim P ≤ ((r + e : ℕ) : WithBot ℕ∞) := by
    dsimp only [P]
    rw [topologicalKrullDim_affineSpace_of_isAffine]
    simp only [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_fin, Nat.cast_add]
    simpa only [add_comm] using add_le_add_right he (r : WithBot ℕ∞)
  have hdimW : topologicalKrullDim W ≤ ((r + e : ℕ) : WithBot ℕ∞) :=
    j.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdimP
  have hdim (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of k))
      {T : Scheme.{u}} (p₁ : T ⟶ W.toScheme) (p₂ : T ⟶ Spec (.of L))
      (hT : IsPullback p₁ p₂ aW s) :
      topologicalKrullDim T ≤ ((r + e : ℕ) : WithBot ℕ∞) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ hT.isoPullback.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_pullback_le_of_field aW s).trans hdimW
  have hcd : j.torsionEtaleCohomologicalDimension ≤ ((2 * (r + e) : ℕ) : ℕ∞) := by
    apply sInf_le
    refine ⟨2 * (r + e), rfl, ?_⟩
    intro F hF q hq
    exact isZero_torsion_higherDirectImage_of_forall_field_dimension_le
      aW aP j rfl (r + e) hdim F hF q (by exact_mod_cast hq)
  obtain ⟨d, hd, hvan, htor⟩ := @finiteEtaleOpen_uniformTorImage
    ell p inferInstance k inferInstance inferInstance _hp _hne.symm
    A inferInstance inferInstance hA W.toScheme P wOver pOver
    (show LocallyOfFiniteType aW from inferInstance)
    (show QuasiCompact aW from inferInstance) (show IsSeparated aW from inferInstance)
    (show LocallyOfFiniteType aP from inferInstance)
    (show QuasiCompact aP from inferInstance) (show IsSeparated aP from inferInstance)
    j ⟨rfl⟩ inferInstance inferInstance
  have hdle : d ≤ 2 * (r + e) := by
    have hh := hd.trans_le hcd
    exact_mod_cast hh
  obtain ⟨n, _hn, hkill⟩ := hA
  have hkill' : ((ell ^ n : ℕ) : A) = 0 := by simpa only [Nat.cast_pow] using hkill
  have hell : IsUnit (ell : k) :=
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime) _hne).isUnit
  have hN : 0 < ell ^ n := pow_pos (Fact.out : ell.Prime).pos n
  have hNk : IsUnit ((ell ^ n : ℕ) : k) := by
    simpa only [Nat.cast_pow] using hell.pow n
  have hcoeff : IsSmoothBaseChangeCoefficients (ell ^ n) A (Spec (.of k)) :=
    ⟨hN, inferInstance, hkill', by
      simpa only [map_natCast] using hNk.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  have hcons (F : Sheaf W.toScheme.smallEtaleTopology (ModuleCat.{u + 1} A))
      (q : ℤ) (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
      Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
    have : Scheme.IsConstructibleSheaf F :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 hF
    have hsingle := (finiteWindow_bounded_iff A W.toScheme _).2
      (DerivedCategory.boundedConstructible_singleFunctor_obj F 0)
    exact (isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
      k A (ell ^ n) hcoeff aW aP j rfl _ hsingle).1 q
  have hclosed (x y : ℤ) (hxy : x ≤ y) (K : DerivedCategoryModule A P)
      (hcK : DerivedCategory.isBoundedConstructible A P K)
      (hK : _root_.DerivedCategory.homologyConcentratedIn x y K) :
      DerivedCategory.isBoundedConstructible A U
          ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K) ∧
        _root_.DerivedCategory.homologyConcentratedIn x
          (y + 2 * (r + e) + 1)
          ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K) := by
    obtain ⟨hh, hc⟩ := (closedImmersion_rightAdjoint_amplitude A i j hij
      x y (2 * (r + e)) (by positivity)
      (fun F q hq ↦ hvan F q (by omega))).2 hcons K hK hcK.1
    exact ⟨finiteWindow_bounded_of_interval A U _ _ _ (by omega) hc hh, hh⟩
  have hclosedTor (x y : ℤ) (hxy : x ≤ y) (K : DerivedCategoryModule A P)
      (hcK : DerivedCategory.isBoundedConstructible A P K)
      (hK : DerivedCategory.hasTorAmplitudeIn A P x y K) :
      DerivedCategory.hasTorAmplitudeIn A U x (y + 2 * (r + e) + 1)
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K) := by
    have : IsFinite i := ((IsClosedImmersion.iff_isFinite_and_mono i).1 inferInstance).1
    let J := (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory
    have hcJ : DerivedCategory.isBoundedConstructible A W.toScheme (J.obj K) :=
      (finiteWindow_bounded_iff A W.toScheme _).2
        (((finiteWindow_bounded_iff A P K).1 hcK).mapDerivedCategory_upperStar j)
    have htJ : DerivedCategory.hasTorAmplitudeIn A W.toScheme x y (J.obj K) := by
      apply DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      exact (DerivedCategory.torAmplitudeIn _ _ x y).prop_of_iso
        ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app K)
        (torAmplitudeIn_leftDerivedUpperStar _ j x y
          (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hK))
    have hQ := (htor x y hxy (J.obj K) hcJ htJ).2.2
    have hQ' : DerivedCategory.hasTorAmplitudeIn A P x (y + 2 * (r + e))
        ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj (J.obj K)) := by
      intro M q hq
      exact hQ M q (by rcases hq with hq | hq <;> omega)
    obtain ⟨δ, hδ⟩ := exists_etale_closedSupportTriangle A i j hij
    exact closedSupport_torAmplitude A i j hij x y (2 * (r + e)) hxy
      (by positivity) K hK hQ' (δ.app K) (hδ K)
  have hNV : IsUnit ((ell ^ n : ℕ) : Γ(V, ⊤)) := by
    simpa only [map_natCast] using
      (hcoeff.2.2.2.map (V ↘ Spec (.of k)).appTop.hom)
  have hNP : IsUnit ((ell ^ n : ℕ) : Γ(P, ⊤)) := by
    simpa only [map_natCast] using hNV.map π.appTop.hom
  let E := Scheme.finiteEtaleTateTwist P (ell ^ n) A hkill' r
  obtain ⟨⟨cover, hcover⟩, hlc, hlex, _hrex⟩ :=
    Scheme.finite_etale_torsion_twist_line P (ell ^ n) hN
      (fun t ↦ by
        simpa only [map_natCast] using (hNP.map (P.presheaf.germ ⊤ t (by trivial)).hom))
      A hkill' r
  have heLocal (t : cover.I₀) : Nonempty
      ((upperStar (ModuleCat.{u + 1} A) (cover.f t)).obj E ≅
        (constantSheaf (cover.X t).smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)) := by
    let T := cover.etalePrecoverageToEtale t
    let e := Scheme.Etale.overSheafEquiv T (ModuleCat.{u + 1} A)
    exact ⟨(Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) T E).symm ≪≫
      e.functor.mapIso (hcover t).some ≪≫
      ((Scheme.Etale.overEquiv T).constantSheafSheafCongrIso _ _
        (ModuleCat.{u + 1} A) Over.mkIdTerminal).app (ModuleCat.of A A)⟩
  have hEfin (t : cover.I₀) : Scheme.IsFiniteSheaf
      ((upperStar (ModuleCat.{u + 1} A) (cover.f t)).obj E) := by
    have := Scheme.isFiniteSheaf_constantSheaf (X := cover.X t) (ModuleCat.of A A)
    exact Scheme.IsFiniteSheaf.of_iso (heLocal t).some.symm
  have : Scheme.IsFiniteSheaf E := Scheme.IsFiniteSheaf.of_cover cover E
  have : Scheme.IsLocallyConstantSheaf E := hlc
  have : Scheme.IsConstructibleSheaf E :=
    Scheme.IsFiniteLocallyConstantSheaf.isConstructibleSheaf (F := E) {}
  have hEflat : ObjectProperty.flat E :=
    (ObjectProperty.flat_iff_preservesFiniteLimits E).2 hlex
  let E₀ := (_root_.DerivedCategory.singleFunctor _ 0).obj E
  have hEt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) P 0 0 E₀ :=
    torAmplitudeIn_singleFunctor_zero_of_flat _ E hEflat
  let H : DerivedCategoryModule A V ⥤ DerivedCategoryModule A P :=
    ((upperStar (ModuleCat.{u + 1} A) π).mapDerivedCategory ⋙
      derivedTensorRight (ModuleCat.{u + 1} A) P E₀) ⋙ shiftFunctor _ (2 * (r : ℤ))
  have hHbc (K : DerivedCategoryModule A V)
      (hcK : DerivedCategory.isBoundedConstructible A V K) :
      DerivedCategory.isBoundedConstructible A P (H.obj K) := by
    have hbc := boundedConstructible_tensor A P
      (((finiteWindow_bounded_iff A V K).1 hcK).mapDerivedCategory_upperStar π)
      (DerivedCategory.boundedConstructible_singleFunctor_obj E 0) ⟨0, 0, hEt⟩
    exact (finiteWindow_bounded_iff A P _).2
      ((DerivedCategory.boundedConstructible _ P).le_shift _ _ hbc)
  have hHhom (K : DerivedCategoryModule A V)
      (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
      _root_.DerivedCategory.homologyConcentratedIn (a - 2 * r) (b - 2 * r) (H.obj K) := by
    have hh := _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_right
      ((upperStar (ModuleCat.{u + 1} A) π).homologyConcentratedIn_mapDerivedCategory_obj hK)
      hEt
    simp only [add_zero] at hh
    have : _root_.DerivedCategory.IsGE
        ((derivedTensorRight (ModuleCat.{u + 1} A) P E₀).obj
          ((upperStar (ModuleCat.{u + 1} A) π).mapDerivedCategory.obj K)) a := hh.1
    have : _root_.DerivedCategory.IsLE
        ((derivedTensorRight (ModuleCat.{u + 1} A) P E₀).obj
          ((upperStar (ModuleCat.{u + 1} A) π).mapDerivedCategory.obj K)) b := hh.2
    exact ⟨_root_.DerivedCategory.TStructure.t.isGE_shift
      ((derivedTensorRight (ModuleCat.{u + 1} A) P E₀).obj
        ((upperStar (ModuleCat.{u + 1} A) π).mapDerivedCategory.obj K))
      a (2 * (r : ℤ)) _,
      _root_.DerivedCategory.TStructure.t.isLE_shift
        ((derivedTensorRight (ModuleCat.{u + 1} A) P E₀).obj
          ((upperStar (ModuleCat.{u + 1} A) π).mapDerivedCategory.obj K))
        b (2 * (r : ℤ)) _⟩
  have hHtor (K : DerivedCategoryModule A V)
      (hK : DerivedCategory.hasTorAmplitudeIn A V a b K) :
      DerivedCategory.hasTorAmplitudeIn A P (a - 2 * r) (b - 2 * r) (H.obj K) := by
    have hpull := (DerivedCategory.torAmplitudeIn _ P a b).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ π).app K)
      (torAmplitudeIn_leftDerivedUpperStar _ π a b
        (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hK))
    have ht := torAmplitudeIn_tensor (ModuleCat.{u + 1} A) P a b 0 0 hpull hEt
    simp only [add_zero] at ht
    exact DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      (torAmplitudeIn_shift _ ht (2 * (r : ℤ)))
  let cp : Compactification π :=
    Compactification.ofIsImmersionAffineSpace (𝟙 _) (Category.id_comp _)
  obtain ⟨adjπ⟩ := affineSpaceAmbientAdjunction_of_compactification
    (ell ^ n) hN A hkill' V hNV r cp
  let I := R(lowerStar (ModuleCat.{u + 1} A) i)
  let J := I.rightAdjoint
  let adjI : I ⊣ J := Adjunction.ofIsLeftAdjoint I
  let lc := unboundedEtaleProperCompositionIso A i π cp c
  let adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ H ⋙ J :=
    (adjI.comp adjπ).ofNatIsoLeft lc
  let iso : G ≅ H ⋙ J := hG.rightAdjointUniq adj
  have hend : b - 2 * (r : ℤ) + 2 * (r + e) + 1 = b + 2 * e + 1 := by ring
  constructor
  · rintro K ⟨hcK, hK⟩
    obtain ⟨hc, hh⟩ := hclosed (a - 2 * r) (b - 2 * r) (by omega)
      (H.obj K) (hHbc K hcK) (hHhom K hK)
    rw [hend] at hh
    exact ⟨(finiteWindow_bounded_iff A U _).2
      ((DerivedCategory.boundedConstructible _ U).prop_of_iso (iso.app K).symm
        ((finiteWindow_bounded_iff A U _).1 hc)),
      (_root_.DerivedCategory.homologyConcentratedIn _ _).prop_of_iso (iso.app K).symm hh⟩
  · rintro K ⟨hcK, hK⟩
    have ht := hHtor K hK
    have hh := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn
      (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht)
    obtain ⟨hc, -⟩ := hclosed (a - 2 * r) (b - 2 * r) (by omega)
      (H.obj K) (hHbc K hcK) hh
    have ht' := hclosedTor (a - 2 * r) (b - 2 * r) (by omega)
      (H.obj K) (hHbc K hcK) ht
    rw [hend] at ht'
    refine ⟨(finiteWindow_bounded_iff A U _).2
      ((DerivedCategory.boundedConstructible _ U).prop_of_iso (iso.app K).symm
        ((finiteWindow_bounded_iff A U _).1 hc)), ?_⟩
    apply DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    exact (DerivedCategory.torAmplitudeIn _ U _ _).prop_of_iso (iso.app K).symm
      (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht')

end AlgebraicGeometry.Etale
