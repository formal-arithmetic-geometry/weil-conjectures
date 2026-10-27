/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D9
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Jacobson.Ideal
import Sheaf.RingTheory.WContractibleJacobsonHenselian
import Sheaf.AlgebraicGeometry.ProperHenselianDerivedRestriction
import WeilConjectures.AlgebraicGeometry.AbelianDerivedGlobalExtPullback
import WeilConjectures.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion

/-! # Torsion comparison over the closed points of a w-contractible base

Source: proper base change, Stacks Project Tag 095T; henselian H0, Tag 0A0C;
Ruimy--Tubach--Wolf, Proposition 1.1.2.
(blueprint: lem-sfb-proper-wcontractible-torsion-rigidity).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 800000 in
-- Comparing derived adjunction and Ext maps exceeds the default elaboration budget.
/-- Proper base change identifies torsion cohomology with that of the closed fibre over
the Jacobson radical of a w-contractible ring.
Source: Stacks Project, Tags 095T and 0A0C; Ruimy--Tubach--Wolf, Proposition 1.1.2.
(blueprint: lem-sfb-proper-wcontractible-torsion-rigidity).

Proof. Put W=Spec R and C=Spec(R/J), where J is the Jacobson radical. The ring R is
henselian along J. Its closed-point subscheme C is w-contractible, as is W. Evaluation
on each of these pro-etale sites is exact, since its terminal representable is projective.
The abelian etale/pro-etale cohomology comparison gives vanishing of higher etale
cohomology for every abelian sheaf on W and C. The H1 exact sequence of the kernel of
an epimorphism then shows that etale global sections on both bases are exact.
Henselian proper H0 comparison, applied to the identity of W, identifies Gamma(W,G)
with Gamma(C,i-star G) for every abelian etale G. For a torsion sheaf F on T, proper
base change gives i-star Rp-star F = Rp0-star t-star F. Exact inverse image commutes
with cohomology, and exact base sections identify total-space cohomology with the
sections of each higher direct image. Apply H0 comparison to those higher direct
images and the base change isomorphism to obtain the desired bijection in every
degree. The Leray comparisons are induced by the same adjunction units and counits
as base change. Their unit-square-counit identity identifies this composite with the
actual Ext pullback cohomologyMap t. The argument uses locally torsion sheaves and
does not assume a uniform annihilator. It includes R=0 and empty total spaces. -/
theorem proper_wContractible_torsion_rigidity
    (R : Type u) [CommRing R] [IsWContractibleRing R]
    {T T₀ : Scheme.{u}} (p : T ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (t : T₀ ⟶ T)
    (p₀ : T₀ ⟶ Spec (CommRingCat.of (R ⧸ Ideal.jacobson (⊥ : Ideal R))))
    (sq : IsPullback t p₀ p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.jacobson (⊥ : Ideal R))))))
    (F : Sheaf T.smallEtaleTopology Ab.{u + 1}) (hF : Scheme.IsTorsionAbelianSheaf F)
    (q : ℕ) : Function.Bijective (cohomologyMap t F q) := by
  have : HenselianRing R (Ideal.jacobson (⊥ : Ideal R)) :=
    (RingTheory.wcontractible_jacobson_henselian.{u, u} R).1
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  have hK : T.HasTorsionEtaleCohomology K.obj := by
    intro n
    have ht : F.IsTorsion := (Scheme.isTorsionAbelianSheaf_characterizations F).1.mp hF
    by_cases hn : n = 0
    · subst n
      exact Sheaf.IsTorsion.of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm ht
    · have hz : IsZero ((DerivedCategory.Plus.homologyFunctor _ n).obj K) := by
        rcases lt_or_gt_of_ne hn with hn | hn
        · exact DerivedCategory.Plus.isZero_homology_of_isGE K 0 n hn
        · exact DerivedCategory.Plus.isZero_homology_of_isLE K 0 n hn
      apply Sheaf.IsTorsion.of_forall_isAddTorsion
      intro U x
      have hx := Functor.map_isZero
        (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (evaluation _ AddCommGrpCat.{u + 1}).obj U) hz
      have hs : Subsingleton _ := AddCommGrpCat.isZero_iff_subsingleton.mp hx
      rw [isOfFinAddOrder_iff_nsmul_eq_zero]
      exact ⟨1, Nat.one_pos, by simpa using hs.elim x 0⟩
  let i := Spec.map
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.jacobson (⊥ : Ideal R))))
  let j := pullback.fst p i
  have hj := proper_henselian_derived_restriction R (Ideal.jacobson (⊥ : Ideal R)) p K hK
  rw [abelianDerivedCohomologyPullback, derivedCohomologyPullback_eq_derivedUnit] at hj
  obtain ⟨b₁, b₂, hb⟩ := exists_addEquiv_derivedGlobal_ext_pullback j F q
  have hbij : Function.Bijective (cohomologyMap j F q) := by
    have : IsIso (etaleDerivedRestriction j K) := hj
    let m := (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
      (etaleDerivedRestriction j K)
    have hm := ConcreteCategory.bijective_of_isIso m
    have hc := b₂.bijective.comp hm
    have heq : b₂ ∘ m = cohomologyMap j F q ∘ b₁ := funext hb
    rw [heq] at hc
    exact (Function.Bijective.of_comp_iff _ b₁.bijective).mp hc
  let e := sq.isoPullback
  have he : Function.Bijective
      (cohomologyMap e.hom ((upperStar AddCommGrpCat.{u + 1} j).obj F) q ∘
        cohomologyMap j F q) := (cohomologyMap_bijective e.hom _ q).comp hbij
  have hmap : Function.Bijective (Sheaf.H.map
      ((upperStarComp AddCommGrpCat.{u + 1} e.hom j).hom.app F) q) := by
    exact Function.bijective_iff_has_inverse.mpr
      ⟨Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} e.hom j).inv.app F) q,
        fun x ↦ by rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id_app,
          Sheaf.H.map_id_apply],
        fun x ↦ by rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id_app,
          Sheaf.H.map_id_apply]⟩
  have heq : cohomologyMap e.hom _ q ∘ cohomologyMap j F q =
      Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} e.hom j).hom.app F) q ∘
        cohomologyMap (e.hom ≫ j) F q :=
    funext (cohomologyPullbackFunctorial e.hom j F q).2.1
  rw [heq] at he
  have h := (Function.Bijective.of_comp_iff' hmap _).mp he
  change Function.Bijective (cohomologyMap
    (sq.isoPullback.hom ≫ pullback.fst p i) F q) at h
  rwa [sq.isoPullback_hom_fst] at h

end AlgebraicGeometry.Etale
