/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheafTransport
import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedLowerStar
import WeilConjectures.WeilSheaf.Localization
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLeftAdjunction

/-!
# Localization in the native Weil sheaf heart

For an open immersion `j` and a complementary closed immersion `i`, the counit of
`j_! ⊣ j^*` and the unit of `i^* ⊣ i_*` form a natural short exact sequence of native
pro-étale Weil sheaves.

## Implementation details

The open adjunction is lifted from the adic adjunction to Frobenius fixed pairs via
`Endofunctor.IsoAlgebra.mapOfNatIsoLeftAdjunction`. Short exactness is detected jointly by the
two exact restriction functors `j^*` and `i^*`.

## References

* Stacks Project, Tags 09AH and 09BM.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

namespace AlgebraicGeometry

open ProEtale
open scoped ProEtale CategoryTheory.Obj

-- Match the coefficient instances of the public imports. The proof-only imports also
-- expose a commutative-ring shortcut, whose use forces expensive sheaf-functor conversions.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing
  ULift.commRing AlgebraicClosure.instCommRing

private noncomputable def nativeOpenAdjunction
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {U S : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [S.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ S) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] :
    ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣ ProEtaleWeilSheaf.upperStar k₀ l j := by
  apply Endofunctor.IsoAlgebra.mapOfNatIsoLeftAdjunction
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l _)
    (ProEtale.adicUpperStarLowerStarAdjunction l _)
    _ _ _ (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l j _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar l _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso l j _)
  intro K
  exact ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    _ K

private lemma shortExact_of_jointly_detected
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (P : C ⥤ D) (Q : C ⥤ E) [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (detect : ∀ M, IsZero (P.obj M) → IsZero (Q.obj M) → IsZero M)
    (S : ShortComplex C) (hP : (S.map P).ShortExact)
    (hQ : (S.map Q).ShortExact) : S.ShortExact := by
  have hkerP : IsZero (P.obj (kernel S.f)) := by
    have hm : Mono (P.map S.f) := hP.mono_f
    exact (isZero_kernel_of_mono (P.map S.f)).of_iso (PreservesKernel.iso P S.f)
  have hkerQ : IsZero (Q.obj (kernel S.f)) := by
    have hm : Mono (Q.map S.f) := hQ.mono_f
    exact (isZero_kernel_of_mono (Q.map S.f)).of_iso (PreservesKernel.iso Q S.f)
  have hcokerP : IsZero (P.obj (cokernel S.g)) := by
    have he : Epi (P.map S.g) := hP.epi_g
    exact (isZero_cokernel_of_epi (P.map S.g)).of_iso (PreservesCokernel.iso P S.g)
  have hcokerQ : IsZero (Q.obj (cokernel S.g)) := by
    have he : Epi (Q.map S.g) := hQ.epi_g
    exact (isZero_cokernel_of_epi (Q.map S.g)).of_iso (PreservesCokernel.iso Q S.g)
  have hhomP : IsZero (P.obj S.homology) :=
    ((S.map P).exact_iff_isZero_homology.1 hP.exact).of_iso (S.mapHomologyIso P).symm
  have hhomQ : IsZero (Q.obj S.homology) :=
    ((S.map Q).exact_iff_isZero_homology.1 hQ.exact).of_iso (S.mapHomologyIso Q).symm
  have : Mono S.f := Preadditive.mono_of_isZero_kernel _ (detect _ hkerP hkerQ)
  have : Epi S.g := Preadditive.epi_of_isZero_cokernel _ (detect _ hcokerP hcokerQ)
  exact ⟨S.exact_iff_isZero_homology.2 (detect _ hhomP hhomQ)⟩

private lemma shortExact_of_localization
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (P : C ⥤ D) (Q : C ⥤ E) (J : D ⥤ C) (I : E ⥤ C)
    [P.Additive] [Q.Additive] [J.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (aj : J ⊣ P) (ai : Q ⊣ I)
    (hj : ∀ N, IsIso (aj.unit.app N)) (hi : ∀ N, IsIso (ai.counit.app N))
    (hPI : ∀ N, IsZero (P.obj (I.obj N)))
    (hQJ : ∀ N, IsZero (Q.obj (J.obj N)))
    (detect : ∀ M, IsZero (Q.obj M) → IsZero (P.obj M) → IsZero M) (M : C) :
    ∃ h : aj.counit.app M ≫ ai.unit.app M = 0,
      (ShortComplex.mk (aj.counit.app M) (ai.unit.app M) h).ShortExact := by
  have h : aj.counit.app M ≫ ai.unit.app M = 0 := by
    have hn := aj.counit.naturality (ai.unit.app M)
    have hz : P.map (ai.unit.app M) = 0 := (hPI _).eq_of_tgt _ _
    change J.map (P.map (ai.unit.app M)) ≫ aj.counit.app _ =
      aj.counit.app M ≫ ai.unit.app M at hn
    rw [hz, Functor.map_zero, zero_comp] at hn
    exact hn.symm
  refine ⟨h, ?_⟩
  let S := ShortComplex.mk (aj.counit.app M) (ai.unit.app M) h
  apply shortExact_of_jointly_detected Q P detect S
  · have hc : IsIso (ai.counit.app (Q.obj M)) := hi _
    have hg : IsIso (Q.map (ai.unit.app M)) := by
      rw [← IsIso.inv_eq_of_inv_hom_id (ai.left_triangle_components M)]
      infer_instance
    have hf : (S.map Q).f = 0 := (hQJ _).eq_of_src _ _
    have : Mono (S.map Q).f := ⟨fun a b _ ↦ (hQJ _).eq_of_tgt a b⟩
    have : Epi (S.map Q).g := inferInstanceAs (Epi (Q.map (ai.unit.app M)))
    exact ⟨(ShortComplex.exact_iff_mono _ hf).2
      (inferInstanceAs (Mono (Q.map (ai.unit.app M))))⟩
  · have hu : IsIso (aj.unit.app (P.obj M)) := hj _
    have hf : IsIso (P.map (aj.counit.app M)) := by
      rw [← IsIso.inv_eq_of_hom_inv_id (aj.right_triangle_components M)]
      infer_instance
    have hg : (S.map P).g = 0 := (hPI _).eq_of_tgt _ _
    have : Epi (S.map P).g := ⟨fun a b _ ↦ (hPI _).eq_of_src a b⟩
    have : Mono (S.map P).f := inferInstanceAs (Mono (P.map (aj.counit.app M)))
    exact ⟨(ShortComplex.exact_iff_epi _ hg).2
      (inferInstanceAs (Epi (P.map (aj.counit.app M))))⟩

private lemma coefficient_square (l : ℕ) [Fact l.Prime]
    {Y A B T : Scheme.{u}} (a : Y ⟶ A) (b : A ⟶ T) (c : Y ⟶ B) (d : B ⟶ T)
    (h : a ≫ b = c ≫ d) :
    (a)^*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l b) ≫
        upperStarAdicConstantSheafHom l a =
      (upperStarCompIso (WeilCoefficients.{u} l) h).hom.app (adicConstantSheaf l T) ≫
        (c)^*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l d) ≫
          upperStarAdicConstantSheafHom l c := by
  rw [← cancel_epi ((upperStarComp (WeilCoefficients.{u} l) a b).hom.app
    (adicConstantSheaf l T))]
  simp only [upperStarCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [upperStarAdicConstantSheafHom_comp, upperStarAdicConstantSheafHom_comp]
  have hc : ∀ (f g : Y ⟶ T) (h : f = g),
      (upperStarCongr (WeilCoefficients.{u} l) h).hom.app (adicConstantSheaf l T) ≫
        upperStarAdicConstantSheafHom l g = upperStarAdicConstantSheafHom l f := by
    intro f g h
    subst g
    simp [upperStarCongr]
  exact (hc _ _ h).symm

attribute [local irreducible] Scheme.Hom.geometricFiber
  Scheme.Hom.geometricFiberMap Scheme.Hom.geometricGaloisFrobenius

attribute [local semireducible] Scheme.Hom.geometricFiber
  Scheme.Hom.geometricFiberMap Scheme.Hom.geometricGaloisFrobenius

/-- For an open immersion `j : U ⟶ X` and a closed immersion `i : Z ⟶ X` with complementary
images, the lifted adjunctions `j_! ⊣ j^*` and `i^* ⊣ i_*` on native pro-étale Weil sheaves
have the underlying units and counits of the adic adjunctions, and the counit `j_! j^* M ⟶ M`
and unit `M ⟶ i_* i^* M` form a short exact sequence for every `M`. -/
theorem ProEtaleWeilSheaf.nativeImmersionHeartLocalization
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    (X U Z : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    ∃ (aj : ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣
        ProEtaleWeilSheaf.upperStar k₀ l j)
      (ai : ProEtaleWeilSheaf.upperStar k₀ l i ⊣ ProEtaleWeilSheaf.lowerStar k₀ l i),
      (∀ N : ProEtaleWeilSheaf k₀ l U,
        (aj.unit.app N).hom.f =
          (adicOpenImmersionLowerShriekAdjunction l
            (Scheme.Hom.geometricFiberMap j
              (comp_over j (Spec (CommRingCat.of k₀))))).unit.app N.carrier) ∧
      (∀ M : ProEtaleWeilSheaf k₀ l X,
        (aj.counit.app M).hom.f =
          (adicOpenImmersionLowerShriekAdjunction l
            (Scheme.Hom.geometricFiberMap j
              (comp_over j (Spec (CommRingCat.of k₀))))).counit.app M.carrier) ∧
      (∀ M : ProEtaleWeilSheaf k₀ l X,
        (ai.unit.app M).hom.f =
          (adicUpperStarLowerStarAdjunction l
            (Scheme.Hom.geometricFiberMap i
              (comp_over i (Spec (CommRingCat.of k₀))))).unit.app M.carrier) ∧
      (∀ N : ProEtaleWeilSheaf k₀ l Z,
        (ai.counit.app N).hom.f =
          (adicUpperStarLowerStarAdjunction l
            (Scheme.Hom.geometricFiberMap i
              (comp_over i (Spec (CommRingCat.of k₀))))).counit.app N.carrier) ∧
      ∀ M : ProEtaleWeilSheaf k₀ l X,
        ∃ h : aj.counit.app M ≫ ai.unit.app M = 0,
          (ShortComplex.mk (aj.counit.app M) (ai.unit.app M) h).ShortExact := by
  let aj := nativeOpenAdjunction k₀ l j
  let ai := ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l i
  refine ⟨aj, ai, (fun _ ↦ rfl), (fun _ ↦ rfl), (fun _ ↦ rfl), (fun _ ↦ rfl), ?_⟩
  intro M
  apply shortExact_of_localization
    (ProEtaleWeilSheaf.upperStar k₀ l j) (ProEtaleWeilSheaf.upperStar k₀ l i)
    (ProEtaleWeilSheaf.extensionByZero k₀ l j) (ProEtaleWeilSheaf.lowerStar k₀ l i)
    aj ai
  · intro N
    have : IsIso ((IsoAlgebra.forget _).map (aj.unit.app N)) :=
      inferInstanceAs (IsIso ((adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app N.carrier))
    exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)
  · intro N
    exact inferInstanceAs (IsIso
      ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l i).counit.app N))
  · exact ProEtaleWeilSheaf.isZero_upperStar_obj_lowerStar_obj i j hij
  · intro N
    apply (ProEtaleWeilSheaf.isZero_iff _).2
    exact isZero_adicUpperStar_adicOpenImmersionLowerShriek _ _
      (Set.disjoint_iff_inter_eq_empty.1
        (Scheme.Hom.isCompl_range_geometricFiberMap i j _ _ hij).disjoint.symm) _
  · exact ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl i j hij

end AlgebraicGeometry
