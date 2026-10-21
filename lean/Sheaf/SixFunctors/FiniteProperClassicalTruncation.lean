/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage

import Mathlib.Tactic.ClearExcept
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# A uniform truncation window for proper classical direct images

Source: Weil conjectures blueprint, main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper-localizing.proof.md, paragraphs "Etale statements" and "Transfer"
(blueprint: lem-sfb-finite-proper-classical-truncation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Finite-interval dévissage along good-truncation triangles. -/
private theorem finite_range_upper_bound
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
    (P : C → Prop)
    (hPiso : ∀ {H H' : C}, (H ≅ H') → P H → P H')
    (e : ℤ) (hF : ∀ (H : C), P H → ∀ p : ℤ, e < p →
      IsZero ((DerivedCategory.homologyFunctor D p).obj
        (F.obj ((DerivedCategory.singleFunctor C 0).obj H))))
    (K : DerivedCategory C) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ q : ℤ, a ≤ q → q ≤ b →
      P ((DerivedCategory.homologyFunctor C q).obj K))
    (r : ℤ) (hr : b + e < r) :
    IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj K)) := by
  suffices H : ∀ (n : ℕ) (K : DerivedCategory C) (a b : ℤ), b - a ≤ n →
      K.IsGE a → K.IsLE b →
      (∀ q : ℤ, a ≤ q → q ≤ b → P ((DerivedCategory.homologyFunctor C q).obj K)) →
      ∀ r : ℤ, b + e < r →
        IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj K)) from
    H (b - a).toNat K a b (by omega) inferInstance inferInstance hK r hr
  intro n
  induction n with
  | zero =>
    intro K a b hab _ _ hK r hr
    by_cases hlt : b < a
    · exact (DerivedCategory.homologyFunctor D r).map_isZero
        (F.map_isZero (DerivedCategory.TStructure.t.isZero K b a hlt))
    · have : K.IsGE b := DerivedCategory.TStructure.t.isGE_of_ge K b a (by omega)
      obtain ⟨Y, ⟨eY⟩⟩ :=
        DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K b
      have hY : P Y := hPiso
        ((DerivedCategory.homologyFunctor C b).mapIso eY ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C b).app Y)
        (hK b (by omega) le_rfl)
      apply (hF Y hY (r - b) (by omega)).of_iso
      exact (DerivedCategory.homologyFunctor D r).mapIso
        (F.mapIso eY ≪≫ F.mapIso
          (((DerivedCategory.singleFunctors C).shiftIso (-b) b 0 (by omega)).app Y).symm ≪≫
          (F.commShiftIso (-b)).app _) ≪≫
        ((DerivedCategory.homologyFunctor D 0).shiftIso (-b) r (r - b) (by omega)).app _
  | succ n ih =>
    intro K a b hab _ _ hK r hr
    by_cases hlt : b < a
    · exact (DerivedCategory.homologyFunctor D r).map_isZero
        (F.map_isZero (DerivedCategory.TStructure.t.isZero K b a hlt))
    have hab' : a ≤ b := by omega
    let t := DerivedCategory.TStructure.t (C := C)
    let T := (t.triangleLTGE b).obj K
    have hT := F.map_distinguished _ (t.triangleLTGE_distinguished b K)
    have h₁ : IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj T.obj₁)) := by
      refine ih T.obj₁ a (b - 1) (by omega) (inferInstanceAs
        (t.IsGE ((t.truncLT b).obj K) a))
        (t.isLE_truncLT_obj K b (b - 1) (by omega)) ?_ r (by omega)
      intro q hqa hqb
      have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K b q (by omega)
      exact hPiso
        (asIso ((DerivedCategory.homologyFunctor C q).map ((t.truncLTι b).app K))).symm
        (hK q hqa (by omega))
    have h₃ : IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj T.obj₃)) := by
      refine ih T.obj₃ b b (by omega) (inferInstanceAs
        (t.IsGE ((t.truncGE b).obj K) b)) (inferInstanceAs
        (t.IsLE ((t.truncGE b).obj K) b)) ?_ r hr
      intro q hqb hbq
      have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K b q hqb
      exact hPiso
        (asIso ((DerivedCategory.homologyFunctor C q).map ((t.truncGEπ b).app K)))
        (hK q (by omega) hbq)
    exact (DerivedCategory.HomologySequence.exact₂ _ hT r).isZero_of_both_zeros
      (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

/-- The canonical good-truncation map induces an isomorphism on degree-`m` total proper
pushforward, with the same window after every base change. The coefficient category is
ordinary, uncompleted, unbounded constant-ring modules; classicality concerns every
cohomology sheaf, without any boundedness assumption.

Source: blueprint main-20261015, sk-prop-ctf-finite-proper-localizing.proof.md,
"Etale statements" and "Transfer" (blueprint: lem-sfb-finite-proper-classical-truncation).

Proof:
1. Finite coefficient modules are torsion. The proper étale cohomological-dimension
   bound, together with the module/abelian-sheaf derived comparison, gives vanishing
   above `2e` on étale module sheaves placed in degree zero.
2. A classical fixed-coefficient pro-étale sheaf descends to the étale site. The
   bounded-below direct-image comparison transfers the bound to pro-étale sheaves.
   The canonical scalar realization preserves the underlying sheaf of sets (its
   sheafification unit is invertible), so its derived direct-image comparison transfers
   the same bound to the intrinsic constant-ring presentation in the statement.
3. Induction on the length of a finite cohomology interval, using the good-truncation
   triangles, gives the upper bound `b + 2e` for bounded classical complexes in degrees
   at most `b`. Exact countable products and left completeness extend this to the
   bound `b + 2e + 1` for complexes unbounded below: total direct image is a right
   adjoint and hence preserves the countable products in the truncation tower.
4. Apply this to `τ_{<N} J`, which is classical and lies in degrees at most `N - 1`.
   Its image vanishes in degrees `m` and `m + 1` by the asserted inequality. The
   cohomology sequence of the image of the canonical truncation triangle proves that
   the indicated map is invertible. Properness and the fibre bound hold for `f_S`,
   so the same argument works for every specified base change. -/
theorem finiteProper_classical_truncation
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (e : ℕ)
    (_hbound : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
      topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞))
    (S : Scheme.{u}) (g : S ⟶ Y)
    (J : Scheme.proEtaleDerivedCategory (pullback f g) A)
    (_hJ : IsClassicalModuleComplex J)
    (m N : ℤ) (_hN : N < m - 2 * (e : ℤ) - 1) :
    IsIso ((DerivedCategory.homologyFunctor _ m).map
      ((Scheme.proEtaleConstantDerivedDirectImage (pullback.snd f g) A).map
        ((CategoryTheory.Triangulated.TStructure.truncGEπ
          DerivedCategory.TStructure.t N).app J))) := by
  /- Transfer the proper torsion bound through the faithful module forgetful functor. -/
  have module_higher_bound
      (A : Type (u + 1)) [CommRing A] [Finite A]
      {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
      (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
      (H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (q : ℕ) (hq : 2 * e < q) :
      IsZero (((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerived q).obj H) := by
    clear * - A X Y f e hd H q hq
    let U := Etale.moduleAbelianForget A Y
    let B := Etale.moduleAbelianForget A X
    have hH : Scheme.IsTorsionAbelianSheaf (B.obj H) :=
      (Scheme.isTorsionAbelianSheaf_characterizations _).1.mpr
        ((Scheme.isTorsionModuleSheaf_iff_isTorsion H).mp inferInstance)
    have hz := Etale.isZero_higherDirectImage_of_isProper_of_fiber_dimension_le
      f e hd (B.obj H) hH q (by exact_mod_cast hq)
    let FAb := Etale.lowerStar AddCommGrpCat.{u + 1} f
    let j := FAb.homologyRightDerivedFunctorPlusObjSingleFunctorIso (B.obj H) q
    have hz' := hz.of_iso j.symm
    let c := (Functor.rightDerivedBaseChange
      (Etale.moduleAbelianLowerStarIso A f).hom q).app H
    have hc : IsIso c := (Etale.module_cohomology_conventions A Y).2.2.1 X f H q
    have hzero : IsZero (U.obj
        (((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerived q).obj H)) :=
      hz'.of_iso (asIso c)
    rw [IsZero.iff_id_eq_zero]
    apply U.map_injective
    rw [U.map_id, U.map_zero]
    exact (IsZero.iff_id_eq_zero _).mp hzero
  /- Descend a classical sheaf and use the bounded-below étale comparison. -/
  have fixed_heart_bound
      (A : Type (u + 1)) [CommRing A] [Finite A]
      {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
      (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
      (H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (hH : IsClassical ((sheafCompose (Scheme.ProEt.topology X)
        (forget (ModuleCat.{u + 1} A))).obj H))
      (q : ℤ) (hq : 2 * (e : ℤ) < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj H))) := by
    clear * - A X Y f e hd H hH q hq module_higher_bound
    obtain ⟨_, _, _, _, _, hc⟩ := proEtaleClassicalSheavesModules X A
    obtain ⟨G, ⟨i⟩⟩ := (hc H).mp hH
    let L := comparisonUpperStar (ModuleCat.{u + 1} A) X
    let M := comparisonUpperStar (ModuleCat.{u + 1} A) Y
    let R := (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
    let K := (DerivedCategory.singleFunctor _ 0).obj G
    have : IsIso (unboundedDirectImageComparisonMap A f K) :=
      unboundedDirectImageComparison_boundedBelow A f K 0
    have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj (R.obj K)) := by
      lift q to ℕ using (by omega)
      exact (module_higher_bound A f e hd G q (by exact_mod_cast hq)).of_iso
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).homologyRightDerivedFunctorObjSingleFunctorIso
          G q)
    have hz' := M.map_isZero hz
    apply hz'.of_iso
    exact (DerivedCategory.homologyFunctor _ q).mapIso
        (((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.mapIso
          ((L.mapDerivedCategorySingleFunctor 0).app G ≪≫
            (DerivedCategory.singleFunctor _ 0).mapIso i)).symm ≪≫
          (asIso (unboundedDirectImageComparisonMap A f K)).symm) ≪≫
      ((M.mapDerivedCategoryHomologyFunctorIso q).app (R.obj K)).symm
  have classical_of_iso {X : Scheme.{u}}
      {R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}}
      {H H' : SheafOfModules.{u + 1} R} (i : H ≅ H')
      (hH : IsClassicalModuleSheaf H) : IsClassicalModuleSheaf H' := by
    clear * - X R H H' i hH
    exact (isClassical_iso_iff
      ((SheafOfModules.toSheaf R ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).mapIso i)).mp hH
  /- The scalar realization has the same underlying set sheaf, by its sheafification unit. -/
  have realizationUnderlyingIso
      (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
      (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
      (sheafCompose (Scheme.ProEt.topology X)
        (forget (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).obj F ≅
      (sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).obj
        ((SheafOfModules.toSheaf _).obj ((Scheme.sfIntrinsicModuleEquivalence X A).functor.obj
          F)) := by
    clear * - X A F
    let P := (finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).obj F.obj
    let a := (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (finiteCoefficientIntrinsicScalarMap X A)).unit.app P
    have : IsIso a := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify (Scheme.ProEt.topology X) P.presheaf)
      exact isIso_toSheafify (Scheme.ProEt.topology X)
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            AddCommGrpCat.{u + 1})).obj F).property
    let i : (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj F ≅
        (SheafOfModules.toSheaf _).obj
          ((Scheme.sfIntrinsicModuleEquivalence X A).functor.obj F) :=
      (fullyFaithfulSheafToPresheaf _ _).preimageIso
        ((PresheafOfModules.toPresheaf _).mapIso (asIso a))
    exact (sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).mapIso i
  /- Carry the heart bound through the canonical coefficient realization. -/
  have intrinsic_heart_bound
      (A : Type u) [CommRing A] [Finite A]
      {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
      (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
      (M : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))
      (hM : IsClassicalModuleSheaf M) (q : ℤ) (hq : 2 * (e : ℤ) < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((Scheme.proEtaleConstantDerivedDirectImage f A).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) := by
    clear * - A X Y f e hd M hM q hq fixed_heart_bound classical_of_iso
      realizationUnderlyingIso
    let E := Scheme.sfIntrinsicModuleEquivalence X A
    let G := Scheme.sfIntrinsicModuleEquivalence Y A
    let H := E.inverse.obj M
    have hH : IsClassicalModuleSheaf (E.functor.obj H) :=
      classical_of_iso (E.counitIso.app M).symm hM
    have hc : IsClassical ((sheafCompose (Scheme.ProEt.topology X)
        (forget (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).obj H) :=
      (isClassical_iso_iff (realizationUnderlyingIso X A H)).mpr hH
    have hz := fixed_heart_bound (ULift.{u + 1, u} A) f e hd H hc q hq
    have hz' := G.functor.map_isZero hz
    apply hz'.of_iso
    let RF := Scheme.proEtaleConstantDerivedDirectImage f A
    let K := (DerivedCategory.singleFunctor _ 0).obj H
    exact (DerivedCategory.homologyFunctor _ q).mapIso
        (RF.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
            (E.counitIso.app M)).symm ≪≫
          RF.mapIso ((E.functor.mapDerivedCategorySingleFunctor 0).app H).symm ≪≫
          (Scheme.sfIntrinsicDerivedDirectImageComparison f A).app K) ≪≫
      ((G.functor.mapDerivedCategoryHomologyFunctorIso q).app
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor.obj K)).symm
  let Z := pullback f g
  let p := pullback.snd f g
  let C := Scheme.proEtaleRingModules Z (Scheme.proEtaleConstantRing Z A)
  let D := Scheme.proEtaleRingModules S (Scheme.proEtaleConstantRing S A)
  let F := Scheme.proEtaleConstantDerivedDirectImage p A
  have : IsProper p := inferInstance
  have hd : ∀ s : S, topologicalKrullDim (p.fiber s) ≤ (e : WithBot ℕ∞) :=
    _hbound S g
  have : HasExactLimitsOfShape (Discrete ℕ) C :=
    Scheme.ProEt.products_exact.{u, 0, 0} Z _ ℕ
  have : HasExactLimitsOfShape (Discrete ℕ) D :=
    Scheme.ProEt.products_exact.{u, 0, 0} S _ ℕ
  have : PreservesLimitsOfShape (Discrete ℕ) F := by
    have := (Scheme.sfIntrinsicConstantModuleAdjunction p A)
      |>.mapDerivedCategoryRightDerivedAdjunction |>.rightAdjoint_preservesLimits
    infer_instance
  have htail (L : DerivedCategory C) (b : ℤ) [L.IsLE b]
      (hc : ∀ q : ℤ, q ≤ b → IsClassicalModuleSheaf
        ((DerivedCategory.homologyFunctor C q).obj L)) :
      (F.obj L).IsLE (b + 2 * (e : ℤ) + 1) := by
    apply DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE F L (b + 2 * (e : ℤ))
    intro n
    let K := (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj L
    have : K.IsGE (-(n : ℤ)) := inferInstance
    have : K.IsLE b := inferInstance
    rw [DerivedCategory.isLE_iff]
    intro r hr
    refine finite_range_upper_bound F (fun H : C ↦ IsClassicalModuleSheaf H)
      (fun i h ↦ classical_of_iso i h) (2 * (e : ℤ))
      (fun H hH q hq ↦ intrinsic_heart_bound A p e hd H hH q hq)
      K (-(n : ℤ)) b ?_ r hr
    intro q hnq hqb
    have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app L (-(n : ℤ)) q hnq
    exact @classical_of_iso Z _ _ _
      (asIso ((DerivedCategory.homologyFunctor C q).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app L))) (hc q hqb)
  let t := DerivedCategory.TStructure.t (C := C)
  let L := (t.truncLT N).obj J
  have : L.IsLE (N - 1) := t.isLE_truncLT_obj J N (N - 1) (by omega)
  have hc : ∀ q : ℤ, q ≤ N - 1 → IsClassicalModuleSheaf
      ((DerivedCategory.homologyFunctor C q).obj L) := by
    intro q hq
    have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app J N q (by omega)
    exact @classical_of_iso Z _ _ _
      (asIso ((DerivedCategory.homologyFunctor C q).map ((t.truncLTι N).app J))).symm
      (_hJ q)
  have hL : (F.obj L).IsLE (N - 1 + 2 * (e : ℤ) + 1) := htail L (N - 1) hc
  have hT := F.map_distinguished _ (t.triangleLTGE_distinguished N J)
  exact DerivedCategory.isIso_homologyMap_mor₂ _ hT m (m + 1) rfl
    (DerivedCategory.isZero_of_isLE _ (N - 1 + 2 * (e : ℤ) + 1) m (by omega) (hX := hL))
    (DerivedCategory.isZero_of_isLE _ (N - 1 + 2 * (e : ℤ) + 1) (m + 1)
      (by omega) (hX := hL))
end AlgebraicGeometry.ProEtale
