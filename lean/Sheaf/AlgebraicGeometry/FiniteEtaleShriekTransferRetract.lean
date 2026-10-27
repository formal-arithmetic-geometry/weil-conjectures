/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleUnitStalkInclusion
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import Mathlib.Data.Int.GCD
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition

/-!
# Finite etale transfer retraction for derived compact supports

Source: Stacks Project, More on Etale Cohomology, Tag 0GKY,
`lemma-loc-constant-shriek-rel-dim-1`, trace-splitting and composition paragraph
(blueprint: lem-weil-pbc-finite-etale-shriek-transfer-retract).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem primary_unit_split
    {C : Type*} [Category C] [Preadditive C] {F H : C}
    (η : F ⟶ H) (t : H ⟶ F) (d q : ℕ)
    (ht : η ≫ t = d • 𝟙 F) (hk : q • 𝟙 F = 0) (hc : Nat.Coprime d q) :
    η ≫ (Nat.gcdA d q • t) = 𝟙 F := by
  rw [Preadditive.comp_zsmul, ht]
  have hab : (1 : ℤ) = Nat.gcdA d q * (d : ℤ) + Nat.gcdB d q * (q : ℤ) := by
    simpa only [hc.gcd_eq_one, Int.natCast_one, mul_comm] using Nat.gcd_eq_gcd_ab d q
  have hi := congrArg (fun z : ℤ ↦ z • 𝟙 F) hab
  simp only [one_smul, add_smul, mul_smul, natCast_zsmul, hk, smul_zero, add_zero] at hi
  exact hi.symm

private theorem unit_stalk_component
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (t : f.GeometricFiber s) :
    (Scheme.pointSmallEtale s).sheafFiber.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G) ≫
      stalkRestrict (ModuleCat.{u + 1} R) f s t ((f)^*[ModuleCat.{u + 1} R].obj G) =
    eqToHom (by rw [t.2]; rfl) ≫
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t.1).app G).inv := by
  obtain ⟨t, rfl⟩ := t
  simp only [eqToHom_refl, Category.id_comp]
  erw [stalkRestrict_eq_counit]
  have hn := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t).inv.naturality
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G)
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  erw [Adjunction.left_triangle_components]
  simp

private theorem trace_stalk_component
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (t : f.GeometricFiber s) :
    sheafFiberToLowerStar (ModuleCat.{u + 1} R) f t ((f)^*[ModuleCat.{u + 1} R].obj G) ≫
      (Scheme.pointSmallEtale s).sheafFiber.map
        ((lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} R) f).counit.app G) =
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t.1).app G).hom ≫
      eqToHom (by rw [t.2]; rfl) := by
  obtain ⟨t, rfl⟩ := t
  erw [← finiteEtaleUnit_stalk_inclusion R f
    ((f)^*[ModuleCat.{u + 1} R].obj G) (t ≫ f) ⟨t, rfl⟩]
  simp only [eqToHom_refl, Category.comp_id]
  have hn := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t).hom.naturality
    ((lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} R) f).counit.app G)
  dsimp only [Functor.comp_map] at hn
  erw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp,
    Adjunction.right_triangle_components]
  simp

private theorem exists_trace_algClosed
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (d : ℕ)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nat.card (f.GeometricFiber s) = d) :
    (∃ t : (f)_*[ModuleCat.{u + 1} R].obj ((f)^*[ModuleCat.{u + 1} R].obj G) ⟶ G,
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G ≫ t =
        (d : R) • 𝟙 G) := by
  classical
  let A := ModuleCat.{u + 1} R
  let H := (f)^*[A].obj G
  let η := (upperStarLowerStarAdjunction A f).unit.app G
  let tr := (lowerStarUpperStarAdjunctionOfIsFinite A f).counit.app G
  refine ⟨tr, ?_⟩
  apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  let s := X.algClosurePoint x
  let Φ := (Scheme.pointSmallEtale s).sheafFiber (A := A)
  let : Fintype (f.GeometricFiber s) := Fintype.ofFinite _
  let ρ := fun t : f.GeometricFiber s ↦ stalkRestrict A f s t H
  let j := fun t : f.GeometricFiber s ↦ sheafFiberToLowerStar A f t H
  have htotal : ∑ t, ρ t ≫ j t = 𝟙 (Φ.obj ((f)_*[A].obj H)) := by
    apply (cancel_mono (Limits.Pi.lift ρ)).mp
    apply Limits.Pi.hom_ext
    intro t
    simp only [Category.assoc, Limits.Pi.lift_π]
    erw [Preadditive.sum_comp, Category.id_comp]
    simp only [Category.assoc]
    change ∑ a, ρ a ≫ (j a ≫ ρ t) = ρ t
    erw [Finset.sum_eq_single t]
    · simp [ρ, j]
    · intro a ha hat
      erw [sheafFiberToLowerStar_stalkRestrict_of_ne A f hat H, Limits.comp_zero]
    · intro ht
      exact (ht (Finset.mem_univ t)).elim
  simp only [CategoryTheory.Functor.map_comp,
    GrothendieckTopology.Point.sheafFiber_map_smul]
  change Φ.map η ≫ Φ.map tr = (d : R) • Φ.map (𝟙 G)
  erw [Φ.map_id]
  calc
    Φ.map η ≫ Φ.map tr = Φ.map η ≫ (∑ t, ρ t ≫ j t) ≫ Φ.map tr := by
      erw [htotal, Category.id_comp]
    _ = ∑ t, (Φ.map η ≫ ρ t) ≫ (j t ≫ Φ.map tr) := by
      erw [Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [Category.assoc]
    _ = ∑ _t : f.GeometricFiber s, 𝟙 (Φ.obj G) := by
      apply Finset.sum_congr rfl
      intro t ht
      erw [unit_stalk_component R f G s t, trace_stalk_component R f G s t]
      simp
    _ = (d : R) • 𝟙 _ := by
      erw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        hdeg _ s, ← Nat.cast_smul_eq_nsmul R]


/-- Primary-torsion compact supports are a retract of compact supports after a finite etale
cover of constant degree prime to the torsion prime, with the forward map induced by the
adjunction unit and the compact-support comparison. The two compactifications are arbitrary.
Neither invertibility of the degree in the coefficient ring, local constancy of the sheaf,
nor connectedness is required.

Source: Stacks Project, More on Etale Cohomology, Tag 0GKY,
`lemma-loc-constant-shriek-rel-dim-1`; Etale Cohomology, Section 03SH and Definition 03SE;
Tag 0F7J for composition
(blueprint: lem-weil-pbc-finite-etale-shriek-transfer-retract).

Proof plan, following the node's six steps:
1. Put E = g^{-1}F and H = g_*E. Apply
   `lem-weil-pbc-finite-etale-module-trace-degree` to obtain a coefficient-linear trace
   t : H -> F with eta followed by t equal to d times the identity. For finite etale g,
   geometric fibres over separably closed fields and their algebraic closures have the same
   cardinality: each finite etale fibre is a disjoint union of rational points.
2. Bezout gives integers a,b with ad + b ell^n = 1. Set rho = a t; the annihilation
   hypothesis implies eta followed by rho is the identity, even if d is a nonunit in Lambda.
3. Finite direct image is exact on abelian sheaves by
   `lemma-weil-pbc-finite-direct-image-exact`. The faithful exact forgetful functor of
   `lem-weil-pbc-module-sheaves-colimits-forgetful` and its compatibility with module direct
   image in `lem-weil-pbc-module-direct-image-left-exact` reflect this exactness on modules.
4. Finite g is proper (`lem-weil-pbc-finite-proper`), so use its identity compactification
   from `def-weil-pbc-projection-compactification`. Extension by zero along the identity is
   the identity. By `lem-weil-pbc-exact-functor-derived-functor`, exactness in step 3 gives
   an isomorphism beta : H[0] -> Rg_! E[0].
5. Apply `lem-weil-pbc-etale-shriek-qcqs-composition` to the identity compactification of g
   and the two prescribed compactifications. Its comparison C, composed with Rh_!(beta),
   gives alpha : Rh_!(H[0]) -> R(hg)_!(E[0]).
6. Define u = Rh_!(eta[0]) followed by alpha, and v = alpha inverse followed by
   Rh_!(rho[0]). Functoriality and rho eta = 1 give u followed by v equal to the identity,
   and the definition of u is exactly the asserted unit formula. -/
theorem exists_finiteEtale_shriek_transfer_retract
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T X Y : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (h : X ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (g : T ⟶ X) [IsFinite g] [Etale g]
    (ch : Compactification h) (chg : Compactification (g ≫ h))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (ell n d : ℕ) (hell : ell.Prime) (hn : 1 ≤ n)
    (hkill : ell ^ n • 𝟙 F = 0) (hd : 1 ≤ d) (hprime : ¬ ell ∣ d)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nat.card (g.GeometricFiber s) = d) :
    ∃ α :
      (Rf_!(ch)[ModuleCat.{u + 1} Λ]+).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((lowerStar (ModuleCat.{u + 1} Λ) g).obj
              ((upperStar (ModuleCat.{u + 1} Λ) g).obj F))) ≅
        (Rf_!(chg)[ModuleCat.{u + 1} Λ]+).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar (ModuleCat.{u + 1} Λ) g).obj F)),
      ∃ (u : (Rf_!(ch)[ModuleCat.{u + 1} Λ]+).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) ⟶
          (Rf_!(chg)[ModuleCat.{u + 1} Λ]+).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
              ((upperStar (ModuleCat.{u + 1} Λ) g).obj F)))
        (v : (Rf_!(chg)[ModuleCat.{u + 1} Λ]+).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
              ((upperStar (ModuleCat.{u + 1} Λ) g).obj F)) ⟶
          (Rf_!(ch)[ModuleCat.{u + 1} Λ]+).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)),
        u ≫ v = 𝟙 _ ∧
          u = (Rf_!(ch)[ModuleCat.{u + 1} Λ]+).map
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).map
              ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F)) ≫ α.hom := by
  classical
  have _hn := hn
  have _hd := hd
  let A := ModuleCat.{u + 1} Λ
  let E := (upperStar A g).obj F
  let H := (lowerStar A g).obj E
  let S := _root_.DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology A) 0
  let B := Rf_!(ch)[A]+
  let η := (upperStarLowerStarAdjunction A g).unit.app F
  obtain ⟨t, ht⟩ := exists_trace_algClosed Λ g F d hdeg
  have hc : Nat.Coprime d (ell ^ n) :=
    (hell.coprime_iff_not_dvd.mpr hprime).symm.pow_right n
  let ρ : H ⟶ F := Nat.gcdA d (ell ^ n) • t
  have ht' : η ≫ t = d • 𝟙 F := by
    simpa only [Nat.cast_smul_eq_nsmul] using ht
  have hsplit : η ≫ ρ = 𝟙 F := primary_unit_split η t d (ell ^ n) ht' hkill hc
  let cg : Compactification g :=
    { Z := T
      i := 𝟙 T
      g := g
      comm := Category.id_comp g
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let ei : openImmersionLowerShriek A (𝟙 T) ≅
      𝟭 (Sheaf T.smallEtaleTopology A) :=
    (upperStarIsoOpenImmersionLowerShriekInv A (Iso.refl T)).symm ≪≫ upperStarId A T
  let eDi := Functor.mapDerivedCategoryPlusNatIso ei ≪≫
    Functor.mapDerivedCategoryPlusIdIso (Sheaf T.smallEtaleTopology A)
  let eg : Rf_!(cg)[A]+ ≅ (lowerStar A g).rightDerivedFunctorPlus :=
    Functor.isoWhiskerRight eDi _ ≪≫ Functor.leftUnitor _
  let β := ((lowerStar A g).mapDerivedCategoryPlusSingleFunctor 0).symm.app E ≪≫
    ((lowerStar A g).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj E)).symm ≪≫
    eg.symm.app ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj E)
  obtain ⟨C⟩ := nonempty_iso_etaleShriek_qcqs_compactification_comp Λ g h cg ch chg
  let α := B.mapIso β ≪≫ C.app ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj E)
  refine ⟨α, B.map (S.map η) ≫ α.hom, α.inv ≫ B.map (S.map ρ), ?_, rfl⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hsplit]
  exact (congrArg B.map (S.map_id F)).trans (B.map_id _)

end AlgebraicGeometry.Etale
