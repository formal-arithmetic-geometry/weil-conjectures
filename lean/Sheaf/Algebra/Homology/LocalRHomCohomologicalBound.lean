/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Sheaf.Algebra.Homology.LocalRHomDefinitions
import Sheaf.Algebra.Homology.LocalRHomSectionActions
import Sheaf.Algebra.Homology.LocalRHomTargetShiftComparison
import Sheaf.Algebra.Homology.LocalRHomCycleUnitNormalization

/-! # Local derived Hom and the lower cohomological bound

Source: Stacks Project, Tags 0A94, 0A95 and 0149.
(blueprint: lem-per-rhom-local-cohomological-bound).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe uC vC u w wSlice
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory.LocalRHom

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max uC vC u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  (R : Sheaf J CommRingCat.{max uC vC u})
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))]

private theorem bound_of_local_comparison
    (K : D.{uC, vC, u, w} J R)
    (P : ℤ → D.{uC, vC, u, w} J R ⥤
      PresheafOfModules.{max uC vC u} (rings.{uC, vC, u} J R).obj)
    (e : ∀ (n : ℤ) (M : D.{uC, vC, u, w} J R) (U : C),
      ((P n).obj M).obj (op U) ≃+
        ((res.{uC, vC, u, w, wSlice} J R U).obj K ⟶
          (res.{uC, vC, u, w, wSlice} J R U).obj (M⟦n⟧)))
    (σ : ∀ n : ℤ, P n ⋙ sh.{uC, vC, u} J R ≅ T.{uC, vC, u, w} J R K n)
    (r b n : ℤ) (M : D.{uC, vC, u, w} J R)
    (hK : K.IsLE r) (hM : M.IsGE b) (hn : n < b - r) :
    IsZero ((T.{uC, vC, u, w} J R K n).obj M) := by
  have hp : IsZero ((P n).obj M) := by
    rw [IsZero.iff_id_eq_zero]
    ext U x
    apply (e n M U.unop).injective
    have := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u}
      (rings.{uC, vC, u} J R) U.unop).1
    have := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u}
      (rings.{uC, vC, u} J R) U.unop).2
    have := hK
    have := hM
    have : (M⟦n⟧).IsGE (b - n) :=
      DerivedCategory.TStructure.t.isGE_shift M b n (b - n) (by omega)
    have : ((res.{uC, vC, u, w, wSlice} J R U.unop).obj K).IsLE r :=
      Functor.isLE_mapDerivedCategory_obj _ K r
    have : ((res.{uC, vC, u, w, wSlice} J R U.unop).obj (M⟦n⟧)).IsGE (b - n) :=
      Functor.isGE_mapDerivedCategory_obj _ (M⟦n⟧) (b - n)
    exact (DerivedCategory.TStructure.t.zero _ r (b - n) (by omega)).trans
      (DerivedCategory.TStructure.t.zero _ r (b - n) (by omega)).symm
  exact ((sh.{uC, vC, u} J R).map_isZero hp).of_iso ((σ n).app M).symm

/-- Local RHom comparison with all its normalizations and the lower cohomological bound.
Source: Stacks 0A94, 0A95, 03EI and 0149
(blueprint: lem-per-rhom-local-cohomological-bound).

Proof:
1. Represent K by the specified complex L. Resolve target complexes functorially
by K-injectives and take the sectionwise cohomology presheaf of Hom(L,I).
Quasi-isomorphism invariance descends this construction to the derived category.
The additive cocycle comparison identifies its sections with local derived Hom.
The component formulas give the compatibility with maps, scalars and restriction.
2. Exact module sheafification commutes with cohomology. The fixed internal-Hom
localization factorization gives the natural sheafification comparison. Its
normalization at arbitrary K-injective representatives is the cycle quotient and
sheafification-unit equation; the representative isomorphism is normalized by
its actual augmentation map. A sheaf cycle restricts to a local chain map whose
components are precisely the Hom-product projections.
3. The normalized triangulated internal-Hom functor and cohomology give a coherent
shift sequence and a homological functor. The presheaf target-shift comparison
has the corresponding sectionwise and sheafification formulas. Compose that
comparison with the third arrow of a triangle to construct its boundary. The
naturality of the two comparison isomorphisms identifies its sheafification
with the prescribed boundary of the shift sequence.
4. Exact slice restriction preserves both cohomological bounds. For n < b-r the
restricted K lies in D^{≤r} and M[n] in D^{≥b-n}, where r < b-n. T-structure
orthogonality makes each local Hom group zero, hence the presheaf and its
sheafification are zero. Neither Tor amplitude nor site dimension is used. -/
theorem local_cohomological_bound (K : D.{uC, vC, u, w} J R) :
    ∃ (P : ℤ → D.{uC, vC, u, w} J R ⥤ PresheafOfModules.{max uC vC u} (rings.{uC, vC, u} J R).obj)
      (e : ∀ (n : ℤ) (M : D.{uC, vC, u, w} J R) (U : C),
        ((P n).obj M).obj (op U) ≃+
          ((res.{uC, vC, u, w, wSlice} J R U).obj K ⟶ (res.{uC, vC, u, w, wSlice} J R U).obj
            (M⟦n⟧)))
      (σ : ∀ n : ℤ, P n ⋙ sh.{uC, vC, u} J R ≅ T.{uC, vC, u, w} J R K n)
      (S : (T.{uC, vC, u, w} J R K 0).ShiftSequence ℤ)
      (τ : ∀ n : ℤ, S.sequence n ≅ T.{uC, vC, u, w} J R K n),
      τ 0 = S.isoZero ∧
      (∀ n : ℤ, (T.{uC, vC, u, w} J R K n).Additive) ∧
      (T.{uC, vC, u, w} J R K 0).IsHomological ∧
      (∀ (n : ℤ) (M N : D.{uC, vC, u, w} J R) (v : M ⟶ N) (U : C)
        (x : ((P n).obj M).obj (op U)),
        e n N U (((P n).map v).app (op U) x) =
          e n M U x ≫ (res.{uC, vC, u, w, wSlice} J R U).map (v⟦n⟧')) ∧
      (∀ (n : ℤ) (M : D.{uC, vC, u, w} J R) (U : C) (a : R.obj.obj (op U))
        (x : ((P n).obj M).obj (op U)),
        e n M U (a • x) = e n M U x ≫
          (sectionDerivedMultiplication.{uC, vC, u, w, wSlice} J R U a).app (M⟦n⟧)) ∧
      (∀ (n : ℤ) (M : D.{uC, vC, u, w} J R) (U V : C) (f : V ⟶ U)
        (x : ((P n).obj M).obj (op U)),
        e n M V (((P n).obj M).map f.op x) = restrictHom.{uC, vC, u, w, wSlice} J R f (e n M U x)) ∧
      (∀ (A : Triangle (D.{uC, vC, u, w} J R)), A ∈ distTriang (D.{uC, vC, u, w} J R) →
        ∀ n : ℤ, ∃ d : (P n).obj A.obj₃ ⟶ (P (n + 1)).obj A.obj₁,
          (∀ (U : C) (x : ((P n).obj A.obj₃).obj (op U)),
            e (n + 1) A.obj₁ U (d.app (op U) x) =
              e n A.obj₃ U x ≫ (res.{uC, vC, u, w, wSlice} J R U).map (A.mor₃⟦n⟧') ≫
                (res.{uC, vC, u, w, wSlice} J R U).map ((shiftFunctorAdd' (D.{uC, vC, u, w} J R) 1 n
                  (n + 1)
                  (add_comm 1 n)).inv.app A.obj₁)) ∧
          (sh.{uC, vC, u} J R).map d ≫ (σ (n + 1)).hom.app A.obj₁ =
            (σ n).hom.app A.obj₃ ≫
              boundary.{uC, vC, u, w} J R K S τ A n) ∧
      (∀ (L I : CochainComplex (Mod.{uC, vC, u} J R) ℤ) [I.IsKInjective]
        (k : DerivedCategory.Q.obj L ≅ K),
        ∃ h : (RH.{uC, vC, u, w} J R (DerivedCategory.Q.obj L)).obj (DerivedCategory.Q.obj I) ≅
            DerivedCategory.Q.obj (homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) L I),
          h.hom ≫ DerivedCategory.Q.map (homAugmentation.{uC, vC, u} J R L I) =
            (WeilConjectures.coefficientHomResolutionIso.{u, uC, vC, w} J R L I).hom ∧
          ∀ (n : ℤ) (U : C)
            (z : ((homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) L I).cycles n).val.obj (op
              U)),
            ∃ a : (complexRes.{uC, vC, u} J R U).obj L ⟶ (complexRes.{uC, vC, u} J R U).obj (I⟦n⟧),
              (∀ (p : ℤ) (W : (Over U)ᵒᵖ),
                ((a.f p).val.app W) =
                  (((homComplexπ.{uC, vC, max uC vC u, max uC vC u} (R := R) L I n p (p + n)
                    rfl).val.app (op U))
                    (((homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) L I).iCycles
                      n).val.app (op U) z)).app W) ∧
              ((σ n).inv.app (DerivedCategory.Q.obj I)).val.app (op U)
                (((DerivedCategory.homologyFunctor (Mod.{uC, vC, u} J R) n).map
                  ((derivedInternalHomOfUniverses.{uC, vC, u, w} J R).map
                    (Prod.mkHom k.inv.op (𝟙 (DerivedCategory.Q.obj I))))).val.app (op U)
                    (cycleClass.{uC, vC, u, w} J R L I h n U z)) =
                ((PresheafOfModules.sheafificationAdjunction.{max uC vC u}
                  (𝟙 (rings.{uC, vC, u} J R).obj)).unit.app
                    ((P n).obj (DerivedCategory.Q.obj I))).app (op U)
                      ((e n (DerivedCategory.Q.obj I) U).symm
                        ((res.{uC, vC, u, w, wSlice} J R U).map k.inv ≫ localizedCocycle.{uC, vC, u,
                          w, wSlice} J R L I n U a))) ∧
      (∀ (r b n : ℤ) (M : D.{uC, vC, u, w} J R), K.IsLE r → M.IsGE b → n < b - r →
        IsZero ((T.{uC, vC, u, w} J R K n).obj M)) := by
  let L := (DerivedCategory.Q (C := Mod.{uC, vC, u} J R)).objPreimage K
  let k : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let P := Model.presheaf.{uC, vC, u, w} J R L
  let e := Sections.sectionEquiv.{uC, vC, u, w, wSlice} J R K L k
  let σ := Model.sheafificationIsoOfRepresentative.{uC, vC, u, w} J R K L k
  let S := Shifts.sequence.{uC, vC, u, w} J R K
  let τ := Shifts.comparison.{uC, vC, u, w} J R K
  obtain ⟨hnat, hsmul, hres⟩ := section_actions.{uC, vC, u, w, wSlice} J R K L k
  obtain ⟨ρ, hρe, hρσ⟩ := target_shift_comparison.{uC, vC, u, w, wSlice} J R K L k
  obtain ⟨hzero, hadd, hhom⟩ := Shifts.properties.{uC, vC, u, w} J R K
  refine ⟨P, e, σ, S, τ, hzero, hadd, hhom, hnat, hsmul, hres, ?_, ?_, ?_⟩
  · intro A _hA n
    let d : (P n).obj A.obj₃ ⟶ (P (n + 1)).obj A.obj₁ :=
      (P n).map A.mor₃ ≫ (ρ 1 n).hom.app A.obj₁
    refine ⟨d, ?_, ?_⟩
    · intro U x
      change e (n + 1) A.obj₁ U
        (((ρ 1 n).hom.app A.obj₁).app (op U) (((P n).map A.mor₃).app (op U) x)) = _
      rw [hρe, hnat]
      simp only [Category.assoc]
      rfl
    · change (sh.{uC, vC, u} J R).map
          ((P n).map A.mor₃ ≫ (ρ 1 n).hom.app A.obj₁) ≫ _ = _
      rw [Functor.map_comp, Category.assoc, hρσ]
      change (sh.{uC, vC, u} J R).map ((P n).map A.mor₃) ≫
        (σ n).hom.app (A.obj₁⟦(1 : ℤ)⟧) ≫ (τ n).inv.app (A.obj₁⟦(1 : ℤ)⟧) ≫
          (S.shiftIso 1 n (n + 1) (add_comm 1 n)).hom.app A.obj₁ ≫
            (τ (n + 1)).hom.app A.obj₁ = _
      have hσ := (σ n).hom.naturality A.mor₃
      dsimp only [Functor.comp_map] at hσ
      erw [reassoc_of% hσ]
      have hτ := (τ n).inv.naturality A.mor₃
      erw [reassoc_of% hτ]
      rfl
  · intro L' I _ k'
    refine ⟨Model.kInjectiveRepresentativeIso.{uC, vC, u, w} J R L' I,
      Model.kInjectiveRepresentativeIso_normalization.{uC, vC, u, w} J R L' I, ?_⟩
    intro n U z
    refine ⟨Cocycle.sheafCycleMap.{uC, vC, u, wSlice} J R L' I U n z,
      Cocycle.sheafCycleMap_component.{uC, vC, u, wSlice} J R L' I U n z, ?_⟩
    exact cycle_unit_normalization.{uC, vC, u, w, wSlice} J R K L k L' I k' n U z
  · intro r b n M hK hM hn
    exact bound_of_local_comparison.{uC, vC, u, w, wSlice} J R K P e σ r b n M hK hM hn

end CategoryTheory.LocalRHom
