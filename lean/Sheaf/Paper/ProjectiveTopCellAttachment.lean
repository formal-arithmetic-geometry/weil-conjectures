/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Attaching the top term of a projective complex

Source: Stacks Project, Tag 09C3, final paragraph of
`proetale.tex`, `lemma-local-structure-constructible-complex`; Tag 064B of
`derived.tex`, `lemma-morphisms-from-projective-complex`.
(blueprint: lem-sf-projective-top-cell-attachment).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CochainComplex

/-- A connecting morphism with bounded projective source is represented by a chain map;
its shifted cone attaches the top term with differential minus that component.

Source: Stacks Project, Tag 09C3, final paragraph, and Tags 064B, 014E, 0145, 014A,
014Q of `derived.tex` (blueprint: lem-sf-projective-top-cell-attachment).

Proof plan:
1. The module-sheaf category is abelian. The complex K is bounded above with projective
terms, so Tag 064B (`CochainComplex.IsKProjective.Qh_map_bijective`, using
`CochainComplex.isKProjective_of_projective`) represents delta by a chain map g.
Choose an actual chain-map representative of its homotopy class.
2. The target single complex vanishes away from b-1. Hence all other components vanish,
and the chain-map equation at b-2 gives K.d (b-2) (b-1) followed by g^(b-1) equal to zero.
3. Rotate the given distinguished triangle twice. Its first map is delta. Compare with
Q of the cone triangle of g, using the canonical single-complex shift identification.
TR3 extends the identity on the first two objects to a triangle morphism. By
`CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂` its third component is invertible.
Shift back, using Q's shift comparison, to obtain Q(Cone(g)[-1]) isomorphic to M.
4. The canonical projections identify the shifted cone in degree q with
K^q plus T^(q-1). The shifted differential is (d_K x, -g x - d_T y).
Consequently the projections give the stated identifications below b and at b,
the support [a,b], the unchanged lower differentials, and last differential -g^(b-1).
Conjugate by the identity below b and minus identity at b to obtain the attached complex
with last differential +g^(b-1).
5. Each term is isomorphic to a term of K, P, or zero. Thus finite freeness is preserved,
with the empty coproduct for zero. This includes P=0, K=0, and b=a+1 and imposes no
constancy condition on the entries of g. -/
theorem projective_top_cell_attachment
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u}) [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
    (a b : ℤ) (hab : a < b) (P : ringedSiteModules.{u} R)
    (M : DerivedCategory (ringedSiteModules.{u} R))
    (K : CochainComplex (ringedSiteModules.{u} R) ℤ)
    (hsupp : ∀ q : ℤ, q < a ∨ b - 1 < q → IsZero (K.X q))
    (hproj : ∀ q : ℤ, Projective (K.X q))
    (v₁ : DerivedCategory.Q.obj ((singleFunctor (ringedSiteModules.{u} R) b).obj P) ⟶ M)
    (v₂ : M ⟶ DerivedCategory.Q.obj K)
    (δ : DerivedCategory.Q.obj K ⟶
      (DerivedCategory.Q.obj ((singleFunctor (ringedSiteModules.{u} R) b).obj P))⟦1⟧)
    (htri : Triangle.mk v₁ v₂ δ ∈ distTriang (DerivedCategory (ringedSiteModules.{u} R))) :
    ∃ (g : K ⟶ (singleFunctor (ringedSiteModules.{u} R) (b - 1)).obj P),
      DerivedCategory.Q.map g ≫
          (((singleFunctors (ringedSiteModules.{u} R)).postcomp DerivedCategory.Q).shiftIso
            1 (b - 1) b (by omega)).inv.app P = δ ∧
      (∀ q : ℤ, q ≠ b - 1 → g.f q = 0) ∧
      K.d (b - 2) (b - 1) ≫ g.f (b - 1) = 0 ∧
      ∃ (D : CochainComplex (ringedSiteModules.{u} R) ℤ)
        (hD : D = (mappingCone g)⟦(-1 : ℤ)⟧),
        Nonempty (DerivedCategory.Q.obj D ≅ M) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero (D.X q)) ∧
        ∃ (eLow : ∀ (q : ℤ), q < b → (D.X q ≅ K.X q)) (eTop : D.X b ≅ P),
          (∀ (q : ℤ) (hq : q < b),
            (eLow q hq).hom =
              (HomologicalComplex.eval _ _ q).map (eqToHom hD) ≫
                (shiftFunctorObjXIso (mappingCone g) (-1) q (q - 1) rfl).hom ≫
                  (mappingCone.fst g).1.v (q - 1) q (by omega)) ∧
          (eTop.hom =
            (HomologicalComplex.eval _ _ b).map (eqToHom hD) ≫
              (shiftFunctorObjXIso (mappingCone g) (-1) b (b - 1) rfl).hom ≫
                (mappingCone.snd g).v (b - 1) (b - 1) (add_zero _) ≫
                  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (b - 1) P).hom) ∧
          (∀ (q : ℤ) (hq : q + 1 < b),
            D.d q (q + 1) ≫ (eLow (q + 1) hq).hom =
              (eLow q (by omega)).hom ≫ K.d q (q + 1)) ∧
          ((eLow (b - 1) (by omega)).inv ≫ D.d (b - 1) b ≫ eTop.hom =
            -(g.f (b - 1) ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (b - 1) P).hom)) ∧
          (((∃ n : ℕ, Nonempty (P ≅ SheafOfModules.free (R := R) (ULift.{u} (Fin n)))) ∧
            (∀ q : ℤ, ∃ n : ℕ,
              Nonempty (K.X q ≅ SheafOfModules.free (R := R) (ULift.{u} (Fin n))))) →
            ∀ q : ℤ, ∃ n : ℕ,
              Nonempty (D.X q ≅ SheafOfModules.free (R := R) (ULift.{u} (Fin n)))) ∧
          ∃ (Dplus : CochainComplex (ringedSiteModules.{u} R) ℤ) (e : D ≅ Dplus)
            (ePlusLow : ∀ (q : ℤ), q < b → (Dplus.X q ≅ K.X q))
            (ePlusTop : Dplus.X b ≅ P),
            (∀ (q : ℤ) (hq : q < b),
              e.hom.f q ≫ (ePlusLow q hq).hom = (eLow q hq).hom) ∧
            (e.hom.f b ≫ ePlusTop.hom = -eTop.hom) ∧
            (∀ (q : ℤ) (hq : q + 1 < b),
              Dplus.d q (q + 1) ≫ (ePlusLow (q + 1) hq).hom =
                (ePlusLow q (by omega)).hom ≫ K.d q (q + 1)) ∧
            ((ePlusLow (b - 1) (by omega)).inv ≫ Dplus.d (b - 1) b ≫ ePlusTop.hom =
              g.f (b - 1) ≫
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (b - 1) P).hom) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      set_option backward.defeqAttrib.useBackward true in
        let A := ringedSiteModules.{u} R
        let T := (singleFunctor A (b - 1)).obj P
        let s := (((singleFunctors A).postcomp DerivedCategory.Q).shiftIso
          1 (b - 1) b (by omega)).app P
        let : ∀ q : ℤ, Projective (K.X q) := hproj
        have : K.IsStrictlyLE (b - 1) :=
          (isStrictlyLE_iff _ _).2 (fun q hq ↦ hsupp q (Or.inr hq))
        have : K.IsKProjective := isKProjective_of_projective K (b - 1)
        obtain ⟨gh, hgh⟩ := (IsKProjective.Qh_map_bijective K
          ((HomotopyCategory.quotient A (.up ℤ)).obj T)).surjective
            ((DerivedCategory.quotientCompQhIso A).hom.app K ≫ δ ≫ s.hom ≫
              (DerivedCategory.quotientCompQhIso A).inv.app T)
        obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective gh
        have hg : DerivedCategory.Q.map g ≫ s.inv = δ := by
          have hh : DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map g) ≫
              (DerivedCategory.quotientCompQhIso A).hom.app T =
              (DerivedCategory.quotientCompQhIso A).hom.app K ≫ DerivedCategory.Q.map g :=
            DerivedCategory.quotientCompQhIso_hom_naturality g
          apply (cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app K)).mp
          rw [← Category.assoc, ← hh, hgh]
          simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id,
            Category.comp_id]
        have hgz (q : ℤ) (hq : q ≠ b - 1) : g.f q = 0 :=
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) (b - 1) P q hq).eq_of_tgt _ _
        refine ⟨g, hg, hgz, ?_, ?_⟩
        · rw [← g.comm]
          change g.f (b - 2) ≫ (0 : T.X (b - 2) ⟶ T.X (b - 1)) = 0
          simp
        · let D := (mappingCone g)⟦(-1 : ℤ)⟧
          have hDM : Nonempty (DerivedCategory.Q.obj D ≅ M) := by
            let Tc := DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle g)
            let Tr := (Triangle.mk v₁ v₂ δ).rotate.rotate
            let e := isoTriangleOfIso₁₂ Tc Tr (DerivedCategory.mappingCone_triangle_distinguished g)
              (rot_of_distTriang _ (rot_of_distTriang _ htri)) (Iso.refl _) s.symm (by
                change DerivedCategory.Q.map g ≫ s.inv = 𝟙 _ ≫ δ
                simpa only [Category.id_comp] using hg)
            exact ⟨(DerivedCategory.Q.commShiftIso (-1)).app (mappingCone g) ≪≫
              (CategoryTheory.shiftFunctor _ (-1)).mapIso (Triangle.π₃.mapIso e) ≪≫
              (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app M⟩
          refine ⟨D, rfl, hDM, ?_, ?_⟩
          · intro q hq
            apply (shiftFunctorObjXIso (mappingCone g) (-1) q (q - 1) rfl).isZero_iff.mpr
            apply (mappingCone.isZero_X_iff g (q - 1)).2
            constructor
            · convert hsupp q (by omega) using 1
              congr 1
              omega
            · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) (b - 1) P (q - 1)
                (by omega)
          · -- Away from the top degree, the second cone summand vanishes.
            let eAll (q : ℤ) (hq : q ≠ b) : D.X q ≅ K.X q :=
              shiftFunctorObjXIso (mappingCone g) (-1) q (q - 1) rfl ≪≫
                { hom := (mappingCone.fst g).1.v (q - 1) q (by omega)
                  inv := (mappingCone.inl g).v q (q - 1) (by omega)
                  hom_inv_id := by
                    apply mappingCone.ext_to g (q - 1) q (by omega)
                    · simp
                    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ)
                        (b - 1) P (q - 1) (by omega)).eq_of_tgt _ _
                  inv_hom_id := by simp }
            let eLow (q : ℤ) (_ : q < b) : D.X q ≅ K.X q := eAll q (by omega)
            let eTop : D.X b ≅ P :=
              shiftFunctorObjXIso (mappingCone g) (-1) b (b - 1) rfl ≪≫
                { hom := (mappingCone.snd g).v (b - 1) (b - 1) (add_zero _)
                  inv := (mappingCone.inr g).f (b - 1)
                  hom_inv_id := by
                    apply mappingCone.ext_to g (b - 1) b (by omega)
                    · exact (hsupp b (Or.inr (by omega))).eq_of_tgt _ _
                    · simp
                  inv_hom_id := by simp } ≪≫
                HomologicalComplex.singleObjXSelf (.up ℤ) (b - 1) P
            let π : D ⟶ K := HomComplex.Cocycle.homOf
              ((-mappingCone.fst g).leftShift (-1) 0 (by omega))
            have hπ (q : ℤ) (hq : q < b) : π.f q = (eLow q hq).hom := by
              change (((-mappingCone.fst g).1).leftShift (-1) 0 (by omega)).v q q
                (add_zero q) = _
              rw [HomComplex.Cochain.leftShift_v _ (-1) 0 (by omega) q q (add_zero q)
                (q - 1) (by omega)]
              simp only [Int.reduceNeg, shiftFunctor_obj_X', shiftFunctor_obj_X, mul_zero,
                Int.reduceSub, mul_neg, neg_mul, one_mul, neg_neg, ne_eq, OfNat.ofNat_ne_zero,
                not_false_eq_true, Int.ediv_self, zero_add, Int.negOnePow_one,
                shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
                HomComplex.Cocycle.coe_neg, HomComplex.Cochain.neg_v, Preadditive.comp_neg,
                Category.id_comp, smul_neg, Units.neg_smul, one_smul]
              exact (Category.id_comp _).symm
            have hlow (q : ℤ) (hq : q + 1 < b) :
                D.d q (q + 1) ≫ (eLow (q + 1) hq).hom =
                  (eLow q (by omega)).hom ≫ K.d q (q + 1) := by
              have hh := (π.comm q (q + 1)).symm
              rw [hπ q (by omega), hπ (q + 1) hq] at hh
              exact hh
            have hlast :
                (eLow (b - 1) (by omega)).inv ≫ D.d (b - 1) b ≫ eTop.hom =
                  -(g.f (b - 1) ≫
                    (HomologicalComplex.singleObjXSelf (.up ℤ) (b - 1) P).hom) := by
              change ((mappingCone.inl g).v (b - 1) (b - 1 - 1) (by omega) ≫ 𝟙 _) ≫
                ((-1 : ℤ).negOnePow • (mappingCone g).d (b - 1 - 1) (b - 1)) ≫
                (𝟙 _ ≫ (mappingCone.snd g).v (b - 1) (b - 1) (add_zero _) ≫
                  (HomologicalComplex.singleObjXSelf (.up ℤ) (b - 1) P).hom) = _
              simp only [Category.id_comp, Category.comp_id, Int.negOnePow_neg,
                Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.comp_neg,
                Preadditive.neg_comp]
              rw [mappingCone.d_snd_v'_assoc g (b - 1)]
              simp [T, singleFunctor, Category.assoc]
            refine ⟨eLow, eTop, ?_, ?_, hlow, hlast, ?_, ?_⟩
            · intro q hq
              change (eLow q hq).hom = 𝟙 _ ≫ (eLow q hq).hom
              exact (Category.id_comp _).symm
            · change eTop.hom = 𝟙 _ ≫ eTop.hom
              exact (Category.id_comp _).symm
            · rintro ⟨hP, hK⟩ q
              by_cases hq : q = b
              · subst q
                obtain ⟨n, ⟨e⟩⟩ := hP
                exact ⟨n, ⟨eTop ≪≫ e⟩⟩
              · obtain ⟨n, ⟨e⟩⟩ := hK q
                exact ⟨n, ⟨eAll q hq ≪≫ e⟩⟩
            · -- Keep the complex and negate its top coordinate identification.
              refine ⟨D, Iso.refl D, eLow, -eTop, ?_, ?_, hlow, ?_⟩
              · intro q hq
                simp
              · simp
              · simpa only [Preadditive.neg_iso_hom, Preadditive.comp_neg, neg_neg] using
                  congrArg Neg.neg hlast

end CochainComplex
