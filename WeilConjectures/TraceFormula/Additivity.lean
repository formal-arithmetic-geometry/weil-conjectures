/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.RecollementTriangle
public import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.TraceFormula.ClosedPieceFrobenius
public import WeilConjectures.TraceFormula.OpenPieceFrobenius
import WeilConjectures.TraceFormula.CompactPullbackShift
import WeilConjectures.CategoryTheory.Monoidal.Rigid.BraidedTrace

/-!

# Additivity of the compactly supported Frobenius trace

Let `Φ` be a finite universal homeomorphism of `X`, `j : U ⟶ X` an open immersion and
`i : Z ⟶ X` a closed immersion onto the complement, both stable under `Φ`. For a Weil object
`(K, φ)` the trace of the compactly supported Frobenius on `RΓ_c(X, K)` is the sum of the traces
on `RΓ_c(U, K|_U)` and `RΓ_c(Z, K|_Z)` (blueprint `prop-trf-trace-additivity-open-closed`,
`sk-i-global-additivity`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The localization triangle -/

section Triangle

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X) [IsClosedImmersion i.left]

omit [IsClosedImmersion i.left] in
/-- The counit of `j_! ⊣ Lj^*` followed by the unit of `Li^* ⊣ Ri_*` vanishes, since
`Lj^* Ri_* = 0`. -/
lemma counit_comp_unit_eq_zero_of_isCompl
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K = 0 :=
  ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).homEquiv _ _).injective
    ((isZero_boundedConstructibleUpperStar_obj_lowerStar_obj ℓ j i hcompl.disjoint _).eq_of_tgt
      _ _)

/-- The open–closed triangle `j_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶` with the extension by zero `j_!`:
the counit of `j_! ⊣ Lj^*` is inverted by `Lj^*`, which kills `Ri_* Li^* K`, and the unit of
`Li^* ⊣ Ri_*` is inverted by `Li^*`, which kills `j_! Lj^* K`; these restrictions jointly
reflect isomorphisms. -/
lemma exists_distTriang_openImmersionLowerShriek_openClosed
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ δ, Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)) δ ∈
      distTriang _ := by
  have : QuasiCompact (j.left ≫ X.hom) := by
    rw [Over.w j]
    infer_instance
  have : QuasiCompact j.left := QuasiCompact.of_comp j.left X.hom
  have hP := jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl
    (Profinite.padicAlgClRingObj ℓ) i.left j.left hcompl.symm
  have h₀ := counit_comp_unit_eq_zero_of_isCompl j i hcompl K
  have hzero : (boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K) ≫
      (boundedConstructible _).ι.map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K) = 0 := by
    rw [← Functor.map_comp, h₀, Functor.map_zero]
  have h₁ : IsIso ((boundedConstructibleUpperStar _ ℓ j).map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K)) :=
    IsIso.of_isIso_fac_left (hh := IsIso.id _)
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
        j).right_triangle_components K)
  have h₂ : IsIso ((boundedConstructibleUpperStar _ ℓ i).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)) :=
    IsIso.of_isIso_fac_right (hh := IsIso.id _)
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).left_triangle_components K)
  have h₁' := (NatIso.isIso_map_iff (boundedConstructibleUpperStarCompatibility
    (Profinite.padicAlgClRingObj ℓ) ℓ j)
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K)).1
    (inferInstanceAs (IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleUpperStar _ ℓ j).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K)))))
  have h₂' := (NatIso.isIso_map_iff (boundedConstructibleUpperStarCompatibility
    (Profinite.padicAlgClRingObj ℓ) ℓ i)
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)).1
    (inferInstanceAs (IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleUpperStar _ ℓ i).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)))))
  have hN := ((boundedConstructible _).ι.map_isZero
    (isZero_boundedConstructibleUpperStar_obj_lowerStar_obj ℓ j i hcompl.disjoint
      ((boundedConstructibleUpperStar _ ℓ i).obj K))).of_iso
    ((boundedConstructibleUpperStarCompatibility _ ℓ j).symm.app _)
  have hA := ((boundedConstructible _).ι.map_isZero
    (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ j i
      hcompl.disjoint ((boundedConstructibleUpperStar _ ℓ j).obj K))).of_iso
    ((boundedConstructibleUpperStarCompatibility _ ℓ i).symm.app _)
  exact Pretriangulated.exists_distTriang_of_jointlyReflectIsomorphisms hP _ _ hzero h₁' hN hA h₂'

variable (ℓ) in
/-- **The open–closed localization triangle** (blueprint
`prop-sf-open-closed-triangle-all-stages`): for an open immersion `j : U ⟶ X` and a closed
immersion `i : Z ⟶ X` onto its complement, the counit `Rj_! Lj^* K ⟶ K` of `Rj_! ⊣ Lj^*` and the
unit `K ⟶ Ri_* Li^* K` of `Li^* ⊣ Ri_*` extend to a distinguished triangle
`Rj_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶ Rj_! Lj^* K[1]` of the ambient derived category
`D(Mod_{ℚ̲̄_ℓ,X})`. Through `Rj_! ≅ j_!`, this is
`exists_distTriang_openImmersionLowerShriek_openClosed`. -/
theorem exists_distTriang_openClosed
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))),
      Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K)) δ ∈ distTriang _ := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openImmersionLowerShriek_openClosed j i hcompl K
  let γ := (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)
  have hε : (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K =
      γ.hom ≫ (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app K :=
    counit_app_ofNatIsoRight_upperShriekIsoUpperStar ℓ j K
  refine ⟨δ ≫ (shiftFunctor _ (1 : ℤ)).map
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
      γ.inv), isomorphic_distinguished _ hδ _ ?_⟩
  refine Triangle.isoMk _ _
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.mapIso γ)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · exact (Category.comp_id _).trans ((congrArg (boundedConstructible _).ι.map hε).trans
      (Functor.map_comp _ _ _))
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · refine (Category.assoc _ _ _).trans ((congrArg (δ ≫ ·) ?_).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
    rw [← Functor.map_comp, Functor.mapIso_hom, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

end Triangle

/-! ### Transport of distinguished triangles along a comparison isomorphism -/

section Transport

variable {Cx Cs Dx Ds : Type*} [Category Cx] [Category Cs] [Category Dx] [Category Ds]
  [HasShift Dx ℤ] [HasShift Ds ℤ] (A : Cx ⥤ Cs) (ιs : Cs ⥤ Ds) (ι : Cx ⥤ Dx) (R : Dx ⥤ Ds)
  [R.CommShift ℤ] (e : A ⋙ ιs ≅ ι ⋙ R)

/-- For a comparison isomorphism `e : A ⋙ ι_s ≅ ι ⋙ R` with `R` commuting with the shifts, the
morphism `ι_s A c ⟶ (ι_s A a)[1]` corresponding to `δ : ι c ⟶ (ι a)[1]`. -/
noncomputable def connectingOfIso {a c : Cx}
    (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    ιs.obj (A.obj c) ⟶ (shiftFunctor Ds (1 : ℤ)).obj (ιs.obj (A.obj a)) :=
  e.hom.app c ≫ R.map δ ≫ (R.commShiftIso (1 : ℤ)).hom.app (ι.obj a) ≫
    (shiftFunctor Ds (1 : ℤ)).map (e.inv.app a)

/-- If `Cx`, `Cs` carry shifts for which `ι`, `ι_s`, `A` and the comparison `e` commute with the
shifts, the morphism `connectingOfIso` attached to `ι δ₀` for `δ₀ : c ⟶ a⟦1⟧` is the image under
`ι_s` of `A δ₀` followed by the commutation of `A` with the shift:
```
ι_s A c ──e──▶ R ι c ──R (ι δ₀ ≫ comm)──▶ R ((ι a)⟦1⟧) ──comm──▶ (R ι a)⟦1⟧ ──e⁻¹⟦1⟧──▶ (ι_s A a)⟦1⟧
   ‖                                                                                       ‖
ι_s A c ─────────ι_s (A δ₀ ≫ comm)─────────▶ ι_s ((A a)⟦1⟧) ─────────comm─────────▶ (ι_s A a)⟦1⟧
```
-/
lemma connectingOfIso_map_comp_commShiftIso [HasShift Cx ℤ] [HasShift Cs ℤ] [A.CommShift ℤ]
    [ιs.CommShift ℤ] [ι.CommShift ℤ] [NatTrans.CommShift e.hom ℤ] {a c : Cx}
    (δ₀ : c ⟶ (shiftFunctor Cx (1 : ℤ)).obj a) :
    connectingOfIso A ιs ι R e (ι.map δ₀ ≫ (ι.commShiftIso (1 : ℤ)).hom.app a) =
      ιs.map (A.map δ₀ ≫ (A.commShiftIso (1 : ℤ)).hom.app a) ≫
        (ιs.commShiftIso (1 : ℤ)).hom.app (A.obj a) := by
  have h₁ := e.hom.naturality δ₀
  have h₂ := NatTrans.shift_app_comm e.hom (1 : ℤ) a
  simp only [Functor.comp_map, Functor.comp_obj, Functor.commShiftIso_comp_hom_app] at h₁ h₂
  simp only [connectingOfIso, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁.symm]
  slice_lhs 2 4 => rw [← h₂]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]

variable [HasZeroObject Dx] [HasZeroObject Ds] [Preadditive Dx] [Preadditive Ds]
  [∀ n : ℤ, (shiftFunctor Dx n).Additive] [∀ n : ℤ, (shiftFunctor Ds n).Additive]
  [Pretriangulated Dx] [Pretriangulated Ds] [R.IsTriangulated]

/-- The image under `A` of a triangle `a ⟶ b ⟶ c` of `Cx` which is distinguished through `ι` is
distinguished through `ι_s`, if `A` is compared with the triangulated functor `R`. -/
lemma distinguished_of_iso {a b c : Cx} {f : a ⟶ b} {g : b ⟶ c}
    {δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)}
    (h : Triangle.mk (ι.map f) (ι.map g) δ ∈ distTriang Dx) :
    Triangle.mk (ιs.map (A.map f)) (ιs.map (A.map g)) (connectingOfIso A ιs ι R e δ) ∈
      distTriang Ds :=
  isomorphic_distinguished _ (R.map_distinguished _ h) _
    (Triangle.isoMk _ _ (e.app a) (e.app b) (e.app c) (e.hom.naturality f) (e.hom.naturality g)
      (by
        simp only [connectingOfIso, Triangle.mk_mor₃, Iso.app_hom, Category.assoc,
          ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj, CategoryTheory.Functor.map_id,
          Category.comp_id]
        rfl))

end Transport

/-! ### Squares with connecting morphisms -/

section ShiftSquares

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]

end ShiftSquares

/-! ### The compactly supported localization triangle -/

section CompactTriangle

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X)

end CompactTriangle

/-! ### The Frobenius square with the connecting morphism on `X` -/

section ConnectingSquare

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {j : U ⟶ X} [IsOpenImmersion j.left] {i : Z ⟶ X}
  {Φ : X ⟶ X} {ΦU : U ⟶ U} [IsUniversalHomeomorphism Φ.left] [IsUniversalHomeomorphism ΦU.left]

variable (ℓ) in
/-- No nonzero maps `(LΦ^* Rj_! N)[1] ⟶ Ri_* M` (blueprint `prop-trf-trace-additivity-open-closed`,
Step 2(c)): by the base change `LΦ^* Rj_! ≅ Rj_! LΦ_U^*` along the cartesian square
`Φ_U ≫ j = j ≫ Φ` and `Rj_! ≅ j_!`, the source is a shifted extension by zero, and the range of
`i` misses that of `j`. -/
lemma eq_zero_of_shift_upperStar_lowerShriek_to_lowerStar
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base)) (hj : ΦU ≫ j = j ≫ Φ)
    (N : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (d : (shiftFunctor _ (1 : ℤ)).obj
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
          ((boundedConstructibleLowerShriek ℓ j).obj N))) ⟶
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
        ((boundedConstructibleLowerStar ℓ i).obj M)) :
    d = 0 := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (isPullback_of_comp_eq_of_isOpenImmersion j hj)
  let e := asIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (isPullback_of_comp_eq_of_isOpenImmersion j hj)).app N) ≪≫
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦU).obj N)
  rw [← cancel_mono ((boundedConstructibleLowerStarCompatibility
      ℓ i).hom.app M),
    ← cancel_epi ((shiftFunctor _ (1 : ℤ)).map
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
        e.inv)), zero_comp, comp_zero]
  exact eq_zero_of_shift_openImmersionLowerShriek_to_lowerStar _ ℓ j i hcompl.disjoint _ _ _ _

set_option maxHeartbeats 1000000 in
-- the triangles are compared through the inclusions of the bounded constructible categories
variable (ℓ) in
/-- **The Frobenius endomorphisms of the localization triangle commute with its connecting
morphism on `X`** (blueprint `prop-trf-trace-additivity-open-closed`, Step 2(c)): let
`ψ_U : LΦ^* Rj_! Lj^* K ⟶ Rj_! Lj^* K`, `φ : LΦ^* K ⟶ K` and `ψ_Z : LΦ^* Ri_* Li^* K ⟶ Ri_* Li^* K`
be compatible with the counit `ε` and the unit `η` of a localization triangle with connecting
morphism `δ`. Then `δ ∘ ψ_Z = ψ_U[1] ∘ LΦ^* δ`, where `LΦ^* δ` is formed through the ambient
derived pullback, which is triangulated: the third map of a morphism of triangles completing
`(ψ_U, φ)` is unique, there being no nonzero maps `(LΦ^* Rj_! Lj^* K)[1] ⟶ Ri_* Li^* K`. -/
theorem map_comp_connecting_eq_of_isCompl
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base)) (hj : ΦU ≫ j = j ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))))
    (hδ : Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K)) δ ∈ distTriang _)
    (ψU : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) ⟶
      (boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))
    (φ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    (ψZ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
      (boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))
    (ha : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K) ≫ φ =
      ψU ≫ (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K)
    (hb : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K) ≫ ψZ =
      φ ≫ (boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map ψZ ≫
        δ =
      connectingOfIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
          L((Φ.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
          (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ Φ) δ ≫
        (shiftFunctor _ (1 : ℤ)).map
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
            ψU) := by
  have hsub : Subsingleton ((shiftFunctor _ (1 : ℤ)).obj
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
          ((boundedConstructibleLowerShriek ℓ j).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)))) ⟶
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))) :=
    ⟨fun a b ↦ (eq_zero_of_shift_upperStar_lowerShriek_to_lowerStar ℓ hcompl hj _ _ a).trans
      (eq_zero_of_shift_upperStar_lowerShriek_to_lowerStar ℓ hcompl hj _ _ b).symm⟩
  have hT := distinguished_of_iso
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
    L((Φ.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ Φ) hδ
  obtain ⟨τ, -, -, -, h⟩ := ((triangle_morphism_extension _ _ hT hδ
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
      φ)).2.1 hsub).2.2
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map ψU)
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map ψZ)
    (by simp only [Triangle.mk_mor₁, ← Functor.map_comp, ha])
    (by simp only [Triangle.mk_mor₂, ← Functor.map_comp, hb])
  exact h.symm

end ConnectingSquare

/-! ### Triangle additivity of the trace -/

attribute [local instance] boundedConstructibleBraiding

section Frobenius

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

variable {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left] [IsFinite Φ.left]
  [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]

namespace WeilBoundedConstructible

/-- The image under `ι` of `δ₀` followed by the commutation of `ι` with the shift. -/
lemma exists_eq_map_comp_commShiftIso {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
    [HasShift D ℤ] {ι : C ⥤ D} (hι : ι.FullyFaithful) [ι.CommShift ℤ] {a c : C}
    (δ : ι.obj c ⟶ (shiftFunctor D (1 : ℤ)).obj (ι.obj a)) :
    ∃ δ₀ : c ⟶ (shiftFunctor C (1 : ℤ)).obj a,
      δ = ι.map δ₀ ≫ (ι.commShiftIso (1 : ℤ)).hom.app a :=
  ⟨hι.preimage (δ ≫ (ι.commShiftIso (1 : ℤ)).inv.app a), by simp⟩

end WeilBoundedConstructible

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
