/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.TraceFormula.CompactCohomology
public import WeilConjectures.TraceFormula.OpenPieceCoherence
public import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
public import WeilConjectures.TraceFormula.CompactPullbackShift
public import WeilConjectures.TraceFormula.PointTrace

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

variable (ℓ) in
/-- The adjunction `Rj_! ⊣ Lj^*` of an open immersion: the adjunction `Rj_! ⊣ Rj^!` transported
along `Rj^! ≅ Lj^*`. -/
noncomputable def boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⊣
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ j).ofNatIsoRight
    (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)

variable (ℓ) in
/-- **The open–closed localization triangle** (blueprint
`prop-sf-open-closed-triangle-all-stages`): for an open immersion `j : U ⟶ X` and a closed
immersion `i : Z ⟶ X` onto its complement, the counit `Rj_! Lj^* K ⟶ K` of `Rj_! ⊣ Lj^*` and the
unit `K ⟶ Ri_* Li^* K` of `Li^* ⊣ Ri_*` extend to a distinguished triangle
`Rj_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶ Rj_! Lj^* K[1]` of the ambient derived category
`D(Mod_{ℚ̲̄_ℓ,X})`. -/
theorem exists_distTriang_openClosed
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))),
      Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            i).unit.app K)) δ ∈ distTriang _ :=
  sorry

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
`ι_s` of `A δ₀` followed by the commutation of `A` with the shift. -/
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

/-- An identity between images of morphisms under a faithful functor `ι` commuting with the
shifts, composed with the commutation of `ι` with the shift, descends along `ι`. -/
lemma eq_comp_shift_map_of_map_comp_commShiftIso (ι : C ⥤ D) [ι.Faithful] [ι.CommShift ℤ]
    {P Q Q' : C} (a : P ⟶ (shiftFunctor C (1 : ℤ)).obj Q)
    (b : P ⟶ (shiftFunctor C (1 : ℤ)).obj Q') (c : Q' ⟶ Q)
    (h : ι.map a ≫ (ι.commShiftIso (1 : ℤ)).hom.app Q =
      (ι.map b ≫ (ι.commShiftIso (1 : ℤ)).hom.app Q') ≫ (shiftFunctor D (1 : ℤ)).map (ι.map c)) :
    a = b ≫ (shiftFunctor C (1 : ℤ)).map c := by
  apply ι.map_injective
  rw [← cancel_mono ((ι.commShiftIso (1 : ℤ)).hom.app Q), h, Functor.map_comp, Category.assoc,
    Category.assoc, Functor.commShiftIso_hom_naturality]

/-- The image of a commutation with a shifted morphism under a functor `ι` commuting with the
shifts. -/
lemma map_comp_commShiftIso_of_comp_eq (ι : C ⥤ D) [ι.CommShift ℤ] {P Q : C} (x : P ⟶ P)
    (y : Q ⟶ Q) (a : P ⟶ (shiftFunctor C (1 : ℤ)).obj Q)
    (h : x ≫ a = a ≫ (shiftFunctor C (1 : ℤ)).map y) :
    ι.map x ≫ ι.map a ≫ (ι.commShiftIso (1 : ℤ)).hom.app Q =
      (ι.map a ≫ (ι.commShiftIso (1 : ℤ)).hom.app Q) ≫ (shiftFunctor D (1 : ℤ)).map (ι.map y) := by
  rw [Category.assoc, ← Functor.commShiftIso_hom_naturality, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, h]

/-- **The Frobenius operators commute with the connecting morphism**, abstractly: let
`θ : A ⟶ F ⋙ A` commute with the shifts, and let `ψ_Z : F M_Z ⟶ M_Z`, `ψ_U : F M_U ⟶ M_U`
commute with `δ₀ : M_Z ⟶ M_U⟦1⟧` through the commutation of `F` with the shift. Then
`E_Z = A ψ_Z ∘ θ` and `E_U = A ψ_U ∘ θ` commute with `A δ₀` followed by the commutation of `A`
with the shift. -/
lemma comp_map_comp_commShiftIso_eq_of_commShift (A : C ⥤ D) (F : C ⥤ C) [A.CommShift ℤ]
    [F.CommShift ℤ] (θ : A ⟶ F ⋙ A) [NatTrans.CommShift θ ℤ] {MZ MU : C} (ψZ : F.obj MZ ⟶ MZ)
    (ψU : F.obj MU ⟶ MU) (δ₀ : MZ ⟶ (shiftFunctor C (1 : ℤ)).obj MU)
    (h : ψZ ≫ δ₀ = F.map δ₀ ≫ (F.commShiftIso (1 : ℤ)).hom.app MU ≫
      (shiftFunctor C (1 : ℤ)).map ψU) (EZ : A.obj MZ ⟶ A.obj MZ) (EU : A.obj MU ⟶ A.obj MU)
    (hZ : EZ = θ.app MZ ≫ A.map ψZ) (hU : EU = θ.app MU ≫ A.map ψU) :
    EZ ≫ A.map δ₀ ≫ (A.commShiftIso (1 : ℤ)).hom.app MU =
      (A.map δ₀ ≫ (A.commShiftIso (1 : ℤ)).hom.app MU) ≫ (shiftFunctor D (1 : ℤ)).map EU := by
  have hθ := NatTrans.shift_app_comm θ (1 : ℤ) MU
  have hn := θ.naturality δ₀
  rw [Functor.commShiftIso_comp_hom_app] at hθ
  simp only [Functor.comp_map] at hn
  rw [hZ, hU, Category.assoc, ← A.map_comp_assoc, h, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, Functor.commShiftIso_hom_naturality, reassoc_of% hn.symm,
    ← reassoc_of% hθ]
  simp only [Functor.map_comp, Category.assoc]

end ShiftSquares

/-! ### The compactly supported localization triangle -/

section CompactTriangle

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X)

variable (ℓ) in
/-- The connecting morphism `RΓ_c(X, Ri_* Li^* K) ⟶ RΓ_c(X, Rj_! Lj^* K)[1]` of the image under
`RΓ_c(X, -) = Ra_{X!}` of a localization triangle with connecting morphism `δ`, through the
ambient lower shriek, which is triangulated. -/
noncomputable def compactLocalizationConnecting
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)))) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left)).ι.obj
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
          ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))) ⟶
      (shiftFunctor _ (1 : ℤ)).obj
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (point k).left)).ι.obj
          ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
            ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)))) :=
  haveI := HasCompactification.of_over (toPoint X)
  connectingOfIso (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left)).ι
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
    (R((toPoint X).left)_!⟦Profinite.padicAlgClRingObj ℓ⟧)
    (boundedConstructibleLowerShriekCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))
    δ

variable (ℓ) in
/-- **The compactly supported localization triangle**: `RΓ_c(X, -)` of a localization triangle
`Rj_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶` is distinguished. -/
theorem compactLocalizationTriangle_distinguished
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))))
    (hδ : Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            i).unit.app K)) δ ∈ distTriang _) :
    Triangle.mk
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K)))
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            i).unit.app K)))
      (compactLocalizationConnecting ℓ j i K δ) ∈ distTriang _ :=
  haveI := HasCompactification.of_over (toPoint X)
  distinguished_of_iso _ _ _ _ _ hδ

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
          ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj N))) ⟶
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj M)) :
    d = 0 := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (isPullback_of_comp_eq_of_isOpenImmersion j hj)
  let e := asIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (isPullback_of_comp_eq_of_isOpenImmersion j hj)).app N) ≪≫
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦU).obj N)
  rw [← cancel_mono ((boundedConstructibleLowerStarCompatibility
      (Profinite.padicAlgClRingObj ℓ) ℓ i).hom.app M),
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
          ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))))
    (hδ : Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            i).unit.app K)) δ ∈ distTriang _)
    (ψU : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))
    (φ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    (ψZ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))
    (ha : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K) ≫ φ =
      ψU ≫ (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K)
    (hb : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
          i).unit.app K) ≫ ψZ =
      φ ≫ (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
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
          ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)))) ⟶
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
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

/-- A dual of an object transported along an isomorphism. -/
noncomputable abbrev hasRightDualOfIso {C : Type*} [Category C] [MonoidalCategory C] {P Q : C}
    (e : P ≅ Q) [HasRightDual Q] : HasRightDual P :=
  @HasRightDual.mk _ _ _ _ Qᘁ (exactPairingCongrLeft e)

/-- **Triangle additivity of the trace** (blueprint `prop-trf-trace-formal-laws`, item (2)): for
a distinguished triangle `P₁ ⟶ P₂ ⟶ P₃ ⟶ P₁[1]` of dualizable objects of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` (through
the inclusion into `D(Mod_{ℚ̲̄_ℓ,s})`) and an endomorphism `(v₁, v₂, v₃)` of it,
`tr v₂ = tr v₁ + tr v₃`. Over the field `ℚ̄_ℓ` the filtered origin required in item (2) is
automatic: by item (4) the trace is the alternating sum of the traces on the cohomology, which is
additive along the long exact cohomology sequence of an endomorphism of a triangle. -/
theorem trace_eq_trace_add_trace_of_distTriang [IsSepClosed k]
    {P₁ P₂ P₃ : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧} [HasRightDual P₁]
    [HasRightDual P₂] [HasRightDual P₃] (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃)
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.obj P₃ ⟶
      (shiftFunctor _ (1 : ℤ)).obj
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (point k).left)).ι.obj P₁))
    (hT : Triangle.mk
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map f)
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map g) δ ∈ distTriang _)
    (v₁ : P₁ ⟶ P₁) (v₂ : P₂ ⟶ P₂) (v₃ : P₃ ⟶ P₃) (h₁ : v₁ ≫ f = f ≫ v₂)
    (h₂ : v₂ ≫ g = g ≫ v₃)
    (h₃ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map v₃ ≫ δ =
      δ ≫ (shiftFunctor _ (1 : ℤ)).map
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (point k).left)).ι.map v₁)) :
    trace v₂ = trace v₁ + trace v₃ := by
  let ι := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
    (point k).left)).ι
  letI := DerivedCategory.braidedCategory' (PointMod ℓ k)
  let : HasRightDual (ι.obj P₁) :=
    @HasRightDual.mk _ _ _ _ (ι.obj (P₁ᘁ)) (ExactPairing.map ι P₁ (P₁ᘁ))
  let : HasRightDual (ι.obj P₂) :=
    @HasRightDual.mk _ _ _ _ (ι.obj (P₂ᘁ)) (ExactPairing.map ι P₂ (P₂ᘁ))
  let : HasRightDual (ι.obj P₃) :=
    @HasRightDual.mk _ _ _ _ (ι.obj (P₃ᘁ)) (ExactPairing.map ι P₃ (P₃ᘁ))
  have key {P : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧} [HasRightDual P]
      [HasRightDual (ι.obj P)] (v : P ⟶ P) : trace (ι.map v) = ι.unitEndRingHom (trace v) :=
    ι.trace_eq_unitEndRingHom_trace v (ι.map v) (Iso.refl _) (by simp)
  have hinj : Function.Injective ι.unitEndRingHom := fun a b h ↦ by
    rw [Functor.unitEndRingHom_apply, Functor.unitEndRingHom_apply] at h
    exact ι.map_injective ((cancel_mono _).1 (by simpa [ι] using h))
  apply hinj
  rw [RingHom.map_add, ← key, ← key, ← key]
  exact trace_eq_trace_add_trace_of_distTriang_of_shiftDecomposition ℓ k
    ((nonempty_shiftDecomposition_point ℓ k P₁).some.map ι)
    ((nonempty_shiftDecomposition_point ℓ k P₂).some.map ι)
    ((nonempty_shiftDecomposition_point ℓ k P₃).some.map ι) (ι.map f) (ι.map g) δ hT
    (ι.map v₁) (ι.map v₂) (ι.map v₃) (by rw [← ι.map_comp, ← ι.map_comp, h₁])
    (by rw [← ι.map_comp, ← ι.map_comp, h₂]) h₃

/-! ### The Frobenius endomorphisms of the triangle -/

/-- The abstract shape of the compatibility of the compactly supported Frobenius with the pullback
to a closed piece: the composition laws `(i ≫ Φ)^♯ = Φ^♯ ≫ i^♯` and `(Φ_Z ≫ i)^♯ = i^♯ ≫ Φ_Z^♯`
and `Φ_Z ≫ i = i ≫ Φ`. -/
lemma frobenius_closedPiece_aux {CX CZ D : Type*} [Category CX] [Category CZ] [Category D]
    {aX : CX ⥤ D} {aZ : CZ ⥤ D} {uΦ : CX ⥤ CX} {ui : CX ⥤ CZ} {uΦZ : CZ ⥤ CZ} {u₁ u₂ : CX ⥤ CZ}
    (pΦ : aX ⟶ uΦ ⋙ aX) (pi : aX ⟶ ui ⋙ aZ) (pΦZ : aZ ⟶ uΦZ ⋙ aZ) (p₁ : aX ⟶ u₁ ⋙ aZ)
    (p₂ : aX ⟶ u₂ ⋙ aZ) (c₁ : u₁ ≅ uΦ ⋙ ui) (c₂ : u₂ ≅ ui ⋙ uΦZ) (K : CX)
    (e : u₂.obj K ⟶ u₁.obj K)
    (h1 : p₁.app K = pΦ.app K ≫ pi.app (uΦ.obj K) ≫ aZ.map (c₁.inv.app K))
    (h2 : p₂.app K = pi.app K ≫ pΦZ.app (ui.obj K) ≫ aZ.map (c₂.inv.app K))
    (h3 : p₂.app K ≫ aZ.map e = p₁.app K) (cmp : uΦZ.obj (ui.obj K) ⟶ ui.obj (uΦ.obj K))
    (hc : cmp = c₂.inv.app K ≫ e ≫ c₁.hom.app K) (φ : uΦ.obj K ⟶ K) (cF : aX.obj K ⟶ aX.obj K)
    (hK : cF = pΦ.app K ≫ aX.map φ) (ψ : uΦZ.obj (ui.obj K) ⟶ ui.obj K)
    (cFZ : aZ.obj (ui.obj K) ⟶ aZ.obj (ui.obj K)) (hKZ : cFZ = pΦZ.app (ui.obj K) ≫ aZ.map ψ)
    (hψ : ψ = cmp ≫ ui.map φ) :
    cF ≫ pi.app K = pi.app K ≫ cFZ := by
  have hn := pi.naturality φ
  simp only [Functor.comp_map] at hn
  rw [hK, hKZ, hψ, hc, Category.assoc, hn]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h2, reassoc_of% h3, h1]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc aZ (c₁.inv.app K) (c₁.hom.app K), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The inverse of `a⁻¹ ≫ (G = H) ≫ b` at an object. -/
lemma iso_symm_trans_eqToIso_trans_inv_app {C D : Type*} [Category C] [Category D]
    {F G H I : C ⥤ D} (a : F ≅ G) (h : F = H) (b : H ≅ I) (K : C) :
    (a.symm ≪≫ eqToIso h ≪≫ b).inv.app K =
      b.inv.app K ≫ eqToHom (congrArg (fun T ↦ T.obj K) h.symm) ≫ a.hom.app K := by
  subst h
  simp

/-- `comp_eq_comp_conj_of_comp_eq` for the component of a natural isomorphism. -/
lemma comp_eq_comp_conj_of_comp_eq_app {B C D : Type*} [Category B] [Category C] [Category D]
    {F₁ : B ⥤ C} {F₂ : C ⥤ D} {G : B ⥤ D} (γ : F₁ ⋙ F₂ ≅ G) (M : B) {a : D} (x : a ⟶ a)
    (y : a ⟶ F₂.obj (F₁.obj M)) (z : G.obj M ⟶ G.obj M)
    (h : x ≫ y ≫ γ.hom.app M = (y ≫ γ.hom.app M) ≫ z) :
    x ≫ y = y ≫ γ.hom.app M ≫ z ≫ γ.inv.app M := by
  rw [← cancel_mono (γ.hom.app M)]
  simpa using h

/-- An endomorphism commuting with `y ≫ g` for an isomorphism `g` commutes with `y` and the
conjugate along `g`. -/
lemma comp_eq_comp_conj_of_comp_eq {D : Type*} [Category D] {a b c : D} (x : a ⟶ a) (y : a ⟶ b)
    (g : b ≅ c) (z : c ⟶ c) (h : x ≫ y ≫ g.hom = (y ≫ g.hom) ≫ z) :
    x ≫ y = y ≫ g.hom ≫ z ≫ g.inv := by
  rw [← cancel_mono g.hom]
  simpa using h

section PieceCoefficients

variable {CX CZ D : Type*} [Category CX] [Category CZ] [Category D] {aX : CX ⥤ D}
  {aZ : CZ ⥤ D} {uΦ : CX ⥤ CX} {ui : CX ⥤ CZ} {uΦZ : CZ ⥤ CZ} {ri : CZ ⥤ CX}

lemma closedPiece_pullback_comm_aux (pΦ : aX ⟶ uΦ ⋙ aX) (pi : aX ⟶ ui ⋙ aZ)
    (pΦZ : aZ ⟶ uΦZ ⋙ aZ) {u₁ u₂ : CX ⥤ CZ} (p₁ : aX ⟶ u₁ ⋙ aZ) (p₂ : aX ⟶ u₂ ⋙ aZ)
    (c₁ : u₁ ≅ uΦ ⋙ ui) (c₂ : u₂ ≅ ui ⋙ uΦZ) (M : CX) (e : u₂.obj M ⟶ u₁.obj M)
    (h1 : p₁.app M = pΦ.app M ≫ pi.app (uΦ.obj M) ≫ aZ.map (c₁.inv.app M))
    (h2 : p₂.app M = pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map (c₂.inv.app M))
    (h3 : p₂.app M ≫ aZ.map e = p₁.app M) (cmp : uΦZ.obj (ui.obj M) ⟶ ui.obj (uΦ.obj M))
    (hc : cmp = c₂.inv.app M ≫ e ≫ c₁.hom.app M) :
    pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map cmp = pΦ.app M ≫ pi.app (uΦ.obj M) := by
  have h3' : pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map (c₂.inv.app M) ≫ aZ.map e =
      pΦ.app M ≫ pi.app (uΦ.obj M) ≫ aZ.map (c₁.inv.app M) := by
    simpa [h1, h2] using h3
  rw [hc, Functor.map_comp, Functor.map_comp, reassoc_of% h3']
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]

lemma closedPiece_eq_aux (adj : ui ⊣ ri) (pΦ : aX ⟶ uΦ ⋙ aX) (pi : aX ⟶ ui ⋙ aZ)
    (pΦZ : aZ ⟶ uΦZ ⋙ aZ) (c : ri ⋙ aX ≅ aZ)
    (hpi : ∀ M, pi.app M = aX.map (adj.unit.app M) ≫ c.hom.app (ui.obj M))
    (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui)
    (hcomm : ∀ M, pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map (cmp.hom.app M) =
      pΦ.app M ≫ pi.app (uΦ.obj M)) (N : CZ) (g : uΦZ.obj N ⟶ N) :
    c.hom.app N ≫ (pΦZ.app N ≫ aZ.map g) ≫ c.inv.app N =
      pΦ.app (ri.obj N) ≫ aX.map (adj.unit.app _ ≫ ri.map (cmp.inv.app (ri.obj N) ≫
        uΦZ.map (adj.counit.app N) ≫ g)) := by
  have hc : c.hom.app N = pi.app (ri.obj N) ≫ aZ.map (adj.counit.app N) := by
    have hn := c.hom.naturality (adj.counit.app N)
    dsimp at hn
    rw [hpi, Category.assoc, ← hn, ← aX.map_comp_assoc, adj.right_triangle_components]
    simp
  have h' : pi.app (ri.obj N) ≫ pΦZ.app (ui.obj (ri.obj N)) =
      pΦ.app (ri.obj N) ≫ pi.app (uΦ.obj (ri.obj N)) ≫ aZ.map (cmp.inv.app (ri.obj N)) := by
    rw [← reassoc_of% (hcomm (ri.obj N)), ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  have hnat := c.hom.naturality (cmp.inv.app (ri.obj N) ≫ uΦZ.map (adj.counit.app N) ≫ g)
  have hn := pΦZ.naturality (adj.counit.app N)
  dsimp at hnat hn
  simp only [Functor.map_comp, Category.assoc] at hnat
  rw [← cancel_mono (c.hom.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.map_comp]
  rw [hnat, ← Category.assoc (aX.map _), ← hpi, ← reassoc_of% h', reassoc_of% hn.symm,
    ← reassoc_of% hc]

lemma closedPiece_coeff_unit_aux (adj : ui ⊣ ri) (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui) (K : CX)
    (φ : uΦ.obj K ⟶ K) :
    uΦ.map (adj.unit.app K) ≫ adj.unit.app (uΦ.obj (ri.obj (ui.obj K))) ≫ ri.map (cmp.inv.app (ri.obj (ui.obj K)) ≫
        uΦZ.map (adj.counit.app (ui.obj K)) ≫ cmp.hom.app K ≫ ui.map φ) =
      φ ≫ adj.unit.app K := by
  have hu := adj.unit.naturality (uΦ.map (adj.unit.app K))
  have hu' := adj.unit.naturality φ
  have hc := cmp.inv.naturality (adj.unit.app K)
  dsimp at hu hu' hc
  rw [reassoc_of% hu, ← Functor.map_comp, reassoc_of% hc, ← Functor.map_comp_assoc uΦZ,
    adj.left_triangle_components]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact hu'.symm

/-- The abstract Frobenius coefficient of the closed piece:
`uΦ ri N ⟶ ri ui uΦ ri N ≅ ri uΦZ ui ri N ⟶ ri uΦZ N ⟶ ri N` for a coefficient map
`g : uΦZ N ⟶ N`, through the unit and counit of `ui ⊣ ri` and the comparison `cmp`. -/
def closedPieceCoeff (adj : ui ⊣ ri) (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui) (N : CZ) (g : uΦZ.obj N ⟶ N) :
    uΦ.obj (ri.obj N) ⟶ ri.obj N :=
  adj.unit.app _ ≫ ri.map (cmp.inv.app (ri.obj N) ≫ uΦZ.map (adj.counit.app N) ≫ g)

/-- `closedPiece_eq_aux` for `closedPieceCoeff`. -/
lemma closedPiece_eq_aux' (adj : ui ⊣ ri) (pΦ : aX ⟶ uΦ ⋙ aX) (pi : aX ⟶ ui ⋙ aZ)
    (pΦZ : aZ ⟶ uΦZ ⋙ aZ) (c : ri ⋙ aX ≅ aZ)
    (hpi : ∀ M, pi.app M = aX.map (adj.unit.app M) ≫ c.hom.app (ui.obj M))
    (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui)
    (hcomm : ∀ M, pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map (cmp.hom.app M) =
      pΦ.app M ≫ pi.app (uΦ.obj M)) (N : CZ) (g : uΦZ.obj N ⟶ N) :
    (c.hom.app N : aX.obj (ri.obj N) ⟶ aZ.obj N) ≫ (pΦZ.app N ≫ aZ.map g) ≫
        (c.inv.app N : aZ.obj N ⟶ aX.obj (ri.obj N)) =
      pΦ.app (ri.obj N) ≫ aX.map (closedPieceCoeff adj cmp N g) :=
  closedPiece_eq_aux adj pΦ pi pΦZ c hpi cmp hcomm N g

/-- `closedPiece_coeff_unit_aux` for `closedPieceCoeff`. -/
lemma closedPiece_coeff_unit_aux' (adj : ui ⊣ ri) (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui) (K : CX)
    (φ : uΦ.obj K ⟶ K) :
    uΦ.map (adj.unit.app K) ≫ closedPieceCoeff adj cmp (ui.obj K) (cmp.hom.app K ≫ ui.map φ) =
      φ ≫ adj.unit.app K := by
  rw [closedPieceCoeff]
  exact closedPiece_coeff_unit_aux adj cmp K φ

variable {CU : Type*} [Category CU] {aU : CU ⥤ D} {uΦU : CU ⥤ CU} {rj : CU ⥤ CX}

lemma openPiece_eq_aux (pΦ : aX ⟶ uΦ ⋙ aX) (pΦU : aU ⟶ uΦU ⋙ aU) (c : rj ⋙ aX ≅ aU)
    (bc : rj ⋙ uΦ ⟶ uΦU ⋙ rj) (N : CU)
    (hB : pΦ.app (rj.obj N) ≫ aX.map (bc.app N) ≫ c.hom.app (uΦU.obj N) =
      c.hom.app N ≫ pΦU.app N) (g : uΦU.obj N ⟶ N) :
    c.hom.app N ≫ (pΦU.app N ≫ aU.map g) ≫ c.inv.app N =
      pΦ.app (rj.obj N) ≫ aX.map (bc.app N ≫ rj.map g) := by
  have hn := c.hom.naturality g
  dsimp at hn
  rw [← Category.assoc, ← Category.assoc, ← hB]
  simp only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hn, Iso.hom_inv_id_app]
  simp


/-- `openPiece_eq_aux` for a coefficient `ψ` given by its defining equation. -/
lemma openPiece_eq_aux' (pΦ : aX ⟶ uΦ ⋙ aX) (pΦU : aU ⟶ uΦU ⋙ aU) (c : rj ⋙ aX ≅ aU)
    (bc : rj ⋙ uΦ ⟶ uΦU ⋙ rj) (N : CU)
    (hB : pΦ.app (rj.obj N) ≫ aX.map (bc.app N) ≫ c.hom.app (uΦU.obj N) =
      c.hom.app N ≫ pΦU.app N) (g : uΦU.obj N ⟶ N) (ψ : uΦ.obj (rj.obj N) ⟶ rj.obj N)
    (hψ : ψ = bc.app N ≫ rj.map g) :
    c.hom.app N ≫ pΦU.app N ≫ aU.map g = (pΦ.app (rj.obj N) ≫ aX.map ψ) ≫ c.hom.app N := by
  rw [hψ, ← openPiece_eq_aux pΦ pΦU c bc N hB g]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
end PieceCoefficients

section Frobenius

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

variable (ℓ) in
/-- The isomorphism `Ra_{X!} Ri_* ≅ Ra_{X!} Ri_! ≅ Ra_{Z!}` for a proper `i : Z ⟶ X`. -/
noncomputable def boundedConstructibleLowerStarCompToPoint (i : Z ⟶ X) [IsProper i.left] :
    boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) ≅
      boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z) :=
  Functor.isoWhiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i).symm _ ≪≫
    boundedConstructibleLowerShriekCompToPoint ℓ i

/-- The pullback `i^♯ : Ra_{X!} ⟶ Ra_{Z!} Li^*` along a proper `i` is `Ra_{X!}` of the unit of
`Li^* ⊣ Ri_*` followed by `Ra_{X!} Ri_* ≅ Ra_{Z!}`. -/
lemma compactPullback_app_eq (i : Z ⟶ X) [IsProper i.left]
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ i).app N =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            i).unit.app N) ≫
        (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj N) := by
  rw [compactPullback_app, boundedConstructibleLowerStarCompToPoint, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom]

variable {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left] [IsFinite Φ.left]
  [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]

namespace WeilBoundedConstructible

omit [IsClosedImmersion i.left] [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left] in
/-- The Frobenius structure of the restriction `K|_Z`. -/
lemma weilUpperStar_obj_str_hom (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ) :
    ((weilUpperStar ℓ ΦZ Φ i hi).obj K).str.hom =
      (weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom := by
  rw [weilUpperStar_obj_str ℓ ΦZ Φ i hi K]
  rfl

omit [IsClosedImmersion i.left] [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] in
/-- The compactly supported Frobenius of the restriction `K|_Z` as `RΓ_c(φ|_Z) ∘ Φ_Z^♯`. -/
lemma compactFrobenius_weilUpperStar (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ) :
    ((weilUpperStar ℓ ΦZ Φ i hi).obj K).compactFrobenius =
      (compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        i).obj K.carrier) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).map
          ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom) := by
  rw [compactFrobenius_eq (X := Z) (Φ := ΦZ) ((weilUpperStar ℓ ΦZ Φ i hi).obj K),
    weilUpperStar_obj_str_hom]
  rfl

set_option maxHeartbeats 1000000 in
-- the coherence of the pullbacks along `Φ_Z ≫ i = i ≫ Φ` is a long elaboration
omit [IsUniversalHomeomorphism ΦZ.left] in
/-- **The compactly supported Frobenius commutes with the pullback to a closed piece**: for a
closed immersion `i` with `Φ_Z ≫ i = i ≫ Φ`, `i^♯ ∘ F_c(K) = F_c(K|_Z) ∘ i^♯`. Through
`F_c = RΓ_c(φ) ∘ Φ^♯` this is the composition law of the pullbacks along
`Φ_Z ≫ i = i ≫ Φ`. -/
theorem compactFrobenius_comp_compactPullback (hi : ΦZ ≫ i = i ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    K.compactFrobenius ≫ (compactPullback ℓ i).app K.carrier =
      (compactPullback ℓ i).app K.carrier ≫
        ((compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar
          (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) ≫
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).map
            ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
              (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map
                K.str.hom)) := by
  have : IsProper (i ≫ Φ).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper (ΦZ ≫ i).left := by
    rw [Over.comp_left]
    infer_instance
  exact frobenius_closedPiece_aux (compactPullback ℓ Φ) (compactPullback ℓ i)
    (compactPullback ℓ ΦZ) (compactPullback ℓ (i ≫ Φ)) (compactPullback ℓ (ΦZ ≫ i))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i Φ)
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ΦZ i) K.carrier
    (eqToHom (by rw [hi])) (compactPullback_comp_app ℓ i Φ K.carrier)
    (compactPullback_comp_app ℓ ΦZ i K.carrier) (compactPullback_app_congr ℓ hi K.carrier)
    ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier)
    (weilUpperStarComparison_hom_app ℓ ΦZ Φ i hi K.carrier) K.str.hom _
    (compactFrobenius_eq K) _ _ rfl rfl

variable (ℓ) in
/-- The operator `E_U` on `RΓ_c(X, Rj_! Lj^* K)`: the compactly supported Frobenius of the
restriction `K|_U`, transported along `Ra_{X!} Rj_! ≅ Ra_{U!}`. -/
noncomputable def compactFrobeniusOpenPiece (hj : ΦU ≫ j = j ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) :=
  (boundedConstructibleLowerShriekCompToPoint ℓ j).hom.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier) ≫
    ((weilUpperStar ℓ ΦU Φ j hj).obj K).compactFrobenius ≫
    (boundedConstructibleLowerShriekCompToPoint ℓ j).inv.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)

variable (ℓ) in
/-- The operator `E_Z` on `RΓ_c(X, Ri_* Li^* K)`: the compactly supported Frobenius of the
restriction `K|_Z`, transported along `Ra_{X!} Ri_* ≅ Ra_{Z!}`. -/
noncomputable def compactFrobeniusClosedPiece (hi : ΦZ ≫ i = i ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) :=
  (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) ≫
    ((compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).map
        ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom)) ≫
    (boundedConstructibleLowerStarCompToPoint ℓ i).inv.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)

set_option maxHeartbeats 1000000 in
-- the closed-piece operator unfolds to a long composite
omit [IsUniversalHomeomorphism ΦZ.left] in
/-- The square of the closed piece: `E_Z ∘ RΓ_c(η) = RΓ_c(η) ∘ F_c(K)` for the unit
`η : K ⟶ Ri_* Li^* K`. -/
theorem compactFrobenius_comp_compactUnit (hi : ΦZ ≫ i = i ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    K.compactFrobenius ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            i).unit.app K.carrier) =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            i).unit.app K.carrier) ≫ compactFrobeniusClosedPiece ℓ hi K := by
  have e := compactPullback_app_eq (ℓ := ℓ) i K.carrier
  have h : K.compactFrobenius ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
        ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
          i).unit.app K.carrier) ≫
        (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) =
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
        ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
          i).unit.app K.carrier) ≫
        (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) ≫
        ((compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar
          (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) ≫
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).map
            ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
              (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map
                K.str.hom)) := by
    rw [← e]
    exact compactFrobenius_comp_compactPullback hi K
  rw [compactFrobeniusClosedPiece,
    ← cancel_mono ((boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)),
    Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

set_option maxHeartbeats 1000000 in
-- the open-piece operator unfolds to a long composite
omit [IsClosedImmersion i.left] in
/-- The square of the open piece (blueprint `prop-trf-trace-additivity-open-closed`, Step 2(a)):
`RΓ_c(ε) ∘ E_U = F_c(K) ∘ RΓ_c(ε)` for the counit `ε : Rj_! Lj^* K ⟶ K`. Through
`F_c = RΓ_c(φ) ∘ Φ^♯` this is the compatibility of the extension by zero with the pullbacks along
the Frobenii, `compToPoint_inv_app_comp_counit_comp_compactPullback`. -/
theorem compactFrobeniusOpenPiece_comp_counit (hj : ΦU ≫ j = j ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    compactFrobeniusOpenPiece ℓ hj K ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
            K.carrier) =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
            K.carrier) ≫ K.compactFrobenius := by
  have h := compToPoint_inv_app_comp_counit_comp_compactPullback ℓ j hj K.carrier
  have hn₁ := (boundedConstructibleLowerShriekCompToPoint ℓ j).inv.naturality
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map K.str.hom)
  have hn₂ := congrArg
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
    ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.naturality
      K.str.hom)
  simp only [Functor.comp_map, Functor.comp_obj] at hn₁
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp, Functor.comp_obj,
    Functor.id_obj] at hn₂
  rw [boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl] at hn₂ ⊢
  rw [compactFrobeniusOpenPiece,
    ← cancel_epi ((boundedConstructibleLowerShriekCompToPoint ℓ j).inv.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier))]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, compactFrobenius_eq K, reassoc_of% h]
  refine Eq.trans (congrArg (fun f ↦ f ≫
    (boundedConstructibleLowerShriekCompToPoint ℓ j).inv.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier) ≫
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
      (((boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
        j).ofNatIsoRight (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)).counit.app
          K.carrier)) (compactFrobenius_weilUpperStar hj K)) ?_
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn₁, hn₂]

omit [IsUniversalHomeomorphism ΦZ.left] in
/-- The pullback square of the closed piece on compactly supported cohomology: for
`Φ_Z ≫ i = i ≫ Φ`, `i^♯ ≫ Φ_Z^♯ ≫ RΓ_c(Z, cmp) = Φ^♯ ≫ i^♯`, where
`cmp : LΦ_Z^* Li^* ≅ Li^* LΦ^*` is the pullback comparison of the square. -/
lemma compactPullback_comp_compactPullback_comparison (hi : ΦZ ≫ i = i ≫ Φ)
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ i).app M ≫
        (compactPullback ℓ ΦZ).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj M) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).map
          ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app M) =
      (compactPullback ℓ Φ).app M ≫
        (compactPullback ℓ i).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj M) := by
  have : IsProper (i ≫ Φ).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper (ΦZ ≫ i).left := by
    rw [Over.comp_left]
    infer_instance
  exact closedPiece_pullback_comm_aux (compactPullback ℓ Φ) (compactPullback ℓ i)
    (compactPullback ℓ ΦZ) (compactPullback ℓ (i ≫ Φ)) (compactPullback ℓ (ΦZ ≫ i))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i Φ)
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ΦZ i) M
    (eqToHom (by rw [hi])) (compactPullback_comp_app ℓ i Φ M)
    (compactPullback_comp_app ℓ ΦZ i M) (compactPullback_app_congr ℓ hi M) _
    (weilUpperStarComparison_hom_app ℓ ΦZ Φ i hi M)

variable (ℓ) in
/-- The Frobenius coefficient `ψ_Z : LΦ^* Ri_* Li^* K ⟶ Ri_* Li^* K` of the closed piece: the
adjoint of `Li^* LΦ^* Ri_* Li^* K ≅ LΦ_Z^* Li^* Ri_* Li^* K ⟶ LΦ_Z^* Li^* K ≅ Li^* LΦ^* K ⟶ Li^* K`,
of the pullback comparison, the counit of `Li^* ⊣ Ri_*` and `Li^* φ`. -/
noncomputable def closedPieceFrobeniusCoeff (hi : ΦZ ≫ i = i ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) :=
  closedPieceCoeff
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ i)
    (weilUpperStarComparison ℓ ΦZ Φ i hi) _
    ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom)

set_option maxHeartbeats 1000000 in
omit [IsUniversalHomeomorphism ΦZ.left] in
/-- The operator `E_Z` of the closed piece is `RΓ_c(X, ψ_Z) ∘ Φ^♯` on `RΓ_c(X, Ri_* Li^* K)`. -/
lemma compactFrobeniusClosedPiece_eq (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ) :
    compactFrobeniusClosedPiece ℓ hi K =
      (compactPullback ℓ Φ).app
          ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
              K.carrier)) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          (closedPieceFrobeniusCoeff ℓ hi K) := by
  rw [compactFrobeniusClosedPiece]
  exact closedPiece_eq_aux'
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ i)
    (compactPullback ℓ Φ) (compactPullback ℓ i) (compactPullback ℓ ΦZ)
    (boundedConstructibleLowerStarCompToPoint ℓ i) (compactPullback_app_eq (ℓ := ℓ) i)
    (weilUpperStarComparison ℓ ΦZ Φ i hi) (compactPullback_comp_compactPullback_comparison hi)
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)
    ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom)

set_option maxHeartbeats 1000000 in
omit [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] [IsFinite ΦZ.left]
  [IsUniversalHomeomorphism ΦZ.left] in
/-- The Frobenius coefficient of the closed piece is compatible with the unit
`η : K ⟶ Ri_* Li^* K`. -/
lemma upperStar_map_unit_comp_closedPieceFrobeniusCoeff (hi : ΦZ ≫ i = i ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
          i).unit.app K.carrier) ≫ closedPieceFrobeniusCoeff ℓ hi K =
      K.str.hom ≫ (boundedConstructibleUpperStarLowerStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ i).unit.app K.carrier := by
  exact closedPiece_coeff_unit_aux'
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ i)
    (weilUpperStarComparison ℓ ΦZ Φ i hi) K.carrier K.str.hom

variable (ℓ) in
/-- The Frobenius coefficient `ψ_U : LΦ^* Rj_! Lj^* K ⟶ Rj_! Lj^* K` of the open piece: the
compact-support base change `LΦ^* Rj_! ⟶ Rj_! LΦ_U^*` along the cartesian square
`Φ_U ≫ j = j ≫ Φ`, followed by `Rj_!` of the Frobenius structure of `K|_U`. -/
noncomputable def openPieceFrobeniusCoeff (hj : ΦU ≫ j = j ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier) :=
  (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (isPullback_of_comp_eq_of_isOpenImmersion j hj)).app _ ≫
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
      ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K.carrier ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map K.str.hom)

set_option maxHeartbeats 1000000 in
omit [IsClosedImmersion i.left] in
/-- The operator `E_U` of the open piece is `RΓ_c(X, ψ_U) ∘ Φ^♯` on `RΓ_c(X, Rj_! Lj^* K)`. -/
lemma compactFrobeniusOpenPiece_eq (hj : ΦU ≫ j = j ≫ Φ) (K : WeilBoundedConstructible ℓ Φ) :
    compactFrobeniusOpenPiece ℓ hj K =
      (compactPullback ℓ Φ).app
          ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
              K.carrier)) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          (openPieceFrobeniusCoeff ℓ hj K) := by
  have h := openPiece_eq_aux' (compactPullback ℓ Φ) (compactPullback ℓ ΦU)
    (boundedConstructibleLowerShriekCompToPoint ℓ j)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (isPullback_of_comp_eq_of_isOpenImmersion j hj))
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)
    (compactPullback_app_comp_baseChange ℓ (isPullback_of_comp_eq_of_isOpenImmersion j hj)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier))
    ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K.carrier ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map K.str.hom)
    (openPieceFrobeniusCoeff ℓ hj K) rfl
  rw [compactFrobeniusOpenPiece, compactFrobenius_weilUpperStar hj K,
    ← cancel_mono ((boundedConstructibleLowerShriekCompToPoint ℓ j).hom.app _),
    Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  simpa only [Category.assoc] using h

omit [IsClosedImmersion i.left] [IsFinite Φ.left] [IsFinite ΦU.left] in
/-- The pullback along `Φ` of the counit `ε : Rj_! Lj^* K ⟶ K` is the compact-support base change
followed by `Rj_!` of the pullback comparison and the counit at `LΦ^* K` (blueprint
`def-exchange-projection` for the open immersion `j`). -/
lemma upperStar_map_counit_eq (hj : ΦU ≫ j = j ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K) =
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
          (isPullback_of_comp_eq_of_isOpenImmersion j hj)).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K) ≫
        (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K) := by
  have sq := isPullback_of_comp_eq_of_isOpenImmersion j hj
  have hC1 := boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isOpenImmersion ℓ sq
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)
  have hEx := Adjunction.exchangeLeft_app_comp_map_counit_app
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq.flip) K
  rw [← boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft
    (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq] at hEx
  have hn := (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
    j).hom.naturality ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K)
  rw [weilUpperStarComparison_hom_app_eq ℓ j hj sq.toCommSq.flip] at hn ⊢
  rw [boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl,
    counit_app_ofNatIsoRight_upperShriekIsoUpperStar,
    counit_app_ofNatIsoRight_upperShriekIsoUpperStar, Functor.map_comp, ← hC1]
  simp only [Category.assoc]
  rw [hEx, reassoc_of% hn]

omit [IsClosedImmersion i.left] [IsFinite Φ.left] [IsFinite ΦU.left] in
/-- The Frobenius coefficient of the open piece is compatible with the counit
`ε : Rj_! Lj^* K ⟶ K`. -/
lemma upperStar_map_counit_comp_str_hom (hj : ΦU ≫ j = j ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
          K.carrier) ≫ K.str.hom =
      openPieceFrobeniusCoeff ℓ hj K ≫
        (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
          K.carrier := by
  have hn := (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.naturality
    K.str.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [upperStar_map_counit_eq hj, openPieceFrobeniusCoeff]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]

/-- The image under `ι` of `δ₀` followed by the commutation of `ι` with the shift. -/
lemma exists_eq_map_comp_commShiftIso {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
    [HasShift D ℤ] {ι : C ⥤ D} (hι : ι.FullyFaithful) [ι.CommShift ℤ] {a c : C}
    (δ : ι.obj c ⟶ (shiftFunctor D (1 : ℤ)).obj (ι.obj a)) :
    ∃ δ₀ : c ⟶ (shiftFunctor C (1 : ℤ)).obj a,
      δ = ι.map δ₀ ≫ (ι.commShiftIso (1 : ℤ)).hom.app a :=
  ⟨hι.preimage (δ ≫ (ι.commShiftIso (1 : ℤ)).inv.app a), by simp⟩

variable (ℓ) in
/-- **The operators `E_Z`, `E_U` commute with the connecting morphism of the compactly supported
localization triangle** (blueprint `prop-trf-trace-additivity-open-closed`, Step 3). Write
`E_Z = RΓ_c(ψ_Z) ∘ Φ^♯` and `E_U = RΓ_c(ψ_U) ∘ Φ^♯` (`compactFrobeniusClosedPiece_eq`,
`compactFrobeniusOpenPiece_eq`) with Frobenius coefficients `ψ_Z`, `ψ_U` compatible with the unit
and counit of the localization triangle. By Hom vanishing these commute with the connecting
morphism `δ` on `X` (`map_comp_connecting_eq_of_isCompl`), and `Φ^♯` commutes with the shifts
(`commShift_compactPullback`). -/
theorem compactFrobenius_connecting_compat
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ)
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
                K.carrier))))
    (hδ : Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
            K.carrier))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            i).unit.app K.carrier)) δ ∈ distTriang _) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map (compactFrobeniusClosedPiece ℓ hi K) ≫
        compactLocalizationConnecting ℓ j i K.carrier δ =
      compactLocalizationConnecting ℓ j i K.carrier δ ≫ (shiftFunctor _ (1 : ℤ)).map
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (point k).left)).ι.map (compactFrobeniusOpenPiece ℓ hj K)) := by
  have hX := map_comp_connecting_eq_of_isCompl ℓ hcompl hj K.carrier δ hδ
    (openPieceFrobeniusCoeff ℓ hj K) K.str.hom (closedPieceFrobeniusCoeff ℓ hi K)
    (upperStar_map_counit_comp_str_hom hj K) (upperStar_map_unit_comp_closedPieceFrobeniusCoeff hi K)
  obtain ⟨δ₀, rfl⟩ := exists_eq_map_comp_commShiftIso
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).fullyFaithfulι δ
  rw [connectingOfIso_map_comp_commShiftIso, ← Functor.map_comp_assoc] at hX
  have key₁ := eq_comp_shift_map_of_map_comp_commShiftIso _ _ _ _ hX
  have key₂ := comp_map_comp_commShiftIso_eq_of_commShift
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ) (compactPullback ℓ Φ)
    (closedPieceFrobeniusCoeff ℓ hi K) (openPieceFrobeniusCoeff ℓ hj K) δ₀
    (key₁.trans (Category.assoc _ _ _))
    (compactFrobeniusClosedPiece ℓ hi K) (compactFrobeniusOpenPiece ℓ hj K)
    (compactFrobeniusClosedPiece_eq hi K) (compactFrobeniusOpenPiece_eq hj K)
  have := HasCompactification.of_over (toPoint X)
  rw [compactLocalizationConnecting, connectingOfIso_map_comp_commShiftIso]
  exact map_comp_commShiftIso_of_comp_eq _ _ _ _ key₂

/-- **Additivity of the compactly supported Frobenius along an open–closed decomposition**
(blueprint `prop-trf-trace-additivity-open-closed`, `sk-i-global-additivity`): for an open
immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X`, both stable under the Frobenius,
`tr(F_c | RΓ_c(X, K)) = tr(F_c | RΓ_c(U, K|_U)) + tr(F_c | RΓ_c(Z, K|_Z))`. -/
theorem trace_compactFrobenius_eq_add_of_isCompl [IsSepClosed k]
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ)
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)]
    [hU : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint U)).obj
        ((weilUpperStar ℓ ΦU Φ j hj).obj K).carrier)]
    [hZ : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).obj
        ((weilUpperStar ℓ ΦZ Φ i hi).obj K).carrier)] :
    trace K.compactFrobenius =
      trace ((weilUpperStar ℓ ΦU Φ j hj).obj K).compactFrobenius +
        trace ((weilUpperStar ℓ ΦZ Φ i hi).obj K).compactFrobenius := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openClosed ℓ j i hcompl K.carrier
  have h₁ := compactFrobeniusOpenPiece_comp_counit hj K
  have h₃ := compactFrobenius_connecting_compat ℓ hcompl hj hi K δ hδ
  let : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
            K.carrier))) :=
    @hasRightDualOfIso _ _ _ _ _ ((boundedConstructibleLowerShriekCompToPoint ℓ j).app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) hU
  let : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
            K.carrier))) :=
    @hasRightDualOfIso _ _ _ _ _ ((boundedConstructibleLowerStarCompToPoint ℓ i).app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) hZ
  let : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint U)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) := hU
  let : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) := hZ
  have hT := compactLocalizationTriangle_distinguished ℓ j i K.carrier δ hδ
  have h₂ := compactFrobenius_comp_compactUnit hi K
  dsimp only [Functor.comp_obj, Functor.id_obj] at hT h₁ h₂ h₃
  rw [trace_eq_trace_add_trace_of_distTriang _ _ _ hT _ _ _ h₁ h₂ h₃]
  congr 1
  · let w : (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) ≅
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint U)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier) :=
      (boundedConstructibleLowerShriekCompToPoint ℓ j).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)
    refine trace_eq_of_iso w _ _ ?_
    simp only [w, compactFrobeniusOpenPiece, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  · let w : (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) ≅
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) :=
      (boundedConstructibleLowerStarCompToPoint ℓ i).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)
    refine trace_eq_of_iso w _ _ ?_
    rw [compactFrobenius_weilUpperStar hi K]
    simp only [w, compactFrobeniusClosedPiece, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id]

end WeilBoundedConstructible

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
