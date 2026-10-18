/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.TraceFormula.CompactPullback

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

/-! ### The ambient lower shriek is triangulated -/

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The derived lower shriek on the derived categories of module objects commutes with the
shifts: it is the composite of the functor induced by the exact extension by zero and a right
derived functor. -/
noncomputable instance : (R(f)_!⟦Λ⟧).CommShift ℤ := by
  unfold rightDerivedLowerShriek
  infer_instance

/-- The derived lower shriek on the derived categories of module objects is triangulated. -/
instance : (R(f)_!⟦Λ⟧).IsTriangulated := by
  unfold rightDerivedLowerShriek
  infer_instance

end Ambient

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

end AlgebraicGeometry.ProEtale.CondensedRing
