/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.TraceFormula.CompactCohomology

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
theorem trace_eq_trace_add_trace_of_distTriang
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
    trace v₂ = trace v₁ + trace v₃ :=
  sorry

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

variable (ℓ) in
/-- **Unfinished gap of this proof** (blueprint `prop-trf-trace-additivity-open-closed`, Steps 2(a)
and 3), for the open piece: the conjugate `E_U` of the compactly supported Frobenius of `K|_U`
commutes with `RΓ_c(ε)` for the counit `ε : Rj_! Lj^* K ⟶ K`, and the operators `E_Z`, `E_U`
commute with the connecting morphism of the compactly supported localization triangle (for any
localization triangle; its connecting morphism is unique by the Hom vanishing of blueprint
`prop-sf-open-closed-triangle-all-stages`).

This is not an input from another subsection but a gap of this proof, left open for two reasons:

* the first square relates the identification `Rj_! ≅ j_!` of the open immersion (through which
  the counit `ε` is defined) with the composition isomorphisms and the compact-support base change
  `Ex_!` along `j` entering the Frobenius comparison `θ` of `Ra_{X!}`; both are comparisons of
  the lower shriek attached to different compactifications, and their compatibility is
  compactification coherence, for which there is no API yet;
* the square with the connecting morphism needs the Frobenius comparison `θ` (built from the
  compact-support base change, the unit of `LΦ^* ⊣ RΦ_*`, `RΦ_! ≅ RΦ_*` and composition
  isomorphisms on `Dᵇc`) to commute with the shifts of the ambient derived categories, for which
  there is no shift-compatibility API for these functors on `Dᵇc`. -/
theorem compactFrobenius_openPiece_compat
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
    compactFrobeniusOpenPiece ℓ hj K ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
            K.carrier) =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
            K.carrier) ≫ K.compactFrobenius ∧
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map (compactFrobeniusClosedPiece ℓ hi K) ≫
        compactLocalizationConnecting ℓ j i K.carrier δ =
      compactLocalizationConnecting ℓ j i K.carrier δ ≫ (shiftFunctor _ (1 : ℤ)).map
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (point k).left)).ι.map (compactFrobeniusOpenPiece ℓ hj K)) :=
  sorry

/-- **Additivity of the compactly supported Frobenius along an open–closed decomposition**
(blueprint `prop-trf-trace-additivity-open-closed`, `sk-i-global-additivity`): for an open
immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X`, both stable under the Frobenius,
`tr(F_c | RΓ_c(X, K)) = tr(F_c | RΓ_c(U, K|_U)) + tr(F_c | RΓ_c(Z, K|_Z))`. -/
theorem trace_compactFrobenius_eq_add_of_isCompl
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
  obtain ⟨h₁, h₃⟩ := compactFrobenius_openPiece_compat ℓ hj hi K δ hδ
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
