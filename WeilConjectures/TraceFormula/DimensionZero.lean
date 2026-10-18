/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ModelDegreeOne
public import WeilConjectures.TraceFormula.ModelDecomposition

/-!

# The trace formula in dimension zero

This file proves the degree one trace formula over the base point `Spec k₀` and over the empty
scheme (blueprint `sk-thm-trace-formula`, Step 1), from which the trace formula for finite models
follows through the induction of `WeilConjectures.TraceFormula.Induction`.

For the point `Z₀ = Spec k₀`, embedded as the origin of the affine line `𝔸¹_{k₀}` with open
complement `𝔾_m`, both of which are smooth curves, the trace formula on `𝔸¹` and on `𝔾_m`
(`modelTraceFormula_of_smoothOfRelativeDimension_one`) gives, by additivity of the compactly
supported Frobenius (`WeilBoundedConstructible.trace_compactFrobenius_eq_add`), the trace formula
for the restrictions to the origin of Weil objects on `𝔸¹`
(`WeilBoundedConstructible.traceFormulaOne_of_isCompl_left`); every Weil object on the origin is
such a restriction, of its pullback along the retraction `𝔸¹ ⟶ Spec k₀`
(`WeilBoundedConstructible.weilUpperStarRetractionIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

namespace WeilBoundedConstructible

/-! ### Restriction along a retraction -/

/-- The coherence behind `weilUpperStarRetractionIso`, for an abstract family of pullback
functors. -/
lemma weilUpperStar_retraction_aux {𝒞 : Type*} [Category 𝒞] {Z X : 𝒞} {DZ DX : Type*}
    [Category DZ] [Category DX]
    (FZZ : (Z ⟶ Z) → DZ ⥤ DZ) (FZX : (Z ⟶ X) → DX ⥤ DZ) (FXZ : (X ⟶ Z) → DZ ⥤ DX)
    (FXX : (X ⟶ X) → DX ⥤ DX)
    (cZZX : ∀ (a : Z ⟶ Z) (b : Z ⟶ X), FZX (a ≫ b) ≅ FZX b ⋙ FZZ a)
    (cZXX : ∀ (a : Z ⟶ X) (b : X ⟶ X), FZX (a ≫ b) ≅ FXX b ⋙ FZX a)
    (cZXZ : ∀ (a : Z ⟶ X) (b : X ⟶ Z), FZZ (a ≫ b) ≅ FXZ b ⋙ FZX a)
    (cXXZ : ∀ (a : X ⟶ X) (b : X ⟶ Z), FXZ (a ≫ b) ≅ FXZ b ⋙ FXX a)
    (cXZZ : ∀ (a : X ⟶ Z) (b : Z ⟶ Z), FXZ (a ≫ b) ≅ FZZ b ⋙ FXZ a)
    (cZZZ : ∀ (a b : Z ⟶ Z), FZZ (a ≫ b) ≅ FZZ b ⋙ FZZ a)
    (ι : FZZ (𝟙 Z) ≅ 𝟭 DZ)
    (hidl : ∀ (b : Z ⟶ Z) (M : DZ), (cZZZ (𝟙 Z) b).hom.app M ≫ ι.hom.app ((FZZ b).obj M) =
      eqToHom (congrArg (fun a ↦ (FZZ a).obj M) (Category.id_comp b)))
    (hidr : ∀ (a : Z ⟶ Z) (M : DZ), (cZZZ a (𝟙 Z)).hom.app M ≫ (FZZ a).map (ι.hom.app M) =
      eqToHom (congrArg (fun f ↦ (FZZ f).obj M) (Category.comp_id a)))
    (A1 : ∀ (a : Z ⟶ Z) (b : Z ⟶ X) (c : X ⟶ Z) (M : DZ),
      (cZXZ (a ≫ b) c).hom.app M ≫ (cZZX a b).hom.app ((FXZ c).obj M) =
        eqToHom (congrArg (fun f ↦ (FZZ f).obj M) (Category.assoc a b c)) ≫
          (cZZZ a (b ≫ c)).hom.app M ≫ (FZZ a).map ((cZXZ b c).hom.app M))
    (A2 : ∀ (a : Z ⟶ X) (b : X ⟶ X) (c : X ⟶ Z) (M : DZ),
      (cZXZ (a ≫ b) c).hom.app M ≫ (cZXX a b).hom.app ((FXZ c).obj M) =
        eqToHom (congrArg (fun f ↦ (FZZ f).obj M) (Category.assoc a b c)) ≫
          (cZXZ a (b ≫ c)).hom.app M ≫ (FZX a).map ((cXXZ b c).hom.app M))
    (A3 : ∀ (a : Z ⟶ X) (b : X ⟶ Z) (c : Z ⟶ Z) (M : DZ),
      (cZZZ (a ≫ b) c).hom.app M ≫ (cZXZ a b).hom.app ((FZZ c).obj M) =
        eqToHom (congrArg (fun f ↦ (FZZ f).obj M) (Category.assoc a b c)) ≫
          (cZXZ a (b ≫ c)).hom.app M ≫ (FZX a).map ((cXZZ b c).hom.app M))
    {ΦZ : Z ⟶ Z} {ΦX : X ⟶ X} {i : Z ⟶ X} {ρ : X ⟶ Z} (hi : ΦZ ≫ i = i ≫ ΦX)
    (hρ : ΦX ≫ ρ = ρ ≫ ΦZ) (hiρ : i ≫ ρ = 𝟙 Z) (M : DZ) :
    (FZZ ΦZ).map ((cZXZ i ρ).inv.app M ≫ eqToHom (congrArg (fun a ↦ (FZZ a).obj M) hiρ) ≫
        ι.hom.app M) =
      ((cZZX ΦZ i).inv.app ((FXZ ρ).obj M) ≫
        eqToHom (congrArg (fun a ↦ (FZX a).obj ((FXZ ρ).obj M)) hi) ≫
        (cZXX i ΦX).hom.app ((FXZ ρ).obj M) ≫
        (FZX i).map ((cXXZ ΦX ρ).inv.app M ≫
          eqToHom (congrArg (fun a ↦ (FXZ a).obj M) hρ) ≫ (cXZZ ρ ΦZ).hom.app M)) ≫
      (cZXZ i ρ).inv.app ((FZZ ΦZ).obj M) ≫
        eqToHom (congrArg (fun a ↦ (FZZ a).obj ((FZZ ΦZ).obj M)) hiρ) ≫
        ι.hom.app ((FZZ ΦZ).obj M) := by
  have T1 (a b b' : Z ⟶ Z) (e : b = b') (N : DZ) : (cZZZ a b).hom.app N ≫
      (FZZ a).map (eqToHom (congrArg (fun f ↦ (FZZ f).obj N) e)) =
      eqToHom (congrArg (fun f ↦ (FZZ (a ≫ f)).obj N) e) ≫ (cZZZ a b').hom.app N := by
    subst e
    simp
  have T2 (a a' : Z ⟶ X) (e : a = a') (c : X ⟶ Z) (N : DZ) : (cZXZ a c).hom.app N ≫
      eqToHom (congrArg (fun f ↦ (FZX f).obj ((FXZ c).obj N)) e) =
      eqToHom (congrArg (fun f ↦ (FZZ (f ≫ c)).obj N) e) ≫ (cZXZ a' c).hom.app N := by
    subst e
    simp
  have T3 (a : Z ⟶ X) (b b' : X ⟶ Z) (e : b = b') (N : DZ) : (cZXZ a b).hom.app N ≫
      (FZX a).map (eqToHom (congrArg (fun f ↦ (FXZ f).obj N) e)) =
      eqToHom (congrArg (fun f ↦ (FZZ (a ≫ f)).obj N) e) ≫ (cZXZ a b').hom.app N := by
    subst e
    simp
  have T4 (a a' : Z ⟶ Z) (e : a = a') (c : Z ⟶ Z) (N : DZ) : (cZZZ a c).hom.app N ≫
      eqToHom (congrArg (fun f ↦ (FZZ f).obj ((FZZ c).obj N)) e) =
      eqToHom (congrArg (fun f ↦ (FZZ (f ≫ c)).obj N) e) ≫ (cZZZ a' c).hom.app N := by
    subst e
    simp
  rw [← cancel_epi ((cZXZ (ΦZ ≫ i) ρ).hom.app M ≫ (cZZX ΦZ i).hom.app ((FXZ ρ).obj M))]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (A1 ΦZ i ρ M), ← Functor.map_comp, Iso.hom_inv_id_app_assoc,
    Functor.map_comp, reassoc_of% (T1 ΦZ (i ≫ ρ) (𝟙 Z) hiρ M), hidr]
  rw [reassoc_of% (T2 _ _ hi ρ M), reassoc_of% (A2 i ΦX ρ M), ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app_assoc, Functor.map_comp_assoc, reassoc_of% (T3 i _ _ hρ M)]
  have A3' : (cZXZ i (ρ ≫ ΦZ)).hom.app M ≫ (FZX i).map ((cXZZ ρ ΦZ).hom.app M) =
      eqToHom (congrArg (fun f ↦ (FZZ f).obj M) (Category.assoc i ρ ΦZ)).symm ≫
        (cZZZ (i ≫ ρ) ΦZ).hom.app M ≫ (cZXZ i ρ).hom.app ((FZZ ΦZ).obj M) := by
    rw [A3, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% A3', Iso.hom_inv_id_app_assoc, reassoc_of% (T4 _ _ hiρ ΦZ M), hidl]
  simp

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- Naturality of the identification `L(i ≫ ρ)^* ≅ L(𝟙)^* ≅ 𝟭` for a retraction. -/
lemma weilUpperStar_retraction_nat_aux {𝒞 : Type*} [Category 𝒞] {Z : 𝒞} {D D' : Type*}
    [Category D] [Category D'] (L : (Z ⟶ Z) → D ⥤ D) (G₁ : D ⥤ D') (G₂ : D' ⥤ D) {a : Z ⟶ Z}
    (c : L a ≅ G₁ ⋙ G₂) (ha : a = 𝟙 Z) (ι : L (𝟙 Z) ≅ 𝟭 D) {M N : D} (φ : M ⟶ N) :
    G₂.map (G₁.map φ) ≫ c.inv.app N ≫ eqToHom (congrArg (fun b ↦ (L b).obj N) ha) ≫
        ι.hom.app N =
      c.inv.app M ≫ eqToHom (congrArg (fun b ↦ (L b).obj M) ha) ≫ ι.hom.app M ≫ φ := by
  subst ha
  have h₁ := c.inv.naturality φ
  have h₂ := ι.hom.naturality φ
  simp only [Functor.comp_map, Functor.id_map] at h₁ h₂
  simp only [eqToHom_refl, Category.id_comp]
  rw [reassoc_of% h₁, h₂]

variable {X Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The restriction along `i : Z ⟶ X` of the pullback of a Weil object `K` on `Z` along a
retraction `ρ : X ⟶ Z` of `i` is `K`. -/
noncomputable def weilUpperStarRetractionIso {ΦZ : Z ⟶ Z} {ΦX : X ⟶ X} {i : Z ⟶ X} {ρ : X ⟶ Z}
    (hi : ΦZ ≫ i = i ≫ ΦX) (hρ : ΦX ≫ ρ = ρ ≫ ΦZ) (hiρ : i ≫ ρ = 𝟙 Z)
    (K : WeilBoundedConstructible ℓ ΦZ) :
    (weilUpperStar ℓ ΦZ ΦX i hi).obj ((weilUpperStar ℓ ΦX ΦZ ρ hρ).obj K) ≅ K :=
  IsoAlgebra.isoMk (((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      i ρ).app K.carrier).symm ≪≫
    eqToIso (congrArg (fun a ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      a).obj K.carrier) hiρ) ≪≫
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Z).app K.carrier) (by
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, weilUpperStar_obj_str, weilUpperStar_obj_str]
    simp only [weilUpperStarComparison, boundedConstructiblePullbackSquareComparison,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
      eqToIso.inv, eqToIso.hom, NatTrans.comp_app, eqToHom_app, Category.assoc, Iso.app_inv,
      Functor.map_comp]
    have h := weilUpperStar_retraction_aux
      (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
      (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
      (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
      (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Z)
      (fun b M ↦ boundedConstructibleUpperStarComp_id_left_app _ ℓ b M)
      (fun a M ↦ boundedConstructibleUpperStarComp_id_right_app _ ℓ a M)
      (fun a b c M ↦ boundedConstructibleUpperStarComp_assoc_app _ ℓ a b c M)
      (fun a b c M ↦ boundedConstructibleUpperStarComp_assoc_app _ ℓ a b c M)
      (fun a b c M ↦ boundedConstructibleUpperStarComp_assoc_app _ ℓ a b c M) hi hρ hiρ K.carrier
    simp only [Functor.map_comp, Category.assoc] at h
    rw [reassoc_of% h, weilUpperStar_retraction_nat_aux
      (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)]
    rfl
    exact hiρ)

/-! ### Invariance and restrictions -/

/-- A right dual transported along an isomorphism. -/
def hasRightDualOfIso' {C : Type*} [Category C] [MonoidalCategory C] {A B : C} (e : A ≅ B)
    [hB : HasRightDual B] : HasRightDual A where
  rightDual := Bᘁ
  exact := exactPairingCongrLeft e

/-- The degree one trace formula is invariant under isomorphisms of Weil objects. -/
lemma TraceFormulaOne.of_iso {Φ : X ⟶ X} [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left]
    {K K' : WeilBoundedConstructible ℓ Φ} (e : K ≅ K') (h : K.TraceFormulaOne) :
    K'.TraceFormulaOne := by
  intro _ iX' iS'
  let iX : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier) := hasRightDualOfIso'
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).mapIso
        ((IsoAlgebra.forget _).mapIso e)) (hB := iX')
  let iS (x : RationalPoint X) : HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier) :=
    hasRightDualOfIso' ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      x).mapIso ((IsoAlgebra.forget _).mapIso e)) (hB := iS' x)
  have h' := @h _ iX iS
  rw [← trace_compactFrobenius_eq_of_iso e, h']
  exact Finset.sum_congr rfl fun x _ ↦ trace_weilStalkFrobenius_eq_of_iso e x.1 x.2

/-- The stalk Frobenius of the restriction of a Weil object along `j : U ⟶ X` at a point `u`
fixed by `Φ_U` has the trace of the stalk Frobenius of the Weil object at `u ≫ j`. -/
lemma trace_weilStalkFrobenius_weilUpperStar {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] {Φ : X ⟶ X}
    {ΦU : U ⟶ U} {j : U ⟶ X} (hj : ΦU ≫ j = j ≫ Φ) (K : WeilBoundedConstructible ℓ Φ)
    (u : RationalPoint U) (hu : u ≫ ΦU = u)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ u).obj
      ((weilUpperStar ℓ ΦU Φ j hj).obj K).carrier)]
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (u ≫ j)).obj
      K.carrier)] :
    trace (((weilUpperStar ℓ ΦU Φ j hj).obj K).weilStalkFrobenius u hu) =
      trace (K.weilStalkFrobenius (u ≫ j) (by rw [Category.assoc, ← hj, ← Category.assoc, hu])) := by
  have hu1 : u ≫ frobeniusIterate ΦU 1 = u := by
    rw [frobeniusIterate_one]
    exact hu
  rw [← trace_stalkFrobenius_one _ u hu1 hu, trace_stalkFrobenius_weilUpperStar,
    trace_stalkFrobenius_one]

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
