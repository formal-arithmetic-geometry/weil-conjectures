/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Fibration
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
      trace (K.weilStalkFrobenius (u ≫ j)
        (by rw [Category.assoc, ← hj, ← Category.assoc, hu])) := by
  have hu1 : u ≫ frobeniusIterate ΦU 1 = u := by
    rw [frobeniusIterate_one]
    exact hu
  rw [← trace_stalkFrobenius_one _ u hu1 hu, trace_stalkFrobenius_weilUpperStar,
    trace_stalkFrobenius_one]

/-! ### Subtracting an open piece -/

/-- **Additivity read backwards**: for an open subscheme `j : U ⟶ X` with closed complement
`i : Z ⟶ X`, both stable under the Frobenius, the degree one trace formula for a Weil object on
`X` and for its restriction to `U` gives the degree one trace formula for its restriction to
`Z`. -/
theorem traceFormulaOne_of_isCompl_left [IsSepClosed k] {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] {Φ : X ⟶ X}
    {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X} [IsOpenImmersion j.left]
    [IsClosedImmersion i.left] (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ)
    [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left]
    [IsUniversalHomeomorphism ΦU.left] [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]
    [Finite {u : RationalPoint U // u ≫ ΦU = u}] (hX : K.TraceFormulaOne)
    (hU : ((weilUpperStar ℓ ΦU Φ j hj).obj K).TraceFormulaOne) :
    ((weilUpperStar ℓ ΦZ Φ i hi).obj K).TraceFormulaOne := by
  classical
  intro _ _ _
  let eU : {u : RationalPoint U // u ≫ ΦU = u} ≃ FixedPoint ΦU 1 :=
    Equiv.subtypeEquivRight fun u ↦ by rw [frobeniusIterate_one]
  let eZ : {z : RationalPoint Z // z ≫ ΦZ = z} ≃ FixedPoint ΦZ 1 :=
    Equiv.subtypeEquivRight fun z ↦ by rw [frobeniusIterate_one]
  let eX : FixedPoint Φ 1 ≃ {x : RationalPoint X // x ≫ Φ = x} :=
    Equiv.subtypeEquivRight fun x ↦ by rw [frobeniusIterate_one]
  let e : {u : RationalPoint U // u ≫ ΦU = u} ⊕ {z : RationalPoint Z // z ≫ ΦZ = z} ≃
      {x : RationalPoint X // x ≫ Φ = x} :=
    (Equiv.sumCongr eU eZ).trans ((fixedPointSumEquiv hcompl hj hi 1).trans eX)
  let _ := Fintype.ofFinite {u : RationalPoint U // u ≫ ΦU = u}
  let _ : Fintype {x : RationalPoint X // x ≫ Φ = x} := Fintype.ofEquiv _ e
  let _ : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier) := (nonempty_hasRightDual_compactCohomology _).some
  let _ : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint U)).obj
        ((weilUpperStar ℓ ΦU Φ j hj).obj K).carrier) :=
    (nonempty_hasRightDual_compactCohomology _).some
  let _ (x : RationalPoint X) : HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier) :=
    (nonempty_hasRightDual_stalk _ x).some
  let _ (u : RationalPoint U) : HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ u).obj
        ((weilUpperStar ℓ ΦU Φ j hj).obj K).carrier) :=
    (nonempty_hasRightDual_stalk _ u).some
  have hXeq : trace K.compactFrobenius = ∑ x : {x : RationalPoint X // x ≫ Φ = x},
      trace (K.weilStalkFrobenius x.1 x.2) := hX
  have hUeq : trace ((weilUpperStar ℓ ΦU Φ j hj).obj K).compactFrobenius =
      ∑ u : {u : RationalPoint U // u ≫ ΦU = u},
        trace (((weilUpperStar ℓ ΦU Φ j hj).obj K).weilStalkFrobenius u.1 u.2) := hU
  have hadd := trace_compactFrobenius_eq_add hcompl hj hi K
  rw [hXeq, hUeq, ← e.sum_comp, Fintype.sum_sum_type] at hadd
  refine add_left_cancel (hadd.symm.trans ?_)
  congr 1
  · exact Finset.sum_congr rfl fun u _ ↦
      (trace_weilStalkFrobenius_weilUpperStar hj K u.1 u.2).symm
  · exact Finset.sum_congr rfl fun z _ ↦
      (trace_weilStalkFrobenius_weilUpperStar hi K z.1 z.2).symm

/-! ### Restriction along the identity and the empty scheme -/

/-- The restriction of a Weil object along the identity is the Weil object itself. -/
noncomputable def weilUpperStarIdIso {Φ : X ⟶ X} (h : Φ ≫ 𝟙 X = 𝟙 X ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) : (weilUpperStar ℓ Φ Φ (𝟙 X) h).obj K ≅ K :=
  IsoAlgebra.isoMk ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).app
      K.carrier) (by
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, weilUpperStar_obj_str]
    simp only [weilUpperStarComparison, boundedConstructiblePullbackSquareComparison,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
      eqToIso.inv, eqToIso.hom, NatTrans.comp_app, eqToHom_app, Category.assoc, Iso.app_inv]
    rw [← cancel_epi ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ Φ
      (𝟙 X)).hom.app K.carrier), Iso.hom_inv_id_app_assoc,
      reassoc_of% (boundedConstructibleUpperStarComp_id_right_app _ ℓ Φ K.carrier)]
    have h₂ := (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.naturality
      K.str.hom
    simp only [CategoryTheory.Functor.id_map] at h₂
    rw [h₂, reassoc_of% (boundedConstructibleUpperStarComp_id_left_app _ ℓ Φ K.carrier)]
    simp)

/-- **The degree one trace formula over the empty scheme**: by additivity along the decomposition
of the empty scheme into two copies of itself (`trace_compactFrobenius_eq_add`), the trace of the
compactly supported Frobenius is twice itself, hence zero, and there are no rational points. -/
theorem traceFormulaOne_of_isEmpty [IsSepClosed k] {Φ : X ⟶ X} [IsFinite Φ.left]
    [IsUniversalHomeomorphism Φ.left] [IsEmpty X.left] (K : WeilBoundedConstructible ℓ Φ) :
    K.TraceFormulaOne := by
  intro _ _ _
  have hΦ : Φ ≫ 𝟙 X = 𝟙 X ≫ Φ := by
    rw [Category.comp_id, Category.id_comp]
  have : IsOpenImmersion (𝟙 X : X ⟶ X).left := by
    rw [Over.id_left]
    infer_instance
  have : IsClosedImmersion (𝟙 X : X ⟶ X).left := by
    rw [Over.id_left]
    infer_instance
  let _ : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        ((weilUpperStar ℓ Φ Φ (𝟙 X) hΦ).obj K).carrier) :=
    (nonempty_hasRightDual_compactCohomology _).some
  have hadd := trace_compactFrobenius_eq_add
    ⟨Set.disjoint_left.2 fun x ↦ isEmptyElim x,
      codisjoint_iff.2 (Set.eq_univ_of_forall fun x ↦ isEmptyElim x)⟩ hΦ hΦ K
  rw [trace_compactFrobenius_eq_of_iso (weilUpperStarIdIso hΦ K)] at hadd
  have : IsEmpty {x : RationalPoint X // x ≫ Φ = x} :=
    ⟨fun x ↦ isEmptyElim (x.1.left.base (default : Spec (.of k)))⟩
  rw [Fintype.sum_empty]
  exact (add_right_cancel ((zero_add _).trans hadd)).symm

end WeilBoundedConstructible

/-! ### The base point and the empty scheme as models -/

section Model

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]

/-- The degree one trace formula over an empty model. -/
theorem modelTraceFormulaOne_of_isEmpty [IsAlgClosed k] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k₀)) [LocallyOfFiniteType f₀] [IsEmpty X₀] :
    ModelTraceFormulaOne ℓ (k := k) f₀ := by
  intro X _ _ _ Φ p hΦ K
  have : IsEmpty X.left := ⟨fun x ↦ isEmptyElim (p.base x)⟩
  intro _ _ _
  exact K.traceFormulaOne_of_isEmpty

variable (k₀) in
/-- The origin `Spec k₀ ⟶ 𝔸¹_{k₀}` of the affine line. -/
noncomputable def affineLineOrigin : Spec (.of k₀) ⟶ Spec (.of (MvPolynomial (Fin 1) k₀)) :=
  Spec.map (CommRingCat.ofHom MvPolynomial.constantCoeff)

omit [Finite k₀] in
@[reassoc (attr := simp)]
lemma affineLineOrigin_comp : affineLineOrigin k₀ ≫
    Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀))) = 𝟙 _ := by
  rw [affineLineOrigin, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

instance : IsClosedImmersion (affineLineOrigin k₀) :=
  isClosedImmersion_of_comp_eq_id _ _ affineLineOrigin_comp

variable (k₀) in
/-- The punctured affine line `𝔸¹_{k₀} ∖ {0}`, the open complement of the origin. -/
noncomputable def affineLinePunctured : (Spec (.of (MvPolynomial (Fin 1) k₀))).Opens :=
  ⟨(Set.range (affineLineOrigin k₀).base)ᶜ,
    (affineLineOrigin k₀).isClosedEmbedding.isClosed_range.isOpen_compl⟩

omit [Finite k₀] in
lemma isCompl_range_affineLinePunctured :
    IsCompl (Set.range (affineLinePunctured k₀).ι.base) (Set.range (affineLineOrigin k₀).base) := by
  rw [Scheme.Opens.range_ι]
  exact isCompl_compl.symm

instance : SmoothOfRelativeDimension 1 ((affineLinePunctured k₀).ι ≫
    Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀)))) := by
  have := smoothOfRelativeDimension_spec_mvPolynomial_fin_one (k₀ := k₀)
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- **The degree one trace formula over the base point** (blueprint `sk-thm-trace-formula`,
Step 1): a model of `Spec k₀` is a point `X`, embedded through its retraction as the origin
`i : X ⟶ 𝔸¹` of the base change of the affine line, with open complement the base change of the
punctured line. Every Weil object on `X` is the restriction along `i` of its pullback along the
retraction (`WeilBoundedConstructible.weilUpperStarRetractionIso`), and the trace formula for
the smooth curves `𝔸¹` and `𝔸¹ ∖ {0}` (`modelTraceFormula_of_smoothOfRelativeDimension_one`)
gives the trace formula on `X` (`WeilBoundedConstructible.traceFormulaOne_of_isCompl_left`). -/
theorem modelTraceFormulaOne_id [IsAlgClosed k] :
    ModelTraceFormulaOne ℓ (k := k) (𝟙 (Spec (.of k₀))) := by
  intro X _ _ _ Φ p hΦ K
  have := hΦ.isFinite_self
  have := hΦ.isUniversalHomeomorphism_self
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  obtain ⟨FA, hFA⟩ := Scheme.Hom.exists_isFrobenius
    (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀))))
  let A := stdModel k (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀))))
  let ΦA : A ⟶ A := stdModelFrobenius _ (hFA.comp_eq _)
  have hΦA : IsModelFrobenius ΦA
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀)))) (pullback.fst _ _) :=
    isModelFrobenius_stdModel (k := k) _ hFA
  have := hΦA.isFinite_self
  have := hΦA.isUniversalHomeomorphism_self
  have : IsIso X.hom := hΦ.isPullback.isIso_snd_of_isIso
  have hΦ1 : Φ = 𝟙 X := Over.OverMorphism.ext ((cancel_mono X.hom).1 (by simp))
  subst hΦ1
  have hp' : p ≫ F₀ = p := by
    rw [← hp, Over.id_left, Category.id_comp]
  let i : X ⟶ A := Over.homMk (pullback.lift (p ≫ affineLineOrigin k₀) X.hom (by
      rw [Category.assoc, affineLineOrigin_comp]
      exact hΦ.isPullback.w)) (pullback.lift_snd _ _ _)
  let ρ : A ⟶ X := Over.homMk (A.hom ≫ inv X.hom) (by simp)
  have hi : 𝟙 X ≫ i = i ≫ ΦA := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · simp [i, ΦA, stdModelFrobenius, hF₀.comp_eq_comp (𝟙 _) hFA (affineLineOrigin k₀),
        reassoc_of% hp']
    · simp [i, ΦA, stdModelFrobenius]
  have hρ : ΦA ≫ ρ = ρ ≫ 𝟙 X := Over.OverMorphism.ext (by simp [A, ρ, ΦA, stdModelFrobenius])
  have hiρ : i ≫ ρ = 𝟙 X := by
    refine Over.OverMorphism.ext ?_
    simp [A, i, ρ]
    rfl
  have : IsClosedImmersion i.left := by
    have hs : (inv X.hom ≫ i.left) ≫ A.hom = 𝟙 _ := by simp [A, i]
    have := isClosedImmersion_of_comp_eq_id _ _ hs
    rw [← IsIso.hom_inv_id_assoc X.hom i.left]
    infer_instance
  have hpA : ΦA.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ FA := by
    simp [ΦA, stdModelFrobenius]
  obtain ⟨FU, hFU⟩ := Scheme.Hom.exists_isFrobenius ((affineLinePunctured k₀).ι ≫
    Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀))))
  have hFUc : FU ≫ (affineLinePunctured k₀).ι = (affineLinePunctured k₀).ι ≫ FA :=
    (hFU.comp_eq_comp ((affineLinePunctured k₀).ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀)))) hFA _).symm
  have hΦU := IsModelFrobenius.baseChange (X := A) (Φ := ΦA) _ (affineLinePunctured k₀).ι hΦA
    hpA hFUc hFU
  have : LocallyOfFiniteType (modelBaseChange (X := A) (pullback.fst _ _)
      (affineLinePunctured k₀).ι).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _ ≫ A.hom))
  have : QuasiCompact (modelBaseChange (X := A) (pullback.fst _ _)
      (affineLinePunctured k₀).ι).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd _ _ ≫ A.hom))
  have : IsSeparated (modelBaseChange (X := A) (pullback.fst _ _)
      (affineLinePunctured k₀).ι).hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _ ≫ A.hom))
  have : IsOpenImmersion (modelBaseChangeHom (X := A) (pullback.fst _ _)
      (affineLinePunctured k₀).ι).left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd _ _))
  have := hΦU.isFinite_self
  have := hΦU.isUniversalHomeomorphism_self
  have := hΦU.finite_fixedPoint (m := 1) one_ne_zero
  have : Finite {u : RationalPoint (modelBaseChange (X := A) (pullback.fst _ _)
      (affineLinePunctured k₀).ι) // u ≫ modelBaseChangeEndo _ _ hpA hFUc = u} :=
    Finite.of_equiv (FixedPoint (modelBaseChangeEndo _ _ hpA hFUc) 1)
      (Equiv.subtypeEquivRight fun u ↦ by rw [frobeniusIterate_one])
  have hpb : IsPullback i.left p (pullback.fst _ _) (affineLineOrigin k₀) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) hΦA.isPullback.flip
    rw [Over.w i, affineLineOrigin_comp]
    exact hΦ.isPullback.flip
  have hrange : Set.range i.left.base =
      (pullback.fst _ _ : A.left ⟶ _).base ⁻¹' Set.range (affineLineOrigin k₀).base := by
    rw [← hpb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 (Scheme.Hom.surjective hpb.isoPullback.hom), Set.image_univ,
      Scheme.Pullback.range_fst]
    rfl
  have hrangeU : Set.range
      (modelBaseChangeHom (X := A) (pullback.fst _ _) (affineLinePunctured k₀).ι).left.base =
      (pullback.fst _ _ : A.left ⟶ _).base ⁻¹' Set.range (affineLinePunctured k₀).ι.base :=
    Scheme.Pullback.range_snd _ _
  have hcompl : IsCompl (Set.range (modelBaseChangeHom (X := A) (pullback.fst _ _)
      (affineLinePunctured k₀).ι).left.base) (Set.range i.left.base) := by
    rw [hrangeU, hrange]
    exact isCompl_range_affineLinePunctured.preimage _
  have := smoothOfRelativeDimension_spec_mvPolynomial_fin_one (k₀ := k₀)
  have hAK : ((weilUpperStar ℓ ΦA (𝟙 X) ρ hρ).obj K).TraceFormulaOne :=
    ModelTraceFormulaOne.of_modelTraceFormula
      (modelTraceFormula_of_smoothOfRelativeDimension_one (ℓ := ℓ) (k := k)
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀))))) A ΦA _ hΦA _
  have hUK : ((weilUpperStar ℓ (modelBaseChangeEndo _ _ hpA hFUc) ΦA _
      (modelBaseChangeEndo_comp _ _ hpA hFUc)).obj
        ((weilUpperStar ℓ ΦA (𝟙 X) ρ hρ).obj K)).TraceFormulaOne :=
    ModelTraceFormulaOne.of_modelTraceFormula
      (modelTraceFormula_of_smoothOfRelativeDimension_one (ℓ := ℓ) (k := k)
        ((affineLinePunctured k₀).ι ≫
          Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀))))) _ _ _ hΦU _
  intro _ _ _
  exact WeilBoundedConstructible.TraceFormulaOne.of_iso
    (WeilBoundedConstructible.weilUpperStarRetractionIso hi hρ hiρ K)
    (WeilBoundedConstructible.traceFormulaOne_of_isCompl_left hcompl
      (modelBaseChangeEndo_comp _ _ hpA hFUc) hi _ hAK hUK)

omit [Finite k₀] in
/-- A closed immersion into the spectrum of a field is an isomorphism or has empty source. -/
lemma isIso_or_isEmpty_of_isClosedImmersion {T : Scheme.{u}} (c : T ⟶ Spec (.of k₀))
    [IsClosedImmersion c] : IsIso c ∨ IsEmpty T := by
  rcases isEmpty_or_nonempty T with h | h
  · exact Or.inr h
  · have : Surjective c := ⟨fun _ ↦ ⟨h.some, Subsingleton.elim _ _⟩⟩
    exact Or.inl (isIso_of_isClosedImmersion_of_surjective c)

/-- **The degree one trace formula over a closed subscheme of the base point**, which is either
the base point (`modelTraceFormulaOne_id`) or empty (`modelTraceFormulaOne_of_isEmpty`). -/
theorem modelTraceFormulaOne_of_isClosedImmersion [IsAlgClosed k] {T : Scheme.{u}}
    (c : T ⟶ Spec (.of k₀)) [IsClosedImmersion c] : ModelTraceFormulaOne ℓ (k := k) c := by
  rcases isIso_or_isEmpty_of_isClosedImmersion c with h | h
  · exact ModelTraceFormulaOne.of_iso modelTraceFormulaOne_id (asIso c) (Category.comp_id c)
  · exact modelTraceFormulaOne_of_isEmpty c

end Model

end AlgebraicGeometry.ProEtale.CondensedRing
