/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeIntegralSheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeRetract
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeConjugate
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeDescentMap
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.GLValues
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalizationRegular

/-!
# The rationalised lattice of an integral cocycle is a descent

Let `f : V ⟶ T` be a single-morphism pro-étale cover and `γ` a continuous integral cocycle on
`V ×_T V`. The extension of scalars `ℚ̄_ℓ ⊗ M` of the lattice `M` of `γ`
(`AlgebraicGeometry.integralCocycleLattice`) is trivialised over `V`, and it is the descent of
`ℚ̄_ℓ,Vᴺ` along the matrix `γ⁻¹`
(`AlgebraicGeometry.ProEtale.nonempty_iso_descentSheaf_integralCocycleLattice`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

variable {l : ℕ} [Fact l.Prime] {T V : Scheme.{u}} {f : V ⟶ T} {N : ℕ}
  {γ : ↥(pullback f f) → GL (Fin N) ℤ_[l]}

/-- An integral cocycle is inverted by the symmetry of `V ×_T V`. -/
lemma IsIntegralCocycle.apply_pullbackSymmetry (hγ : IsIntegralCocycle f γ)
    (z : ↥(pullback f f)) : γ ((pullbackSymmetry f f).hom.base z) = (γ z)⁻¹ := by
  let t : pullback f f ⟶ tripleProduct f :=
    pullback.lift (pullbackSymmetry f f).hom (𝟙 _) (by simp)
  have h₁₂ : t ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) =
      (pullbackSymmetry f f).hom := pullback.lift_fst _ _ _
  have h₂₃ : t ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have h₁₃ : t ≫ tripleProj₁₃ f = pullback.snd f f ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, h₁₂, Category.assoc,
        pullback.diagonal_fst, Category.comp_id, pullbackSymmetry_hom_comp_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, h₂₃, Category.id_comp,
        Category.assoc, pullback.diagonal_snd, Category.comp_id]
  have e₁₂ := congrArg (fun φ ↦ φ.base z) h₁₂
  have e₂₃ := congrArg (fun φ ↦ φ.base z) h₂₃
  have e₁₃ := congrArg (fun φ ↦ φ.base z) h₁₃
  simp only [Scheme.Hom.comp_apply] at e₁₂ e₂₃ e₁₃
  have := hγ.cocycle (t.base z)
  rw [e₁₃, e₁₂, e₂₃, hγ.diagonal] at this
  exact eq_inv_of_mul_eq_one_left this.symm

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

open PadicAlgCl AdicSheaf Scheme

variable {l : ℕ} [Fact l.Prime] {T V : Scheme.{u}} {f : V ⟶ T} {N : ℕ}
  {γ : ↥(pullback f f) → GL (Fin N) ℤ_[l]}

variable (l) in
/-- The matrix of locally finite functions `z ↦ γ(z)⁻¹` of an integral cocycle. -/
noncomputable def integralCocycleInvMatrix (hγ : IsIntegralCocycle f γ) :
    Matrix (Fin N) (Fin N) (locallyFiniteFunctions l ↥(pullback f f)) :=
  Matrix.of fun i j ↦ integralToLocallyFiniteFunctions l _
    ⟨fun z ↦ (((γ z)⁻¹ : GL (Fin N) ℤ_[l]) : Matrix (Fin N) (Fin N) ℤ_[l]) i j,
      hγ.continuous_inv i j⟩

/-- The values of `AlgebraicGeometry.ProEtale.integralCocycleInvMatrix`. -/
lemma integralCocycleInvMatrix_map_eval (hγ : IsIntegralCocycle f γ) (z : ↥(pullback f f)) :
    (integralCocycleInvMatrix l hγ).map (locallyFiniteFunctionsEval z) =
      (((γ z)⁻¹ : GL (Fin N) ℤ_[l]) : Matrix (Fin N) (Fin N) ℤ_[l]).map
        (padicIntToPadicAlgCl l) :=
  Matrix.ext fun _ _ ↦ rfl

/-- The matrix `γ⁻¹` is trivial on the diagonal. -/
lemma integralCocycleInvMatrix_map_diagonal (hγ : IsIntegralCocycle f γ) :
    (integralCocycleInvMatrix l hγ).map
      (locallyFiniteFunctionsComp l (pullback.diagonal f).base.hom) = 1 := by
  refine matrix_ext_locallyFiniteFunctionsEval fun v ↦ ?_
  rw [map_locallyFiniteFunctionsComp_map_eval, integralCocycleInvMatrix_map_eval]
  simp [hγ.diagonal, Matrix.map_one _ (map_zero _) (map_one _)]

/-- The cocycle condition for the matrix `γ⁻¹`. -/
lemma integralCocycleInvMatrix_map_tripleProj₁₃ (hγ : IsIntegralCocycle f γ) :
    (integralCocycleInvMatrix l hγ).map (locallyFiniteFunctionsComp l (tripleProj₁₃ f).base.hom) =
      (integralCocycleInvMatrix l hγ).map (locallyFiniteFunctionsComp l
        (pullback.snd (pullback.snd f f) (pullback.fst f f)).base.hom) *
      (integralCocycleInvMatrix l hγ).map (locallyFiniteFunctionsComp l
        (pullback.fst (pullback.snd f f) (pullback.fst f f)).base.hom) := by
  refine matrix_ext_locallyFiniteFunctionsEval fun w ↦ ?_
  rw [Matrix.map_mul, map_locallyFiniteFunctionsComp_map_eval,
    map_locallyFiniteFunctionsComp_map_eval, map_locallyFiniteFunctionsComp_map_eval,
    integralCocycleInvMatrix_map_eval, integralCocycleInvMatrix_map_eval,
    integralCocycleInvMatrix_map_eval, ← Matrix.map_mul, ← Units.val_mul, ← mul_inv_rev,
    ← hγ.cocycle]

section Descent

set_option maxHeartbeats 2000000 in
-- The kernel unfolds the composites of sheaf morphisms in the descent map.
/-- **A criterion for landing in a descent**: a morphism of abelian sheaves into `f_* ℚ̄_ℓ,Vⁿ`
whose sections satisfy `γ · ρ₁^* y = ρ₂^* y` is killed by the descent map of `γ`. -/
lemma comp_descentMap_eq_zero [WeaklyEtale f] {n : ℕ}
    (Γ : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l ↥(pullback f f)))
    {Z : Sheaf (ProEt.topology T) Ab.{u + 1}}
    (Φ : Z ⟶ ((AdicSheaf.restrictPadicInt T l).obj
      ((f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ AdicSheaf.unit l V))).X)
    (h : ∀ (T' : T.ProEt) (s : Z.obj.obj (op T')) (i : Fin n),
      ∑ j, locallyFiniteFunctionsComp l
          (pullback.snd T'.hom (pullback.fst f f ≫ f)).base.hom (Γ i j) *
        locallyFiniteFunctionsComp l (descentρ₁ f T').base.hom
          (comps (l := l) (B := V) (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T')
            (Φ.hom.app (op T') s) j) =
      locallyFiniteFunctionsComp l (descentρ₂ f T').base.hom
          (comps (l := l) (B := V) (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T')
            (Φ.hom.app (op T') s) i)) :
    Φ ≫ ((AdicSheaf.restrictPadicInt T l).map (descentMap f Γ)).hom = 0 := by
  ext T' s
  have key : ((Φ ≫ ((AdicSheaf.restrictPadicInt T l).map (descentMap f Γ)).hom).hom.app T') s =
      0 := by
    refine comps_injective (B := pullback f f) (n := n)
      (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (pullback.fst f f ≫ f)).obj T'.unop) ?_
    refine (comps_descentMap f Γ T'.unop (Φ.hom.app T' s)).trans ?_
    rw [comps_zero]
    funext i
    rw [h T'.unop s i, sub_self]
    rfl
  rw [key]
  simp

end Descent

section Triv

variable [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparated f]

/-- **The trivialisation of the rationalised lattice** of an integral cocycle over the cover:
`f^* (ℚ̄_ℓ ⊗ M) ≅ ℚ̄_ℓ ⊗ f^* M ≅ ℚ̄_ℓ ⊗ ℤ_ℓ,Vᴺ ≅ ℚ̄_ℓ,Vᴺ`. -/
noncomputable def integralCocycleLatticeTriv (hγ : IsIntegralCocycle f γ) :
    (f)^*ᵃ[l].obj ((adicSheafExtendScalars T l).obj (integralCocycleLattice l hγ)) ≅
      ⨁ fun _ : Fin N ↦ AdicSheaf.unit l V :=
  ((padicIntModUpperStarCompAdicSheafExtendScalarsIso l f).app _).symm ≪≫
    (adicSheafExtendScalars V l).mapIso (upperStarIntegralCocycleLatticeIso hγ) ≪≫
    (adicSheafExtendScalars V l).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ adicSheafExtendScalarsRegularIso l V

omit [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparated f] in
/-- The adjoint of `ℚ̄_ℓ ⊗ ℤ_ℓ,V ≅ ℚ̄_ℓ,V` is the inclusion `ℤ_ℓ,V ⟶ ℚ̄_ℓ,V`. -/
lemma homEquiv_adicSheafExtendScalarsRegularIso_hom :
    ((adicSheafExtendScalarsRestrictAdjunction V l).homEquiv _ _
      (adicSheafExtendScalarsRegularIso l V).hom).hom = padicIntSheafToAdicConstantSheaf V l := by
  rw [Adjunction.homEquiv_unit, Mod.comp_hom']
  exact adicSheafExtendScalarsUnitAb_regular_comp l V

/-- The morphism `ℚ̄_ℓ ⊗ ℤ_ℓ,Vᴺ ⟶ ℚ̄_ℓ,Vᴺ` of the trivialisation. -/
noncomputable abbrev regularBiproductTriv :
    (adicSheafExtendScalars V l).obj (⨁ fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l)) ⟶
      ⨁ fun _ : Fin N ↦ AdicSheaf.unit l V :=
  ((adicSheafExtendScalars V l).mapBiproduct _).hom ≫
    (biproduct.mapIso fun _ ↦ adicSheafExtendScalarsRegularIso l V).hom

/-- **The adjoint of the trivialisation, restricted to `ℤ_ℓ`-modules**, computed through the
conjugate isomorphism. -/
lemma homEquiv_homEquiv_integralCocycleLatticeTriv_hom (hγ : IsIntegralCocycle f γ) :
    (adicSheafExtendScalarsRestrictAdjunction T l).homEquiv _ _
      ((adicUpperStarLowerStarAdjunction l f).homEquiv _ _ (integralCocycleLatticeTriv hγ).hom) =
      (padicIntModUpperStarLowerStarAdjunction l f).homEquiv _ _
        ((upperStarIntegralCocycleLatticeIso hγ).hom ≫
          (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv _ _
            (regularBiproductTriv (l := l) (V := V) (N := N))) ≫
        (adicLowerStarRestrictPadicIntIso l f).inv.app _ := by
  rw [← Adjunction.homEquiv_naturality_left]
  exact Adjunction.homEquiv_homEquiv_pullIsoOfComapIso_inv
    (adicSheafExtendScalarsRestrictAdjunction V l) (adicSheafExtendScalarsRestrictAdjunction T l)
    (padicIntModUpperStarLowerStarAdjunction l f) (adicUpperStarLowerStarAdjunction l f)
    (adicLowerStarRestrictPadicIntIso l f) (integralCocycleLattice l hγ) _

omit [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparated f] in
/-- The components of the adjoint of `ℚ̄_ℓ ⊗ ℤ_ℓ,Vᴺ ≅ ℚ̄_ℓ,Vᴺ`. -/
lemma homEquiv_regularBiproductTriv_comp_π (j : Fin N) :
    (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv
        (⨁ fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l))
        (⨁ fun _ : Fin N ↦ AdicSheaf.unit l V)
        (regularBiproductTriv (l := l) (V := V) (N := N)) ≫
      (AdicSheaf.restrictPadicInt V l).map
        (biproduct.π (fun _ : Fin N ↦ AdicSheaf.unit l V) j) =
    biproduct.π (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l)) j ≫
      (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv
        (Mod.regular (padicIntAbSheaf V l)) (AdicSheaf.unit l V)
        (adicSheafExtendScalarsRegularIso l V).hom := by
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left,
    regularBiproductTriv, Category.assoc, biproduct.mapIso_hom, biproduct.map_π,
    Functor.mapBiproduct_hom, biproduct.lift_π_assoc]

/-- The components of the free pullback of the lattice, as abelian sheaves. -/
lemma upperStarIntegralCocycleLatticeIso_hom_hom_π (hγ : IsIntegralCocycle f γ) (j : Fin N) :
    (upperStarIntegralCocycleLatticeIso hγ).hom.hom ≫
        (biproduct.π (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l)) j).hom =
      (upperStarIntegralCocycleLatticeXIso hγ).hom ≫ biproduct.π _ j := by
  have e : (upperStarIntegralCocycleLatticeIso hγ).hom.hom =
      (upperStarIntegralCocycleLatticeXIso hγ).hom ≫ ((Mod.forget _).mapBiproduct
        (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l))).inv := rfl
  have h : ((Mod.forget _).mapBiproduct
      (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l))).hom ≫ biproduct.π _ j =
      (Mod.forget _).map (biproduct.π _ j) := biproduct.lift_π _ _
  have h' : ((Mod.forget _).mapBiproduct
      (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l))).inv ≫
        (biproduct.π (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l)) j).hom =
      biproduct.π _ j := by
    rw [Iso.inv_comp_eq]
    exact h.symm
  rw [e, Category.assoc, h']
  rfl

/-- **The components of the trivialisation on sections**: the `j`-th component of the image of a
section `z` of `f^* M` is the `j`-th coordinate of `z`, an integral function. -/
lemma comps_homEquiv_regularBiproductTriv (hγ : IsIntegralCocycle f γ) (U : V.ProEt)
    (z : ((padicIntModUpperStar l f).obj (integralCocycleLattice l hγ)).X.obj.obj (op U))
    (j : Fin N) :
    comps (l := l) (B := V) (Z := U)
      (((upperStarIntegralCocycleLatticeIso hγ).hom ≫
        (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv _ _
          (regularBiproductTriv (l := l) (V := V) (N := N))).hom.hom.app (op U) z) j =
      integralToLocallyFiniteFunctions l _
        (((upperStarIntegralCocycleLatticeXIso hγ).hom ≫ biproduct.π _ j).hom.app (op U) z).down
    := by
  have e : comps (l := l) (B := V) (Z := U)
      (((upperStarIntegralCocycleLatticeIso hγ).hom ≫
        (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv _ _
          (regularBiproductTriv (l := l) (V := V) (N := N))).hom.hom.app (op U) z) j =
      (((upperStarIntegralCocycleLatticeIso hγ).hom ≫
        (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv _ _
          (regularBiproductTriv (l := l) (V := V) (N := N)) ≫
        (AdicSheaf.restrictPadicInt V l).map
          (biproduct.π (fun _ : Fin N ↦ AdicSheaf.unit l V) j)).hom.hom.app (op U) z).down := rfl
  rw [e, homEquiv_regularBiproductTriv_comp_π, ← Category.assoc, Mod.comp_hom', Mod.comp_hom',
    upperStarIntegralCocycleLatticeIso_hom_hom_π, homEquiv_adicSheafExtendScalarsRegularIso_hom,
    padicIntSheafToAdicConstantSheaf_eq]
  rfl

/-- The adjoint of the trivialisation, restricted to `ℤ_ℓ`-modules, as a morphism of abelian
sheaves. -/
lemma homEquiv_comp_descentMap_hom (hγ : IsIntegralCocycle f γ) :
    ((adicSheafExtendScalarsRestrictAdjunction T l).homEquiv _ _
      ((adicUpperStarLowerStarAdjunction l f).homEquiv _ _ (integralCocycleLatticeTriv hγ).hom) ≫
      (AdicSheaf.restrictPadicInt T l).map (descentMap f (integralCocycleInvMatrix l hγ))).hom =
      0 := by
  rw [homEquiv_homEquiv_integralCocycleLatticeTriv_hom, Mod.comp_hom', Mod.comp_hom',
    padicIntModUpperStarLowerStarAdjunction]
  erw [Adjunction.modAdjunction_homEquiv_apply_hom]
  rw [Adjunction.homEquiv_unit]
  done

end Triv

end AlgebraicGeometry.ProEtale
