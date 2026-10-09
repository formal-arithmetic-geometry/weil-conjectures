/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom

/-!
# Morphisms of finite free `ℚ̄_ℓ,V`-modules as matrices of functions

An endomorphism `ψ` of the unit module `ℚ̄_ℓ,V` is multiplication by the locally finite continuous
function `AlgebraicGeometry.ProEtale.AdicSheaf.unitEndFun ψ` on `V`, the image of `1`
(`AlgebraicGeometry.ProEtale.adicConstantSheaf_app_eq_mul`); conversely every such function `a`
gives the endomorphism `AlgebraicGeometry.ProEtale.AdicSheaf.unitMul a`. Composition corresponds to
multiplication. Consequently a morphism `ℚ̄_ℓ,Vⁿ ⟶ ℚ̄_ℓ,Vᵐ` is the same as an `m × n` matrix of
functions (`AlgebraicGeometry.ProEtale.AdicSheaf.unitMatrix`,
`AlgebraicGeometry.ProEtale.AdicSheaf.ofUnitMatrix`), compatibly with composition.

For a weakly étale `g : W ⟶ V`, pulling back an endomorphism of `ℚ̄_ℓ,V` pulls back its function
along `g` (`AlgebraicGeometry.ProEtale.adicConstantSheafEndFun_adicUpperStar`): on sections the
comparison `g^* ℚ̄_ℓ,V ≅ ℚ̄_ℓ,W` is the identity (`AlgebraicGeometry.ProEtale.
upperStarIsoLocalizationRestriction_inv_app_comp_adicUpperStarUnitIso`).
-/

@[expose] public section

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T : Type*} [TopologicalSpace T]

/-- Evaluation of locally finite functions at a point. -/
noncomputable def locallyFiniteFunctionsEval (t : T) :
    locallyFiniteFunctions l T →+* PadicAlgCl l where
  toFun f := f.1 t
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma locallyFiniteFunctionsEval_apply (t : T) (f : locallyFiniteFunctions l T) :
    locallyFiniteFunctionsEval t f = f.1 t :=
  rfl

/-- A nowhere vanishing locally finite function is invertible. -/
lemma isUnit_of_forall_ne_zero (f : locallyFiniteFunctions l T) (hf : ∀ t, f.1 t ≠ 0) :
    IsUnit f := by
  have hc : Continuous fun t ↦ (f.1 t)⁻¹ := f.1.continuous.inv₀ hf
  let g : C(T, PadicAlgCl l) := ⟨fun t ↦ (f.1 t)⁻¹, hc⟩
  have hg : g ∈ locallyFiniteFunctions l T := by
    intro x
    obtain ⟨U, hU, hfU⟩ := f.2 x
    refine ⟨U, hU, ?_⟩
    obtain ⟨S, hS⟩ := Module.Finite.iff_fg.1 hfU
    let E := IntermediateField.adjoin ℚ_[l] (S : Set (PadicAlgCl l))
    have : FiniteDimensional ℚ_[l] E := IntermediateField.finiteDimensional_adjoin
      fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hfE : ∀ y ∈ U, f.1 y ∈ E := fun y hy ↦ by
      have : f.1 y ∈ Submodule.span ℚ_[l] (S : Set (PadicAlgCl l)) := by
        rw [hS]; exact Submodule.subset_span ⟨y, hy, rfl⟩
      exact (Submodule.span_le (p := Subalgebra.toSubmodule E.toSubalgebra)).2
        (fun z hz ↦ IntermediateField.subset_adjoin _ _ hz) this
    refine Submodule.finiteDimensional_of_le (S₂ := Subalgebra.toSubmodule E.toSubalgebra) ?_
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact E.inv_mem (hfE y hy)
  have h1 : f * ⟨g, hg⟩ = 1 := Subtype.ext (ContinuousMap.ext fun t ↦ mul_inv_cancel₀ (hf t))
  exact ⟨⟨f, ⟨g, hg⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end PadicAlgCl

open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal

universe u

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {V : Scheme.{u}}

/-- A `ℚ̄_ℓ,V`-linear endomorphism of `ℚ̄_ℓ,V` is multiplication by the image of `1`. -/
lemma adicConstantSheaf_app_eq_mul (f : adicConstantSheaf l V ⟶ adicConstantSheaf l V)
    (hf : (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ f =
      adicConstantSheaf l V ◁ f ≫ MonObj.mul) (U : V.ProEtᵒᵖ)
    (s : (adicConstantSheaf l V).obj.obj U) :
    f.hom.app U s = ULift.up (s.down * (f.hom.app U (ULift.up 1)).down) := by
  have h2 := congrArg (fun g ↦ μ (sheafToPresheaf _ _) (adicConstantSheaf l V)
    (adicConstantSheaf l V) ≫ (sheafToPresheaf _ _).map g) hf
  simp only [Functor.map_comp] at h2
  rw [← μ_natural_right_assoc, ← Category.assoc, adicConstantSheaf_μ_comp_map_mul'] at h2
  have h3 := congrArg (fun g ↦ g.app U (s ⊗ₜ (ULift.up 1 : (adicConstantSheaf l V).obj.obj U))) h2
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h3
  erw [adicConstantSheaf_mul_app_tmul, adicConstantSheaf_mul_app_tmul] at h3
  simp only [mul_one] at h3
  exact h3

/-- The terminal object `V ⟶ V` of the small pro-étale site of `V`. -/
noncomputable abbrev proEtTop (V : Scheme.{u}) : V.ProEt := Scheme.ProEt.mk (𝟙 V)

/-- The morphism from any object of the pro-étale site of `V` to `proEtTop V`. -/
noncomputable def toProEtTop (U : V.ProEt) : U ⟶ proEtTop V :=
  MorphismProperty.Over.homMk U.hom (Category.comp_id _)

/-- The function on `V` corresponding to an endomorphism `f` of `ℚ̄_ℓ,V`: the image of `1`. -/
noncomputable def adicConstantSheafEndFun (f : adicConstantSheaf l V ⟶ adicConstantSheaf l V) :
    PadicAlgCl.locallyFiniteFunctions l V :=
  (f.hom.app (op (proEtTop V)) (ULift.up 1)).down

lemma adicConstantSheaf_app_one (f : adicConstantSheaf l V ⟶ adicConstantSheaf l V)
    (U : V.ProEt) :
    f.hom.app (op U) (ULift.up 1) = ULift.up (PadicAlgCl.locallyFiniteFunctionsComp l
      U.hom.base.hom (adicConstantSheafEndFun f)) := by
  have h := NatTrans.naturality_apply f.hom (toProEtTop U).op
    (ULift.up 1 : (adicConstantSheaf l V).obj.obj (op (proEtTop V)))
  have h1 : (adicConstantSheaf l V).obj.map (toProEtTop U).op
      (ULift.up 1 : (adicConstantSheaf l V).obj.obj (op (proEtTop V))) = ULift.up 1 := rfl
  rw [h1] at h
  rw [h]
  rfl

/-- `ℚ̄_ℓ,V`-linear endomorphisms of `ℚ̄_ℓ,V` are determined by their function. -/
lemma adicConstantSheaf_end_ext {f g : adicConstantSheaf l V ⟶ adicConstantSheaf l V}
    (hf : (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ f =
      adicConstantSheaf l V ◁ f ≫ MonObj.mul)
    (hg : (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ g =
      adicConstantSheaf l V ◁ g ≫ MonObj.mul)
    (h : adicConstantSheafEndFun f = adicConstantSheafEndFun g) : f = g := by
  apply Sheaf.hom_ext
  ext U s
  rw [adicConstantSheaf_app_eq_mul f hf, adicConstantSheaf_app_eq_mul g hg,
    adicConstantSheaf_app_one, adicConstantSheaf_app_one, h]

lemma adicConstantSheafEndFun_comp (f g : adicConstantSheaf l V ⟶ adicConstantSheaf l V)
    (hg : (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ g =
      adicConstantSheaf l V ◁ g ≫ MonObj.mul) :
    adicConstantSheafEndFun (f ≫ g) = adicConstantSheafEndFun f * adicConstantSheafEndFun g := by
  change ((g.hom.app _) (f.hom.app _ (ULift.up 1))).down = _
  rw [adicConstantSheaf_app_eq_mul g hg]
  rfl

/-- The product of a function `s` on `T` with the pullback of a function `a` on `V` along
`g : T ⟶ V`. -/
noncomputable def mulPullback {T : Scheme.{u}} (s : PadicAlgCl.locallyFiniteFunctions l T)
    (g : T ⟶ V) (a : PadicAlgCl.locallyFiniteFunctions l V) :
    PadicAlgCl.locallyFiniteFunctions l T :=
  s * PadicAlgCl.locallyFiniteFunctionsComp l g.base.hom a

/-- Multiplication by a locally finite function `a` on `V`, an endomorphism of `ℚ̄_ℓ,V`. -/
noncomputable def adicConstantSheafMul (a : PadicAlgCl.locallyFiniteFunctions l V) :
    adicConstantSheaf l V ⟶ adicConstantSheaf l V :=
  ⟨{ app U := ModuleCat.ofHom
      { toFun s := ULift.up (mulPullback (T := U.unop.left) s.down U.unop.hom a)
        map_add' s t := by
          exact congrArg ULift.up (add_mul _ _ _)
        map_smul' r s := by
          exact congrArg ULift.up (smul_mul_assoc _ _ _) }
     naturality U U' g := by
       ext s
       refine ULift.ext _ _ (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
       change s.down.1 (g.unop.left x) * a.1 (U'.unop.hom x) =
         s.down.1 (g.unop.left x) * a.1 (U.unop.hom (g.unop.left x))
       congr 1
       exact congrArg a.1 (by rw [← MorphismProperty.Over.w g.unop]; rfl) }⟩

lemma adicConstantSheafMul_app (a : PadicAlgCl.locallyFiniteFunctions l V) (U : V.ProEtᵒᵖ)
    (s : (adicConstantSheaf l V).obj.obj U) :
    (adicConstantSheafMul a).hom.app U s =
      ULift.up (mulPullback (T := U.unop.left) s.down U.unop.hom a) :=
  rfl

lemma adicConstantSheafEndFun_mul (a : PadicAlgCl.locallyFiniteFunctions l V) :
    adicConstantSheafEndFun (adicConstantSheafMul a) = a := by
  change 1 * _ = a
  rw [one_mul]
  rfl

lemma adicConstantSheafMul_linear (a : PadicAlgCl.locallyFiniteFunctions l V) :
    (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ adicConstantSheafMul a =
      adicConstantSheaf l V ◁ adicConstantSheafMul a ≫ MonObj.mul := by
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, Functor.map_comp, ← μ_natural_right_assoc, ← Category.assoc,
    adicConstantSheaf_μ_comp_map_mul']
  ext U : 2
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change ULift.up ((s.down * t.down) * _) = ULift.up (s.down * (t.down * _))
  rw [mul_assoc]

section Restriction

variable {W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)

lemma localizationRestriction_adicConstantSheaf :
    (localizationRestriction (WeilCoefficients.{u} l) g hg).obj (adicConstantSheaf l V) =
      adicConstantSheaf l W :=
  rfl

/-- For a weakly étale `g`, the comparison `g^* ℚ̄_ℓ,V ≅ ℚ̄_ℓ,W`, seen on the restriction, is the
identity. -/
lemma upperStarIsoLocalizationRestriction_inv_app_comp_adicUpperStarUnitIso :
    (upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) g hg).inv.app
        (adicConstantSheaf l V) ≫ (adicUpperStarUnitIso l g).hom.hom =
      eqToHom (localizationRestriction_adicConstantSheaf g hg) := by
  let adj1 := upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g
  let adj2 := localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) g hg
  have key (k : (localizationRestriction (WeilCoefficients.{u} l) g hg).obj
      (adicConstantSheaf l V) ⟶ adicConstantSheaf l W) :
      adj2.homEquiv _ _ k = adj1.homEquiv _ _
        ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) g hg).hom.app _ ≫ k) := by
    rw [adj1.homEquiv_naturality_right, Adjunction.homEquiv_unit]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  apply (adj2.homEquiv _ _).injective
  erw [key, Iso.hom_inv_id_app_assoc]
  simp only [adicUpperStarUnitIso, Mod.regularIsoOfIsIso_hom_hom]
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  ext U s
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  erw [localizationRestrictionLowerStarAdjunction_unit_app_hom_app]
  rfl

lemma adicUpperStarUnitIso_hom_hom_eq :
    (adicUpperStarUnitIso l g).hom.hom =
      (upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) g hg).hom.app
        (adicConstantSheaf l V) := by
  rw [← Iso.hom_inv_id_app_assoc (upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l)
    g hg) (adicConstantSheaf l V) (adicUpperStarUnitIso l g).hom.hom,
    upperStarIsoLocalizationRestriction_inv_app_comp_adicUpperStarUnitIso, eqToHom_refl,
    Category.comp_id]

include hg in
/-- The function of the pullback of an endomorphism of `ℚ̄_ℓ,V` along a weakly étale `g` is the
pullback of its function. -/
lemma adicConstantSheafEndFun_adicUpperStar (ψ : AdicSheaf.unit l V ⟶ AdicSheaf.unit l V) :
    adicConstantSheafEndFun ((adicUpperStarUnitIso l g).inv ≫ (g)^*ᵃ[l].map ψ ≫
      (adicUpperStarUnitIso l g).hom).hom =
      PadicAlgCl.locallyFiniteFunctionsComp l g.base.hom (adicConstantSheafEndFun ψ.hom) := by
  let e := upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) g hg
  let f : adicConstantSheaf l V ⟶ adicConstantSheaf l V := ψ.hom
  have h1 : ((adicUpperStarUnitIso l g).inv ≫ (g)^*ᵃ[l].map ψ ≫
      (adicUpperStarUnitIso l g).hom).hom =
      (localizationRestriction (WeilCoefficients.{u} l) g hg).map f := by
    have h0 : (adicUpperStarUnitIso l g).hom.hom ≫ ((adicUpperStarUnitIso l g).inv ≫
        (g)^*ᵃ[l].map ψ ≫ (adicUpperStarUnitIso l g).hom).hom =
        ((g)^*ᵃ[l].map ψ).hom ≫ (adicUpperStarUnitIso l g).hom.hom :=
      congrArg (fun k ↦ k.hom) (Iso.hom_inv_id_assoc (adicUpperStarUnitIso l g)
        ((g)^*ᵃ[l].map ψ ≫ (adicUpperStarUnitIso l g).hom))
    rw [adicUpperStarUnitIso_hom_hom_eq g hg] at h0
    rw [← cancel_epi (e.hom.app (adicConstantSheaf l V))]
    refine h0.trans ?_
    exact e.hom.naturality f
  rw [h1]
  change ((f.hom.app _) (ULift.up 1)).down = _
  erw [adicConstantSheaf_app_one]
  rfl

end Restriction

namespace AdicSheaf

/-- The function on `V` of an endomorphism of the unit `ℚ̄_ℓ,V`-module. -/
noncomputable def unitEndFun (ψ : unit l V ⟶ unit l V) : PadicAlgCl.locallyFiniteFunctions l V :=
  adicConstantSheafEndFun ψ.hom

lemma unit_hom_linear (ψ : unit l V ⟶ unit l V) :
    (MonObj.mul : adicConstantSheaf l V ⊗ adicConstantSheaf l V ⟶ _) ≫ ψ.hom =
      adicConstantSheaf l V ◁ ψ.hom ≫ MonObj.mul :=
  IsModHom.smul_hom (A := adicConstantSheaf l V) (f := ψ.hom)

lemma unitEndFun_injective : Function.Injective (unitEndFun (l := l) (V := V)) :=
  fun ψ ψ' h ↦ Mod.hom_ext _ _ (adicConstantSheaf_end_ext (unit_hom_linear ψ)
    (unit_hom_linear ψ') h)

lemma unitEndFun_comp (ψ ψ' : unit l V ⟶ unit l V) :
    unitEndFun (ψ ≫ ψ') = unitEndFun ψ * unitEndFun ψ' :=
  adicConstantSheafEndFun_comp ψ.hom ψ'.hom (unit_hom_linear ψ')

lemma unitEndFun_id : unitEndFun (𝟙 (unit l V)) = 1 :=
  rfl

lemma unitEndFun_add (ψ ψ' : unit l V ⟶ unit l V) :
    unitEndFun (ψ + ψ') = unitEndFun ψ + unitEndFun ψ' :=
  rfl

lemma unitEndFun_zero : unitEndFun (0 : unit l V ⟶ unit l V) = 0 :=
  rfl

/-- Multiplication by a locally finite function, an endomorphism of the unit module. -/
noncomputable def unitMul (a : PadicAlgCl.locallyFiniteFunctions l V) : unit l V ⟶ unit l V :=
  Mod.homMk (adicConstantSheafMul a) (adicConstantSheafMul_linear a)

lemma unitEndFun_unitMul (a : PadicAlgCl.locallyFiniteFunctions l V) :
    unitEndFun (unitMul a) = a :=
  adicConstantSheafEndFun_mul a

end AdicSheaf

namespace AdicSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

/-- The matrix of functions of a morphism between finite free `ℚ̄_ℓ,V`-modules. -/
noncomputable def unitMatrix (ψ : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V) :
    Matrix κ ι (PadicAlgCl.locallyFiniteFunctions l V) :=
  fun i j ↦ unitEndFun (biproduct.ι (fun _ : ι ↦ unit l V) j ≫ ψ ≫
    biproduct.π (fun _ : κ ↦ unit l V) i)

/-- `unitEndFun` as an additive map. -/
noncomputable def unitEndFunAddHom :
    (unit l V ⟶ unit l V) →+ PadicAlgCl.locallyFiniteFunctions l V where
  toFun := unitEndFun
  map_zero' := unitEndFun_zero
  map_add' := unitEndFun_add

lemma unitMatrix_comp (ψ : (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V)
    (ψ' : (⨁ fun _ : κ ↦ unit l V) ⟶ ⨁ fun _ : ν ↦ unit l V) :
    unitMatrix (ψ ≫ ψ') = unitMatrix ψ' * unitMatrix ψ := by
  refine Matrix.ext fun i j ↦ ?_
  have : biproduct.ι (fun _ : ι ↦ unit l V) j ≫ (ψ ≫ ψ') ≫ biproduct.π (fun _ : ν ↦ unit l V) i =
      ∑ k, (biproduct.ι (fun _ : ι ↦ unit l V) j ≫ ψ ≫ biproduct.π (fun _ : κ ↦ unit l V) k) ≫
        (biproduct.ι (fun _ : κ ↦ unit l V) k ≫ ψ' ≫ biproduct.π (fun _ : ν ↦ unit l V) i) := by
    simp only [Category.assoc, ← Preadditive.comp_sum]
    congr 2
    conv_lhs => rw [← Category.id_comp (ψ' ≫ _), ← biproduct.total, Preadditive.sum_comp]
    simp only [Category.assoc]
  rw [unitMatrix, this]
  change unitEndFunAddHom _ = _
  rw [map_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  change unitEndFun _ = _
  rw [unitEndFun_comp, mul_comm]
  rfl

lemma unitMatrix_id [DecidableEq ι] :
    unitMatrix (𝟙 (⨁ fun _ : ι ↦ unit l V)) = 1 := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [unitMatrix, Matrix.one_apply, Category.id_comp]
  by_cases h : i = j
  · subst h
    rw [biproduct.ι_π_self, if_pos rfl]
    rfl
  · rw [biproduct.ι_π_ne _ (Ne.symm h), if_neg h]
    rfl

lemma unitMatrix_injective :
    Function.Injective (unitMatrix (l := l) (V := V) (ι := ι) (κ := κ)) := by
  intro ψ ψ' h
  refine biproduct.hom_ext' _ _ fun j ↦ biproduct.hom_ext _ _ fun i ↦ ?_
  have := congrFun (congrFun h i) j
  simpa only [Category.assoc] using unitEndFun_injective this

/-- The morphism between finite free `ℚ̄_ℓ,V`-modules given by a matrix of functions. -/
noncomputable def ofUnitMatrix (N : Matrix κ ι (PadicAlgCl.locallyFiniteFunctions l V)) :
    (⨁ fun _ : ι ↦ unit l V) ⟶ ⨁ fun _ : κ ↦ unit l V :=
  biproduct.matrix fun j i ↦ unitMul (l := l) (V := V) (N i j)

lemma unitMatrix_ofUnitMatrix (N : Matrix κ ι (PadicAlgCl.locallyFiniteFunctions l V)) :
    unitMatrix (ofUnitMatrix N) = N := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [unitMatrix, ofUnitMatrix, biproduct.matrix_π, biproduct.ι_desc]
  exact unitEndFun_unitMul _

end AdicSheaf

end AlgebraicGeometry.ProEtale
