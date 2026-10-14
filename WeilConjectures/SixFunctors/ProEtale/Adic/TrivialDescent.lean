/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.SheafGluing
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSection

/-!
# Descent of trivial `ℓ`-adic sheaves along pro-étale covers

Let `f : W ⟶ X` be weakly étale, surjective and quasi-compact, and `γ` a cocycle of matrices of
locally finite functions on `W ×_X W`. The sheaf `G` on `X` whose sections over `T` are the
columns `y` of locally finite functions on `T ×_X W` with `γ(w₁, w₂) y(t, w₁) = y(t, w₂)` is the
kernel of a morphism `f_* ℚ̄_ℓⁿ ⟶ (p₁ f)_* ℚ̄_ℓⁿ`. The adjoint `f^* G ⟶ ℚ̄_ℓⁿ` of the inclusion
is an isomorphism, computed on sections through the identification of `f^*` with restriction
along the localization functor: a section `y` restricts along the graph of `T ⟶ W` to
`y(t, a t)`, and conversely `c ↦ γ(a t, w) c(t)`. Its transition matrix is `γ`, by the kernel
condition, the composites of adjunctions computing the pullbacks of the trivialisation
(`AlgebraicGeometry.ProEtale.AdicSheaf.exists_iso_transitionMatrix_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

namespace AdicSheaf

section Components

variable {B : Scheme.{u}} {n : ℕ}

/-- The pullback of a function on `B` to an object `Z` of the pro-étale site of `B`. -/
noncomputable abbrev pullFun (Z : B.ProEt) (a : PadicAlgCl.locallyFiniteFunctions l B) :
    PadicAlgCl.locallyFiniteFunctions l Z.left :=
  PadicAlgCl.locallyFiniteFunctionsComp l Z.hom.base.hom a

/-- The components of a section of `ℚ̄_ℓ,Bⁿ` over `Z`: a column of locally finite functions. -/
noncomputable def comps {Z : B.ProEt} (x : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z)) :
    Fin n → PadicAlgCl.locallyFiniteFunctions l Z.left :=
  fun i ↦ ((biproduct.π (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z) x).down

/-- The sections of a sheaf of modules over `Z`, as an additive functor. -/
noncomputable abbrev sectionsFunctor (Z : B.ProEt) : AdicSheaf l B ⥤ WeilCoefficients.{u} l :=
  AdicSheaf.forget B ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op Z)

lemma sectionsFunctor_map_apply {Z : B.ProEt} {M N : AdicSheaf l B} (φ : M ⟶ N)
    (x : M.X.obj.obj (op Z)) : ((sectionsFunctor Z).map φ).hom x = φ.hom.hom.app (op Z) x :=
  rfl

/-- A section of `ℚ̄_ℓ,Bⁿ` is the sum of its components. -/
lemma eq_sum_comps {Z : B.ProEt} (x : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z)) :
    x = ∑ i, (biproduct.ι (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z)
      ((biproduct.π (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z) x) := by
  have e := congrArg (fun φ ↦ ((sectionsFunctor (l := l) Z).map φ).hom x)
    (biproduct.total (f := fun _ : Fin n ↦ unit l B))
  simp only [CategoryTheory.Functor.map_id, Functor.map_sum, ModuleCat.hom_sum,
    LinearMap.sum_apply, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  exact e.symm

/-- Sections of `ℚ̄_ℓ,Bⁿ` are determined by their components. -/
lemma comps_injective {Z : B.ProEt} :
    Function.Injective (comps (l := l) (B := B) (n := n) (Z := Z)) := by
  intro x x' h
  rw [eq_sum_comps x, eq_sum_comps x']
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact ULift.ext _ _ (congrFun h i)

/-- The section of `ℚ̄_ℓ,Bⁿ` over `Z` with given components. -/
noncomputable def ofComps {Z : B.ProEt} (c : Fin n → PadicAlgCl.locallyFiniteFunctions l Z.left) :
    (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z) :=
  ∑ i, (biproduct.ι (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z) (ULift.up (c i))

lemma comps_ofComps {Z : B.ProEt} (c : Fin n → PadicAlgCl.locallyFiniteFunctions l Z.left) :
    comps (ofComps (l := l) (B := B) c) = c := by
  classical
  funext j
  simp only [comps, ofComps, ← sectionsFunctor_map_apply, map_sum, ← ModuleCat.comp_apply,
    ← Functor.map_comp]
  rw [Finset.sum_eq_single j]
  · rw [biproduct.ι_π_self, CategoryTheory.Functor.map_id]
    rfl
  · intro i _ hij
    rw [biproduct.ι_π_ne _ hij, Functor.map_zero]
    rfl
  · simp

/-- Every column of functions is the components of a section. -/
lemma comps_surjective {Z : B.ProEt} :
    Function.Surjective (comps (l := l) (B := B) (n := n) (Z := Z)) :=
  fun c ↦ ⟨ofComps c, comps_ofComps c⟩

/-- The components of the restriction of a section are the pulled back components. -/
lemma comps_map {Z Z' : B.ProEt} (k : Z' ⟶ Z)
    (x : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z)) :
    comps ((⨁ fun _ : Fin n ↦ unit l B).X.obj.map k.op x) =
      fun i ↦ PadicAlgCl.locallyFiniteFunctionsComp l k.left.base.hom (comps x i) := by
  funext i
  have e := NatTrans.naturality_apply (biproduct.π (fun _ : Fin n ↦ unit l B) i).hom.hom k.op x
  simp only [comps]
  erw [e]
  rfl

/-- The components of the image of a section under a morphism of free modules. -/
lemma comps_app {Z : B.ProEt} (ψ : (⨁ fun _ : Fin n ↦ unit l B) ⟶ ⨁ fun _ : Fin n ↦ unit l B)
    (x : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z)) :
    comps (ψ.hom.hom.app (op Z) x) = fun i ↦ ∑ j,
      pullFun Z (unitMatrix ψ i j) * comps x j := by
  funext i
  conv_lhs => rw [eq_sum_comps x]
  simp only [comps, map_sum]
  rw [show ∀ (g : Fin n → ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l Z.left)),
    (∑ j, g j).down = ∑ j, (g j).down from fun g ↦ map_sum AddEquiv.ulift g _]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have e : (biproduct.π (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z) (ψ.hom.hom.app (op Z)
      ((biproduct.ι (fun _ : Fin n ↦ unit l B) j).hom.hom.app (op Z)
        ((biproduct.π (fun _ : Fin n ↦ unit l B) j).hom.hom.app (op Z) x))) =
      (biproduct.ι (fun _ : Fin n ↦ unit l B) j ≫ ψ ≫
        biproduct.π (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z)
          ((biproduct.π (fun _ : Fin n ↦ unit l B) j).hom.hom.app (op Z) x) := rfl
  erw [e, adicConstantSheaf_app_eq_mul _ (unit_hom_linear _), adicConstantSheaf_app_one]
  rw [mul_comm]
  rfl

end Components

section Pull

variable {W P : Scheme.{u}} (a : P ⟶ W) {n : ℕ}

/-- Pulling back functions along `a : P ⟶ W`, as a morphism of modules
`ℚ̄_ℓ,W ⟶ a_* ℚ̄_ℓ,P`. -/
noncomputable def toLowerStarUnit : unit l W ⟶ (a)_*ᵃ[l].obj (unit l P) :=
  (adicUpperStarLowerStarAdjunction l a).unit.app (unit l W) ≫
    (a)_*ᵃ[l].map (adicUpperStarUnitIso l a).hom

lemma toLowerStarUnit_hom : (toLowerStarUnit (l := l) a).hom = adicConstantSheafToLowerStar l a := by
  rw [toLowerStarUnit, Mod.comp_hom', adicLowerStar_map_hom, adicUpperStarLowerStarAdjunction,
    Adjunction.modAdjunction_unit_app_hom]
  simp only [adicUpperStarUnitIso, Mod.regularIsoOfIsIso_hom_hom]
  exact ((upperStarLowerStarAdjunction _ a).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- Pulling back columns of functions along `a : P ⟶ W`, as a morphism
`ℚ̄_ℓ,Wⁿ ⟶ a_* ℚ̄_ℓ,Pⁿ`: the adjoint of `a^* ℚ̄_ℓ,Wⁿ ≅ ℚ̄_ℓ,Pⁿ`. -/
noncomputable def freePull :
    (⨁ fun _ : Fin n ↦ unit l W) ⟶ (a)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l P) :=
  (adicUpperStarLowerStarAdjunction l a).unit.app _ ≫
    (a)_*ᵃ[l].map (freeUpperStarIso l (Fin n) a).hom

lemma freePull_eq : freePull (l := l) (n := n) a =
    (adicUpperStarLowerStarAdjunction l a).homEquiv _ _ (freeUpperStarIso l (Fin n) a).hom :=
  ((adicUpperStarLowerStarAdjunction l a).homEquiv_unit _ _ _).symm

lemma freePull_π (i : Fin n) :
    freePull (l := l) a ≫ (a)_*ᵃ[l].map (biproduct.π (fun _ : Fin n ↦ unit l P) i) =
      biproduct.π (fun _ : Fin n ↦ unit l W) i ≫ toLowerStarUnit a := by
  rw [freePull, Category.assoc, ← Functor.map_comp, freeUpperStarIso_hom_π, Functor.map_comp]
  have := (adicUpperStarLowerStarAdjunction l a).unit.naturality
    (biproduct.π (fun _ : Fin n ↦ unit l W) i)
  simp only [Functor.comp_map, Functor.id_map] at this
  rw [← Category.assoc]
  erw [← this]
  rw [Category.assoc]
  rfl

/-- **Pulling back columns of functions**, on sections. -/
lemma comps_freePull {Z : W.ProEt} (x : (⨁ fun _ : Fin n ↦ unit l W).X.obj.obj (op Z)) :
    comps (B := P) (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj Z)
      ((freePull (l := l) a).hom.hom.app (op Z) x) = fun i ↦
        PadicAlgCl.locallyFiniteFunctionsComp l (pullback.fst Z.hom a).base.hom (comps x i) := by
  funext i
  change ((freePull a ≫ (a)_*ᵃ[l].map (biproduct.π (fun _ : Fin n ↦ unit l P) i)).hom.hom.app
    (op Z) x).down = _
  rw [freePull_π, Mod.comp_hom', ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, toLowerStarUnit_hom]
  rfl

end Pull

section DescentMap

variable {X W : Scheme.{u}} (f : W ⟶ X) {n : ℕ}
  (γ : Matrix (Fin n) (Fin n) (PadicAlgCl.locallyFiniteFunctions l ↥(Limits.pullback f f)))

/-- The first half of the descent map, `y ↦ γ · p₁^* y`. -/
noncomputable def descentMapFst :
    (f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l W) ⟶
      (pullback.fst f f ≫ f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f)) :=
  (f)_*ᵃ[l].map (freePull (pullback.fst f f) ≫ (pullback.fst f f)_*ᵃ[l].map (ofUnitMatrix γ)) ≫
      (adicLowerStarComp l (pullback.fst f f) f).hom.app
        (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f))

/-- The second half of the descent map, `y ↦ p₂^* y`. -/
noncomputable def descentMapSnd :
    (f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l W) ⟶
      (pullback.fst f f ≫ f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f)) :=
  (f)_*ᵃ[l].map (freePull (pullback.snd f f)) ≫
      (adicLowerStarComp l (pullback.snd f f) f).hom.app
        (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f)) ≫
        (adicLowerStarCongr l pullback.condition.symm).hom.app
          (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f))

/-- The morphism `f_* ℚ̄_ℓ,Wⁿ ⟶ (p₁ f)_* ℚ̄_ℓ,(W ×_X W)ⁿ`, `y ↦ γ · p₁^* y - p₂^* y`, whose
kernel is the descent of `ℚ̄_ℓ,Wⁿ` along `γ`. -/
noncomputable def descentMap :
    (f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l W) ⟶
      (pullback.fst f f ≫ f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f)) :=
  descentMapFst f γ - descentMapSnd f

/-- The map `T ×_X (W ×_X W) ⟶ T ×_X W` induced by the first projection. -/
noncomputable abbrev descentρ₁ (T : X.ProEt) :
    Limits.pullback T.hom (pullback.fst f f ≫ f) ⟶ Limits.pullback T.hom f :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst f f)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The map `T ×_X (W ×_X W) ⟶ T ×_X W` induced by the second projection. -/
noncomputable abbrev descentρ₂ (T : X.ProEt) :
    Limits.pullback T.hom (pullback.fst f f ≫ f) ⟶ Limits.pullback T.hom f :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd f f)
    (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition)

/-- The components of a difference of sections. -/
lemma comps_sub {B : Scheme.{u}} {Z : B.ProEt}
    (x x' : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z)) :
    comps (x - x') = comps x - comps x' := by
  funext i
  simp only [comps, map_sub, Pi.sub_apply]
  rfl

/-- The restriction along the composition isomorphism of base changes. -/
lemma pullbackComp_hom_app_left_comp_fst {Y : Scheme.{u}} (a : Y ⟶ W) (T : X.ProEt) :
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) a f).hom.app T).left ≫
      pullback.fst (pullback.snd T.hom f) a =
        pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a)
          (by rw [pullback.condition, Category.assoc]) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, MorphismProperty.Over.pullbackComp_left_fst_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, pullback.lift_snd, ← Category.assoc]
    congr 1
    exact MorphismProperty.Over.w ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale)
      (Q := ⊤) a f).hom.app T)

/-- Sections of a composite of morphisms. -/
lemma comp_hom_app_apply {B : Scheme.{u}} {M N K : AdicSheaf l B} (φ : M ⟶ N) (ψ : N ⟶ K)
    (U : B.ProEtᵒᵖ) (x : M.X.obj.obj U) :
    (φ ≫ ψ).hom.hom.app U x = ψ.hom.hom.app U (φ.hom.hom.app U x) :=
  rfl

/-- The composition isomorphism of pushforwards on sections. -/
lemma adicLowerStarComp_hom_app_apply {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (M : AdicSheaf l T) (V : R.ProEtᵒᵖ) (x : ((h₁)_*ᵃ[l].obj M |> (h₂)_*ᵃ[l].obj).X.obj.obj V) :
    ((adicLowerStarComp l h₁ h₂).hom.app M).hom.hom.app V x =
      M.X.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V.unop).op x := by
  rw [adicLowerStarComp_hom_app_hom, lowerStarComp_hom_app_hom_app]
  rfl

/-- The pushforward of a morphism on sections. -/
lemma adicLowerStar_map_hom_app_apply {S T : Scheme.{u}} (h : T ⟶ S) {M N : AdicSheaf l T}
    (φ : M ⟶ N) (V : S.ProEtᵒᵖ) (x : ((h)_*ᵃ[l].obj M).X.obj.obj V) :
    ((h)_*ᵃ[l].map φ).hom.hom.app V x =
      φ.hom.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).obj V.unop)) x :=
  rfl

/-- Sections of a difference of morphisms. -/
lemma hom_app_sub {B : Scheme.{u}} {M N : AdicSheaf l B} (φ ψ : M ⟶ N) (U : B.ProEtᵒᵖ)
    (x : M.X.obj.obj U) : (φ - ψ).hom.hom.app U x = φ.hom.hom.app U x - ψ.hom.hom.app U x := by
  change ((sectionsFunctor (l := l) U.unop).map (φ - ψ)).hom x = _
  rw [Functor.map_sub]
  rfl

/-- The first half of the descent map on sections. -/
lemma comps_descentMap_fst (T : X.ProEt)
    (y : (⨁ fun _ : Fin n ↦ unit l W).X.obj.obj
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T))) :
    comps (B := Limits.pullback f f)
      (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (pullback.fst f f ≫ f)).obj T)
      ((descentMapFst (l := l) f γ).hom.hom.app (op T) y) = fun i ↦
        ∑ j, PadicAlgCl.locallyFiniteFunctionsComp l
          (pullback.snd T.hom (pullback.fst f f ≫ f)).base.hom (γ i j) *
          PadicAlgCl.locallyFiniteFunctionsComp l (descentρ₁ f T).base.hom (comps y j) := by
  delta descentMapFst
  erw [Mod.comp_hom', ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  erw [adicLowerStarComp_hom_app_hom, lowerStarComp_hom_app_hom_app, comps_map]
  erw [adicLowerStar_map_hom, lowerStar_map_hom_app', Mod.comp_hom',
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    adicLowerStar_map_hom, lowerStar_map_hom_app', comps_app, comps_freePull,
    unitMatrix_ofUnitMatrix]
  funext i
  have h₁ := MorphismProperty.Over.w ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale)
    (Q := ⊤) (pullback.fst f f) f).hom.app T)
  have h₂ := pullbackComp_hom_app_left_comp_fst f (pullback.fst f f) T
  refine Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
  simp only [PadicAlgCl.locallyFiniteFunctionsComp_apply_coe, ContinuousMap.comp_apply,
    AddSubmonoidClass.coe_finsetSum, ContinuousMap.sum_apply, MulMemClass.coe_mul,
    ContinuousMap.mul_apply, pullFun]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 2
  · exact congrArg (fun φ ↦ φ.base x) h₁
  · exact congrArg (fun φ ↦ φ.base x) h₂

omit [Fact l.Prime] in
/-- The identification `g_* ≅ g'_*` for `g = g'`, on sections of free modules. -/
lemma comps_adicLowerStarCongr {B : Scheme.{u}} [Fact l.Prime] {g g' : B ⟶ X} (h : g = g')
    (T : X.ProEt) (x : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj T))) :
    comps (B := B) (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g').obj T)
      (((adicLowerStarCongr l h).hom.app (⨁ fun _ : Fin n ↦ unit l B)).hom.hom.app (op T) x) =
        fun i ↦ PadicAlgCl.locallyFiniteFunctionsComp l
          (pullback.lift (pullback.fst T.hom g') (pullback.snd T.hom g')
            (by rw [pullback.condition, h])).base.hom (comps x i) := by
  subst h
  have e : pullback.lift (pullback.fst T.hom g) (pullback.snd T.hom g) pullback.condition =
      𝟙 _ := pullback.hom_ext (by simp) (by simp)
  rw [e]
  rfl

/-- The second half of the descent map on sections. -/
lemma comps_descentMap_snd (T : X.ProEt)
    (y : (⨁ fun _ : Fin n ↦ unit l W).X.obj.obj
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T))) :
    comps (B := Limits.pullback f f)
      (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (pullback.fst f f ≫ f)).obj T)
      (((f)_*ᵃ[l].map (freePull (pullback.snd f f)) ≫
        (adicLowerStarComp l (pullback.snd f f) f).hom.app (⨁ fun _ : Fin n ↦
          unit l (Limits.pullback f f)) ≫
          (adicLowerStarCongr l pullback.condition.symm).hom.app _).hom.hom.app (op T) y) =
        fun i ↦ PadicAlgCl.locallyFiniteFunctionsComp l (descentρ₂ f T).base.hom (comps y i) := by
  rw [comp_hom_app_apply, comp_hom_app_apply, adicLowerStar_map_hom_app_apply]
  rw [comps_adicLowerStarCongr]
  generalize hz : (freePull (l := l) (n := n) (pullback.snd f f)).hom.hom.app
    (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T)) y = z
  erw [adicLowerStarComp_hom_app_apply (l := l) (pullback.snd f f) f
    (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f)) (op T) z]
  rw [comps_map, ← hz, comps_freePull]
  funext i
  have h₁ := pullbackComp_hom_app_left_comp_fst f (pullback.snd f f) T
  have key : pullback.lift (pullback.fst T.hom (pullback.fst f f ≫ f))
      (pullback.snd T.hom (pullback.fst f f ≫ f))
        (pullback.condition.trans (congrArg (pullback.snd T.hom (pullback.fst f f ≫ f) ≫ ·)
          pullback.condition)) ≫
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
        (pullback.snd f f) f).hom.app T).left ≫
      pullback.fst (pullback.snd T.hom f) (pullback.snd f f) = descentρ₂ f T := by
    rw [h₁]
    exact pullback.hom_ext (by simp) (by simp)
  refine Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
  simp only [PadicAlgCl.locallyFiniteFunctionsComp_apply_coe, ContinuousMap.comp_apply]
  exact congrArg (fun φ ↦ (comps y i).1 (φ.base x)) key

/-- **The descent map on sections**: `y ↦ γ · p₁^* y - p₂^* y`. -/
lemma comps_descentMap (T : X.ProEt)
    (y : (⨁ fun _ : Fin n ↦ unit l W).X.obj.obj
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T))) :
    comps (B := Limits.pullback f f)
      (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (pullback.fst f f ≫ f)).obj T)
      ((descentMap (l := l) f γ).hom.hom.app (op T) y) = fun i ↦
        (∑ j, PadicAlgCl.locallyFiniteFunctionsComp l
          (pullback.snd T.hom (pullback.fst f f ≫ f)).base.hom (γ i j) *
          PadicAlgCl.locallyFiniteFunctionsComp l (descentρ₁ f T).base.hom (comps y j)) -
        PadicAlgCl.locallyFiniteFunctionsComp l (descentρ₂ f T).base.hom (comps y i) := by
  rw [descentMap, hom_app_sub, comps_sub, comps_descentMap_fst]
  have e : descentMapSnd (l := l) (n := n) f = (f)_*ᵃ[l].map (freePull (pullback.snd f f)) ≫
      (adicLowerStarComp l (pullback.snd f f) f).hom.app (⨁ fun _ : Fin n ↦
        unit l (Limits.pullback f f)) ≫
        (adicLowerStarCongr l pullback.condition.symm).hom.app _ := rfl
  rw [e, comps_descentMap_snd]
  rfl

end DescentMap

end AdicSheaf

end AlgebraicGeometry.ProEtale
