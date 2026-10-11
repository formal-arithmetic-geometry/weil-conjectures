/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.SheafOfSections
public import WeilConjectures.ConstructibleSheaf.Biproduct
public import WeilConjectures.ConstructibleSheaf.FreeLifting
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.CategoryTheory.Sites.Point.Linear
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Finite locally constant sheaves of modules and representations of `π₁`

Let `Y` be a connected scheme with a geometric point `s`, let `G = π₁(Y, s)` be a fundamental
group of the fibre functor at `s` and let `Λ` be a finite ring. We show that the geometric stalk
at `s` is an equivalence between finite locally constant sheaves of `Λ`-modules on the small
étale site of `Y` and finite `Λ`-modules with a continuous `G`-action
(`AlgebraicGeometry.Scheme.FiniteLocallyConstantModule.toRep`).

The underlying sheaf of sets of a finite locally constant sheaf of `Λ`-modules `F` is finite
locally constant, so `G` acts on its stalk `F_s`
(`AlgebraicGeometry.Scheme.FiniteLocallyConstant.smul`); the action is `Λ`-linear because the
addition `F ⊞ F ⟶ F` and the scalar multiplications are morphisms of sheaves. Full faithfulness
follows from the full faithfulness of the stalk functor on finite locally constant sheaves of
sets onto `G`-equivariant maps. For essential surjectivity, the free sheaf `Λ[Q]` on a finite
étale `Y`-scheme `Q` is finite locally constant with stalk the permutation representation
`Λ[Q_s]`, and every finite continuous representation is the cokernel of a map between
permutation representations of finite continuous `G`-sets; cokernels of finite locally constant
sheaves are finite locally constant, and the stalk functor is right exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PreGaloisCategory

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]

variable (Y) in
/-- The category of finite locally constant sheaves of `Λ`-modules on the small étale site of
`Y`. -/
abbrev FiniteLocallyConstantModule :=
  ObjectProperty.FullSubcategory
    (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦ IsFiniteLocallyConstantSheaf F)

namespace FiniteLocallyConstantModule

/-- The forgetful functor from `Λ`-modules to `Type (u + 1)`. -/
abbrev forgetModule : ModuleCat.{u + 1} Λ ⥤ Type (u + 1) := CategoryTheory.forget _

instance : PreservesFilteredColimitsOfSize.{u, u} (forgetModule Λ) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

variable {Λ}

/-- The underlying sheaf of sets of a finite locally constant sheaf of modules over a finite
ring is finite locally constant. -/
lemma isFiniteLocallyConstantSheafOfTypes_forget [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose Y.smallEtaleTopology (forgetModule Λ)).obj F) := by
  refine ⟨?_, ⟨fun Ω _ _ s ↦ (ConcreteCategory.isFinitelyGenerated_iff_finite _).2 ?_⟩⟩
  · obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
    refine ⟨d.cover, fun i ↦ ?_⟩
    have := d.isConstant i
    have : ((sheafCompose _ (forgetModule Λ)).obj
        (F.over (d.cover.etalePrecoverageToEtale i))).IsConstant _ := inferInstance
    exact Sheaf.isConstant_congr _ (F := (sheafCompose _ (forgetModule Λ)).obj
      (F.over (d.cover.etalePrecoverageToEtale i)))
      ((fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _))
  · have h := (inferInstance : IsFiniteSheaf F).isFinitelyGenerated_sheafFiber Ω s
    rw [ModuleCat.isFinitelyGenerated_iff] at h
    have : Finite ((pointSmallEtale s).sheafFiber.obj F : ModuleCat.{u + 1} Λ) :=
      Module.finite_of_finite Λ
    exact @Finite.of_equiv _ _ this
      (((pointSmallEtale s).sheafFiberCompIso (forgetModule Λ)).app F).toEquiv.symm

variable [Finite Λ]

variable (Λ Y) in
/-- The underlying finite locally constant sheaf of sets of a finite locally constant sheaf of
`Λ`-modules. -/
noncomputable def forget : Y.FiniteLocallyConstantModule Λ ⥤ Y.FiniteLocallyConstant :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ sheafCompose Y.smallEtaleTopology (forgetModule Λ))
    fun F ↦ have := F.property; isFiniteLocallyConstantSheafOfTypes_forget F.obj

section Stalk

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- The stalk of a finite locally constant sheaf of `Λ`-modules. -/
noncomputable abbrev stalk (F : Y.FiniteLocallyConstantModule Λ) : ModuleCat.{u + 1} Λ :=
  (pointSmallEtale s).sheafFiber.obj F.obj

/-- The map on stalks induced by a morphism of finite locally constant sheaves of `Λ`-modules. -/
noncomputable abbrev stalkMap {F F' : Y.FiniteLocallyConstantModule Λ} (f : F ⟶ F') :
    stalk s F ⟶ stalk s F' :=
  (pointSmallEtale s).sheafFiber.map f.hom

/-- The stalk of the underlying sheaf of sets of `F` is the underlying set of the stalk of
`F`. -/
noncomputable def forgetStalkEquiv (F : Y.FiniteLocallyConstantModule Λ) :
    FiniteLocallyConstant.stalk s ((forget Y Λ).obj F) ≃ stalk s F :=
  (((pointSmallEtale s).sheafFiberCompIso (forgetModule Λ)).app F.obj).toEquiv

lemma forgetStalkEquiv_naturality {F F' : Y.FiniteLocallyConstantModule Λ} (f : F ⟶ F')
    (x : FiniteLocallyConstant.stalk s ((forget Y Λ).obj F)) :
    forgetStalkEquiv s F' (FiniteLocallyConstant.stalkMap s ((forget Y Λ).map f) x) =
      stalkMap s f (forgetStalkEquiv s F x) :=
  ConcreteCategory.congr_hom
    (((pointSmallEtale s).sheafFiberCompIso (forgetModule Λ)).hom.naturality f.hom) x

lemma forgetStalkEquiv_symm_naturality {F F' : Y.FiniteLocallyConstantModule Λ} (f : F ⟶ F')
    (x : stalk s F) :
    (forgetStalkEquiv s F').symm (stalkMap s f x) =
      FiniteLocallyConstant.stalkMap s ((forget Y Λ).map f) ((forgetStalkEquiv s F).symm x) := by
  rw [Equiv.symm_apply_eq, forgetStalkEquiv_naturality, Equiv.apply_symm_apply]

end Stalk
section Action

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) [ConnectedSpace Y]
  (G : Type u) [Group G] [∀ P, MulAction G ((FiniteEtale.fiber s).obj P)]
  [IsNaturalSMul (FiniteEtale.fiber s) G]

/-- The action of `G = π₁(Y, s)` on the stalk `F_s` of a finite locally constant sheaf of
`Λ`-modules, through the action on the stalk of the underlying sheaf of sets. -/
noncomputable def smul {F : Y.FiniteLocallyConstantModule Λ} (g : G) (x : stalk s F) :
    stalk s F :=
  forgetStalkEquiv s F (FiniteLocallyConstant.smul s G g ((forgetStalkEquiv s F).symm x))

lemma stalkMap_smul {F F' : Y.FiniteLocallyConstantModule Λ} (f : F ⟶ F') (g : G)
    (x : stalk s F) : stalkMap s f (smul s G g x) = smul s G g (stalkMap s f x) := by
  simp only [smul]
  rw [← forgetStalkEquiv_naturality, FiniteLocallyConstant.stalkMap_smul,
    forgetStalkEquiv_symm_naturality]

/-- The direct sum `F ⊞ F` of a finite locally constant sheaf of `Λ`-modules with itself. -/
noncomputable abbrev double (F : Y.FiniteLocallyConstantModule Λ) :
    Y.FiniteLocallyConstantModule Λ :=
  ⟨F.obj ⊞ F.obj, by have := F.property; exact IsFiniteLocallyConstantSheaf.biprod _ _⟩

lemma smul_add {F : Y.FiniteLocallyConstantModule Λ} (g : G) (x y : stalk s F) :
    smul s G g (x + y) = smul s G g x + smul s G g y := by
  have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  let fst : double F ⟶ F := ObjectProperty.homMk biprod.fst
  let snd : double F ⟶ F := ObjectProperty.homMk biprod.snd
  let inl : F ⟶ double F := ObjectProperty.homMk biprod.inl
  let inr : F ⟶ double F := ObjectProperty.homMk biprod.inr
  let add : double F ⟶ F := ObjectProperty.homMk (biprod.desc (𝟙 _) (𝟙 _))
  have hadd (w : stalk s (double F)) :
      stalkMap s add w = stalkMap s fst w + stalkMap s snd w := by
    have : (biprod.desc (𝟙 F.obj) (𝟙 F.obj)) = biprod.fst + biprod.snd := by
      simp [biprod.desc_eq]
    change (pointSmallEtale s).sheafFiber.map (biprod.desc (𝟙 F.obj) (𝟙 F.obj)) w = _
    rw [this, Functor.map_add]
    rfl
  have hcomp {A B C : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (a : A ⟶ B) (b : B ⟶ C)
      (w) : (pointSmallEtale s).sheafFiber.map (a ≫ b) w =
        (pointSmallEtale s).sheafFiber.map b ((pointSmallEtale s).sheafFiber.map a w) := by
    rw [Functor.map_comp, ConcreteCategory.comp_apply]
  have hid {A : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (w) :
      (pointSmallEtale s).sheafFiber.map (𝟙 A) w = w := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hzero {A B : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (w) :
      (pointSmallEtale s).sheafFiber.map (0 : A ⟶ B) w = 0 := by
    rw [Functor.map_zero]
    rfl
  let z := stalkMap s inl x + stalkMap s inr y
  have e₁ : stalkMap s fst (stalkMap s inl x) = x := by
    change (pointSmallEtale s).sheafFiber.map (biprod.fst : F.obj ⊞ F.obj ⟶ F.obj)
      ((pointSmallEtale s).sheafFiber.map (biprod.inl : F.obj ⟶ F.obj ⊞ F.obj) x) = x
    rw [← hcomp, biprod.inl_fst, hid]
  have e₂ : stalkMap s fst (stalkMap s inr y) = 0 := by
    change (pointSmallEtale s).sheafFiber.map (biprod.fst : F.obj ⊞ F.obj ⟶ F.obj)
      ((pointSmallEtale s).sheafFiber.map (biprod.inr : F.obj ⟶ F.obj ⊞ F.obj) y) = 0
    rw [← hcomp, biprod.inr_fst, hzero]
  have e₃ : stalkMap s snd (stalkMap s inl x) = 0 := by
    change (pointSmallEtale s).sheafFiber.map (biprod.snd : F.obj ⊞ F.obj ⟶ F.obj)
      ((pointSmallEtale s).sheafFiber.map (biprod.inl : F.obj ⟶ F.obj ⊞ F.obj) x) = 0
    rw [← hcomp, biprod.inl_snd, hzero]
  have e₄ : stalkMap s snd (stalkMap s inr y) = y := by
    change (pointSmallEtale s).sheafFiber.map (biprod.snd : F.obj ⊞ F.obj ⟶ F.obj)
      ((pointSmallEtale s).sheafFiber.map (biprod.inr : F.obj ⟶ F.obj ⊞ F.obj) y) = y
    rw [← hcomp, biprod.inr_snd, hid]
  have hfst : stalkMap s fst z = x := by
    simp only [z, map_add, e₁, e₂, add_zero]
  have hsnd : stalkMap s snd z = y := by
    simp only [z, map_add, e₃, e₄, zero_add]
  rw [← hfst, ← hsnd, ← hadd, ← stalkMap_smul, hadd, stalkMap_smul, stalkMap_smul]

lemma smul_smul {F : Y.FiniteLocallyConstantModule Λ} (g : G) (c : Λ) (x : stalk s F) :
    smul s G g (c • x) = c • smul s G g x := by
  let m : F ⟶ F := ObjectProperty.homMk (c • 𝟙 F.obj)
  have hm (w : stalk s F) : stalkMap s m w = c • w := by
    change (pointSmallEtale s).sheafFiber.map (c • 𝟙 F.obj) w = _
    rw [GrothendieckTopology.Point.sheafFiber_map_smul, CategoryTheory.Functor.map_id]
    rfl
  rw [← hm, stalkMap_smul, hm]

lemma one_smul {F : Y.FiniteLocallyConstantModule Λ} (x : stalk s F) : smul s G 1 x = x := by
  simp [smul, FiniteLocallyConstant.one_smul]

lemma mul_smul {F : Y.FiniteLocallyConstantModule Λ} (g h : G) (x : stalk s F) :
    smul s G (g * h) x = smul s G g (smul s G h x) := by
  simp [smul, FiniteLocallyConstant.mul_smul]

/-- Blueprint `sk-i-real-galois`: the representation of `G = π₁(Y, s)` on the stalk `F_s` of a
finite locally constant sheaf of `Λ`-modules. -/
noncomputable def representation (F : Y.FiniteLocallyConstantModule Λ) :
    Representation Λ G (stalk s F) where
  toFun g :=
    { toFun := smul s G g
      map_add' := smul_add s G g
      map_smul' := smul_smul s G g }
  map_one' := LinearMap.ext (one_smul s G)
  map_mul' g h := LinearMap.ext (mul_smul s G g h)

lemma representation_apply (F : Y.FiniteLocallyConstantModule Λ) (g : G) (x : stalk s F) :
    representation s G F g x = smul s G g x := rfl

variable (Λ) in
/-- Blueprint `sk-i-real-galois`: the geometric stalk functor from finite locally constant
sheaves of `Λ`-modules to `Λ`-linear representations of `G = π₁(Y, s)`. -/
noncomputable def toRep : Y.FiniteLocallyConstantModule Λ ⥤ Rep.{u + 1} Λ G where
  obj F := Rep.of (representation s G F)
  map {F F'} f := Rep.ofHom
    ((stalkMap s f).hom.intertwiningMap_of_isIntertwiningMap fun g x ↦ stalkMap_smul s G f g x)
  map_id F := by
    ext x
    change stalkMap s (𝟙 F) x = x
    simp [stalkMap]
  map_comp f f' := by
    ext x
    change stalkMap s (f ≫ f') x = stalkMap s f' (stalkMap s f x)
    simp [stalkMap]

lemma toRep_map_hom_apply {F F' : Y.FiniteLocallyConstantModule Λ} (f : F ⟶ F')
    (x : stalk s F) : ((toRep Λ s G).map f).hom x = stalkMap s f x := rfl

end Action

end FiniteLocallyConstantModule

end AlgebraicGeometry.Scheme
