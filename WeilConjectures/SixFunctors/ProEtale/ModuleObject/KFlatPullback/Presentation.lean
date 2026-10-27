/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.KFlatPullback.TensorSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsFilteredColimit
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Cofree
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered

/-!
# Reduction to finitely presented modules for sections of tensor products

Let `S ≅ Spec R` be a scheme such that every faithfully flat ind-étale `R`-algebra has a
retraction, `B` a commutative monoid object in abelian pro-étale sheaves on `S`, and `W` the
terminal object of the small pro-étale site of `S`. Taking sections over `W` is exact on
`B`-module objects, and the sections over `W` of `M ⊗_B N` only depend on the sections of `N`
(`AlgebraicGeometry.ProEtale.bijective_modSections_whiskerLeft`).

We show that, for a complex `M` of `B`-modules, the complex of sections over `W` of `M ⊗_B N` is
acyclic for every `N` as soon as it is acyclic for every finitely presented `N`, i.e. for the
cokernels of all morphisms `B^m ⟶ B^n`
(`AlgebraicGeometry.ProEtale.acyclic_modSections_tensorRight_of_finitelyPresented`).

## Proof

* Morphisms `B ⟶ N` correspond to sections of `N` over the terminal object `W`
  (`AlgebraicGeometry.ProEtale.exists_modSections_map_unitSection_eq`,
  `AlgebraicGeometry.ProEtale.hom_ext_of_modSections_map_unitSection`).
* Hence every `N` receives a morphism `coker (T : ⊕_J B ⟶ ⊕_I B) ⟶ N` which is bijective on
  sections over `W`, so that `M ⊗ coker T` and `M ⊗ N` have the same sections over `W`.
* Sections over the quasi-compact quasi-separated object `W` commute with filtered colimits, so
  every section of `X ⊗ ⊕_I B` comes from a finite subsum, and every column of `T` factors through
  a finite subsum. A cycle of the complex of sections of `M ⊗ coker T` thus comes from a cycle for
  the cokernel of a morphism between finite sums.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite
open Limits.CoproductsFromFiniteFiltered

namespace CategoryTheory.Limits

/-- The inclusion of a finite subcoproduct into a coproduct is a split monomorphism. -/
instance isSplitMono_finiteSubcoproductsCocone_ι_app {C : Type*} [Category* C]
    [HasZeroMorphisms C] [HasFiniteCoproducts C] {α : Type*} (f : α → C) [HasCoproduct f]
    (s : Finset (Discrete α)) :
    IsSplitMono ((finiteSubcoproductsCocone f).ι.app s) := by
  classical
  refine ⟨⟨Sigma.desc fun i ↦ if h : (⟨i⟩ : Discrete α) ∈ s then
    Sigma.ι (fun x : s ↦ (Discrete.functor f).obj x) ⟨⟨i⟩, h⟩ else 0, ?_⟩⟩
  refine Sigma.hom_ext _ _ fun ⟨⟨i⟩, h⟩ ↦ ?_
  simp only [finiteSubcoproductsCocone_ι_app, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as,
    Cofan.mk_ι_app, colimit.ι_desc, dif_pos h]
  exact (Category.comp_id _).symm

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable {S : Scheme.{u}} {B : Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}} [MonObj B]
  [IsCommMonObj B]

/-- The unit section `1 ∈ B(W)` of the regular module over an object `W`. -/
noncomputable def unitSection (W : S.ProEt) :
    (modSections (B := B) W).obj (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) B)) :=
  Sheaf.unitHomEval W (F := B) MonObj.one

/-- Every section of a module object over a terminal object `W` is the image of the unit section
under a morphism out of the regular module. -/
lemma exists_modSections_map_unitSection_eq {W : S.ProEt} (hW : IsTerminal W)
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) B) (x : (modSections W).obj N) :
    ∃ f : 𝟙_ (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) B) ⟶ N,
      (modSections W).map f (unitSection W) = x := by
  obtain ⟨s, rfl⟩ := Sheaf.unitHomEval_surjective hW N.X x
  refine ⟨Mod.regularLift N s, ?_⟩
  exact congrArg (Sheaf.unitHomEval W (F := N.X)) (Mod.one_comp_regularLift N s)

/-- Morphisms out of the regular module are determined by the image of the unit section over a
terminal object. -/
lemma hom_ext_of_modSections_map_unitSection {W : S.ProEt} (hW : IsTerminal W)
    {N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) B}
    {f g : 𝟙_ (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) B) ⟶ N}
    (h : (modSections W).map f (unitSection W) = (modSections W).map g (unitSection W)) :
    f = g :=
  Mod.regular_hom_ext (Sheaf.unitHomEval_injective hW N.X h)

set_option hygiene false in
/-- The category of `B`-module objects. -/
local notation "𝒟" => Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) B

omit [IsCommMonObj B] in
/-- The category of `B`-module objects has all colimits indexed by categories in `Type (u + 1)`.
-/
lemma hasColimitsOfSize_mod : HasColimitsOfSize.{u + 1, u + 1} 𝒟 :=
  IsGrothendieckAbelian.hasColimits _

omit [IsCommMonObj B] in
/-- The category of `B`-module objects has colimits of shape `K` for every `K : Type (u + 1)`. -/
lemma hasColimitsOfShape_mod (K : Type (u + 1)) [Category.{u + 1} K] : HasColimitsOfShape K 𝒟 :=
  hasColimitsOfSize_mod.has_colimits_of_shape K

attribute [local instance] hasColimitsOfShape_mod

omit [IsCommMonObj B] in
/-- Over a weakly contractible object, epimorphisms of module objects are surjective on sections.
-/
lemma surjective_modSections_map_of_epi {W : S.ProEt}
    (hW : (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1} W) {X Y : 𝒟} (g : X ⟶ Y)
    [Epi g] : Function.Surjective ((modSections W).map g) := by
  have : Epi g.hom := (Mod.forget B).map_epi g
  exact surjective_app_of_isWeaklyContractible_ab hW g.hom

/-- Over a weakly contractible object, the sections of `X ⊗ -` of a cokernel sequence form an exact
sequence. -/
lemma exists_modSections_whiskerLeft_eq_of_cokernel {W : S.ProEt}
    (hW : (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1} W) (X : 𝒟) {P Q : 𝒟}
    (T : P ⟶ Q) (v : (modSections W).obj (X ⊗ Q))
    (hv : (modSections W).map (X ◁ cokernel.π T) v = 0) :
    ∃ w, (modSections W).map (X ◁ T) w = v := by
  have := preservesHomology_modSections (B := B) hW
  have hex := (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk ((tensorLeft X).map T) ((tensorLeft X).map (cokernel.π T))
      (by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]))
    (CokernelCofork.mapIsColimit _ (cokernelIsCokernel T) (tensorLeft X))).map (modSections W)
  rw [ShortComplex.ab_exact_iff] at hex
  exact hex v hv

omit [IsCommMonObj B] in
/-- **Sections over a quasi-compact quasi-separated object commute with filtered colimits** of
module objects. -/
lemma exists_modSections_map_eq_of_isColimit {W : S.ProEt} [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
    {F : K ⥤ 𝒟} {c : Cocone F} (hc : IsColimit c) (x : (modSections W).obj c.pt) :
    ∃ k y, (modSections W).map (c.ι.app k) y = x := by
  have : PreservesColimitsOfSize.{u + 1, u + 1} (Mod.forget B) :=
    (Mod.forgetCofreeAdjunction B).leftAdjoint_preservesColimits
  exact Concrete.isColimit_exists_rep _
    (Scheme.ProEt.isColimitSectionsOfIsColimit (isColimitOfPreserves (Mod.forget B) hc) W) x

/-- Every section of `X ⊗ ∐ f` over a quasi-compact quasi-separated object comes from a finite
subcoproduct. -/
lemma exists_modSections_whiskerLeft_finiteSubcoproduct {W : S.ProEt} [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] (X : 𝒟) {I : Type (u + 1)} (f : I → 𝒟)
    (x : (modSections W).obj (X ⊗ ∐ f)) :
    ∃ (s : Finset (Discrete I))
      (y : (modSections W).obj (X ⊗ (liftToFinsetObj (Discrete.functor f)).obj s)),
      (modSections W).map (X ◁ (finiteSubcoproductsCocone f).ι.app s) y = x := by
  have : PreservesColimitsOfSize.{u + 1, u + 1} (tensorLeft X) :=
    (ihom.adjunction X).leftAdjoint_preservesColimits
  exact exists_modSections_map_eq_of_isColimit
    (isColimitOfPreserves (tensorLeft X) (isColimitFiniteSubproductsCocone f)) x

/-- Every morphism from the regular module to a coproduct factors through a finite subcoproduct.
-/
lemma exists_comp_finiteSubcoproductsCocone_ι_eq {W : S.ProEt} (hT : IsTerminal W)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] {I : Type (u + 1)} (f : I → 𝒟)
    (g : 𝟙_ 𝒟 ⟶ ∐ f) :
    ∃ (s : Finset (Discrete I)) (c : 𝟙_ 𝒟 ⟶ (liftToFinsetObj (Discrete.functor f)).obj s),
      c ≫ (finiteSubcoproductsCocone f).ι.app s = g := by
  obtain ⟨s, y, hy⟩ := exists_modSections_map_eq_of_isColimit (W := W)
    (isColimitFiniteSubproductsCocone f) ((modSections W).map g (unitSection W))
  obtain ⟨c, rfl⟩ := exists_modSections_map_unitSection_eq hT _ y
  refine ⟨s, c, hom_ext_of_modSections_map_unitSection hT ?_⟩
  rw [Functor.map_comp, ConcreteCategory.comp_apply]
  exact hy

/-- If a cycle of the sections of `X₀ ⊗ P ⟶ X₁ ⊗ P ⟶ X₂ ⊗ P` is a boundary, so is its image
under `g : P ⟶ N`. -/
lemma exists_modSections_whiskerRight_eq_whiskerLeft {W : S.ProEt} {X₀ X₁ X₂ : 𝒟}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) {P N : 𝒟} (g : P ⟶ N)
    (hP : ∀ z, (modSections W).map (b ▷ P) z = 0 → ∃ y, (modSections W).map (a ▷ P) y = z)
    {z : (modSections W).obj (X₁ ⊗ P)} (hz : (modSections W).map (b ▷ P) z = 0) :
    ∃ y, (modSections W).map (a ▷ N) y = (modSections W).map (X₁ ◁ g) z := by
  obtain ⟨y, rfl⟩ := hP z hz
  refine ⟨(modSections W).map (X₀ ◁ g) y, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, whisker_exchange, Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- Exactness of the sections of `X₀ ⊗ - ⟶ X₁ ⊗ - ⟶ X₂ ⊗ -` transfers along a morphism
`g : P ⟶ N` such that `X₁ ◁ g` is surjective and `X₂ ◁ g` is injective on sections. -/
lemma forall_exists_modSections_of_whiskerLeft {W : S.ProEt} {X₀ X₁ X₂ : 𝒟}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) {P N : 𝒟} (g : P ⟶ N)
    (h₁ : Function.Surjective ((modSections W).map (X₁ ◁ g)))
    (h₂ : Function.Injective ((modSections W).map (X₂ ◁ g)))
    (hP : ∀ z, (modSections W).map (b ▷ P) z = 0 → ∃ y, (modSections W).map (a ▷ P) y = z)
    (z : (modSections W).obj (X₁ ⊗ N)) (hz : (modSections W).map (b ▷ N) z = 0) :
    ∃ y, (modSections W).map (a ▷ N) y = z := by
  obtain ⟨z, rfl⟩ := h₁ z
  refine exists_modSections_whiskerRight_eq_whiskerLeft a b g hP (h₂ ?_)
  rw [map_zero, ← hz, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp, whisker_exchange]

/-- Exactness for the cokernels of morphisms between finite sums of copies of the regular module
indexed by arbitrary finite types follows from the case of the types `Fin n`. -/
lemma forall_exists_modSections_cokernel_of_finite {W : S.ProEt} {X₀ X₁ X₂ : 𝒟}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (hfin : ∀ (m n : ℕ) (T : (∐ fun _ : Fin m ↦ 𝟙_ 𝒟) ⟶ ∐ fun _ : Fin n ↦ 𝟙_ 𝒟) z,
      (modSections W).map (b ▷ cokernel T) z = 0 →
        ∃ y, (modSections W).map (a ▷ cokernel T) y = z)
    (J I : Type (u + 1)) [Finite J] [Finite I]
    (T : (∐ fun _ : J ↦ 𝟙_ 𝒟) ⟶ ∐ fun _ : I ↦ 𝟙_ 𝒟) (z) :
    (modSections W).map (b ▷ cokernel T) z = 0 →
      ∃ y, (modSections W).map (a ▷ cokernel T) y = z := by
  obtain ⟨m, ⟨eJ⟩⟩ := Finite.exists_equiv_fin J
  obtain ⟨n, ⟨eI⟩⟩ := Finite.exists_equiv_fin I
  let iJ : (∐ fun _ : J ↦ 𝟙_ 𝒟) ≅ ∐ fun _ : Fin m ↦ 𝟙_ 𝒟 :=
    Sigma.whiskerEquiv (f := fun _ : J ↦ 𝟙_ 𝒟) (g := fun _ : Fin m ↦ 𝟙_ 𝒟) eJ fun _ ↦ Iso.refl _
  let iI : (∐ fun _ : I ↦ 𝟙_ 𝒟) ≅ ∐ fun _ : Fin n ↦ 𝟙_ 𝒟 :=
    Sigma.whiskerEquiv (f := fun _ : I ↦ 𝟙_ 𝒟) (g := fun _ : Fin n ↦ 𝟙_ 𝒟) eI fun _ ↦ Iso.refl _
  let φ : cokernel (iJ.inv ≫ T ≫ iI.hom) ≅ cokernel T :=
    cokernel.mapIso _ _ iJ.symm iI.symm (by simp)
  exact forall_exists_modSections_of_whiskerLeft a b φ.hom
    (ConcreteCategory.bijective_of_isIso ((modSections W).map (X₁ ◁ φ.hom))).2
    (ConcreteCategory.bijective_of_isIso ((modSections W).map (X₂ ◁ φ.hom))).1
    (hfin m n _) z

/-- Every module object receives a morphism from a sum of copies of the regular module which is
surjective on sections over a terminal object `W`. -/
lemma exists_sigma_unit_surjective_modSections {W : S.ProEt} (hT : IsTerminal W) (N : 𝒟) :
    ∃ ε : (∐ fun _ : (modSections W).obj N ↦ 𝟙_ 𝒟) ⟶ N,
      Function.Surjective ((modSections W).map ε) := by
  choose f hf using exists_modSections_map_unitSection_eq hT N
  refine ⟨Sigma.desc f, fun x ↦ ⟨(modSections W).map (Sigma.ι _ x) (unitSection W), ?_⟩⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Sigma.ι_desc, hf]

omit [IsCommMonObj B] in
/-- Let `ε : Q ⟶ N` and `ε' : P ⟶ ker ε` be surjective on sections over a weakly contractible
object `W`. Then the morphism `coker (P ⟶ Q) ⟶ N` induced by `ε` is bijective on sections over
`W`. -/
lemma bijective_modSections_cokernel_desc {W : S.ProEt}
    (hW : (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1} W) {P Q N : 𝒟} (ε : Q ⟶ N)
    (ε' : P ⟶ kernel ε) (hε : Function.Surjective ((modSections W).map ε))
    (hε' : Function.Surjective ((modSections W).map ε')) :
    Function.Bijective ((modSections W).map
      (cokernel.desc (ε' ≫ kernel.ι ε) ε
        (by rw [Category.assoc, kernel.condition, comp_zero]))) := by
  have := preservesHomology_modSections (B := B) hW
  have hex : ∀ x, (modSections W).map ε x = 0 →
      ∃ k, (modSections W).map (kernel.ι ε) k = x := by
    have hex := (ShortComplex.exact_of_f_is_kernel
      (ShortComplex.mk (kernel.ι ε) ε (kernel.condition ε)) (kernelIsKernel ε)).map
      (modSections W)
    rw [ShortComplex.ab_exact_iff] at hex
    exact hex
  refine ⟨(injective_iff_map_eq_zero _).2 fun v hv ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨v, rfl⟩ := surjective_modSections_map_of_epi hW (cokernel.π _) v
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, cokernel.π_desc] at hv
    obtain ⟨k, rfl⟩ := hex v hv
    obtain ⟨k, rfl⟩ := hε' k
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← Category.assoc, cokernel.condition, Functor.map_zero]
    rfl
  · obtain ⟨v, rfl⟩ := hε x
    refine ⟨(modSections W).map (cokernel.π _) v, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, cokernel.π_desc]

/-- **Presentations up to sections.** Every module object `N` receives a morphism from the
cokernel of a morphism `T` between sums of copies of the regular module which is bijective on
sections over a weakly contractible terminal object `W`. -/
lemma exists_cokernel_bijective_modSections {W : S.ProEt} (hT : IsTerminal W)
    (hW : (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1} W) (N : 𝒟) :
    ∃ (J I : Type (u + 1)) (T : (∐ fun _ : J ↦ 𝟙_ 𝒟) ⟶ ∐ fun _ : I ↦ 𝟙_ 𝒟)
      (c : cokernel T ⟶ N), Function.Bijective ((modSections W).map c) := by
  obtain ⟨ε, hε⟩ := exists_sigma_unit_surjective_modSections hT N
  obtain ⟨ε', hε'⟩ := exists_sigma_unit_surjective_modSections hT (kernel ε)
  exact ⟨_, _, _, _, bijective_modSections_cokernel_desc hW ε ε' hε hε'⟩

set_option maxHeartbeats 400000 in
-- The unification of finite subcoproducts with sums indexed by finite types is expensive.
/-- Exactness of the sections of `X₀ ⊗ - ⟶ X₁ ⊗ - ⟶ X₂ ⊗ -` at the cokernel of a morphism `T`
between arbitrary sums of copies of the regular module follows from the case of finite sums:
a cycle comes from a cycle for the cokernel of a morphism between finite subsums. -/
lemma forall_exists_modSections_cokernel {W : S.ProEt} (hT : IsTerminal W)
    {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : W.left ≅ Spec R) {X₀ X₁ X₂ : 𝒟} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (hfin : ∀ (J I : Type (u + 1)) [Finite J] [Finite I]
      (T : (∐ fun _ : J ↦ 𝟙_ 𝒟) ⟶ ∐ fun _ : I ↦ 𝟙_ 𝒟) z,
      (modSections W).map (b ▷ cokernel T) z = 0 →
        ∃ y, (modSections W).map (a ▷ cokernel T) y = z)
    {J I : Type (u + 1)} (T : (∐ fun _ : J ↦ 𝟙_ 𝒟) ⟶ ∐ fun _ : I ↦ 𝟙_ 𝒟)
    (z : (modSections W).obj (X₁ ⊗ cokernel T))
    (hz : (modSections W).map (b ▷ cokernel T) z = 0) :
    ∃ y, (modSections W).map (a ▷ cokernel T) y = z := by
  classical
  have hW := Scheme.ProEt.isWeaklyContractible_of_forall_exists_retraction.{u + 1} hR e
  have : IsAffine W.left := .of_isIso e.hom
  let fJ := fun _ : J ↦ 𝟙_ 𝒟
  let fI := fun _ : I ↦ 𝟙_ 𝒟
  let ιJ := (finiteSubcoproductsCocone fJ).ι
  let ιI := (finiteSubcoproductsCocone fI).ι
  -- lift `z` to the sum and lift its boundary to the relations
  have : Epi (X₁ ◁ cokernel.π T) := (tensorLeft X₁).map_epi _
  obtain ⟨z, rfl⟩ := surjective_modSections_map_of_epi hW (X₁ ◁ cokernel.π T) z
  obtain ⟨w, hw⟩ := exists_modSections_whiskerLeft_eq_of_cokernel hW X₂ T
    ((modSections W).map (b ▷ _) z) (by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← whisker_exchange,
        Functor.map_comp, ConcreteCategory.comp_apply, hz])
  -- both come from finite subsums
  obtain ⟨s₁, z, rfl⟩ := exists_modSections_whiskerLeft_finiteSubcoproduct X₁ fI z
  obtain ⟨t, w, rfl⟩ := exists_modSections_whiskerLeft_finiteSubcoproduct X₂ fJ w
  -- the restriction of `T` to `t` lands in a finite subsum
  have hcol (j : t) := exists_comp_finiteSubcoproductsCocone_ι_eq hT fI
    (Sigma.ι (fun x : t ↦ (Discrete.functor fJ).obj x) j ≫ ιJ.app t ≫ T)
  choose sj cj hcj using hcol
  let s₂ := s₁ ∪ t.attach.biUnion sj
  have h₁ : s₁ ≤ s₂ := Finset.subset_union_left
  have hj (j : t) : sj j ≤ s₂ :=
    (Finset.subset_biUnion_of_mem sj (Finset.mem_attach _ j)).trans Finset.subset_union_right
  have htr {s s' : Finset (Discrete I)} (h : s ≤ s') :
      (liftToFinsetObj (Discrete.functor fI)).map (homOfLE h) ≫ ιI.app s' = ιI.app s :=
    (finiteSubcoproductsCocone fI).w (homOfLE h)
  let T₁ : (liftToFinsetObj (Discrete.functor fJ)).obj t ⟶
      (liftToFinsetObj (Discrete.functor fI)).obj s₂ :=
    Sigma.desc fun j ↦ cj j ≫ (liftToFinsetObj (Discrete.functor fI)).map (homOfLE (hj j))
  have hT₁ : T₁ ≫ ιI.app s₂ = ιJ.app t ≫ T := by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    rw [Sigma.ι_desc_assoc, Category.assoc, htr, hcj]
  let g : cokernel T₁ ⟶ cokernel T := cokernel.desc T₁ (ιI.app s₂ ≫ cokernel.π T) (by
    rw [← Category.assoc, hT₁, Category.assoc, cokernel.condition, comp_zero])
  have hinj : Function.Injective ((modSections W).map (X₂ ◁ ιI.app s₂)) :=
    (AddCommGrpCat.mono_iff_injective _).1 (inferInstanceAs
      (Mono ((modSections W).map ((tensorLeft X₂).map (ιI.app s₂)))))
  have key : (modSections W).map (X₂ ◁ (liftToFinsetObj (Discrete.functor fI)).map (homOfLE h₁))
      ((modSections W).map (b ▷ _) z) = (modSections W).map (X₂ ◁ T₁) w := by
    refine hinj ?_
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← whiskerLeft_comp,
      Category.assoc]
    rw [htr, hT₁, ← whisker_exchange, Functor.map_comp, ConcreteCategory.comp_apply,
      whiskerLeft_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact hw.symm
  have hg : cokernel.π T₁ ≫ g = ιI.app s₂ ≫ cokernel.π T := cokernel.π_desc _ _ _
  obtain ⟨y, hy⟩ := exists_modSections_whiskerRight_eq_whiskerLeft a b g
    (hfin t s₂ T₁) (z := (modSections W).map
      (X₁ ◁ ((liftToFinsetObj (Discrete.functor fI)).map (homOfLE h₁) ≫ cokernel.π T₁)) z) (by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, whisker_exchange, whiskerLeft_comp,
        Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply, key, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← whiskerLeft_comp, cokernel.condition, MonoidalPreadditive.whiskerLeft_zero,
        Functor.map_zero]
      rfl)
  refine ⟨y, hy.trans ?_⟩
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← whiskerLeft_comp,
    Category.assoc, hg]
  rw [← Category.assoc, htr, whiskerLeft_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  rfl

/-- **Reduction to finitely presented modules.** Let `W` be a terminal object of the small
pro-étale site of `S` with `W ≅ Spec R`, where every faithfully flat ind-étale `R`-algebra has a
retraction. If the sections over `W` of `X₀ ⊗ P ⟶ X₁ ⊗ P ⟶ X₂ ⊗ P` are exact at `X₁ ⊗ P` for
every finitely presented module `P = coker (B^m ⟶ B^n)`, then they are exact for every module. -/
theorem forall_exists_modSections_of_finitelyPresented {W : S.ProEt} (hT : IsTerminal W)
    {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : W.left ≅ Spec R) [Abelian.HasFunctorialFlatResolution 𝒟] {X₀ X₁ X₂ : 𝒟}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (hfin : ∀ (m n : ℕ) (T : (∐ fun _ : Fin m ↦ 𝟙_ 𝒟) ⟶ ∐ fun _ : Fin n ↦ 𝟙_ 𝒟) z,
      (modSections W).map (b ▷ cokernel T) z = 0 →
        ∃ y, (modSections W).map (a ▷ cokernel T) y = z)
    (N : 𝒟) (z : (modSections W).obj (X₁ ⊗ N)) (hz : (modSections W).map (b ▷ N) z = 0) :
    ∃ y, (modSections W).map (a ▷ N) y = z := by
  obtain ⟨J, I, T, c, hc⟩ := exists_cokernel_bijective_modSections hT
    (Scheme.ProEt.isWeaklyContractible_of_forall_exists_retraction.{u + 1} hR e) N
  exact forall_exists_modSections_of_whiskerLeft a b c
    (bijective_modSections_whiskerLeft hR e X₁ c hc).2
    (bijective_modSections_whiskerLeft hR e X₂ c hc).1
    (forall_exists_modSections_cokernel hT hR e a b
      (forall_exists_modSections_cokernel_of_finite a b hfin) T) z hz

/-- The complex of sections over `W` of `M ⊗ N` is acyclic if and only if every cycle is a
boundary. -/
lemma acyclic_modSections_tensorRight_iff (W : S.ProEt) (M : CochainComplex 𝒟 ℤ) (N : 𝒟) :
    (((modSections W).mapHomologicalComplex (.up ℤ)).obj
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj M)).Acyclic ↔
    ∀ (p : ℤ) (z : (modSections W).obj (M.X p ⊗ N)),
      (modSections W).map (M.d p (p + 1) ▷ N) z = 0 →
        ∃ y, (modSections W).map (M.d (p - 1) p ▷ N) y = z := by
  refine forall_congr' fun p ↦ ?_
  rw [HomologicalComplex.exactAt_iff' _ (p - 1) p (p + 1) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  rfl

/-- **Reduction to finitely presented modules.** Let `S ≅ Spec R`, where every faithfully flat
ind-étale `R`-algebra has a retraction, and `W` the terminal object of the small pro-étale site
of `S`. For a complex `M` of `B`-modules, if the complex of sections over `W` of `M ⊗_B P` is
acyclic for every finitely presented `P = coker (B^m ⟶ B^n)`, then so is the complex of sections
over `W` of `M ⊗_B N` for every `N`. -/
theorem acyclic_modSections_tensorRight_of_finitelyPresented {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : S ≅ Spec R) [Abelian.HasFunctorialFlatResolution 𝒟] (M : CochainComplex 𝒟 ℤ)
    (hM : ∀ (m n : ℕ) (T : (∐ fun _ : Fin m ↦ 𝟙_ 𝒟) ⟶ (∐ fun _ : Fin n ↦ 𝟙_ 𝒟)),
      (((modSections (Scheme.ProEt.mk (𝟙 S))).mapHomologicalComplex (.up ℤ)).obj
        (((tensorRight (cokernel T)).mapHomologicalComplex (.up ℤ)).obj M)).Acyclic)
    (N : 𝒟) :
    (((modSections (Scheme.ProEt.mk (𝟙 S))).mapHomologicalComplex (.up ℤ)).obj
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj M)).Acyclic := by
  rw [acyclic_modSections_tensorRight_iff]
  intro p
  exact forall_exists_modSections_of_finitelyPresented (Scheme.ProEt.isTerminalMkId S) hR e
    (M.d (p - 1) p) (M.d p (p + 1))
    (fun m n T ↦ (acyclic_modSections_tensorRight_iff _ M (cokernel T)).1 (hM m n T) p) N

end AlgebraicGeometry.ProEtale
