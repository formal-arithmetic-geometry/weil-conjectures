/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Sheaf.Paper.RingedTopoiTensorSections
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Paper.RingedTopoiDerivedPullback

/-! # Compatible central scalars and derived ringed-topos pullback

Source: Stacks Project, Cohomology on Sites, Tag 06YY (lemma-derived-base-change),
Modules on Sites, Tag 03D6 (definition-pushforward), and Conventions, section-algebra.
The compatible-central-scalar refinement is the agent-supplied prerequisite implicit
in the K-flat computation (blueprint: lem-pur-ringed-derived-pullback-linear).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Restrict the existing global-section action on module-sheaf Hom groups along `s`.
On a morphism `f`, its value at `U,x` is `(s r).val U • f.val.app U x`.
This is the actual sectionwise action, with Mathlib's existing preadditive structure.

Source: Stacks Project, Modules on Sites, Tag 03D6; Conventions, section-algebra
(blueprint: lem-pur-ringed-derived-pullback-linear). -/
@[instance_reducible]
noncomputable def scalarSectionLinear
    (R : Type v) [CommRing R] {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J CommRingCat.{u})
    (s : R →+* RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    Linear R (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A)) := by
  letI : Linear (RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf A)) :=
    homLinear A.obj (RingedTensor.ringSheaf A).property
  exact
    { homModule := fun M N ↦ Module.compHom (M ⟶ N) s
      smul_comp := fun M N P r f g ↦ Linear.smul_comp M N P (s r) f g
      comp_smul := fun M N P f r g ↦ Linear.comp_smul M N P f (s r) g }

set_option maxHeartbeats 400000 in
-- Elaborating the sectionwise scalar actions and the large dependent derived-functor
-- interface exceeds the default heartbeat budget; compilation stays below 60 seconds.
set_option backward.isDefEq.respectTransparency false in
/-- Canonical K-flat derived pullback is linear over compatible actual scalar sections.
The two module-category structures are the explicitly constructed sectionwise actions;
the derived structures are Mathlib's induced localization structures. The universal
property on `LF,epsilon` specifies the left derived functor, not an arbitrary functor
with objectwise comparison isomorphisms. It includes the canonical K-flat construction
of `ringedTopoiDerivedPullback` and every realization canonically isomorphic to it.
The generalized-element form of `hs` says exactly that the structural map sends the
inverse image of each global scalar section to the specified target scalar section.

Source: Stacks Project, Cohomology on Sites, Tag 06YY (lemma-derived-base-change),
Modules on Sites, Tag 03D6, and Conventions, section-algebra. The scalar refinement
is agent supplied (blueprint: lem-pur-ringed-derived-pullback-linear).

Proof:
1. For the test sheaf underlying a module M, transport the equation expressing scalar
multiplication by `sA r` through `I.moduleSMul`. Naturality of the underlying-sheaf
isomorphism identifies its image with the corresponding module endomorphism. The
compatibilities `hstruct` and `hs` identify the image of the scalar with `sB r`.
2. Tensor balancing gives `1 tensor (k • m) = c(k) • (1 tensor m)`. The module
sheafification adjunction and extension-of-scalars Hom extensionality reduce equality
of the sheaf maps to this calculation. Transport by `hobj` and `hmap`, and apply
`Functor.linear_iff`, to obtain ordinary pullback linearity.
3. The exact derived realization supplied by the existing K-flat derived-pullback
construction is additive. Uniqueness of the left derived functor transports this
additivity to the supplied realization `LF`.
4. For each scalar r compare the natural endomorphisms `LF.map (r • id)` and `r • id`
of LF. The left-derived universal property `Functor.leftDerived_ext` reduces equality
to naturality of epsilon at `r • id`. Ordinary pullback and localization are linear,
so this naturality equation is exactly the required equality. Finally use
`Functor.linear_iff` to obtain linearity on every Hom group. No additional K-flat
resolutions or flatness of the structural map are needed. -/
theorem ringedDerivedPullback_linear
    (R : Type v) [CommRing R]
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (A : Sheaf JC CommRingCat.{u}) (B : Sheaf JD CommRingCat.{u})
    (u : RingedToposMorphism
      (RingedTensor.ringSheaf B)
      (RingedTensor.ringSheaf A))
    (AI : Sheaf JD CommRingCat.{u}) (I : AlgebraicInverseImage u.inverse A AI)
    (c : AI ⟶ B)
    (hstruct : I.ringUnderlying.hom ≫
      (sheafCompose JD (CategoryTheory.forget CommRingCat)).map c = u.ringMap)
    (sA : R →+* RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat RingCat))
    (sB : R →+* RingCat.sectionsSubring (B.obj ⋙ forget₂ CommRingCat RingCat))
    (hs : ∀ (r : R) (T : Sheaf JC (Type u))
      (a : T ⟶ (sheafCompose JC (CategoryTheory.forget CommRingCat)).obj A),
      (∀ (U : Cᵒᵖ) (x : T.obj.obj U), a.hom.app U x = (sA r).val U) →
      ∀ (V : Dᵒᵖ) (x : (u.inverse.obj T).obj.obj V),
        ((u.inverse.map a) ≫ u.ringMap).hom.app V x = (sB r).val V)
    (uStar : ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A) ⥤
      ringedSiteModules.{u, u, u, u} (RingedTensor.ringSheaf B))
    (hobj : ∀ M : ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A)} (f : M ⟶ N),
      uStar.map f = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf B))]
    (LF : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf B)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf A)) (ComplexShape.up ℤ))] :
    (fun [_lA : Linear R (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf A))]
      [_lB : Linear R (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf B))] ↦
      LF.Additive ∧ Functor.Linear R LF ∧
        ∀ (X : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
          (RingedTensor.ringSheaf A))) (r : R),
          LF.map (r • (𝟙 X : X ⟶ X)) =
            r • (𝟙 (LF.obj X) : LF.obj X ⟶ LF.obj X))
      (_lA := scalarSectionLinear R A sA) (_lB := scalarSectionLinear R B sB) := by
  classical
  let := scalarSectionLinear R A sA
  let := scalarSectionLinear R B sB
  have hord : Functor.Linear R uStar := by
    rw [Functor.linear_iff]
    intro M r
    let f : M ⟶ M := r • 𝟙 M
    let T := (RingedTensor.underlying A).obj M
    let a : T ⟶ (sheafCompose JC (CategoryTheory.forget CommRingCat)).obj A :=
      ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (sA r).val U)
         naturality := fun U V i ↦ by
           ext x
           exact ((sA r).property i).symm }⟩
    have hf (U : Cᵒᵖ) (x : M.val.obj U) :
        f.val.app U x = (sA r).val U • x := by rfl
    -- Evaluate the transported scalar graph at the inverse image of an arbitrary section.
    have hi (V : Dᵒᵖ) (m : (I.modules.obj M).val.obj V) :
        ∃ k : AI.obj.obj V, (I.modules.map f).val.app V m = k • m ∧
          c.hom.app V k = (sB r).val V := by
      let x := (I.moduleUnderlying.hom.app M).hom.app V m
      refine ⟨I.ringUnderlying.hom.hom.app V ((u.inverse.map a).hom.app V x), ?_, ?_⟩
      · have ht := I.moduleSMul M T a (𝟙 T) ((RingedTensor.underlying A).map f)
          (fun U z ↦ hf U z) V x
        have hn := I.moduleUnderlying.inv.naturality f
        have hn' := congrArg (fun q ↦ q.hom.app V x) hn
        have hx := congrArg (fun q ↦ q.hom.app V m)
          (I.moduleUnderlying.hom_inv_id_app M)
        change (I.moduleUnderlying.inv.app M).hom.app V x = m at hx
        have hid : (u.inverse.map (𝟙 T)).hom.app V x = x := by
          rw [u.inverse.map_id]
          rfl
        rw [hid] at ht
        change (I.moduleUnderlying.inv.app M).hom.app V
          ((u.inverse.map ((RingedTensor.underlying A).map f)).hom.app V x) =
            I.ringUnderlying.hom.hom.app V ((u.inverse.map a).hom.app V x) •
              (show (I.modules.obj M).val.obj V from
                (I.moduleUnderlying.inv.app M).hom.app V x) at ht
        change (I.moduleUnderlying.inv.app M).hom.app V
          ((u.inverse.map ((RingedTensor.underlying A).map f)).hom.app V x) =
            (I.modules.map f).val.app V
              ((I.moduleUnderlying.inv.app M).hom.app V x) at hn'
        rw [hx] at hn' ht
        exact hn'.symm.trans ht
      · have hh := hs r T a (fun _ _ ↦ rfl) V x
        rw [← hstruct] at hh
        exact hh
    -- The sheafification adjunction lets us test the two maps on tensor generators.
    have hcor : changeOfRingsHom c (I.modules.obj M) (I.modules.map f) =
        r • 𝟙 (changeOfRings.{u, u, u} c (I.modules.obj M)) := by
      let S := PresheafOfModules.sheafification (𝟙 (RingedTensor.ringSheaf B).obj)
      let adj := PresheafOfModules.sheafificationAdjunction
        (𝟙 (RingedTensor.ringSheaf B).obj)
      let P := changeOfRingsPresheaf.{u, u, u} c (I.modules.obj M)
      let g : P ⟶ P :=
        { app := fun V ↦ (ModuleCat.extendScalars (c.hom.app V).hom).map
            ((I.modules.map f).val.app V)
          naturality := changeOfRingsHom_naturality c (I.modules.obj M) (I.modules.map f) }
      change S.map g = r • 𝟙 (S.obj P)
      apply (adj.homEquiv P (S.obj P)).injective
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
      rw [adj.unit_naturality g]
      apply PresheafOfModules.hom_ext
      intro V
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      obtain ⟨k, hk, hc⟩ := hi V m
      let := (c.hom.app V).hom.toAlgebra
      change (adj.unit.app P).app V
          ((1 : B.obj.obj V) ⊗ₜ[AI.obj.obj V] (I.modules.map f).val.app V m) =
        (sB r).val V • (adj.unit.app P).app V
          ((1 : B.obj.obj V) ⊗ₜ[AI.obj.obj V] m)
      have hb : ((1 : B.obj.obj V) ⊗ₜ[AI.obj.obj V] (k • m)) =
          (c.hom.app V k) • ((1 : B.obj.obj V) ⊗ₜ[AI.obj.obj V] m) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
        rfl
      rw [hk, hb, hc]
      exact ((adj.unit.app P).app V).hom.map_smul _ _
    change uStar.map f = r • 𝟙 (uStar.obj M)
    rw [hmap, hcor]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp,
      eqToHom_trans, eqToHom_refl]
  have := hord
  have : PreservesFiniteLimits u.inverse := u.leftExact
  obtain ⟨LF₀, ε₀, hLF₀, ⟨hshift, hexact⟩, _⟩ :=
    ringedTopoiDerivedPullback.{u, w} u.inverse u.direct u.adj I c uStar hobj hmap
  have := hLF₀
  let := hshift
  have : LF₀.IsTriangulated := hexact
  have hadd : LF.Additive := Functor.additive_of_iso
    (Functor.leftDerivedUnique (LF := LF) (LF' := LF₀) epsilon ε₀
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).symm
  have hlin : Functor.Linear R LF := by
    rw [Functor.linear_iff]
    intro X r
    let γ₁ : LF ⟶ LF :=
      { app := fun Y ↦ LF.map (r • 𝟙 Y)
        naturality := fun Y Z f ↦ by
          simp only [← LF.map_comp, Linear.comp_smul, Linear.smul_comp,
            Category.comp_id, Category.id_comp] }
    let γ₂ : LF ⟶ LF :=
      { app := fun Y ↦ r • 𝟙 (LF.obj Y)
        naturality := fun Y Z f ↦ by simp }
    -- The universal property detects equality after the canonical comparison.
    have heq : γ₁ = γ₂ := by
      apply Functor.leftDerived_ext LF epsilon
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) LF
      ext Y
      have hn := epsilon.naturality (r • 𝟙 Y)
      change LF.map (r • 𝟙 (DerivedCategory.Qh.obj Y)) ≫ epsilon.app Y =
        (r • 𝟙 (LF.obj (DerivedCategory.Qh.obj Y))) ≫ epsilon.app Y
      simpa using hn
    exact congrArg (fun γ : LF ⟶ LF ↦ γ.app X) heq
  exact ⟨hadd, hlin, fun X r ↦ by
    have := hlin
    simp⟩

end SheafOfModules
