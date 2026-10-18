/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated

import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Sheaf.Paper.ContinuousConstructibleIntegralModel
import Sheaf.Paper.ContinuousConstructibleIntegralImage
import Sheaf.Paper.ContinuousConstructibleIntegralDenominators
import all Sheaf.Paper.IntegralConstructibleSequentialHom
import Sheaf.Paper.IntegralConstructibleSheafHom
import Sheaf.Paper.ContinuousIntegralComplexTelescope
import Sheaf.Paper.ContinuousIntegralDerivedUnit
import Sheaf.Paper.ContinuousIntegralScalarExact
import Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars

/-!

# Bounded constructible `E`-coefficients as `𝒪_E`-coefficients with `ℓ` inverted

Let `X` be a scheme, `ℓ` a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`) with ring of integers `𝒪_E`. The condensed rings
`𝒪̲_E = Profinite.padicIntegersRingObj ℓ E` and `E̲ = Profinite.continuousMapRingObj E`, for the
norm of `E` restricted from `ℚ̄_ℓ`, pull back along `p_X : X_proét ⟶ *_proét` to the
coefficient ring objects `𝒪_{E,X} = p_X^* 𝒪̲_E` and `E_X = p_X^* E̲` of abelian pro-étale sheaves
on `X` (`ProEtale.condensedRingObj`), and the pullback of the inclusion `𝒪̲_E ⟶ E̲`
(`ProEtale.padicIntegersRingObjToContinuousMapRingObj`) is a morphism of ring objects
`φ : 𝒪_{E,X} ⟶ E_X` (`ProEtale.padicIntegersToPadicSubfield`).

The derived extension of scalars
```
E ⊗ᴸ_{𝒪_E} - = L(extendScalars φ) : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})
```
of `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` preserves bounded
constructible complexes (`ProEtale.boundedConstructible_derivedExtendScalars_obj`), so it
restricts to a functor
`D_cons(X_proét, 𝒪_E) ⥤ D_cons(X_proét, E)` (`ProEtale.boundedConstructibleExtendScalars`) on
the bounded constructible derived categories `ProEtale.BoundedConstructible` of
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.

For `X` topologically noetherian, this file states that the restricted functor exhibits
`D_cons(X_proét, E)` as `D_cons(X_proét, 𝒪_E)` with `ℓ` inverted: it is a localization functor
with respect to the class
`CategoryTheory.Rationalization.W (Submonoid.powers ℓ) D_cons(X_proét, 𝒪_E)` of morphisms whose
mapping cone is killed by some power `ℓⁿ`
(`ProEtale.isLocalization_boundedConstructibleExtendScalars`). Consequently
`D_cons(X_proét, E)` is equivalent to the rationalization of `D_cons(X_proét, 𝒪_E)` at the
powers of `ℓ` (`ProEtale.rationalizationEquivalence`), compatibly with the localization
functors (`ProEtale.rationalizationQCompEquivalenceIso`).

The statement is made on bounded constructible complexes only: on the full derived categories
`D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})` is not a localization at the morphisms with `ℓ`-power-torsion
mapping cone in general. The rationalization statements below retain the upstream
triangulated instance. Its arbitrary-coefficient form is disputed in its defining module;
the valid integral-coefficient specialization is proved separately in
`Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated`.

Neither description is taken as a definition: `E_X` is defined by its sections, not as
`𝒪_{E,X}[1/ℓ]`, following `WeilConjectures/RefactorInstruction.tex`. Finiteness of `E` is what
makes inverting `ℓ` the right statement: `𝒪_E` is then a discrete valuation ring in which every
nonzero element divides a power of `ℓ`.

## Sorried input

* `ProEtale.isLocalization_boundedConstructibleExtendScalars`: on bounded constructible
  complexes, `L(extendScalars φ)` is a localization functor for the morphisms with
  `ℓ`-power-torsion mapping cone.

The remaining `sorry`s are inherited from
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`,
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

-/

@[expose] public section


attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
-- Use the proved integral specialization before the generic conditional Serre instance.
attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_padicIntegers

universe u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false in
private theorem eventually_eq_of_homColimit
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {I : Type*} [SmallCategory I] [IsFiltered I] [Quiver.IsThin I]
    (D : I ⥤ C) (c : Cocone D) (K : C) (hK : homColimitProperty D c K)
    (i : I) (f g : K ⟶ D.obj i) (h : f ≫ c.ι.app i = g ≫ c.ι.app i) :
    ∃ (j : I) (u : i ⟶ j), f ≫ D.map u = g ≫ D.map u := by
  let H := shiftFunctor C (0 : ℤ) ⋙ preadditiveCoyoneda.obj (Opposite.op K)
  obtain ⟨hc⟩ : Nonempty (IsColimit (H.mapCocone c)) :=
    (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (hK 0)
  let e := shiftFunctorZero C ℤ
  let x : H.obj (D.obj i) := f ≫ e.inv.app (D.obj i)
  let y : H.obj (D.obj i) := g ≫ e.inv.app (D.obj i)
  have hxy : (H.mapCocone c).ι.app i x = (H.mapCocone c).ι.app i y := by
    change (f ≫ e.inv.app _) ≫ (shiftFunctor C (0 : ℤ)).map (c.ι.app i) =
      (g ≫ e.inv.app _) ≫ (shiftFunctor C (0 : ℤ)).map (c.ι.app i)
    have hn : e.inv.app (D.obj i) ≫ (shiftFunctor C (0 : ℤ)).map (c.ι.app i) =
        c.ι.app i ≫ e.inv.app c.pt := by
      simpa only [CategoryTheory.Functor.id_map, Functor.const_obj_obj] using
        (e.inv.naturality (c.ι.app i)).symm
    simpa only [Category.assoc, hn] using
      congrArg (fun a ↦ a ≫ e.inv.app c.pt) h
  obtain ⟨j, u, v, huv⟩ := Concrete.isColimit_exists_of_rep_eq (D ⋙ H) hc x y hxy
  have hv : v = u := Subsingleton.elim _ _
  subst v
  refine ⟨j, u, ?_⟩
  have hh := congrArg (fun z ↦ z ≫ e.hom.app (D.obj j)) huv
  change ((f ≫ e.inv.app _) ≫ (shiftFunctor C (0 : ℤ)).map (D.map u)) ≫
      e.hom.app _ = ((g ≫ e.inv.app _) ≫
        (shiftFunctor C (0 : ℤ)).map (D.map u)) ≫ e.hom.app _ at hh
  simpa only [Category.assoc, ← e.inv.naturality_assoc, CategoryTheory.Functor.id_map,
    Iso.inv_hom_id_app, Category.comp_id] using hh

private theorem isIso_pow_smul_id
    {R : Type*} {C : Type*} [CommRing R] [Category C] [Preadditive C] [Linear R C]
    (r : R) (Y : C) [IsIso (r • 𝟙 Y)] (n : ℕ) : IsIso (r ^ n • 𝟙 Y) := by
  induction n with
  | zero => simpa using (inferInstance : IsIso (𝟙 Y))
  | succ n ih =>
    have := ih
    rw [show r ^ (n + 1) • 𝟙 Y = (r ^ n • 𝟙 Y) ≫ (r • 𝟙 Y) by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, ← mul_smul,
        ← pow_succ']]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem localization_of_scalar_fractions
    {R : Type*} [CommRing R]
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear R D]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R]
    [Pretriangulated C] [IsTriangulated C]
    (M : Submonoid R) (F : C ⥤ D) [F.Linear R] [F.EssSurj]
    (hi : ∀ (m : R), m ∈ M → ∀ Y : D, IsIso (m • 𝟙 Y))
    (hd : ∀ (X Y : C) (f : F.obj X ⟶ F.obj Y),
      ∃ m ∈ M, ∃ g : X ⟶ Y, m • f = F.map g)
    (hk : ∀ (X Y : C) (f g : X ⟶ Y), F.map f = F.map g →
      ∃ m ∈ M, m • f = m • g) :
    F.IsLocalization (Rationalization.W M C) := by
  let W := Rationalization.W M C
  have hW : W.IsInvertedBy F := by
    intro X Y s hs
    obtain ⟨a, ha, r, hr⟩ := Rationalization.exists_comp_eq_smul_id hs
    obtain ⟨Z, g, h, hT, b, hb, hZ⟩ := hs
    obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₂ _ hT (b • 𝟙 Y) (by
      change (b • 𝟙 Y) ≫ g = 0
      simpa using congrArg (g ≫ ·) hZ)
    change b • 𝟙 Y = l ≫ s at hl
    have := hi a ha (F.obj X)
    have := hi b hb (F.obj Y)
    let r' := F.map r ≫ inv (a • 𝟙 (F.obj X))
    let l' : F.obj Y ⟶ F.obj X := inv (b • 𝟙 (F.obj Y)) ≫ F.map l
    have hr' : F.map s ≫ r' = 𝟙 _ := by
      simp only [r', ← Category.assoc, ← F.map_comp, hr,
        Functor.map_smul, F.map_id, IsIso.hom_inv_id]
    have hl' : l' ≫ F.map s = 𝟙 _ := by
      simp only [l', Category.assoc, ← F.map_comp, ← hl,
        Functor.map_smul, F.map_id, IsIso.inv_hom_id]
    have he : r' = l' := by
      calc
        r' = (l' ≫ F.map s) ≫ r' := by rw [hl', Category.id_comp]
        _ = l' := by rw [Category.assoc, hr', Category.comp_id]
    exact ⟨⟨r', hr', by rw [he]; exact hl'⟩⟩
  let Q := Rationalization.Q M C
  let G := Localization.Construction.lift F hW
  have fac : Q ⋙ G = F := Localization.Construction.fac F hW
  let : Localization.Lifting Q W F G := ⟨eqToIso fac⟩
  have : G.Linear R :=
    (Localization.functor_linear_iff Q W R F G).1 inferInstance
  have hmap {X Y : C} (f : X ⟶ Y) : G.map (Q.map f) = F.map f := by
    simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
      using Functor.congr_hom fac f
  have : G.Full := by
    constructor
    rintro ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ f
    change F.obj X ⟶ F.obj Y at f
    obtain ⟨m, hm, g, hg⟩ := hd X Y f
    have := Rationalization.isIso_smul_id hm (Q.obj X)
    have := hi m hm (F.obj X)
    refine ⟨inv (m • 𝟙 (Q.obj X)) ≫ Q.map g, ?_⟩
    rw [G.map_comp, G.map_inv]
    apply (cancel_epi (G.map (m • 𝟙 (Q.obj X)))).1
    rw [IsIso.hom_inv_id_assoc, hmap]
    simpa only [Functor.map_smul, G.map_id, Linear.smul_comp, Category.id_comp] using hg.symm
  have : G.Faithful := by
    constructor
    rintro ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ f g h
    change Q.obj X ⟶ Q.obj Y at f g
    obtain ⟨a, ha, f₀, hf⟩ := Rationalization.exists_smul_eq_map f
    obtain ⟨b, hb, g₀, hg⟩ := Rationalization.exists_smul_eq_map g
    have hf' : (a * b) • f = Q.map (b • f₀) := by
      rw [mul_comm, mul_smul, hf, Functor.map_smul]
    have hg' : (a * b) • g = Q.map (a • g₀) := by
      rw [mul_smul, hg, Functor.map_smul]
    obtain ⟨c, hc, hfg⟩ := hk X Y (b • f₀) (a • g₀) (by
      rw [← hmap, ← hmap, ← hf', ← hg', Functor.map_smul, Functor.map_smul, h])
    apply Rationalization.smul_left_injective (M.mul_mem hc (M.mul_mem ha hb))
    dsimp only
    rw [mul_smul, mul_smul c, hf', hg', ← Functor.map_smul,
      ← Functor.map_smul, hfg]
  have : G.EssSurj := by
    constructor
    intro Y
    obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage F Y
    exact ⟨Q.obj X, ⟨e⟩⟩
  exact ⟨hW, { }⟩

private theorem scalarSequence_map_zero
    {C : Type*} [Category C] [Preadditive C] (ℓ : ℕ) (K : C) (n : ℕ) :
    (Functor.ofSequence (fun _ ↦ ℓ • 𝟙 K)).map (homOfLE (Nat.zero_le n)) =
      ℓ ^ n • 𝟙 K := by
  induction n with
  | zero =>
    change (Functor.ofSequence (fun _ ↦ ℓ • 𝟙 K)).map (𝟙 (0 : ℕ)) = _
    change 𝟙 K = ℓ ^ 0 • 𝟙 K
    simp
  | succ n ih =>
    have h : homOfLE (Nat.zero_le (n + 1)) =
        homOfLE (Nat.zero_le n) ≫ homOfLE (Nat.le_add_right n 1) := Subsingleton.elim _ _
    rw [h, Functor.map_comp, ih, Functor.ofSequence_map_homOfLE_succ]
    change (ℓ ^ n • 𝟙 K) ≫ (ℓ • 𝟙 K) = ℓ ^ (n + 1) • 𝟙 K
    simp only [Preadditive.comp_nsmul, Category.comp_id, pow_succ, mul_smul]
    exact smul_comm _ _ _

private theorem map_comp_unit {C D : Type*} [Category C] [Category D]
    (Q : C ⥤ D) {X Y Z : C} {T : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (i : Q.obj Z ⟶ T) (j : Q.obj X ⟶ T)
    (hp : f ≫ g = h) (hz : Q.map h ≫ i = j) :
    Q.map f ≫ Q.map g ≫ i = j := by
  rw [← Category.assoc, ← Q.map_comp, hp, hz]

private theorem eq_after_unit {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) {A B Z T : C}
    (f g : A ⟶ B) (b : B ⟶ Z) (a : Z ⟶ T) (p : T ≅ G.obj (F.obj Z))
    (hu : a ≫ p.hom = adj.unit.app Z) (h : F.map f = F.map g) :
    (f ≫ b) ≫ a = (g ≫ b) ≫ a := by
  apply (cancel_mono p.hom).1
  simp only [Category.assoc, hu]
  rw [← Category.assoc, ← Category.assoc, ← adj.unit_naturality,
    ← adj.unit_naturality, F.map_comp, F.map_comp, h]

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false in
private theorem integral_map_eq_eventually
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (A B : integralConstructible ℓ E X) (f g : A ⟶ B)
    (h : (integralScalarExtension ℓ E X).map f.hom =
      (integralScalarExtension ℓ E X).map g.hom) :
    ∃ n : ℕ, ℓ ^ n • f = ℓ ^ n • g := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let C := DerivedCategory.Q.objPreimage B.obj
  let eB := DerivedCategory.Q.objObjPreimageIso B.obj
  obtain ⟨c, ⟨hc⟩, p, hp⟩ := integralComplexLocalization_colimit ℓ E X C
  obtain ⟨z, hz⟩ := integralScalar_derivedUnit_complex ℓ E X C
  dsimp only [integralScalarExtension] at z hz
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (integralScalarMap ℓ E) X)
  have hunit := map_comp_unit DerivedCategory.Q (c.ι.app 0) p.hom _ z.hom
    (adj.unit.app (DerivedCategory.Q.obj C)) hp hz
  let f' := f.hom ≫ eB.inv
  let g' := g.hom ≫ eB.inv
  have hu : DerivedCategory.Q.map (c.ι.app 0) ≫
      (DerivedCategory.Q.mapIso p ≪≫ z).hom = adj.unit.app (DerivedCategory.Q.obj C) :=
    hunit
  have hfg : f' ≫ DerivedCategory.Q.map (c.ι.app 0) =
      g' ≫ DerivedCategory.Q.map (c.ι.app 0) :=
    eq_after_unit _ _ adj f.hom g.hom eB.inv
      (DerivedCategory.Q.map (c.ι.app 0)) (DerivedCategory.Q.mapIso p ≪≫ z) hu h
  let e : ℕ ≌ AsSmall.{u + 1} ℕ := AsSmall.equiv
  let D := e.inverse ⋙ integralLocalizationSequence ℓ C
  let c' := c.whisker e.inverse
  have hc' : IsColimit c' := hc.whiskerEquivalence e.symm
  have hD : ∃ a : ℤ, ∀ n, (DerivedCategory.Q.obj (D.obj n)).IsGE a := by
    obtain ⟨a, ha⟩ := B.property.1.1
    have : B.obj.IsGE a := ha
    exact ⟨a, fun n ↦ DerivedCategory.TStructure.t.isGE_of_iso eB.symm a⟩
  let P := ObjectProperty.isoClosure (IsConstructibleModuleObject R)
  have hA : homColimitProperty (D ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.mapCocone c') A.obj := by
    apply CategoryTheory.homColimit_bounded _ _ P
    · rintro M ⟨N, hN, ⟨eN⟩⟩
      exact CategoryTheory.homColimit_iso _ _
        ((DerivedCategory.singleFunctor _ 0).mapIso eN)
        (integralConstructible_sheaf_hom_colimit ℓ E X N hN D c' ⟨hc'⟩ hD)
    · exact A.property.1
    · intro n
      exact ⟨_, A.property.2 n, ⟨Iso.refl _⟩⟩
  let : Quiver.IsThin (AsSmall.{u + 1} ℕ) := fun i j ↦
    ⟨fun f g ↦ e.inverse.map_injective (Subsingleton.elim _ _)⟩
  obtain ⟨j, v, hv⟩ := eventually_eq_of_homColimit
    (D ⋙ DerivedCategory.Q) (DerivedCategory.Q.mapCocone c') A.obj hA
    (e.functor.obj 0) f' g' hfg
  have hm : (integralLocalizationSequence ℓ C).map (e.inverse.map v) =
      ℓ ^ (e.inverse.obj j) • 𝟙 C := by
    have hv' : e.inverse.map v = homOfLE (Nat.zero_le (e.inverse.obj j)) :=
      Subsingleton.elim _ _
    rw [hv']
    exact scalarSequence_map_zero ℓ C _
  change f' ≫ DerivedCategory.Q.map ((integralLocalizationSequence ℓ C).map
      (e.inverse.map v)) = g' ≫ DerivedCategory.Q.map
        ((integralLocalizationSequence ℓ C).map (e.inverse.map v)) at hv
  rw [hm, Functor.map_nsmul, CategoryTheory.Functor.map_id] at hv
  refine ⟨e.inverse.obj j, ?_⟩
  apply (boundedConstructible R).ι.map_injective
  change ℓ ^ (e.inverse.obj j) • f.hom = ℓ ^ (e.inverse.obj j) • g.hom
  apply (cancel_mono eB.inv).1
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id,
    f', g'] using hv


set_option backward.isDefEq.respectTransparency false in
private theorem integralScalarExtension_additive
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) : (integralScalarExtension ℓ E X).Additive := by
  let F := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)
  have : PreservesFiniteLimits F := integralScalarExtension_exact ℓ E X
  change F.leftDerivedFunctor.Additive
  exact Functor.additive_of_iso F.leftDerivedFunctorIsoMapDerivedCategory.symm

set_option backward.isDefEq.respectTransparency false in
private theorem continuousScalar_isLocalization
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    [(boundedConstructible (condensedRingObj (integralCoeff ℓ E) X)).IsTriangulated]
    [(integralScalarExtension ℓ E X).Additive]
    (hP : ∀ K : integralConstructible ℓ E X,
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X)
        ((integralScalarExtension ℓ E X).obj K.obj)) :
    ((boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X)).lift
      ((boundedConstructible (condensedRingObj (integralCoeff ℓ E) X)).ι ⋙
        integralScalarExtension ℓ E X) hP).IsLocalization
      (Rationalization.W (Submonoid.powers (ℓ : ℤ)) (integralConstructible ℓ E X)) := by
  let B := BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X)
  let F := (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X)).lift
    ((boundedConstructible (condensedRingObj (integralCoeff ℓ E) X)).ι ⋙
      integralScalarExtension ℓ E X) hP
  change F.IsLocalization _
  have : F.Additive := by
    dsimp only [F]
    infer_instance
  have : F.EssSurj := by
    constructor
    intro K
    obtain ⟨M, ⟨e⟩⟩ := continuousConstructible_integral_model ℓ E X K
    exact ⟨M, ⟨ObjectProperty.isoMk _ e⟩⟩
  have hi (Y : B) : IsIso ((ℓ : ℤ) • 𝟙 Y) := by
    have : IsIso ((boundedConstructible _).ι.map ((ℓ : ℤ) • 𝟙 Y)) := by
      change IsIso ((ℓ : ℤ) • 𝟙 Y.obj)
      simpa only [natCast_zsmul] using derived_nsmul_isIso ℓ E X Y.obj
    exact isIso_of_reflects_iso _ (boundedConstructible _).ι
  apply localization_of_scalar_fractions (Submonoid.powers (ℓ : ℤ)) F
  · intro m hm Y
    obtain ⟨n, rfl⟩ := hm
    have := hi Y
    exact isIso_pow_smul_id (ℓ : ℤ) Y n
  · intro K L f
    obtain ⟨n, g, hg⟩ := continuousConstructible_clear_denominators
      ℓ E X K L f.hom
    refine ⟨(ℓ : ℤ) ^ n, ⟨n, rfl⟩, g, ?_⟩
    apply (boundedConstructible _).ι.map_injective
    change (ℓ : ℤ) ^ n • f.hom = (integralScalarExtension ℓ E X).map g.hom
    simpa only [← Nat.cast_pow, natCast_zsmul] using hg
  · intro K L f g h
    obtain ⟨n, hn⟩ := integral_map_eq_eventually ℓ E X K L f g
      (congrArg (fun v ↦ v.hom) h)
    refine ⟨(ℓ : ℤ) ^ n, ⟨n, rfl⟩, ?_⟩
    simpa only [← Nat.cast_pow, natCast_zsmul] using hn

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

-- Cache the small-colimit instances used by the graded tensor typeclasses in L(-).
local instance moduleTensorLeft_smallColimits
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  (ihom.adjunction M).leftAdjoint_preservesColimits

local instance moduleTensorRight_smallColimits
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) := by
  infer_instance

-- These direct instances avoid inspecting a graded tensor diagram during synthesis.
local instance moduleTensorLeft_preservesColimit
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {I : Type} [SmallCategory I]
    (D : I ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :
    PreservesColimit D (tensorLeft M) := by
  infer_instance

local instance moduleTensorRight_preservesColimit
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {I : Type} [SmallCategory I]
    (D : I ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :
    PreservesColimit D (tensorRight M) := by
  infer_instance

/-! ### The inclusion `𝒪_{E,X} ⟶ E_X` -/

/-- The inclusion `𝒪̲_E ⟶ E̲` of ring objects of condensed abelian groups, for a finite
subextension `E`: the abelian sheaf morphism underlying
`Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing`. -/
noncomputable def padicIntegersRingObjToContinuousMapRingObj :
    Profinite.padicIntegersRingObj.{u} ℓ E.1 ⟶ Profinite.continuousMapRingObj E.1 :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ℓ E.1)

instance : IsMonHom (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E) :=
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing.{u} ℓ E.1)))

/-- The inclusion `𝒪_{E,X} ⟶ E_X` of coefficient ring objects on `X_proét`: the pullback along
`p_X` of the inclusion `𝒪̲_E ⟶ E̲` of condensed rings. It is a morphism of ring objects, `p_X^*`
being monoidal. -/
noncomputable abbrev padicIntegersToPadicSubfield :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X ⟶
      condensedRingObj (Profinite.continuousMapRingObj E.1) X :=
  (upperStarFromPoint X).map (padicIntegersRingObjToContinuousMapRingObj ℓ E)

/-! ### Extension of scalars on bounded constructible complexes -/

/-- The derived extension of scalars `E ⊗ᴸ_{𝒪_E} - : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})` preserves
bounded constructible complexes.

Source: the exact scalar-extension argument of the rationalization comparison, using
`CondensedRing.integralScalarExtension_exact` and
`boundedConstructible_leftDerivedExtendScalars_obj`.
Proof: give E the norm induced by its fixed embedding. Its integral coefficient ring
and inclusion agree definitionally with the continuous integral coefficients. Scalar
extension is exact, so the generic finite-presentation and homology argument preserves
constructibility and the same cohomological bounds. No noetherian assumption is needed.
(blueprint: lem-sfb-extend-scalars-bounded-constructible) -/
lemma boundedConstructible_derivedExtendScalars_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X)
      ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.obj K) :=
  by
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
    let : NormedAlgebra ℚ_[ℓ] E.1 :=
      { norm_smul_le c x := by
          change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
            ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
            PadicAlgCl.norm_extends] }
    have : PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)) :=
      CondensedRing.integralScalarExtension_exact ℓ E.1 X
    exact boundedConstructible_leftDerivedExtendScalars_obj _ _ _ K hK

/-- The derived extension of scalars `E ⊗ᴸ_{𝒪_E} - : D_cons(X_proét, 𝒪_E) ⥤ D_cons(X_proét, E)`
on bounded constructible complexes: the restriction of
`L(extendScalars (padicIntegersToPadicSubfield X ℓ E))`. -/
noncomputable def boundedConstructibleExtendScalars :
    BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) ⥤
      BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X) :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙
      (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor)
    fun K ↦ boundedConstructible_derivedExtendScalars_obj X ℓ E K.obj K.property

/-- The restricted derived extension of scalars is compatible with the inclusions. -/
noncomputable def boundedConstructibleExtendScalarsCompatibility :
    boundedConstructibleExtendScalars X ℓ E ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙
        (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor :=
  ObjectProperty.liftCompιIso _ _ _

/-! ### `E` as `𝒪_E` with `ℓ` inverted -/

variable [TopologicalSpace.NoetherianSpace X]

set_option backward.isDefEq.respectTransparency false in
/-- On a topologically noetherian scheme, the derived extension of scalars
`E ⊗ᴸ_{𝒪_E} - : D_cons(X_proét, 𝒪_E) ⥤ D_cons(X_proét, E)` on bounded constructible complexes
is a localization functor with respect to the morphisms whose mapping cone is killed by some
power of `ℓ`: the bounded constructible `E`-coefficient derived category is the bounded
constructible `𝒪_E`-coefficient one with `ℓ` inverted. -/
instance isLocalization_boundedConstructibleExtendScalars :
    (boundedConstructibleExtendScalars X ℓ E).IsLocalization
      (Rationalization.W (Submonoid.powers (ℓ : ℤ))
        (BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) := by
  let : (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)).IsTriangulated :=
    isTriangulated_boundedConstructible_padicIntegers X ℓ E
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  have : (CondensedRing.integralScalarExtension ℓ E.1 X).Additive :=
    CondensedRing.integralScalarExtension_additive ℓ E.1 X
  have : (boundedConstructible
      (condensedRingObj (CondensedRing.integralCoeff ℓ E.1) X)).IsTriangulated :=
    isTriangulated_boundedConstructible_padicIntegers X ℓ E
  have hF : (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor =
      CondensedRing.integralScalarExtension ℓ E.1 X := by
    dsimp only [CondensedRing.integralScalarExtension]
    rfl
  have hP (K : CondensedRing.integralConstructible ℓ E.1 X) :
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X)
        ((CondensedRing.integralScalarExtension ℓ E.1 X).obj K.obj) := by
    rw [← hF]
    exact boundedConstructible_derivedExtendScalars_obj X ℓ E K.obj K.property
  unfold boundedConstructibleExtendScalars
  convert (CondensedRing.continuousScalar_isLocalization ℓ E.1 X hP) using 1 <;> rfl

/-- The bounded constructible `E`-coefficient derived category `D_cons(X_proét, E)` is
equivalent to the rationalization of the bounded constructible `𝒪_E`-coefficient derived
category `D_cons(X_proét, 𝒪_E)` at the powers of `ℓ`. -/
noncomputable def rationalizationEquivalence :
    Rationalization (Submonoid.powers (ℓ : ℤ))
        (BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) ≌
      BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X) :=
  Localization.uniq (Rationalization.Q _ _) (boundedConstructibleExtendScalars X ℓ E)
    (Rationalization.W (Submonoid.powers (ℓ : ℤ)) _)

/-- Under `rationalizationEquivalence`, the localization functor to the rationalization
corresponds to the derived extension of scalars `E ⊗ᴸ_{𝒪_E} -` on bounded constructible
complexes. -/
noncomputable def rationalizationQCompEquivalenceIso :
    Rationalization.Q (Submonoid.powers (ℓ : ℤ)) _ ⋙ (rationalizationEquivalence X ℓ E).functor ≅
      boundedConstructibleExtendScalars X ℓ E :=
  Localization.compUniqFunctor (Rationalization.Q _ _) _
    (Rationalization.W (Submonoid.powers (ℓ : ℤ)) _)

end AlgebraicGeometry.ProEtale
