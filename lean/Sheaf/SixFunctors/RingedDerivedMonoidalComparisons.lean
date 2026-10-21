/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.SixFunctors.RingedDerivedComparisonData
import Sheaf.SixFunctors.RingedDerivedAdjointLift
import Sheaf.SixFunctors.RingedDerivedTensorLift
import Sheaf.SixFunctors.RingedDerivedCompositionComparison
import Sheaf.SixFunctors.RingedDerivedIdentityComparison
import Sheaf.SixFunctors.RingedDerivedTwoIsoComparison
import Sheaf.CategoryTheory.GeometricModuleConstruction

/-! # Existence of normalized derived monoidal comparisons on ringed topoi

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0D6D, 07A6, 0D6E, 0FPI.
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits WeilConjectures SheafOfModules
namespace CategoryTheory.RingedDerivedComparisons

attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem geometric_composites {X Y Z : Site.{u, w}}
    (f : Morphism X Y) (g : Morphism Y Z) :
    ∃ (k : Morphism X Z) (θ : k.inverse ≅ g.inverse ⋙ f.inverse),
      k.ringMap = θ.hom.app ((sheafCompose Z.J
        (CategoryTheory.forget CommRingCat.{u})).obj Z.A) ≫
          f.inverse.map g.ringMap ≫ f.ringMap := by
  let := f.leftExact
  let := g.leftExact
  let d : RingedToposMorphism.RingData X.ring Z.ring := {
    inverse := g.inverse ⋙ f.inverse
    direct := f.direct ⋙ g.direct
    adj := g.adj.comp f.adj
    leftExact := comp_preservesFiniteLimits _ _
    ringMap := f.inverse.map g.ringMap ≫ f.ringMap
    ring_zero := by
      intro T z hz U t
      convert (by
        simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
        f.ring_zero (g.inverse.obj T) (g.inverse.map z ≫ g.ringMap)
          (g.ring_zero T z hz) U t) using 1; rfl
    ring_one := by
      intro T z hz U t
      convert (by
        simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
        f.ring_one (g.inverse.obj T) (g.inverse.map z ≫ g.ringMap)
          (g.ring_one T z hz) U t) using 1; rfl
    ring_add := by
      intro T x y z hz U t
      convert (by
        simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
        f.ring_add (g.inverse.obj T) (g.inverse.map x ≫ g.ringMap)
          (g.inverse.map y ≫ g.ringMap) (g.inverse.map z ≫ g.ringMap)
          (g.ring_add T x y z hz) U t) using 1 <;> rfl
    ring_mul := by
      intro T x y z hz U t
      convert (by
        simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
        f.ring_mul (g.inverse.obj T) (g.inverse.map x ≫ g.ringMap)
          (g.inverse.map y ≫ g.ringMap) (g.inverse.map z ≫ g.ringMap)
          (g.ring_mul T x y z hz) U t) using 1 <;> rfl }
  obtain ⟨m⟩ := SheafOfModules.ringData_inducedModules X.A Z.A d
  exact ⟨d.withModules m, Iso.refl _, (Category.id_comp _).symm⟩

private theorem geometric_identities (X : Site.{u, w}) :
    ∃ (f : Morphism X X) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))),
      f.ringMap = θ.hom.app ((sheafCompose X.J
        (CategoryTheory.forget CommRingCat.{u})).obj X.A) := by
  let f : Morphism X X := {
    inverse := 𝟭 _
    direct := 𝟭 _
    adj := Adjunction.id
    leftExact := inferInstance
    ringMap := 𝟙 _
    ring_zero := by intro T z hz U t; simpa using hz U t
    ring_one := by intro T z hz U t; simpa using hz U t
    ring_add := by intro T x y z hz U t; simpa using hz U t
    ring_mul := by intro T x y z hz U t; simpa using hz U t
    modules := 𝟭 _
    additive := inferInstance
    underlying := Iso.refl _
    module_linear := by
      intro M T a x y z hz U t
      simpa [Adjunction.homEquiv, Adjunction.id] using hz U t }
  exact ⟨f, Iso.refl _, rfl⟩

private theorem homEquiv_of_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R')
    (c : L ≅ L') (U : C) (E : D) (b : L.obj U ⟶ E) :
    a.homEquiv U E b ≫ (conjugateIsoEquiv a a' c.symm).hom.app E =
      a'.homEquiv U E (c.inv.app U ≫ b) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  let κ := conjugateIsoEquiv a a' c.symm
  change (a.unit.app U ≫ R.map b) ≫ κ.hom.app E = _
  rw [Category.assoc, κ.hom.naturality, ← Category.assoc]
  change (a.unit.app U ≫ (conjugateEquiv a a' c.inv).app (L.obj U)) ≫ _ = _
  rw [unit_conjugateEquiv, Category.assoc, ← R'.map_comp]

private theorem counit_of_homEquiv
    {C : Type*} {D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R')
    (c : L ≅ L') (κ : R ≅ R')
    (hc : ∀ (U : C) (E : D) (b : L.obj U ⟶ E),
      a.homEquiv U E b ≫ κ.hom.app E = a'.homEquiv U E (c.inv.app U ≫ b)) (E : D) :
    L.map (κ.hom.app E) ≫ c.hom.app (R'.obj E) ≫ a'.counit.app E =
      a.counit.app E := by
  have h := hc (R.obj E) E (a.counit.app E)
  rw [Adjunction.homEquiv_unit] at h
  simp only [Adjunction.right_triangle_components, Category.id_comp] at h
  have h' := congrArg (a'.homEquiv (R.obj E) E).symm h
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at h'
  rw [c.hom.naturality_assoc, h']
  simp only [Iso.hom_inv_id_app_assoc]

private theorem composition_counit_of_homEquiv {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (c : lk.edge.left ≅ lg.edge.left ⋙ lf.edge.left)
    (κ : lk.edge.right ≅ lf.edge.right ⋙ lg.edge.right)
    (hc : ∀ (U : Z.D) (E : X.D) (b : lk.edge.left.obj U ⟶ E),
      lk.edge.derivedAdjunction.homEquiv U E b ≫ κ.hom.app E =
        (lg.edge.derivedAdjunction.comp lf.edge.derivedAdjunction).homEquiv U E
          (c.inv.app U ≫ b)) (E : X.D) :
    lk.edge.left.map (κ.hom.app E) ≫
      c.hom.app ((lf.edge.right ⋙ lg.edge.right).obj E) ≫
      lf.edge.left.map (lg.edge.derivedAdjunction.counit.app (lf.edge.right.obj E)) ≫
      lf.edge.derivedAdjunction.counit.app E = lk.edge.derivedAdjunction.counit.app E := by
  simpa only [Adjunction.comp_counit_app] using
    counit_of_homEquiv lk.edge.derivedAdjunction
      (lg.edge.derivedAdjunction.comp lf.edge.derivedAdjunction) c κ hc E

private theorem tensor_model (X : Site.{u, w}) :
    ∃ r : RingedTensorModel X.corner, ∀ P Q hP hQ,
      r.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom := by
  let ι : ObjectProperty.FullSubcategory X.corner.mateFlat ⥤
      ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
        (J := X.J) (R := X.A)) := {
    obj := fun P ↦ ⟨P.obj,
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
    map := fun a ↦ ObjectProperty.homMk a.hom }
  let r : RingedTensorModel X.corner := {
    representative := Functor.isoWhiskerLeft (ι.prod ι) X.model.comparison }
  exact ⟨r, fun _ _ _ _ ↦ rfl⟩

private theorem normalizedLift_exists {X Y : Site.{u, w}} (f : Morphism X Y) :
    Nonempty (Lift f) := by
  obtain ⟨d⟩ := adjointLift_exists f
  obtain ⟨rY, hY⟩ := tensor_model Y
  obtain ⟨rX, hX⟩ := tensor_model X
  obtain ⟨t⟩ := tensorLift_exists d.edge rY rX hY hX
  exact ⟨{
    edge := d.edge
    inverse_eq := d.inverse_eq
    direct_eq := d.direct_eq
    geometric_adjunction := d.geometric_adjunction
    pushforward_eq := d.pushforward_eq
    structural_map := d.structural_map
    ordinary_adjunction := d.ordinary_adjunction
    right_additive := d.right_additive
    eta := d.eta
    isRightDerived := d.isRightDerived
    eta_injective := d.eta_injective
    epsilon_flat := d.epsilon_flat
    canonical_adjunction := d.canonical_adjunction
    tensorModelY := rY
    tensorModelX := rX
    tensorModelY_eq := hY
    tensorModelX_eq := hX
    monoidal := t.monoidal
    tensor_canonical := t.tensor_canonical
    unit_canonical := t.unit_canonical
    symmetric := t.symmetric }⟩

/-- The simultaneous normalized monoidal derived comparisons of ringed topoi.
Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0D6D, 07A6, 0D6E and 0FPI.
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons).

Proof: construct the geometric composite and identity explicitly, including their
structural ring maps and induced module direct images. For each morphism use the
normalized scalar-extension adjunction and the resolving-class derived adjunction;
restrict the site's existing tensor models to flat-term K-flat representatives.
The tensor-coherence theorem equips this adjoint lift with the required normalized
symmetric strong monoidal structure. Choose these lifts simultaneously.

Apply the composition, identity and specified geometric 2-isomorphism comparison
lemmas to these lifts. Each supplies the ordinary and derived representative
formulas and the tensor/unit diagrams. Define every derived right comparison as
the adjunction mate of its left comparison. Naturality of the unit and the mate
unit equation prove the Hom-bijection equation. For composition, evaluate that
equation on the counit, apply the inverse Hom bijection, and use naturality of
the left comparison and the triangle identity. The composite-adjunction counit
formula gives exactly the displayed four-factor counit equation. The identity
and 2-isomorphism Hom equations are the same mate calculation, in the indicated
orientations. No flatness or boundedness hypothesis is added. -/
theorem ringedDerivedMonoidalComparisons : Nonempty (System.{u, w}) := by
  classical
  let l := fun {X Y : Site.{u, w}} (f : Morphism X Y) ↦
    Classical.choice (normalizedLift_exists f)
  refine ⟨{
    lift := l
    composites := geometric_composites
    identities := geometric_identities
    composition := ?_
    identity := ?_
    twoIso := ?_ }⟩
  · intro X Y Z f g k θ hθ
    obtain ⟨c⟩ := compositionCore_exists (l f) (l g) (l k) θ hθ
    exact ⟨{
      ordinary := c.ordinary
      ordinary_insertion := c.ordinary_insertion
      ordinary_right := c.ordinary_right
      ordinary_mate := c.ordinary_mate
      pullback := c.pullback
      pullback_model := c.pullback_model
      kappa := conjugateIsoEquiv (l k).edge.derivedAdjunction
        ((l g).edge.derivedAdjunction.comp (l f).edge.derivedAdjunction) c.pullback.symm
      kappa_model := c.kappa_model
      tensor := c.tensor
      unit := c.unit
      homEquiv := homEquiv_of_conjugate (l k).edge.derivedAdjunction
        ((l g).edge.derivedAdjunction.comp (l f).edge.derivedAdjunction) c.pullback
      counit := composition_counit_of_homEquiv (l f) (l g) (l k)
        c.pullback _ (homEquiv_of_conjugate (l k).edge.derivedAdjunction
          ((l g).edge.derivedAdjunction.comp (l f).edge.derivedAdjunction) c.pullback) }⟩
  · intro X f θ hθ
    obtain ⟨c⟩ := identityComparison_exists (l f) θ hθ
    exact ⟨{
      ordinary := c.ordinary
      ordinary_insertion := c.ordinary_insertion
      ordinary_right := c.ordinary_right
      ordinary_mate := c.ordinary_mate
      pullback := c.pullback
      pullback_model := c.pullback_model
      pushforward := conjugateIsoEquiv (l f).edge.derivedAdjunction
        (Adjunction.id (C := X.D)) c.pullback.symm
      pushforward_model := c.pushforward_model
      tensor := c.tensor
      unit := c.unit
      homEquiv := homEquiv_of_conjugate (l f).edge.derivedAdjunction
        (Adjunction.id (C := X.D)) c.pullback }⟩
  · intro X Y h k θ hθ
    obtain ⟨c⟩ := twoIsoComparison_exists (l h) (l k) θ hθ
    exact ⟨{
      ordinary := c.ordinary
      ordinary_insertion := c.ordinary_insertion
      ordinary_right := c.ordinary_right
      ordinary_mate := c.ordinary_mate
      pullback := c.pullback
      pullback_model := c.pullback_model
      pushforward := conjugateIsoEquiv (l k).edge.derivedAdjunction
        (l h).edge.derivedAdjunction c.pullback
      pushforward_model := c.pushforward_model
      tensor := c.tensor
      unit := c.unit
      homEquiv := fun U E b ↦ (homEquiv_of_conjugate (l k).edge.derivedAdjunction
        (l h).edge.derivedAdjunction c.pullback.symm U E b).symm }⟩

end CategoryTheory.RingedDerivedComparisons
