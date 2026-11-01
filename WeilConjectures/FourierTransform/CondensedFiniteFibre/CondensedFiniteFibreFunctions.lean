/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.FiniteEtaleStalk
public import WeilConjectures.WeilObject.Sheaf.StalkUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.WeilSheaf.LocalFrobeniusLarge.LocalFrobeniusLargeCoefficients
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.TraceFormula.PointFiberFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import WeilConjectures.FourierTransform.CondensedUnitFibre.CondensedUnitFibreMaps

/-!
# Functions on a finite étale fibre with condensed coefficients

Source: blueprint latest, `sec-fourier-transform/sk-lem-as-properties/lem-fd-as-trace.proof.md`,
first paragraph (blueprint: lem-fd-condensed-finite-fibre-functions).

The auxiliary maps below are the actual coefficient-unit comparisons and counit projections.
The statement includes their universal property, scalar sections, functoriality, Frobenius and
idempotent images. No comparison map is supplied as unconstrained data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedFiniteFibre

private theorem unitPullback_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T U V : Scheme.{u}} (a : T ⟶ U) (b : U ⟶ V) :
    (upperStarComp Λ a b).hom.app (unit Λ V) ≫
      (upperStar Λ a).map (unitPullback Λ b).hom ≫
      (unitPullback Λ a).hom = (unitPullback Λ (a ≫ b)).hom := by
  exact upperStarComp_hom_app_unit Λ a b

private theorem baseChange_projection_units
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y X Y' X' P : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}
    {a : Y' ⟶ Y} {b : X' ⟶ X} (sq : CommSq a f' f b)
    (x : P ⟶ X') (y : P ⟶ Y') (hy : y ≫ f' = x)
    (hxy : (y ≫ a) ≫ f = x ≫ b)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (N : Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj Λ Y'))
    (W : Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1}) (condensedRingObj Λ P))
    (ua : (upperStar Λ a).obj M ⟶ N) (uy : (upperStar Λ y).obj N ⟶ W)
    (uya : (upperStar Λ (y ≫ a)).obj M ⟶ W)
    (hu : (upperStarComp Λ y a).hom.app M ≫ (upperStar Λ y).map ua ≫ uy = uya) :
    (upperStarComp Λ x b).hom.app ((lowerStar Λ f).obj M) ≫
      (upperStar Λ x).map ((lowerStarBaseChange Λ sq).app M ≫ (lowerStar Λ f').map ua) ≫
      (stalkLowerStarProj Λ hy N ≫ uy) = stalkLowerStarProj Λ hxy M ≫ uya := by
  simp only [Functor.map_comp, Category.assoc]
  rw [stalkLowerStarProj_naturality_assoc Λ hy ua,
    stalkLowerStarProj_lowerStarBaseChange'_assoc Λ sq hy hxy, hu]

private theorem component_comp_left
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y X P Q : Scheme.{u}} (f : Y ⟶ X) (σ : Q ⟶ P)
    (x : P ⟶ X) (y : P ⟶ Y) (hy : y ≫ f = x)
    (hy' : (σ ≫ y) ≫ f = σ ≫ x) :
    component Λ f (σ ≫ x) (σ ≫ y) hy' =
      (upperStarComp Λ σ x).hom.app (push Λ f) ≫
      (upperStar Λ σ).map (component Λ f x y hy) ≫
      (unitPullback Λ σ).hom := by
  have hu : (upperStarComp Λ σ y).inv.app (unit Λ Y) ≫
      (unitPullback Λ (σ ≫ y)).hom =
      (upperStar Λ σ).map (unitPullback Λ y).hom ≫
        (unitPullback Λ σ).hom := by
    apply (cancel_epi ((upperStarComp Λ σ y).hom.app
      (unit Λ Y))).mp
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
      (unitPullback_comp Λ σ y).symm
  rw [component, component,
    stalkLowerStarProj_comp_left Λ σ hy hy']
  simp only [Functor.map_comp, Category.assoc]
  rw [hu]

private theorem component_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y X P : Scheme.{u}} (f : Y ⟶ X) {x x' : P ⟶ X} {y y' : P ⟶ Y}
    (ex : x = x') (ey : y = y') (hy : y ≫ f = x) (hy' : y' ≫ f = x') :
    (upperStarCongr Λ ex).hom.app (push Λ f) ≫
      component Λ f x' y' hy' = component Λ f x y hy := by
  subst ex
  subst ey
  simp [upperStarCongr_self]

private theorem baseChange_units_paste
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y X Y' X' Y'' X'' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {f'' : Y'' ⟶ X''}
    {a : Y' ⟶ Y} {b : X' ⟶ X} {a' : Y'' ⟶ Y'} {b' : X'' ⟶ X'}
    (sq : CommSq a f' f b) (sq' : CommSq a' f'' f' b')
    (sq'' : CommSq (a' ≫ a) f'' f (b' ≫ b))
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (N : Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj Λ Y'))
    (O : Mod (Sheaf (Scheme.ProEt.topology Y'') Ab.{u + 1}) (condensedRingObj Λ Y''))
    (ua : (upperStar Λ a).obj M ⟶ N) (ua' : (upperStar Λ a').obj N ⟶ O)
    (uaa : (upperStar Λ (a' ≫ a)).obj M ⟶ O)
    (hu : (upperStarComp Λ a' a).hom.app M ≫ (upperStar Λ a').map ua ≫ ua' = uaa) :
    (upperStarComp Λ b' b).hom.app ((lowerStar Λ f).obj M) ≫
      (upperStar Λ b').map ((lowerStarBaseChange Λ sq).app M ≫ (lowerStar Λ f').map ua) ≫
      ((lowerStarBaseChange Λ sq').app N ≫ (lowerStar Λ f'').map ua') =
      (lowerStarBaseChange Λ sq'').app M ≫ (lowerStar Λ f'').map uaa := by
  have hn := (lowerStarBaseChange Λ sq').naturality ua
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((upperStar Λ b').map ((lowerStar Λ f').map ua)), hn,
    Category.assoc, ← Category.assoc ((upperStar Λ b').map
      ((lowerStarBaseChange Λ sq).app M)), ← Category.assoc,
    lowerStarBaseChange_app_paste Λ sq sq' sq'' M]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [hu]

private theorem exchange_paste
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y X Y' X' Y'' X'' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {f'' : Y'' ⟶ X''}
    {a : Y' ⟶ Y} {b : X' ⟶ X} {a' : Y'' ⟶ Y'} {b' : X'' ⟶ X'}
    (sq : CommSq a f' f b) (sq' : CommSq a' f'' f' b')
    (sq'' : CommSq (a' ≫ a) f'' f (b' ≫ b)) :
    (upperStarComp Λ b' b).hom.app (push Λ f) ≫
      (upperStar Λ b').map (exchange Λ sq) ≫
      exchange Λ sq' = exchange Λ sq'' := by
  unfold exchange
  exact baseChange_units_paste Λ sq sq' sq''
    (unit Λ Y) (unit Λ Y') (unit Λ Y'') (unitPullback Λ a).hom
    (unitPullback Λ a').hom (unitPullback Λ (a' ≫ a)).hom (unitPullback_comp Λ a' a)

private theorem returnEnd_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] [IsSepClosed k]
    {Y X : Scheme.{u}} {f : Y ⟶ X} {a : Y ⟶ Y} {b : X ⟶ X}
    (sq : CommSq a f f b) (σ : Spec (.of k) ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ b = σ ≫ x) :
    returnEnd Λ sq σ x hx = (pointComparison Λ
      (upperStarIsoIdOfIsSepClosed Λ σ) b hx).hom.app (push Λ f) ≫
        (upperStar Λ x).map (exchange Λ sq) := rfl

private theorem natural_exchange_commutes {C E : Type*} [Category C] [Category E]
    (L : C ⥤ E) (B : C ⥤ C) (α : L ⋙ 𝟭 E ⟶ B ⋙ L) {M : C}
    (e : End M) (t : B.obj M ⟶ M) (ht : B.map e ≫ t = t ≫ e) :
    L.map e ≫ (α.app M ≫ L.map t) = (α.app M ≫ L.map t) ≫ L.map e := by
  have hn := α.naturality e
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← L.map_comp, ht,
    L.map_comp, Category.assoc]

private theorem returnEnd_commutes
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] [IsSepClosed k]
    {Y X : Scheme.{u}} {f : Y ⟶ X} {a : Y ⟶ Y} {b : X ⟶ X}
    (sq : CommSq a f f b) (σ : Spec (.of k) ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ b = σ ≫ x)
    (e : End (push Λ f))
    (he : (upperStar Λ b).map e ≫ exchange Λ sq = exchange Λ sq ≫ e) :
    (upperStar Λ x).map e ≫ returnEnd Λ sq σ x hx =
      returnEnd Λ sq σ x hx ≫ (upperStar Λ x).map e := by
  exact natural_exchange_commutes (upperStar Λ x) (upperStar Λ b)
    (pointComparison Λ (upperStarIsoIdOfIsSepClosed Λ σ) b hx).hom e (exchange Λ sq) he

/-- The coefficient unit, using the recorded pulled-back condensed ring.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
abbrev unit (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  CondensedUnitFibre.unit (Profinite.padicAlgClRingObj l) T

/-- The canonical unit comparison, in the direction from the pullback to the unit.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
abbrev unitPullback (l : ℕ) [Fact l.Prime] {T U : Scheme.{u}} (a : T ⟶ U) :=
  CondensedUnitFibre.unitPullback (Profinite.padicAlgClRingObj l) a

/-- Direct image of the coefficient unit.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
abbrev push (l : ℕ) [Fact l.Prime] {Y X : Scheme.{u}} (f : Y ⟶ X) :=
  CondensedUnitFibre.push (Profinite.padicAlgClRingObj l) f

/-- The counit projection followed by the canonical coefficient-unit comparison.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
abbrev component (l : ℕ) [Fact l.Prime] {Y X P : Scheme.{u}} (f : Y ⟶ X)
    (x : P ⟶ X) (y : P ⟶ Y) (h : y ≫ f = x) :=
  CondensedUnitFibre.component (Profinite.padicAlgClRingObj l) f x y h

/-- The coefficient-unit exchange attached to a commutative square. For an isomorphism
square this is the induced Weil structure; for maps of covers it is pullback of functions.
Source: blueprint finite-fibre paragraph (blueprint: lem-fd-condensed-finite-fibre-functions). -/
abbrev exchange (l : ℕ) [Fact l.Prime] {Y X Y' X' : Scheme.{u}}
    {f : Y ⟶ X} {f' : Y' ⟶ X'} {a : Y' ⟶ Y} {b : X' ⟶ X}
    (sq : CommSq a f' f b) :=
  CondensedUnitFibre.exchange (Profinite.padicAlgClRingObj l) sq

/-- The canonical scalar of an endomorphism of the unit at an algebraically closed point.
The inverse regular-endomorphism equivalence recovers its global section; the coefficient
section equivalence recovers the function, evaluated at the unique point.
Source: blueprint scalar-fibre clause (blueprint: lem-fd-condensed-finite-fibre-functions). -/
def scalar (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (e : End (CondensedUnitFibre.unit (Profinite.padicAlgClRingObj l) (Spec (.of k)))) :
        PadicAlgCl l :=
  ((padicAlgClSectionRingEquiv l (Spec (.of k))).symm
    ((RingEquiv.ofBijective Mod.regularEndRingHom
      Mod.regularEndRingHom_bijective).symm e)).1 (IsLocalRing.closedPoint k)

/-- Scalar fibre coordinates are obtained by the actual counit projections, with sections
represented by maps from the regular module. This is the usual terminal-section convention.
Source: blueprint scalar-fibre clause (blueprint: lem-fd-condensed-finite-fibre-functions). -/
def coordinates (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (x : Spec (.of k) ⟶ X)
    (v : CondensedUnitFibre.unit (Profinite.padicAlgClRingObj l) (Spec (.of k)) ⟶
      (upperStar (Profinite.padicAlgClRingObj l) x).obj (CondensedUnitFibre.push
          (Profinite.padicAlgClRingObj l) f)) :
    FibrePoints f x → PadicAlgCl l :=
  fun y ↦ scalar l (v ≫ CondensedUnitFibre.component (Profinite.padicAlgClRingObj l) f x y.1 y.2)

/-- Base change of a morphism to the datum's chosen algebraic closure. This uses exactly
`FiniteFieldDatum.geometricFiber`, rather than a second choice of algebraic closure.
Source: blueprint finite-cover setup (blueprint: lem-fd-condensed-finite-fibre-functions). -/
@[irreducible] def geometricMap (D : FiniteFieldDatum.{u})
    {Y₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (f₀ : Y₀ ⟶ X₀) :
    (D.geometricFiber Y₀).left ⟶ (D.geometricFiber X₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- The canonical Weil structure on the direct image of the coefficient unit, for a square of
isomorphisms: the base-change exchange followed by the direct image of the coefficient-unit
comparison. Its forward map is `CondensedUnitFibre.exchange (Profinite.padicAlgClRingObj l) sq`.
Source: blueprint finite-fibre paragraph, induced Weil structure
(blueprint: lem-fd-condensed-finite-fibre-functions). -/
abbrev weil (l : ℕ) [Fact l.Prime] {Y X : Scheme.{u}} {f : Y ⟶ X} {a : Y ⟶ Y} {b : X ⟶ X}
    [IsIso a] [IsIso b] (sq : CommSq a f f b) :=
  CondensedUnitFibre.weil (Profinite.padicAlgClRingObj l) sq

/-- The local return operator of the induced coefficient-unit Weil structure.
Source: blueprint local Frobenius clause (blueprint: lem-fd-condensed-finite-fibre-functions). -/
abbrev returnEnd (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [IsSepClosed k]
    {Y X : Scheme.{u}} {f : Y ⟶ X} {a : Y ⟶ Y} {b : X ⟶ X}
    (sq : CommSq a f f b) (σ : Spec (.of k) ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ b = σ ≫ x) :=
  CondensedUnitFibre.returnEnd (Profinite.padicAlgClRingObj l) sq σ x hx

private theorem scalar_add (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (e f : End (CondensedUnitFibre.unit (Profinite.padicAlgClRingObj l) (Spec (.of k)))) :
        scalar l (e + f) = scalar l e + scalar l f := by
  simp only [scalar, map_add]
  rfl

private theorem scalar_comp (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (e f : End (CondensedUnitFibre.unit (Profinite.padicAlgClRingObj l) (Spec (.of k)))) :
        scalar l (e ≫ f) = scalar l e * scalar l f := by
  change scalar l (f * e) = _
  simp only [scalar, map_mul]
  exact mul_comm _ _

private theorem scalar_bijective (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] :
    Function.Bijective (scalar l (k := k)) := by
  let a := (RingEquiv.ofBijective
    (Mod.regularEndRingHom
      (R := condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of k))))
    Mod.regularEndRingHom_bijective).symm
  let b := (padicAlgClSectionRingEquiv l (Spec (.of k))).symm
  have heval : Function.Bijective
      (fun f : PadicAlgCl.finiteIntermediateFieldValued l (Spec (.of k)) ↦
        f.1 (IsLocalRing.closedPoint k)) := by
    constructor
    · intro f g h
      apply Subtype.ext
      apply ContinuousMap.ext
      intro x
      have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      simpa only [hx] using h
    · intro c
      refine ⟨⟨ContinuousMap.const _ c, ?_⟩, rfl⟩
      exact ⟨IntermediateField.adjoin ℚ_[l] {c},
        IntermediateField.finiteDimensional_adjoin fun z _ ↦ Algebra.IsIntegral.isIntegral z,
        fun _ ↦ IntermediateField.subset_adjoin ℚ_[l] _ (Set.mem_singleton c)⟩
  exact heval.comp (b.bijective.comp a.bijective)

private theorem coordinates_add_abstract {C : Type*} [Category C] [Preadditive C]
    {I R : Type*} [Add R] {U M : C} (p : I → (M ⟶ U))
    (s : End U → R) (hs : ∀ a b, s (a + b) = s a + s b) (v w : U ⟶ M) :
    (fun y ↦ s ((v + w) ≫ p y)) =
      (fun y ↦ s (v ≫ p y)) + (fun y ↦ s (w ≫ p y)) := by
  funext y
  rw [Preadditive.add_comp, hs]
  rfl

private theorem fan_coordinates_bijective {C : Type*} [Category C] {I V : Type*}
    (U M : C) (p : I → (M ⟶ U)) (s : End U → V) (hs : Function.Bijective s)
    (h : IsLimit (Fan.mk M p)) :
    Function.Bijective (fun v : U ⟶ M ↦ fun i ↦ s (v ≫ p i)) := by
  constructor
  · intro v w heq
    apply Fan.IsLimit.hom_ext h
    intro i
    exact hs.injective (congrFun heq i)
  · intro v
    choose w hw using fun i ↦ hs.surjective (v i)
    refine ⟨Fan.IsLimit.lift h w, ?_⟩
    funext i
    exact (congrArg s (Fan.IsLimit.fac h w i)).trans (hw i)

private theorem image_idempotent {C : Type*} [Category C] [HasImages C]
    {M : C} (e : End M) [Epi (factorThruImage e)] (he : e ≫ e = e) :
    image.ι e ≫ e = image.ι e := by
  apply (cancel_epi (factorThruImage e)).mp
  simpa only [← Category.assoc, image.fac] using he

private theorem image_coordinate_range {C E : Type*} [Category C] [Category E]
    [HasImages C] (L : C ⥤ E) {M : C} (e : End M) [Epi (factorThruImage e)]
    (he : e ≫ e = e) {U : E} {V : Type*} (φ : (U ⟶ L.obj M) → V) :
    Set.range (fun v : U ⟶ L.obj (image e) ↦ φ (v ≫ L.map (image.ι e))) =
      Set.range (fun v : U ⟶ L.obj M ↦ φ (v ≫ L.map e)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨v ≫ L.map (image.ι e), ?_⟩
    apply congrArg φ
    rw [Category.assoc, ← L.map_comp, image_idempotent e he]
  · rintro _ ⟨v, rfl⟩
    refine ⟨v ≫ L.map (factorThruImage e), ?_⟩
    apply congrArg φ
    rw [Category.assoc, ← L.map_comp, image.fac]

private theorem restrict_image {C E : Type*} [Category C] [Category E] [HasImages C]
    (L : C ⥤ E) [L.PreservesMonomorphisms] {M : C} (e : End M)
    [Epi (factorThruImage e)] (he : e ≫ e = e) (T : End (L.obj M))
    (hc : L.map e ≫ T = T ≫ L.map e) :
    ∃! S : End (L.obj (image e)), S ≫ L.map (image.ι e) = L.map (image.ι e) ≫ T := by
  have hri : L.map (factorThruImage e) ≫ L.map (image.ι e) = L.map e := by
    rw [← L.map_comp, image.fac]
  have hie : L.map (image.ι e) ≫ L.map e = L.map (image.ι e) := by
    rw [← L.map_comp, image_idempotent e he]
  refine ⟨L.map (image.ι e) ≫ T ≫ L.map (factorThruImage e), ?_, ?_⟩
  · simp only [Category.assoc]
    rw [hri, ← hc, ← Category.assoc, hie]
  · intro S hS
    apply (cancel_mono (L.map (image.ι e))).mp
    rw [hS]
    simp only [Category.assoc]
    rw [hri, ← hc, ← Category.assoc, hie]

private theorem power_square {Y X : Scheme.{u}} {f : Y ⟶ X}
    {a : Y ⟶ Y} {b : X ⟶ X} (sq : CommSq a f f b) (n : ℕ) :
    CommSq (localPositivePower a n) f f (localPositivePower b n) := by
  induction n with
  | zero => exact sq
  | succ n ih =>
    constructor
    simp only [localPositivePower, Category.assoc]
    rw [sq.w, ← Category.assoc, ih.w, Category.assoc]

private theorem isoChain_succ {C : Type*} [Category C] (P : ℕ → C) (M : C)
    (initial : P 0 ≅ M) (step : ∀ n, P (n + 1) ≅ P n) (n : ℕ) :
    CondensedModule.isoChain P M initial step (n + 1) =
      step n ≪≫ CondensedModule.isoChain P M initial step n := rfl

private theorem power_isIso {T : Scheme.{u}} (a : T ⟶ T) [IsIso a] (n : ℕ) :
    IsIso (localPositivePower a n) := by
  induction n with
  | zero => exact inferInstanceAs (IsIso a)
  | succ n ih =>
    let := ih
    change IsIso (localPositivePower a n ≫ a)
    infer_instance

private theorem isoChain_eq {C : Type*} [Category C] (P : ℕ → C) (M : C)
    (initial : P 0 ≅ M) (step : ∀ n, P (n + 1) ≅ P n) (m : ∀ n, P n ≅ M)
    (h₀ : initial = m 0) (hs : ∀ n, step n ≪≫ m n = m (n + 1)) (n : ℕ) :
    CondensedModule.isoChain P M initial step n = m n := by
  induction n with
  | zero => exact h₀
  | succ n ih => rw [isoChain_succ, ih, hs]

private theorem evaluateInitial_refl {C : Type*} [Category C]
    (F : C ⥤ C) (M : C) (θ : F.obj M ≅ M) :
    CondensedModule.evaluateInitial F F (Iso.refl F) M θ = θ := by
  apply Iso.ext
  simp [CondensedModule.evaluateInitial]

private def genericIterate {C : Type*} [Category C] {T : Scheme.{u}}
    (U : (T ⟶ T) → C ⥤ C)
    (c : ∀ r s, U (r ≫ s) ≅ U s ⋙ U r)
    (e : ∀ {r s : T ⟶ T}, r = s → (U r ≅ U s))
    (a : T ⟶ T) (M : C) (θ : (U a).obj M ≅ M) :
    ∀ n, (U (localPositivePower a n)).obj M ≅ M :=
  CondensedModule.isoChain (fun n ↦ (U (localPositivePower a n)).obj M) M
    (CondensedModule.evaluateInitial (U (localPositivePower a 0)) (U a) (e rfl) M θ)
    (fun n ↦ CondensedModule.evaluateStep (U (localPositivePower a n)) (U a)
      (U (localPositivePower a (n + 1))) (c (localPositivePower a n) a) M θ)

private def coefficientIterate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {T : Scheme.{u}} (a : T ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (θ : (upperStar Λ a).obj M ≅ M) :=
  genericIterate (fun r ↦ upperStar Λ r) (fun r s ↦ upperStarComp Λ r s)
    (fun h ↦ upperStarCongr Λ h) a M θ

private theorem genericIterate_square {C : Type*} [Category C]
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : (X ⟶ X) → C ⥤ C)
    (c : ∀ r s, U (r ≫ s) ≅ U s ⋙ U r)
    (e : ∀ {r s : X ⟶ X}, r = s → (U r ≅ U s))
    (he : ∀ r, e (r := r) rfl = Iso.refl (U r)) (M : C)
    (W : ∀ {a : Y ⟶ Y} {b : X ⟶ X}, IsIso a → IsIso b →
      CommSq a f f b → ((U b).obj M ≅ M))
    (hW : ∀ {a a' : Y ⟶ Y} {b b' : X ⟶ X}
      (ha : IsIso a) (ha' : IsIso a') (hb : IsIso b) (hb' : IsIso b')
      (sq : CommSq a f f b) (sq' : CommSq a' f f b')
      (sq'' : CommSq (a' ≫ a) f f (b' ≫ b)),
      (c b' b).app M ≪≫ (U b').mapIso (W ha hb sq) ≪≫ W ha' hb' sq' =
        W (by let := ha; let := ha'; infer_instance)
          (by let := hb; let := hb'; infer_instance) sq'')
    {a : Y ⟶ Y} {b : X ⟶ X} [ha : IsIso a] [hb : IsIso b]
    (sq : CommSq a f f b) :
    genericIterate U c e b M (W ha hb sq) =
      (fun n ↦ W (power_isIso a n) (power_isIso b n) (power_square sq n)) := by
  funext n
  unfold genericIterate
  refine isoChain_eq _ _ _ _
    (fun m ↦ W (power_isIso a m) (power_isIso b m) (power_square sq m)) ?_ ?_ n
  · simp only [localPositivePower, he, evaluateInitial_refl]
  · intro m
    unfold CondensedModule.evaluateStep
    simpa only [Iso.trans_assoc] using
      hW ha (power_isIso a m) hb (power_isIso b m)
        sq (power_square sq m) (power_square sq (m + 1))

private theorem iterate_eq_coefficient (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (a : T ⟶ T) (M : CondensedModule.Modules l T)
    (θ : (upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M) :
    CondensedModule.iterate l a M θ =
      coefficientIterate (Profinite.padicAlgClRingObj l) a M θ := by
  unfold CondensedModule.iterate coefficientIterate genericIterate CondensedModule.iterateStep
  rfl

private def fibrePermutation {Y X P : Scheme.{u}} {f : Y ⟶ X}
    (a : Aut Y) (b : Aut X) (σ : Aut P) (sq : CommSq a.hom f f b.hom)
    (x : P ⟶ X) (hx : x ≫ b.hom = σ.hom ≫ x) : FibrePoints f x ≃ FibrePoints f x where
  toFun y := ⟨σ.inv ≫ y.1 ≫ a.hom, by
    simp only [Category.assoc, sq.w]
    rw [← Category.assoc y.1 f b.hom, y.2, hx]
    simp⟩
  invFun y := ⟨σ.hom ≫ y.1 ≫ a.inv, by
    have hi : a.inv ≫ f = f ≫ b.inv := by
      apply (cancel_epi a.hom).mp
      simp only [Iso.hom_inv_id_assoc]
      rw [← Category.assoc, sq.w, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [Category.assoc, hi]
    rw [← Category.assoc y.1 f b.inv, y.2, ← Category.assoc, ← hx]
    simp⟩
  left_inv y := by
    apply Subtype.ext
    simp [Category.assoc]
  right_inv y := by
    apply Subtype.ext
    simp [Category.assoc]

private theorem fibrePermutation_spec {Y X P : Scheme.{u}} {f : Y ⟶ X}
    (a : Aut Y) (b : Aut X) (σ : Aut P) (sq : CommSq a.hom f f b.hom)
    (x : P ⟶ X) (hx : x ≫ b.hom = σ.hom ≫ x) (y : FibrePoints f x) :
    σ.hom ≫ (fibrePermutation a b σ sq x hx y).1 = y.1 ≫ a.hom := by
  simp [fibrePermutation]

private theorem geometric_square (D : FiniteFieldDatum.{u})
    {Y₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (f₀ : Y₀ ⟶ X₀) :
    CommSq (D.geometricFrobenius Y₀).hom (geometricMap D f₀) (geometricMap D f₀)
      (D.geometricFrobenius X₀).hom := by
  let := Fintype.ofFinite D.k₀
  let τ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
  let g := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have hfst : geometricMap D f₀ ≫ pullback.fst X₀.hom g =
      pullback.fst Y₀.hom g ≫ f₀.left := by
    simp only [geometricMap, Over.pullback_map_left, g, pullback.lift_fst]
  have hsnd : geometricMap D f₀ ≫ pullback.snd X₀.hom g = pullback.snd Y₀.hom g := by
    simp only [geometricMap, Over.pullback_map_left, g, pullback.lift_snd]
  constructor
  change D.galoisMap Y₀.hom τ ≫ geometricMap D f₀ =
    geometricMap D f₀ ≫ D.galoisMap X₀.hom τ
  apply pullback.hom_ext
  · rw [Category.assoc, hfst, ← Category.assoc, (D.galoisMap_projections Y₀.hom τ).1,
      Category.assoc, (D.galoisMap_projections X₀.hom τ).1, hfst]
  · rw [Category.assoc, hsnd, (D.galoisMap_projections Y₀.hom τ).2,
      Category.assoc, (D.galoisMap_projections X₀.hom τ).2, ← Category.assoc, hsnd]
-- The concrete comparison interface contains many nested pullback functors.

set_option maxHeartbeats 0 in
-- The kernel compares the exact pullback and monoidal unit instances under the field binders.
end WeilConjectures.CondensedFiniteFibre
