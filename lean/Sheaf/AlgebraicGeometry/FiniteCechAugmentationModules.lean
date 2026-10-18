/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleGeometricFibreInverseImageConstant
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Exact finite Cech augmentation for module sheaves

Source: Stacks Project, etale-cohomology.tex, Tag 09Z2, lemma-cohomological-descent-finite,
geometric-stalk proof; the same finite-product contraction for modules
(blueprint: lem-trf-finite-cech-augmentation-modules).

The definitions fix the scheme terms, unit-defined cofaces, alternating differential,
augmentation, coefficient functors and maps of covers. The theorem asserts their exactness
and coherent naturality; it does not quantify over possible choices of these maps.
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped Simplicial

namespace AlgebraicGeometry

/-- The scheme in simplicial degree `q` of the augmented Cech nerve of `p`.
Source: Stacks Project, Tag 09Z2 (blueprint: lem-trf-finite-cech-augmentation-modules). -/
noncomputable def finiteCechScheme {Y Z : Scheme.{u}} (p : Z ⟶ Y) (q : ℕ) : Scheme :=
  (Arrow.mk p).cechNerve.obj (op ⦋q⦌)

/-- The projection to the base in degree `q` of the augmented Cech nerve.
Source: Stacks Project, Tag 09Z2 (blueprint: lem-trf-finite-cech-augmentation-modules). -/
noncomputable def finiteCechProjection {Y Z : Scheme.{u}} (p : Z ⟶ Y) (q : ℕ) :
    finiteCechScheme p q ⟶ Y :=
  (Arrow.mk p).augmentedCechNerve.hom.app (op ⦋q⦌)

/-- The module-sheaf term `p_{q*} p_q^{-1} F` of the finite Cech augmentation.
Source: Stacks Project, Tag 09Z2 (blueprint: lem-trf-finite-cech-augmentation-modules). -/
noncomputable def finiteCechTerm (Λ : Type (u + 1)) [CommRing Λ]
    {Y Z : Scheme.{u}} (p : Z ⟶ Y) (q : ℕ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (Etale.lowerStar (ModuleCat.{u + 1} Λ) (finiteCechProjection p q)).obj
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (finiteCechProjection p q)).obj F)

/-- The coefficient functor in degree `n` of the canonical Čech augmentation.
Source: Stacks Tag 09Z2 (blueprint: lem-trf-finite-cech-augmentation-modules). -/
noncomputable def finiteCechTermFunctor (Λ : Type (u + 1)) [CommRing Λ]
    {Y Z : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ) :=
  Etale.upperStar (ModuleCat.{u + 1} Λ) (finiteCechProjection p n) ⋙
    Etale.lowerStar (ModuleCat.{u + 1} Λ) (finiteCechProjection p n)

/-- The canonical restriction for a commuting triangle, obtained from the unit for `r`
and the direct/inverse-image composition comparisons. No map is chosen.
Source: Stacks Tags 09Z2 and 03CB
(blueprint: lem-trf-finite-cech-augmentation-modules). -/
noncomputable def finiteCechTriangleMap (Λ : Type (u + 1)) [CommRing Λ]
    {Y V W : Scheme.{u}} (f : V ⟶ Y) (g : W ⟶ Y) (r : W ⟶ V) (h : g = r ≫ f)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F) :=
  (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).unit.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F)) ≫
    (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) r f g h).hom.app _ ≫
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).map
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) r f g h).inv.app F)

/-- The `i`th coface is restriction along the actual coordinate-deleting projection
of the scheme Čech nerve, with its canonical coefficient transport.
Source: Stacks Tag 09Z2 (blueprint: lem-trf-finite-cech-augmentation-modules). -/
noncomputable def finiteCechCoface (Λ : Type (u + 1)) [CommRing Λ]
    {Y Z : Scheme.{u}} (p : Z ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (n : ℕ) (i : Fin (n + 2)) :
    finiteCechTerm Λ p n F ⟶ finiteCechTerm Λ p (n + 1) F :=
  finiteCechTriangleMap Λ (finiteCechProjection p n) (finiteCechProjection p (n + 1))
    ((Arrow.mk p).cechNerve.δ i) (by
      have w := (Arrow.mk p).augmentedCechNerve.hom.naturality (SimplexCategory.δ i).op
      exact (w.trans (Category.comp_id _)).symm) F

/-- The fixed alternating differential, with signs `+,-,+,...`.
Source: Stacks Tag 09Z2 (blueprint: lem-trf-finite-cech-augmentation-modules). -/
noncomputable def finiteCechDifferential (Λ : Type (u + 1)) [CommRing Λ]
    {Y Z : Scheme.{u}} (p : Z ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    finiteCechTerm Λ p n F ⟶ finiteCechTerm Λ p (n + 1) F :=
  ∑ i : Fin (n + 2), if Even (i : ℕ) then finiteCechCoface Λ p F n i
    else -finiteCechCoface Λ p F n i

/-- The augmentation is the adjunction unit in degree zero.
Source: Stacks Tag 09Z2 (blueprint: lem-trf-finite-cech-augmentation-modules). -/
noncomputable def finiteCechAugmentation (Λ : Type (u + 1)) [CommRing Λ]
    {Y Z : Scheme.{u}} (p : Z ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    F ⟶ finiteCechTerm Λ p 0 F :=
  (Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} Λ) (finiteCechProjection p 0)).unit.app F

/-- The canonical map of Čech terms induced by a map of covers. It goes from the
terms for `p` to the terms for `p'`, and applies `a` to every scheme coordinate.
Source: Stacks Tags 09Z2 and 03CB
(blueprint: lem-trf-finite-cech-augmentation-modules). -/
noncomputable def finiteCechCoverMap (Λ : Type (u + 1)) [CommRing Λ]
    {Y Z W : Scheme.{u}} (p : Z ⟶ Y) (p' : W ⟶ Y) (a : W ⟶ Z) (ha : a ≫ p = p')
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    finiteCechTerm Λ p n F ⟶ finiteCechTerm Λ p' n F :=
  finiteCechTriangleMap Λ (finiteCechProjection p n) (finiteCechProjection p' n)
    ((Arrow.mapAugmentedCechNerve (Arrow.homMk (f := Arrow.mk p') (g := Arrow.mk p)
      a (𝟙 Y) (by simpa using ha))).left.app (op ⦋n⦌)) (by
        have w := congrArg (fun t ↦ t.app (op ⦋n⦌))
          (Arrow.mapAugmentedCechNerve (Arrow.homMk (f := Arrow.mk p') (g := Arrow.mk p)
            a (𝟙 Y) (by simpa using ha))).w
        exact (w.trans (Category.comp_id _)).symm) F

/-- Exactness and coherent naturality of the *fixed* canonical augmented alternating
Čech sequence. All fields are propositions about the maps defined above; there are no
complexes, cofaces, augmentations, term isomorphisms, or comparison maps to choose.
`augmentationMono` is exactness at `F`; `augmentationExact` is exactness at degree zero;
`positiveExact` includes the square-zero equation and exactness at every later term.
Coefficient identities and composition are built into `finiteCechTermFunctor`. The final
fields state the coface and augmentation squares, mixed coefficient/cover square, and
identity and composition laws for the fixed cover maps.
Source: Stacks Tag 09Z2, with unit coherence from Tag 03CB
(blueprint: lem-trf-finite-cech-augmentation-modules). -/
structure FiniteCechAugmentationProperties (Λ : Type (u + 1)) [CommRing Λ]
    {Y Z : Scheme.{u}} (p : Z ⟶ Y) : Prop where
  augmentationMono : ∀ F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ),
    Mono (finiteCechAugmentation Λ p F)
  augmentationExact : ∀ F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ),
    ∃ h : finiteCechAugmentation Λ p F ≫ finiteCechDifferential Λ p F 0 = 0,
      (ShortComplex.mk (finiteCechAugmentation Λ p F) (finiteCechDifferential Λ p F 0)
        h).Exact
  positiveExact : ∀ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ),
    ∃ h : finiteCechDifferential Λ p F n ≫ finiteCechDifferential Λ p F (n + 1) = 0,
      (ShortComplex.mk (finiteCechDifferential Λ p F n)
        (finiteCechDifferential Λ p F (n + 1)) h).Exact
  coefficientAugmentation :
    ∀ (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (α : F ⟶ G),
      finiteCechAugmentation Λ p F ≫ (finiteCechTermFunctor Λ p 0).map α =
        α ≫ finiteCechAugmentation Λ p G
  coefficientCoface :
    ∀ (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (α : F ⟶ G)
      (n : ℕ) (i : Fin (n + 2)),
      finiteCechCoface Λ p F n i ≫ (finiteCechTermFunctor Λ p (n + 1)).map α =
        (finiteCechTermFunctor Λ p n).map α ≫ finiteCechCoface Λ p G n i
  coverAugmentation : ∀ {W : Scheme.{u}} (p' : W ⟶ Y) [IsFinite p'] [Surjective p']
    (a : W ⟶ Z) (ha : a ≫ p = p')
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      finiteCechAugmentation Λ p F ≫ finiteCechCoverMap Λ p p' a ha F 0 =
        finiteCechAugmentation Λ p' F
  coverCoface : ∀ {W : Scheme.{u}} (p' : W ⟶ Y) [IsFinite p'] [Surjective p']
    (a : W ⟶ Z) (ha : a ≫ p = p')
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) (i : Fin (n + 2)),
      finiteCechCoface Λ p F n i ≫ finiteCechCoverMap Λ p p' a ha F (n + 1) =
        finiteCechCoverMap Λ p p' a ha F n ≫ finiteCechCoface Λ p' F n i
  coverCoefficient : ∀ {W : Scheme.{u}} (p' : W ⟶ Y) [IsFinite p'] [Surjective p']
    (a : W ⟶ Z) (ha : a ≫ p = p')
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (α : F ⟶ G) (n : ℕ),
      finiteCechCoverMap Λ p p' a ha F n ≫ (finiteCechTermFunctor Λ p' n).map α =
        (finiteCechTermFunctor Λ p n).map α ≫ finiteCechCoverMap Λ p p' a ha G n
  coverIdentity : ∀ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ),
    finiteCechCoverMap Λ p p (𝟙 Z) (Category.id_comp p) F n =
      𝟙 (finiteCechTerm Λ p n F)
  coverComposition : ∀ {W V : Scheme.{u}} (p' : W ⟶ Y) (p'' : V ⟶ Y)
    [IsFinite p'] [Surjective p'] [IsFinite p''] [Surjective p'']
    (a : W ⟶ Z) (ha : a ≫ p = p') (b : V ⟶ W) (hb : b ≫ p' = p'')
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ),
      finiteCechCoverMap Λ p p' a ha F n ≫ finiteCechCoverMap Λ p' p'' b hb F n =
        finiteCechCoverMap Λ p p'' (b ≫ a) (by rw [Category.assoc, ha, hb]) F n

/-- Exactness of the augmented alternating Cech complex for a finite surjective cover.
Source: Stacks Project, etale-cohomology.tex, Tag 09Z2, lemma-cohomological-descent-finite
(blueprint: lem-trf-finite-cech-augmentation-modules).

Proof. Put `C⁻¹ = F` and `C^q = p_{q*}p_q⁻¹F`. The inverse-image and direct-image
units give module-linear cofaces and the augmentation, and the composition-unit equations
make the alternating differential square to zero. For a geometric point, finite base change
and the finite lifting theorem identify the degree-q stalk with maps from the finite nonempty
fibre `E^(q+1)` to `F_y`; the cofaces delete coordinates. Prepending a chosen point of `E`
gives a contracting homotopy, including the augmentation degree. Exact geometric stalks and
the stalk isomorphism criterion imply exactness of the underlying abelian complex; the
faithful exact forgetful functor returns exactness for module sheaves. Naturality in `F`
follows from naturality of units. A morphism of finite surjective covers induces the maps
on each fibre-product degree by the same unit and composition equations, giving naturality
in covers. The edge cases `F = 0`, an empty base, an isomorphism or radicial cover, and a
one- or two-point fibre satisfy the same complex; surjectivity is needed for nonemptiness.
-/
theorem finite_cech_augmentation_modules (Λ : Type (u + 1)) [CommRing Λ]
    {Y Z : Scheme.{u}} (p : Z ⟶ Y) [IsFinite p] [Surjective p] :
    FiniteCechAugmentationProperties Λ p := by
  sorry

end AlgebraicGeometry
