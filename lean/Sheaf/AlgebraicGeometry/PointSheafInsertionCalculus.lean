/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Endomorphism
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.CategoryTheory.SiteInverseImageCompositionGenerators
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso

/-!
# Normalized sheaf insertion at an automorphic point

Source: Stacks Project, Sites and Sheaves, Tags 03CE, 03CB and 06UM;
Modules on Sites, Tags 03CZ, 03EK and 03D3; Deligne, Weil II, (1.1.7)
(blueprint: lem-trf-point-sheaf-insertion-calculus).

The natural-number index `n` denotes the positive exponent `n + 1` throughout.
All helper constructions use the original small pro-etale site, with object universe
`u + 1` and morphism universe `u`. Coefficients and modules use the standard `ULift`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Ordinary tensor pullback along the positive power `h^(n+1)`.
Source: Stacks 03D2 (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafPullback {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) :=
  proEtaleConstantRingPullback A (h ^ (n + 1)).hom

/-- The constant-ring comparison for restriction along an automorphism. It is the
sheafification compatibility of the continuous and cocontinuous postcomposition functor,
so its hom preserves each constant section.
Source: Stacks 03CE and 0H7J (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafRestrictionCoefficients {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ) :
    proEtaleConstantRing s A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        (h ^ (n + 1)).hom (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)).obj
          (proEtaleConstantRing s A) :=
  let F := MorphismProperty.Over.map (f := (h ^ (n + 1)).hom) (P := @WeaklyEtale)
    ⊤ (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)
  letI : F.IsContinuous (ProEt.topology s) (ProEt.topology s) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)
  letI : F.IsCocontinuous (ProEt.topology s) (ProEt.topology s) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)
  (F.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    (ProEt.topology s) (ProEt.topology s)).app
      ((Functor.const s.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))

/-- Reindex module sections by postcomposition with `h^(n+1)`. Scalars are transported
by the canonical constant-ring restriction comparison, not an arbitrary ring map.
Source: Stacks 03CE (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafRestriction {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) :=
  proEtaleObjectModuleRestriction (ProEt.mk (h ^ (n + 1)).hom) A
    (pointSheafRestrictionCoefficients h A n)

/-- The graph `(u,id)` in the inverse-image comma index. Mathlib orders the fibre
product factors as `(U,s)`; this is `(id,u)` in that order.
Source: Stacks 03CE and 00VC (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafGraph {s : Scheme.{u}} (h : Aut s) (n : ℕ) (U : s.ProEt) :=
  (proEtaleObjectInverseImageIndexPoint (ProEt.mk (h ^ (n + 1)).hom) U).hom

/-- The graph-index colimit insertion, sheafification, and scalar unit. The published
module adjunction is normalized by precisely that tensor insertion.
Source: Stacks 03D3 and 00VC (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafGraphInsertion {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) (F : proEtaleRingModules s (proEtaleConstantRing s A)) (U : s.ProEt)
    (x : F.val.obj (op ((MorphismProperty.Over.map (f := (h ^ (n + 1)).hom)
      (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)).obj U))) :
    ((pointSheafPullback h A n).obj F).val.obj (op U) :=
  proEtalePullbackTensorGenerator (h ^ (n + 1)).hom
    (proEtaleConstantRing s A) (proEtaleConstantRing s A)
    (proEtaleConstantRingComparison (h ^ (n + 1)).hom A) F _ U
    (pointSheafGraph h n U) x 1

/-- Restriction along `h^(n+1) : (s,h^(n+1)) → (s,id)`.
Source: Stacks 06UM (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafRestrictionArrow {s : Scheme.{u}} (h : Aut s) (n : ℕ) :
    ProEt.mk (h ^ (n + 1)).hom ⟶ ProEt.mk (𝟙 s) :=
  MorphismProperty.Over.homMk (h ^ (n + 1)).hom (Category.comp_id _)

/-- The specified section insertion `j`: first restrict, then insert at the graph and
extend scalars by the tensor unit.
Source: Stacks 06UM (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafInsertion {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) (F : proEtaleRingModules s (proEtaleConstantRing s A))
    (x : F.val.obj (op (ProEt.mk (𝟙 s)))) :
    ((pointSheafPullback h A n).obj F).val.obj (op (ProEt.mk (𝟙 s))) :=
  pointSheafGraphInsertion h A n F (ProEt.mk (𝟙 s))
    (F.val.map (pointSheafRestrictionArrow h n).op x)

/-- Sections at the final object with scalars restricted along the actual constant
section homomorphism. `ULift A` is canonically the original ring `A`.
Source: Stacks 06UM and 0H7J (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafSections (s : Scheme.{u}) (A : Type u) [CommRing A] :
    proEtaleRingModules s (proEtaleConstantRing s A) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1, u} A) :=
  SheafOfModules.forget
    ((sheafCompose (ProEt.topology s) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing s A)) ⋙
    PresheafOfModules.evaluation _ (op (ProEt.mk (𝟙 s))) ⋙
    ModuleCat.restrictScalars
      ((toSheafify (ProEt.topology s)
        ((Functor.const s.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op (ProEt.mk (𝟙 s)))).hom

/-- The canonical module compositor, oriented from successive to direct pullback.
Its chosen presentation comes from the uniquely characterized adjunction comparison;
the last equality merely identifies the composite power with `h^(m+2)`.
Source: Stacks 03CB and 03D3 (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafCompositor {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (m : ℕ) :
    pointSheafPullback h A m ⋙ pointSheafPullback h A 0 ≅
      pointSheafPullback h A (m + 1) :=
  (proEtaleConstantRingModulePullbackComposition (h ^ (0 + 1)).hom
    (h ^ (m + 1)).hom A).choose.symm ≪≫
      eqToIso (congrArg (proEtaleConstantRingPullback A)
        (by
          simp only [zero_add, pow_one]
          exact (congrArg Iso.hom (pow_succ h (m + 1))).symm))

/-- The canonical identification of direct and successive reindexing site objects.
Source: Stacks 03CB (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafReindexCompositor {s : Scheme.{u}} (h : Aut s) (m : ℕ) :=
  MorphismProperty.Over.mapComp (Q := ⊤)
    (inferInstance : WeaklyEtale (h ^ (0 + 1)).hom)
    (inferInstance : WeaklyEtale (h ^ (m + 1)).hom)
    (h ^ ((m + 1) + 1)).hom
    (by
      simp only [zero_add, pow_one]
      exact congrArg Iso.hom (pow_succ h (m + 1)))

/-- Cochain complexes of sections, with their actual sectionwise differentials.
Source: Stacks 06UM (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafSectionComplex (s : Scheme.{u}) (A : Type u) [CommRing A] :=
  (pointSheafSections s A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise ordinary pullback of cochain complexes.
Source: Stacks 06UM (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafPullbackComplex {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) :=
  (pointSheafPullback h A n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Normalized insertion calculus, including its equality of chain maps.
Source: Stacks 03CE, 03CB and 06UM; Modules on Sites 03CZ, 03EK and 03D3;
Deligne, Weil II, (1.1.7) (blueprint: lem-trf-point-sheaf-insertion-calculus).

Proof:
1. Apply `lem-sfb-proetale-object-inverse-image-restriction` to `(s,h^(n+1))`.
Its distinguished initial index is the graph `(u,id)` and its coprojection followed
by sheafification gives restriction as the underlying inverse image. Isomorphisms
are weakly etale by `lem-weil-iso-weakly-etale`, so every power is a site object.
2. The constant-section structure map is invertible by
`prop-weil-pbc-proetale-constant-ring-map`. Apply
`lem-weil-sheaf-scalar-extension-ring-iso` to the actual scalar extension. Its inverse
sends a section to its inverse-image coprojection tensored with one. This gives the
module-linear isomorphisms `e`, natural in modules and site objects, and the graph
normalization below.
3. `lem-trf-constant-coefficient-composition` identifies the specified coefficient
maps for successive powers. `lem-sf-proetale-tensor-composition-unit` identifies the
canonical adjunction compositor with its tensor formula, taking nested scalar units
to the single scalar unit. This is precisely `pointSheafCompositor`, in the direction
from successive to direct pullback.
4. `lem-trf-site-inverse-image-composition-generators` takes the two nested graph
coprojections to the direct graph. The fibre-product universal property
(`def-pc-fibre-product`) retains the first and last graph coordinates. The tensor
formula of step 3 retains the scalar unit. Equality on all original sections, then
inverting the normalized isomorphisms, gives the displayed coherence equation.
5. At the final object the definition of insertion is restriction followed by the
inverse of `e`. This gives the equation with restriction. Restriction commutes with
module maps (`def-weil-sheaf-of-modules-category`) and preserves constant scalars
(`def-weil-pbc-constant-sheaf`), so the specified functions are linear and natural,
yielding `j` with exactly the prescribed underlying functions.
6. Apply `e` for the direct power to the proposed composite of insertions. Coherence
from step 4 and naturality in the restriction arrow turn it into the two successive
restrictions of the original sheaf. Presheaf functoriality identifies their composite
with restriction along the product power. Cancel `e` to obtain the section cocycle.
7. For a complex, apply naturality of `j` to every differential. The resulting equation
is the chain-map condition, with linear components. Apply the same equation to each
component of an arbitrary chain map to get naturality of `J`. Naturality of the
compositor makes its degreewise maps the chain isomorphism `t`. The section cocycle
in every degree gives equality of chain maps, using componentwise extensionality.
No boundedness, constructibility or exactness of evaluation is used. -/
theorem pointSheafInsertionCalculus (k : Type u) [Field k] [IsAlgClosed k]
    (h : Aut (Spec (CommRingCat.of k))) (A : Type u) [CommRing A] [Finite A] :
    ∃ (e : ∀ n : ℕ, pointSheafPullback h A n ≅ pointSheafRestriction h A n)
      (j : ∀ n : ℕ, pointSheafSections (Spec (CommRingCat.of k)) A ⟶
        pointSheafPullback h A n ⋙ pointSheafSections (Spec (CommRingCat.of k)) A)
      (J : ∀ (n : ℕ)
        (K : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ),
        (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).obj K ⟶
          (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).obj
            ((pointSheafPullbackComplex h A n).obj K))
      (t : ∀ (m : ℕ)
        (K : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ),
        (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).obj
          ((pointSheafPullbackComplex h A 0).obj
            ((pointSheafPullbackComplex h A m).obj K)) ≅
        (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).obj
          ((pointSheafPullbackComplex h A (m + 1)).obj K)),
      (∀ (n : ℕ)
        (F : proEtaleRingModules (Spec (CommRingCat.of k))
          (proEtaleConstantRing (Spec (CommRingCat.of k)) A))
        (U : (Spec (CommRingCat.of k)).ProEt)
        (x : F.val.obj (op ((MorphismProperty.Over.map (f := (h ^ (n + 1)).hom)
          (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)).obj U))),
        ((e n).hom.app F).val.app (op U) (pointSheafGraphInsertion h A n F U x) = x) ∧
      (∀ (m : ℕ)
        (F : proEtaleRingModules (Spec (CommRingCat.of k))
          (proEtaleConstantRing (Spec (CommRingCat.of k)) A))
        (U : (Spec (CommRingCat.of k)).ProEt)
        (x : ((pointSheafPullback h A 0).obj
          ((pointSheafPullback h A m).obj F)).val.obj (op U)),
        ((e (m + 1)).hom.app F).val.app (op U)
          (((pointSheafCompositor h A m).hom.app F).val.app (op U) x) =
        F.val.map ((pointSheafReindexCompositor h m).hom.app U).op
          (((e m).hom.app F).val.app
            (op ((MorphismProperty.Over.map (f := (h ^ (0 + 1)).hom)
              (P := @WeaklyEtale) ⊤
                (inferInstance : WeaklyEtale (h ^ (0 + 1)).hom)).obj U))
            (((e 0).hom.app ((pointSheafPullback h A m).obj F)).val.app (op U) x))) ∧
      (∀ (n : ℕ)
        (F : proEtaleRingModules (Spec (CommRingCat.of k))
          (proEtaleConstantRing (Spec (CommRingCat.of k)) A))
        (x : F.val.obj (op (ProEt.mk (𝟙 (Spec (CommRingCat.of k)))))),
        (j n).app F x = pointSheafInsertion h A n F x) ∧
      (∀ (n : ℕ)
        (F : proEtaleRingModules (Spec (CommRingCat.of k))
          (proEtaleConstantRing (Spec (CommRingCat.of k)) A))
        (x : F.val.obj (op (ProEt.mk (𝟙 (Spec (CommRingCat.of k)))))),
        ((e n).hom.app F).val.app (op (ProEt.mk (𝟙 (Spec (CommRingCat.of k)))))
          ((j n).app F x) = F.val.map (pointSheafRestrictionArrow h n).op x) ∧
      (∀ (m : ℕ)
        (F : proEtaleRingModules (Spec (CommRingCat.of k))
          (proEtaleConstantRing (Spec (CommRingCat.of k)) A)),
        (j (m + 1)).app F = (j m).app F ≫
          (j 0).app ((pointSheafPullback h A m).obj F) ≫
          (pointSheafSections (Spec (CommRingCat.of k)) A).map
            ((pointSheafCompositor h A m).hom.app F)) ∧
      (∀ (n : ℕ)
        (K : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ) (i : ℤ),
        (J n K).f i = (j n).app (K.X i)) ∧
      (∀ (n : ℕ)
        (K L : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ) (v : K ⟶ L),
        (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).map v ≫ J n L =
          J n K ≫ (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).map
            ((pointSheafPullbackComplex h A n).map v)) ∧
      (∀ (m : ℕ)
        (K : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ) (i : ℤ),
        (t m K).hom.f i = (pointSheafSections (Spec (CommRingCat.of k)) A).map
          ((pointSheafCompositor h A m).hom.app (K.X i))) ∧
      (∀ (m : ℕ)
        (K : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ),
        J (m + 1) K = J m K ≫
          J 0 ((pointSheafPullbackComplex h A m).obj K) ≫ (t m K).hom) := by
  sorry

end AlgebraicGeometry.Scheme
