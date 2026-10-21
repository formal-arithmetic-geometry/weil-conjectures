/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.SixFunctors.RingedDerivedComparisonData
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Coherence equations for the explicit canonical derived comparisons

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0FPT.
(blueprint: lem-sfb-ringed-derived-tensor-diagrams).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  WeilConjectures SheafOfModules
namespace CategoryTheory.RingedDerivedComparisons


/-- The localized scalar-action unit map, with no choice of monoidal structure.
Source: Stacks Project, Cohomology on Sites, Tag 07A4; Modules on Sites, Tag 03EL.
(blueprint: lem-sfb-ringed-derived-tensor-diagrams). -/
def canonicalDerivedUnitComparison {X Y : Site.{u, w}}
    (e : RingedTensorEdge Y.corner X.corner)
    (j : e.pullback.obj (SheafOfModules.unit Y.ring) ≅ SheafOfModules.unit X.ring) :
    e.left.obj Y.closed.monoidal.tensorUnit ⟶ X.closed.monoidal.tensorUnit :=
  e.left.map Y.coherence.unitIso.hom ≫
    derivedPullbackComplexComparison e.pullback e.left e.epsilon
      (ringedTensorUnitComplex.{u, u, u} Y.J Y.A) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        e.pullback (ComplexShape.up ℤ) 0).hom.app (SheafOfModules.unit Y.ring) ≫
        (CochainComplex.singleFunctor X.modules 0).map j.hom) ≫
    X.coherence.unitIso.inv

/-- The three oplax coherence diagrams and the signed symmetry equation for the
specified comparison maps. Naturality is already supplied by tensorComparison.
Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0FPT.
(blueprint: lem-sfb-ringed-derived-tensor-diagrams). -/
def CanonicalTensorDiagrams {X Y : Site.{u, w}}
    (e : RingedTensorEdge Y.corner X.corner)
    (rY : RingedTensorModel Y.corner) (rX : RingedTensorModel X.corner)
    (j : e.pullback.obj (SheafOfModules.unit Y.ring) ≅ SheafOfModules.unit X.ring) : Prop :=
  letI : MonoidalCategory Y.D := Y.closed.monoidal
  letI : MonoidalCategory X.D := X.closed.monoidal
  let F : Y.D ⥤ X.D := e.left
  let t : ∀ U V : Y.D, F.obj (U ⊗ V) ≅ F.obj U ⊗ F.obj V :=
    fun U V ↦ (e.tensorComparison rY rX).app (U, V)
  let a : F.obj (𝟙_ Y.D) ⟶ 𝟙_ X.D := canonicalDerivedUnitComparison e j
  IsIso a ∧
  (∀ U V W : Y.D,
    (t (U ⊗ V) W).hom ≫ (t U V).hom ▷ F.obj W ≫
        (α_ (F.obj U) (F.obj V) (F.obj W)).hom =
      F.map (α_ U V W).hom ≫ (t U (V ⊗ W)).hom ≫
        F.obj U ◁ (t V W).hom) ∧
  (∀ U : Y.D, (λ_ (F.obj U)).inv =
    F.map (λ_ U).inv ≫ (t (𝟙_ Y.D) U).hom ≫ a ▷ F.obj U) ∧
  (∀ U : Y.D, (ρ_ (F.obj U)).inv =
    F.map (ρ_ U).inv ≫ (t U (𝟙_ Y.D)).hom ≫ F.obj U ◁ a) ∧
  (∀ U V : Y.D,
    (t U V).hom ≫
        (X.symmetry.toBraidedCategory.braiding (F.obj U) (F.obj V)).hom =
      F.map (Y.symmetry.toBraidedCategory.braiding U V).hom ≫ (t V U).hom)

/-- Localizing the cochain coherence equations gives the diagrams for the explicit
canonical tensor and scalar-action unit maps.
Source: Stacks Project, Cohomology on Sites, Tag 07A4 and the signed model of 0FPT;
Modules on Sites, Tag 03EL.
(blueprint: lem-sfb-ringed-derived-tensor-diagrams).

Proof:
1. Use simultaneous flat-term K-flat representatives. Their tensors and pullbacks
remain in that class. The representative characterization of tensorComparison
identifies its components with the localized ordinary cochain comparisons.
2. The degree-zero coefficient complex is flat-term K-flat. Its derived pullback
comparison is therefore invertible. The given j is an ordinary unit isomorphism,
and the single-complex comparison and the site's recorded unit identifications
are isomorphisms. Their composite a is invertible.
3. On three representatives compare the two associativity routes after each
homogeneous pure-tensor summand inclusion. The recorded associators are ordinary
reassociation; the cochain pullback coherence theorem gives equality on each
such summand. Tensor extensionality and the direct-sum universal property give
the chain-map equality. Substitute the recorded tensor-model equations and
localize it to obtain the displayed associativity equation.
4. For each unitor, the same computation on a degree-zero coefficient and a
homogeneous section is scalar multiplication. The normalization of j is the
right action equation; balancing and the coefficient-ring unit give the left
action equation as well. The recorded unitors and unitIso identify their
localizations with the two displayed inverse-unitor equations.
5. The two symmetry routes send a tensor in degrees p,q to its swapped tensor
with sign (-1)^(p*q), by the cochain signed-braiding equation and the recorded
signed braiding models. Thus their localized maps agree. Finally every derived
object is isomorphic to a flat-term K-flat representative. Naturality conjugates
the four diagram equalities to arbitrary objects. No exactness of the ordinary
pullback and no boundedness assumption is used. -/
theorem canonicalTensorDiagrams {X Y : Site.{u, w}}
    (e : RingedTensorEdge Y.corner X.corner)
    (rY : RingedTensorModel Y.corner) (rX : RingedTensorModel X.corner)
    (hY : ∀ P Q hP hQ,
      rY.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (Y.model.iso Y.J Y.A Y.closed P Q hP.1 hQ.1).hom)
    (hX : ∀ P Q hP hQ,
      rX.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom)
    (j : e.pullback.obj (SheafOfModules.unit Y.ring) ≅ SheafOfModules.unit X.ring)
    (hj : ∀ M : Y.modules,
      (e.ordinaryTensor.mu M (SheafOfModules.unit Y.ring)).hom ≫
          (SheafOfModules.monoidalCategory X.A).tensorHom (𝟙 _) j.hom ≫
          ((SheafOfModules.monoidalCategory X.A).rightUnitor (e.pullback.obj M)).hom =
        e.pullback.map ((SheafOfModules.monoidalCategory Y.A).rightUnitor M).hom) :
    CanonicalTensorDiagrams e rY rX j := by sorry

end CategoryTheory.RingedDerivedComparisons
