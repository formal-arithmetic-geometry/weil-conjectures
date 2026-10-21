/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.OrientedProductPointsConservative
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Comap

import Sheaf.SixFunctors.ProperBaseChangeModules
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.CategoryTheory.Sites.LocalOrientedProjectionExact
import Sheaf.Paper.OrientedAffineNeighbourhoodLimit
import Sheaf.CategoryTheory.Sites.OrientedProductSliceLocalization
import Sheaf.CategoryTheory.SitePointFibre
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.Paper.OrientedNearbyCycles
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity
import WeilConjectures.AlgebraicGeometry.StrictHenselization

/-!
# Proper fibre formula and exchange on vanishing topoi

Source: Orgogozo, Modifications et cycles proches sur une base générale, Lemma 9.1.1
and the two consequences before Proposition 9.1.2, printed pp. 19–20; ILO XI §§1.4, 2.3,
2.7 (blueprint: lem-trf-oriented-proper-fibre-exchange).

## Main definitions

* `fibreLift`: the geometric-fibre morphism specified by the strict-local specialization.
* `fibreExchange`, `baseExchange`, `firstExchange`: the three canonical derived mates.

## Main statements

* `properFibreExchange`: invertibility on D⁺ and the explicit fibre counit equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v s

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.AdicSites

namespace AlgebraicGeometry.OrientedNearbyCycles.ProperFibre

/-- Transport of ordinary étale direct image to the recorded small presentation.
Source: ILO XI §1.4 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def originalDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  f.Etale.sheafPushforwardContinuous
    (Type (max (u + 1) v)) Y.smallEtaleTopology X.smallEtaleTopology

/-- The direct-image transport is restriction along the same base-change functor.
Source: ILO XI §1.4 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def directTransport {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleMorphism.{u, v} f).direct ⋙ (etaleSheafEquivalence Y).inverse ≅
      (etaleSheafEquivalence X).inverse ⋙ originalDirect f :=
  NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _ (Iso.refl _))

/-- A geometric-point composite has the canonical stalk/skyscraper identification.
Source: ILO XI §1.8; Stacks 03Q1
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def originalPointComposition {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    (Scheme.pointSmallEtale x).skyscraperSheafFunctor ⋙ originalDirect.{u, v} f ≅
      (Scheme.pointSmallEtale (x ≫ f)).skyscraperSheafFunctor :=
  conjugateIsoEquiv
    ((f.Etale.sheafAdjunctionContinuous (Type (max (u + 1) v)) _ _).comp
      (Scheme.pointSmallEtale x).skyscraperSheafAdjunction)
    (Scheme.pointSmallEtale (x ≫ f)).skyscraperSheafAdjunction
    ((GrothendieckTopology.Point.sheafFiberIso (Scheme.pointSmallEtaleComapIso f x)).symm ≪≫
      GrothendieckTopology.Point.sheafFiberComapIso (Scheme.pointSmallEtale x) f.Etale
        (Scheme.Hom.coverPreserving_etale f) (Type (max (u + 1) v)))

/-- The same restriction identity in the other direction of site transport.
Source: ILO XI §1.4 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def forwardTransport {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleSheafEquivalence.{u, v} X).functor ⋙ (etaleMorphism f).direct ≅
      originalDirect f ⋙ (etaleSheafEquivalence Y).functor :=
  NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _ (Iso.refl _))

/-- The canonical composite-point isomorphism, induced by pullback of pointed lifts.
Source: Stacks 03Q1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def pointComposition {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ((geometricEtalePoint.{u, v} x).comp (etaleMorphism f)).direct ≅
      (geometricEtalePoint (x ≫ f)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (forwardTransport f)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (originalPointComposition f x) _)



/-- The pointed étale lift from the actual strict-localization limit.
Source: Stacks 04HX; ILO XI §1.8 (blueprint: lem-trf-oriented-proper-fibre-exchange).
Proof: the pointed neighbourhood defines a limit leg. For a non-affine neighbourhood,
shrink to an affine open containing the point and compose its leg. Two choices agree
on a common pointed refinement. Étale uniqueness on a strictly local base makes a map
with the same closed-point lift unique. -/
theorem strictLift_existsUnique {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (U : S.Etale)
    (l : (Scheme.pointSmallEtale s).fiber.obj U) :
    ∃! a : Scheme.strictHenselizationScheme s ⟶ U.left,
      a ≫ U.hom = Scheme.strictHenselizationStructuralMap s ∧
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation s)) ≫ a =
        l.left := by
  sorry

/-- The limit leg specified by its closed-point lift.
Source: Stacks 04HX (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def strictLift {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (U : S.Etale) (l : (Scheme.pointSmallEtale s).fiber.obj U) :=
  (strictLift_existsUnique s U l).choose

section Specialization
variable {S : Scheme.{u}} {Ω Ξ : Type u}
  [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
  (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ S)
  (c : Scheme.strictHenselizationScheme t ⟶ Scheme.strictHenselizationScheme s)
  (hc : c ≫ Scheme.strictHenselizationStructuralMap s =
    Scheme.strictHenselizationStructuralMap t)

include hc in
/-- Restriction along a specialization sends a pointed lift to a pointed lift.
Source: ILO XI §1.8 (blueprint: lem-trf-oriented-proper-fibre-exchange).
Proof: compose the structural equation for strictLift with c and the closed point of
the strict localization at t; hc and evaluation over S give precisely t. -/
theorem specializedLift_over (U : S.Etale) (l : (Scheme.pointSmallEtale s).fiber.obj U) :
    (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation t)) ≫
      c ≫ strictLift s U l) ≫ U.hom = t := by
  sorry

/-- The geometric lift obtained by restriction along the prescribed c.
Source: ILO XI §1.8 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def specializedLift (U : S.Etale) (l : (Scheme.pointSmallEtale s).fiber.obj U) :
    (Scheme.pointSmallEtale t).fiber.obj U :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation t)) ≫
      c ≫ strictLift s U l) (specializedLift_over s t c hc U l)

/-- Naturality of strict-local restriction on geometric lifts.
Source: ILO XI §1.8 (blueprint: lem-trf-oriented-proper-fibre-exchange).
Proof: composing a strict-local leg with a pointed étale map gives the leg determined
by the composite closed-point lift, by strictLift_existsUnique. Compose that equality
with c and evaluation at t. -/
theorem specializedLift_naturality {U V : S.Etale} (a : U ⟶ V) :
    (Scheme.pointSmallEtale s).fiber.map a ≫
        (TypeCat.ofHom (specializedLift s t c hc V)) =
      (TypeCat.ofHom (specializedLift s t c hc U)) ≫
        (Scheme.pointSmallEtale t).fiber.map a := by
  sorry

/-- The morphism of site points specified by the strict-localization morphism c.
Source: ILO XI §1.8 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def specializationPoint : Scheme.pointSmallEtale t ⟶ Scheme.pointSmallEtale s :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (specializedLift s t c hc U)
     naturality := fun _ _ a ↦ specializedLift_naturality s t c hc a }⟩

/-- The direct-image 2-morphism, with inverse-image mate given by germ restriction.
Source: ILO XI §1.8 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def specializationDirect : (geometricEtalePoint.{u, v} t).direct ⟶
    (geometricEtalePoint.{u, v} s).direct :=
  Functor.whiskerLeft punctualEquivalence.functor
    (Functor.whiskerRight
      (conjugateEquiv (Scheme.pointSmallEtale t).skyscraperSheafAdjunction
        (Scheme.pointSmallEtale s).skyscraperSheafAdjunction
        (specializationPoint s t c hc).sheafFiber)
      (etaleSheafEquivalence S).functor)

end Specialization

/-- The stalk/skyscraper adjunction at the identity of an algebraically closed field is
an equivalence. Source: Stacks 03Q1; ILO XI §1.8
(blueprint: lem-trf-oriented-proper-fibre-exchange).
Proof: every étale scheme over an algebraically closed field is a disjoint union of
copies of its spectrum. A sheaf is therefore determined by its value at that spectrum;
the germ and skyscraper evaluation maps are mutually inverse. This proves both triangle
maps invertible in the transported site, without a bound on the coefficient universe. -/
theorem fieldPoint_equivalence (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    (∀ H, IsIso ((geometricEtalePoint.{u, v} (𝟙 (Spec (.of Ω)))).adj.unit.app H)) ∧
      (∀ M, IsIso ((geometricEtalePoint.{u, v} (𝟙 (Spec (.of Ω)))).adj.counit.app M)) := by
  sorry

/-- The global-sections morphism of the étale topos of an algebraically closed field,
using the inverse of its canonical geometric point.
Source: Stacks 03Q1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fieldSections (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    GeometricMorphism
      (Sheaf (etaleTopology.{u, v} (Spec (.of Ω))) (Type (max (u + 1) v)))
      (Sheaf punctualSite.{max (u + 1) v}.topology (Type (max (u + 1) v))) :=
  let p := geometricEtalePoint.{u, v} (𝟙 (Spec (.of Ω)))
  letI := (fieldPoint_equivalence.{u, v} Ω).1
  letI := (fieldPoint_equivalence.{u, v} Ω).2
  { inverse := p.direct
    direct := p.inverse
    adj := p.adj.toEquivalence.symm.toAdjunction
    leftExact := by dsimp [p, geometricEtalePoint]; infer_instance }

/-- The canonical unit identification over an algebraically closed field.
Source: Stacks 03Q1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fieldUnit (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    𝟭 (Sheaf (etaleTopology.{u, v} (Spec (.of Ω))) (Type (max (u + 1) v))) ≅
      (geometricEtalePoint.{u, v} (𝟙 (Spec (.of Ω)))).inverse ⋙
        (geometricEtalePoint.{u, v} (𝟙 (Spec (.of Ω)))).direct :=
  letI := (fieldPoint_equivalence.{u, v} Ω).1
  NatIso.ofComponents (fun H ↦ asIso
    ((geometricEtalePoint.{u, v} (𝟙 (Spec (.of Ω)))).adj.unit.app H))

/-- The point of the vanishing topos determined by the geometric specialization.
Source: Orgogozo 9.1.1; ILO XI §1.8
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def pointOrientation {Y S : Scheme.{u}} (g : Y ⟶ S)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (y : Spec (.of Ω) ⟶ Y) (t : Spec (.of Ξ) ⟶ S)
    (c : Scheme.strictHenselizationScheme t ⟶ Scheme.strictHenselizationScheme (y ≫ g))
    (hc : c ≫ Scheme.strictHenselizationStructuralMap (y ≫ g) =
      Scheme.strictHenselizationStructuralMap t) :
    ((geometricEtalePoint.{u, v} t).comp (identity _)).direct ⟶
      ((geometricEtalePoint.{u, v} y).comp (etaleMorphism g)).direct :=
  (Functor.rightUnitor _).hom ≫ specializationDirect (y ≫ g) t c hc ≫
    (pointComposition g y).inv

/-- The canonical induced map V_(h g) → V_g, with both projection identifications.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def properLift {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) :=
  lift.{u, v} g (VanishingTopos (h ≫ g)) (sheaf_isTopos _)
    ((p₁ (h ≫ g)).comp (etaleMorphism h)) (p₂ (h ≫ g))
    (orientation (h ≫ g) ≫
      (Functor.isoWhiskerLeft (p₁ (h ≫ g)).direct (etaleComposition h g)).inv ≫
      (Functor.associator _ _ _).inv)

/-- Constant-module direct image and inverse image for the induced proper-source map.
Source: Orgogozo 9.1.1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def properModules {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) :=
  moduleMorphism (vanishingDatum.{u, v} g) (vanishingDatum (h ≫ g))
    (properLift h g).morphism

/-- The geometric fibre's sections morphism. Its direct image is Γ on the fibre:
first push to Spec Ω and then take the identity-point stalk, which equals Γ there.
Source: Orgogozo 9.1.1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fibreGlobal {X Y : Scheme.{u}} (h : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :=
  (etaleMorphism.{u, v} (pullback.snd h y)).comp (fieldSections Ω)

/-- The identity-point composite is identified using its actual pullback of lifts.
Source: Stacks 03Q1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def pointOverField {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    (geometricEtalePoint.{u, v} (𝟙 (Spec (.of Ω)))).direct ⋙
        (etaleMorphism y).direct ≅ (geometricEtalePoint y).direct :=
  pointComposition y (𝟙 _) ≪≫ eqToIso
    (congrArg (fun a ↦ (geometricEtalePoint.{u, v} a).direct) (Category.id_comp y))

/-- The canonical factorization h i = y Γ of the proper geometric fibre.
The inserted unit is the canonical geometric-point equivalence, so no arbitrary
isomorphism of the two inverse images is chosen.
Source: Orgogozo 9.1.1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fibreFactor {X Y : Scheme.{u}} (h : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ((etaleMorphism.{u, v} (pullback.fst h y)).comp (etaleMorphism h)).direct ≅
      ((fibreGlobal h y).comp (geometricEtalePoint y)).direct :=
  etaleComposition (pullback.fst h y) h ≪≫
    eqToIso (congrArg (fun a ↦ (etaleMorphism.{u, v} a).direct)
      (pullback.condition (f := h) (g := y))) ≪≫
    (etaleComposition (pullback.snd h y) y).symm ≪≫
    Functor.isoWhiskerRight (Functor.rightUnitor _).symm _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (etaleMorphism.{u, v} (pullback.snd h y)).direct (fieldUnit Ω)) _ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pointOverField y)



section Fibre
variable {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
  {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
  (y : Spec (.of Ω) ⟶ Y) (t : Spec (.of Ξ) ⟶ S)
  (c : Scheme.strictHenselizationScheme t ⟶ Scheme.strictHenselizationScheme (y ≫ g))
  (hc : c ≫ Scheme.strictHenselizationStructuralMap (y ≫ g) =
    Scheme.strictHenselizationStructuralMap t)

/-- The factorization over S, obtained by composing the geometric-fibre square with g.
Source: Orgogozo 9.1.1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fibreFactorBase :
    ((etaleMorphism.{u, v} (pullback.fst h y)).comp (etaleMorphism (h ≫ g))).direct ≅
      (((fibreGlobal h y).comp (geometricEtalePoint y)).comp (etaleMorphism g)).direct :=
  Functor.isoWhiskerLeft _ (etaleComposition h g).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fibreFactor h y) _

/-- The orientation on the geometric fibre is precisely the pullback of c.
Source: Orgogozo 9.1.1, proof, Step 1
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fibreOrientation :
    (((fibreGlobal.{u, v} h y).comp (geometricEtalePoint t)).comp (identity _)).direct ⟶
      ((etaleMorphism (pullback.fst h y)).comp (etaleMorphism (h ≫ g))).direct :=
  (Functor.rightUnitor _).hom ≫
    Functor.whiskerLeft (fibreGlobal h y).direct
      (specializationDirect (y ≫ g) t c hc) ≫
    (Functor.isoWhiskerLeft (fibreGlobal h y).direct (pointComposition g y)).inv ≫
    (Functor.associator _ _ _).inv ≫ (fibreFactorBase h g y).inv

/-- The universal lift φ_z, with its two projection identifications and orientation.
Source: Orgogozo 9.1.1, proof, Step 1; ILO XI Theorem 1.4
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fibreLift :=
  lift.{u, v} (h ≫ g)
    (Sheaf (etaleTopology (pullback h y)) (Type (max (u + 1) v))) (sheaf_isTopos _)
    (etaleMorphism (pullback.fst h y)) ((fibreGlobal h y).comp (geometricEtalePoint t))
    (fibreOrientation h g y t c hc)

/-- The point z, retaining the identifications of both projections.
Source: ILO XI §1.8 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def pointLift :=
  lift.{u, v} g _ (sheaf_isTopos punctualSite.{max (u + 1) v}.topology)
    (geometricEtalePoint y) (geometricEtalePoint t) (pointOrientation g y t c hc)

/-- First projection of h̄ φ_z, identified with y Γ.
Source: Orgogozo 9.1.1, proof, Step 1
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fibreSquareFirst :
    ((((fibreLift.{u, v} h g y t c hc).morphism.comp (properLift h g).morphism).comp
      (p₁ g)).direct) ≅ ((fibreGlobal h y).comp (geometricEtalePoint y)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (properLift h g).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fibreLift h g y t c hc).first _ ≪≫ fibreFactor h y

/-- First projection of z Γ with the same target as fibreSquareFirst.
Source: ILO XI Theorem 1.4 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def pointSquareFirst :
    ((((fibreGlobal.{u, v} h y).comp (pointLift g y t c hc).morphism).comp
      (p₁ g)).direct) ≅ ((fibreGlobal h y).comp (geometricEtalePoint y)).direct :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (pointLift g y t c hc).first

/-- Second projection of h̄ φ_z is the constant point t.
Source: Orgogozo 9.1.1, proof, Step 1
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fibreSquareSecond :
    ((((fibreLift.{u, v} h g y t c hc).morphism.comp (properLift h g).morphism).comp
      (p₂ g)).direct) ≅ ((fibreGlobal h y).comp (geometricEtalePoint t)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (properLift h g).second ≪≫ (fibreLift h g y t c hc).second

/-- Second projection of z Γ is likewise the specified t.
Source: ILO XI Theorem 1.4 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def pointSquareSecond :
    ((((fibreGlobal.{u, v} h y).comp (pointLift g y t c hc).morphism).comp
      (p₂ g)).direct) ≅ ((fibreGlobal h y).comp (geometricEtalePoint t)).direct :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (pointLift g y t c hc).second

/-- The fibre square is uniquely fixed by both projection identifications.
Source: Orgogozo 9.1.1, proof, Step 1; ILO XI Theorem 1.4
(blueprint: lem-trf-oriented-proper-fibre-exchange).
Proof: both composites have the first component y Γ and second component t Γ.
The orientation of fibreLift was defined by pulling back c using fibreFactorBase.
Thus both cones have the same orientation, not merely isomorphic projections.
Apply the uniqueness clause of lem-trf-oriented-product-universal. -/
theorem fibreSquare_existsUnique :
    ∃! e : ((fibreLift.{u, v} h g y t c hc).morphism.comp (properLift h g).morphism).direct ≅
        ((fibreGlobal h y).comp (pointLift g y t c hc).morphism).direct,
      Functor.isoWhiskerRight e (p₁ g).direct ≪≫ pointSquareFirst h g y t c hc =
          fibreSquareFirst h g y t c hc ∧
        Functor.isoWhiskerRight e (p₂ g).direct ≪≫ pointSquareSecond h g y t c hc =
          fibreSquareSecond h g y t c hc := by
  sorry

/-- The actual commutation identification, fixed by the universal property.
Source: Orgogozo 9.1.1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fibreSquare := (fibreSquare_existsUnique.{u, v} h g y t c hc).choose

/-- Exact inverse image along φ_z on the recorded constant-module categories.
Source: Orgogozo 9.1.1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fibreModules :=
  moduleMorphism (vanishingDatum.{u, v} (h ≫ g)) (etaleDatum (pullback h y))
    (fibreLift h g y t c hc).morphism

/-- The stalk inverse image at the prescribed z.
Source: Orgogozo 9.1.1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def pointModules :=
  moduleMorphism (vanishingDatum.{u, v} g) punctualSite (pointLift g y t c hc).morphism

/-- The global-sections morphism on constant modules; its push is K-injective RΓ.
Source: Orgogozo 9.1.1 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def globalModules :=
  moduleMorphism punctualSite.{max (u + 1) v} (etaleDatum (pullback h y)) (fibreGlobal h y)

/-- The restriction map θ_z: the mate of the specified fibre square, using the ordinary
module adjunctions and their K-injective derived adjunctions. This is a natural
transformation, not a bare isomorphism of the two complexes.
Source: Orgogozo 9.1.1, proof, Step 1
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fibreExchange (Λ : Type v) [CommRing Λ] :
    (properModules h g).push (Coeff.{u, v} Λ) ⋙
        (pointModules g y t c hc).pull (Coeff.{u, v} Λ) ⟶
      (fibreModules h g y t c hc).pull (Coeff.{u, v} Λ) ⋙
        (globalModules h y).push (Coeff.{u, v} Λ) :=
  ordinaryExchange (f := properModules h g) (g := pointModules g y t c hc)
    (h := fibreModules h g y t c hc) (k := globalModules h y)
    (GeometricMorphism.inverseIso (fibreSquare h g y t c hc)) (Coeff.{u, v} Λ)

end Fibre

/-- The module inverse image of the first projection.
Source: ILO XI §1.3 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def firstModules {X S : Scheme.{u}} (f : X ⟶ S) :=
  moduleMorphism (etaleDatum.{u, v} X) (vanishingDatum f) (p₁ f)

/-- The first-projection comparison is the mate of the first projection of the
universal h̄ lift. In particular it uses precisely the direct-image counit of h.
Source: Orgogozo, consequence before 9.1.2, proof, Step 7
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def firstExchange {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    (Λ : Type v) [CommRing Λ] :
    (etaleModules h).push (Coeff.{u, v} Λ) ⋙ (firstModules g).pull (Coeff.{u, v} Λ) ⟶
      (firstModules (h ≫ g)).pull (Coeff.{u, v} Λ) ⋙ (properModules h g).push (Coeff.{u, v} Λ) :=
  ordinaryExchange (f := etaleModules h) (g := firstModules g)
    (h := firstModules (h ≫ g)) (k := properModules h g)
    (GeometricMorphism.inverseIso (properLift h g).first).symm (Coeff.{u, v} Λ)



section BaseChange
variable {X Y S T : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) (q : T ⟶ S)

/-- The actual base change h_T : X_T → Y_T, using the two scheme pullbacks.
Source: Orgogozo, consequence before 9.1.2
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def baseArrow : pullback (h ≫ g) q ⟶ pullback g q :=
  pullback.lift (pullback.fst (h ≫ g) q ≫ h) (pullback.snd (h ≫ g) q)
    (by simpa only [Category.assoc] using pullback.condition (f := h ≫ g) (g := q))

/-- The first base-change square is the defining equation of the pullback lift.
Source: Orgogozo, consequence before 9.1.2
(blueprint: lem-trf-oriented-proper-fibre-exchange).
Proof: apply pullback.lift_fst to the definition of baseArrow. -/
theorem baseArrow_over :
    baseArrow h g q ≫ pullback.fst g q = pullback.fst (h ≫ g) q ≫ h := by
  sorry

/-- The structure morphism f_T is h_T followed by g_T.
Source: Orgogozo, consequence before 9.1.2
(blueprint: lem-trf-oriented-proper-fibre-exchange).
Proof: this is pullback.lift_snd for baseArrow. -/
theorem baseArrow_structure :
    baseArrow h g q ≫ pullback.snd g q = pullback.snd (h ≫ g) q := by
  sorry

/-- Commutation of the square used to induce v_f.
Source: Orgogozo, consequence before 9.1.2
(blueprint: lem-trf-oriented-proper-fibre-exchange).
Proof: replace h_T g_T by f_T using baseArrow_structure and apply the scheme pullback
condition. No properness or other hypothesis is needed to construct the square. -/
theorem baseSource_comm :
    pullback.fst (h ≫ g) q ≫ (h ≫ g) =
      (baseArrow h g q ≫ pullback.snd g q) ≫ q := by
  sorry

/-- The universal lift v_f of the scheme base-change square.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def baseSourceLift :=
  squareLift.{u, v} (h ≫ g) (baseArrow h g q ≫ pullback.snd g q)
    (pullback.fst (h ≫ g) q) q (baseSource_comm h g q)

/-- The universal lift v_g of the scheme base-change square.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def baseTargetLift :=
  squareLift.{u, v} g (pullback.snd g q) (pullback.fst g q) q
    (pullback.condition (f := g) (g := q))

/-- First projection of h̄ v_f, expressed by its actual scheme morphism to Y.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def baseFirstLeft :
    ((((baseSourceLift.{u, v} h g q).morphism.comp (properLift h g).morphism).comp
      (p₁ g)).direct) ≅
        ((p₁ (baseArrow h g q ≫ pullback.snd g q)).comp
          (etaleMorphism (pullback.fst (h ≫ g) q ≫ h))).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (properLift h g).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (baseSourceLift h g q).first _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleComposition (pullback.fst (h ≫ g) q) h)

/-- First projection of v_g h̄_T, with the same target and its canonical scheme equality.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def baseFirstRight :
    ((((properLift.{u, v} (baseArrow h g q) (pullback.snd g q)).morphism.comp
      (baseTargetLift g q).morphism).comp (p₁ g)).direct) ≅
        ((p₁ (baseArrow h g q ≫ pullback.snd g q)).comp
          (etaleMorphism (pullback.fst (h ≫ g) q ≫ h))).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (baseTargetLift g q).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (properLift (baseArrow h g q) (pullback.snd g q)).first _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleComposition (baseArrow h g q) (pullback.fst g q)) ≪≫
    Functor.isoWhiskerLeft _ (eqToIso
      (congrArg (fun a ↦ (etaleMorphism.{u, v} a).direct) (baseArrow_over h g q)))

/-- Second projection of h̄ v_f is q p₂.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def baseSecondLeft :
    ((((baseSourceLift.{u, v} h g q).morphism.comp (properLift h g).morphism).comp
      (p₂ g)).direct) ≅
        ((p₂ (baseArrow h g q ≫ pullback.snd g q)).comp (etaleMorphism q)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (properLift h g).second ≪≫ (baseSourceLift h g q).second

/-- Second projection of v_g h̄_T is the same q p₂.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def baseSecondRight :
    ((((properLift.{u, v} (baseArrow h g q) (pullback.snd g q)).morphism.comp
      (baseTargetLift g q).morphism).comp (p₂ g)).direct) ≅
        ((p₂ (baseArrow h g q ≫ pullback.snd g q)).comp (etaleMorphism q)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (baseTargetLift g q).second ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (properLift (baseArrow h g q) (pullback.snd g q)).second _

/-- The comparison square, uniquely normalized on both projections.
Source: Orgogozo, consequence before 9.1.2; ILO XI §1.9
(blueprint: lem-trf-oriented-proper-fibre-exchange).
Proof: the two composites have first component h a = b h_T by baseArrow_over and
second component q p₂. The squareLift orientations are induced by the very same
commutative scheme square; associativity and baseSource_comm identify their pastings.
Apply the unique-compatible-isomorphism clause of the oriented-product universal
property, retaining both displayed projection equations. -/
theorem baseSquare_existsUnique :
    ∃! e : ((baseSourceLift.{u, v} h g q).morphism.comp (properLift h g).morphism).direct ≅
        ((properLift (baseArrow h g q) (pullback.snd g q)).morphism.comp
          (baseTargetLift g q).morphism).direct,
      Functor.isoWhiskerRight e (p₁ g).direct ≪≫ baseFirstRight h g q =
          baseFirstLeft h g q ∧
        Functor.isoWhiskerRight e (p₂ g).direct ≪≫ baseSecondRight h g q =
          baseSecondLeft h g q := by
  sorry

/-- The canonical square chosen from its uniquely determining projection equations.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def baseSquare := (baseSquare_existsUnique.{u, v} h g q).choose

/-- Exact inverse image v_f^* on constant modules.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def baseSourceModules :=
  squareModules.{u, v} (h ≫ g) (baseArrow h g q ≫ pullback.snd g q)
    (pullback.fst (h ≫ g) q) q (baseSource_comm h g q)

/-- Exact inverse image v_g^* on constant modules.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def baseTargetModules :=
  squareModules.{u, v} g (pullback.snd g q) (pullback.fst g q) q
    (pullback.condition (f := g) (g := q))

/-- The ordinary counit-defined base-change mate, for arbitrary T → S.
Source: Orgogozo, consequence before 9.1.2, proof, Step 6
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def baseExchange (Λ : Type v) [CommRing Λ] :
    (properModules h g).push (Coeff.{u, v} Λ) ⋙ (baseTargetModules g q).pull (Coeff.{u, v} Λ) ⟶
      (baseSourceModules h g q).pull (Coeff.{u, v} Λ) ⋙
        (properModules (baseArrow h g q) (pullback.snd g q)).push (Coeff.{u, v} Λ) :=
  ordinaryExchange (f := properModules h g) (g := baseTargetModules g q)
    (h := baseSourceModules h g q) (k := properModules (baseArrow h g q) (pullback.snd g q))
    (GeometricMorphism.inverseIso (baseSquare h g q)) (Coeff.{u, v} Λ)

end BaseChange



/-- The adjunct of fibre restriction: the square identification followed by the
pulled-back direct-image counit. This fixes the normalization of θ_z.
Source: Orgogozo 9.1.1, proof, Step 1
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
def fibreCounit {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (y : Spec (.of Ω) ⟶ Y) (t : Spec (.of Ξ) ⟶ S)
    (c : Scheme.strictHenselizationScheme t ⟶ Scheme.strictHenselizationScheme (y ≫ g))
    (hc : c ≫ Scheme.strictHenselizationStructuralMap (y ≫ g) =
      Scheme.strictHenselizationStructuralMap t)
    (Λ : Type v) [CommRing Λ] (A : VanishingDerived (h ≫ g) Λ) :
    ((globalModules.{u, v} h y).pull (Coeff.{u, v} Λ)).obj
        (((pointModules.{u, v} g y t c hc).pull (Coeff.{u, v} Λ)).obj
          (((properModules.{u, v} h g).push (Coeff.{u, v} Λ)).obj A)) ⟶
      ((fibreModules.{u, v} h g y t c hc).pull (Coeff.{u, v} Λ)).obj A :=
  (derivedSquare (f := properModules.{u, v} h g) (g := pointModules.{u, v} g y t c hc)
    (h := fibreModules.{u, v} h g y t c hc) (k := globalModules.{u, v} h y)
    (GeometricMorphism.inverseIso (fibreSquare.{u, v} h g y t c hc)) (Coeff.{u, v} Λ)).hom.app
      (((properModules.{u, v} h g).push (Coeff.{u, v} Λ)).obj A) ≫
    ((fibreModules.{u, v} h g y t c hc).pull (Coeff.{u, v} Λ)).map
      (((properModules.{u, v} h g).adj (Coeff.{u, v} Λ)).counit.app A)

/-- Boundedness below in the existing standard derived t-structure.
Source: Orgogozo §1, D⁺ convention
(blueprint: lem-trf-oriented-proper-fibre-exchange). -/
abbrev IsBoundedBelow (V : Site.{s}) (R : Type s) [CommRing R] (A : V.derived R) : Prop :=
  DerivedCategory.TStructure.t.plus A

/-- Proper geometric-fibre formula, its direct-image-counit normalization, arbitrary
scheme base change, and first-projection exchange, on D⁺ with torsion coefficients.

Source: Orgogozo, Lemma 9.1.1 and its two consequences before Proposition 9.1.2,
printed pp. 19–20; ILO XI §§2.3, 2.7
(blueprint: lem-trf-oriented-proper-fibre-exchange).

Proof (the reviewed seven-step DAG proof, retained unchanged in the node):
1. The universal property constructs φ_z from i, constant t and c. Its composite with
h̄ is z Γ. Define θ_z as the mate of fibreSquare; its adjunct is exactly fibreCounit.
2. In the cofiltered affine pointed triple system at z, each component functor to the
pointed étale neighbourhoods of y, g(y), and t is initial. A prescribed neighbourhood
is dominated by a triple obtained by affine shrinkings of its pullbacks. Two arrows
are connected after a common triple refinement, equalizing the pointed component maps
by lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered, and shrinking again. Thus the
component limits are Y_(y), S_(g(y)), S_(t); their arrow is c. Fibre products commute
with limits, giving lim X ×_Y U = X ×_Y Y_(y).
3. Use lem-trf-oriented-affine-neighbourhood-limit, the universal inverse-image formula,
lem-trf-oriented-slice-localization and lem-trf-oriented-derived-cohomology-continuity
to identify the stalk with RΓ of the strict-local oriented product Q. The first
components X ×_Y U are proper over affine U, hence qcqs; all transitions are affine.
For a K-injective J, slice restriction j*J is K-injective because j* has the exact
left adjoint j! (lem-weil-pbc-ringed-sheaf-slice-adjunction): maps from an acyclic N
are adjoint to maps from the acyclic j!N into J. The stalk colimit and continuity
therefore compute the actual restriction map, not an unrelated cohomology isomorphism.
4. At a geometric x of X_y, the same slice and continuity calculation computes the
restriction i_y* Rπ_* A on Q by the oriented product of the strict localization at x
with S_(t). The map to S_(g(y)) is local between strictly henselian local schemes.
Apply lem-trf-local-oriented-projection-exact: its direct image is the inverse image
by the canonical section. Sections on S_(t) equal its closed-point stalk, and
lem-pe-left-module-derived-evaluation-forget transports this to modules. The result
is the germ A_(x,t,c). Derived stalk conservativity proves the restriction invertible.
The map i_y itself need not be a closed immersion when Ω is larger than the strict
residue field; the argument uses the geometric-fibre map and does not assume that.
5. Apply det-properbasechange-modules to the proper X ×_Y Y_(y) → Y_(y) and Rπ_* A.
The underlying cohomology sheaves are m-torsion because mΛ = 0. Strictly henselian
sections/stalk equality, the isomorphism in step 4, and derived composition give the
fibre formula. Mate pasting identifies the composite with θ_z as defined in step 1;
this supplies its naturality and the displayed counit compatibility.
6. For T → S and z' above z use the same Ω for y' and y. The geometric scheme fibres
(X_T)_(y') and X_y are canonically identical, and their universal φ maps agree after
v_f. Properness is stable under base change. Under the two fibre formulas the stalk
of the adjunction-defined baseExchange is the identity restriction of the same RΓ.
Mate pasting and conservativity of the oriented points prove the base-change clause.
7. Ordinary module proper base change identifies the stalk of p₁* Rh_* B with
RΓ(X_y,i*B). The fibre formula identifies the other side with RΓ(X_y,φ_z* p₁*B).
The first projection of fibreLift identifies these coefficients. Both comparisons
are adjoint to the same pulled-back counit; mate pasting makes firstExchange the
identity under these fibre identifications. Oriented-point conservativity finishes.
Only boundedness below, properness, and mΛ = 0 enter this argument. -/
theorem properFibreExchange {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) [IsProper h]
    (Λ : Type v) [CommRing Λ] (m : ℕ) (hm : 1 ≤ m) (hΛ : (m : Λ) = 0) :
    (∀ (Ω Ξ : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
      (y : Spec (.of Ω) ⟶ Y) (t : Spec (.of Ξ) ⟶ S)
      (c : Scheme.strictHenselizationScheme t ⟶ Scheme.strictHenselizationScheme (y ≫ g))
      (hc : c ≫ Scheme.strictHenselizationStructuralMap (y ≫ g) =
        Scheme.strictHenselizationStructuralMap t)
      (A : VanishingDerived (h ≫ g) Λ),
      IsBoundedBelow (vanishingDatum.{u, v} (h ≫ g)) (Coeff.{u, v} Λ) A →
        IsIso ((fibreExchange.{u, v} h g y t c hc Λ).app A) ∧
          (((globalModules.{u, v} h y).adj (Coeff.{u, v} Λ)).homEquiv _ _).symm
              ((fibreExchange.{u, v} h g y t c hc Λ).app A) = fibreCounit.{u, v} h g y t c hc Λ A) ∧
    (∀ (T : Scheme.{u}) (q : T ⟶ S) (A : VanishingDerived (h ≫ g) Λ),
      IsBoundedBelow (vanishingDatum.{u, v} (h ≫ g)) (Coeff.{u, v} Λ) A →
        IsIso ((baseExchange.{u, v} h g q Λ).app A)) ∧
    (∀ B : EtaleDerived X Λ, IsBoundedBelow (etaleDatum.{u, v} X) (Coeff.{u, v} Λ) B →
      IsIso ((firstExchange.{u, v} h g Λ).app B)) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles.ProperFibre
