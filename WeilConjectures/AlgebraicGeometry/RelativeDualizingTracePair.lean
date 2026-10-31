/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceModuleDerivedExchange
public import WeilConjectures.AlgebraicGeometry.SpaceAffineSectionsCompositors
public import WeilConjectures.AlgebraicGeometry.SpaceAffineHomComparison
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations

/-! # Relative dualizing trace pairs on algebraic spaces

Source: Stacks Project, spaces-duality.tex, Tag 0E5X and the following Hom characterization
(blueprint: def-sfb-relative-dualizing-trace-pair).

The trace compatibility equation uses the canonical counit-mate exchange. It avoids
choosing an inverse to an exchange map before its invertibility has been proved.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}
variable [∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]

/-- The Yoneda map of a scheme morphism, between the existing represented spaces.
Source: Stacks, Tag 025Y (blueprint: def-sfb-relative-dualizing-trace-pair). -/
def traceSchemeMap {Y Y' : Over S} (g : Y' ⟶ Y) : schemeSpace Y' ⟶ schemeSpace Y :=
  ObjectProperty.homMk ⟨yoneda.map g⟩

/-- The regular-function structure map `O_Y → f_*O_X`, transported to the small models.
Source: Stacks, Tag 03G8 (blueprint: def-sfb-relative-dualizing-trace-pair). -/
def traceSmallStructureMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit Y.smallStructureRings ⟶
      (smallModuleDirectImage f).obj (SheafOfModules.unit X.smallStructureRings) :=
  (smallModuleUnitIso Y).hom ≫
    Y.smallModuleRestriction.map (moduleStructureMap f) ≫
    Y.smallModuleRestriction.map
      ((moduleDirectImage f).map
        (fullModuleSection X (SheafOfModules.unit X.smallStructureRings) (𝟙 _)))

/-- The comparison from an ordinary direct image in degree zero to its derived image,
induced by the universal right-derived unit.
Source: Stacks, Tag 079V (blueprint: def-sfb-relative-dualizing-trace-pair). -/
def traceDirectImageComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y) (M : X.SmallModules) :
    (DerivedCategory.singleFunctor Y.SmallModules 0).obj ((smallModuleDirectImage f).obj M) ⟶
      (derivedDirectImage f).obj ((DerivedCategory.singleFunctor X.SmallModules 0).obj M) :=
  (DerivedCategory.singleFunctorIsoCompQ Y.SmallModules 0).hom.app _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (smallModuleDirectImage f) (.up ℤ) 0).inv.app M) ≫
    spaceRightDerivedComplexUnit (smallModuleDirectImage f)
      ((HomologicalComplex.single X.SmallModules (.up ℤ) (0 : ℤ)).obj M) ≫
    (derivedDirectImage f).map
      ((DerivedCategory.singleFunctorIsoCompQ X.SmallModules 0).inv.app M)

/-- The canonical derived structure pullback `Lf^*O_Y → O_X`, adjoint to the regular-function
structure map followed by its right-derived comparison; not a chosen identification.
Source: Stacks, Tags 03D7 and 06YY (blueprint: def-sfb-relative-dualizing-trace-pair). -/
def traceDerivedStructureMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (spaceDerivedPullback f).obj Y.derivedStructure ⟶ X.derivedStructure :=
  ((spaceDerivedAdjunction f).homEquiv _ _).symm
    ((DerivedCategory.singleFunctor Y.SmallModules 0).map (traceSmallStructureMap f) ≫
      traceDirectImageComparison f (SheafOfModules.unit X.smallStructureRings))

/-- A complex and an actual trace to the structure sheaf in degree zero.
Source: Stacks, Tag 0E5X (blueprint: def-sfb-relative-dualizing-trace-pair). -/
structure RelativeDualizingTracePair (Y : Over S) {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) where
  /-- The complex in the ambient derived category of module sheaves. -/
  complex : X.DerivedModules
  /-- Its trace, in the target's ambient derived category. -/
  trace : (derivedDirectImage f).obj complex ⟶ (schemeSpace Y).derivedStructure

/-- The trace-preservation equation for an isomorphism on a fixed source.
Source: Stacks, Tag 0E5Z (blueprint: def-sfb-relative-dualizing-trace-pair). -/
def TracePreserving {Y : Over S} {X : AlgebraicSpace S} {f : X ⟶ schemeSpace Y}
    (P Q : RelativeDualizingTracePair Y f) (e : P.complex ≅ Q.complex) : Prop :=
  (derivedDirectImage f).map e.hom ≫ Q.trace = P.trace

/-- Trace compatibility after base change, expressed without an arbitrary comparison.
If exchange is invertible, this says exactly that the target trace is the pulled trace.
The final map is `traceDerivedStructureMap`, the canonical derived pullback of regular
functions adjoint to `moduleStructureMap`, not a freely chosen identification.
Source: Stacks, Tags 0E5X and 0E6C
(blueprint: def-sfb-relative-dualizing-trace-pair). -/
def TraceBaseChangeCompatible {Y Y' : Over S} {X X' : AlgebraicSpace S}
    {f : X ⟶ schemeSpace Y} {f' : X' ⟶ schemeSpace Y'}
    (P : RelativeDualizingTracePair Y f) (Q : RelativeDualizingTracePair Y' f')
    (g : Y' ⟶ Y) (p : X' ⟶ X)
    (sq : p ≫ f = f' ≫ traceSchemeMap g)
    (e : (spaceDerivedPullback p).obj P.complex ≅ Q.complex) : Prop :=
  moduleDerivedExchange f f' (traceSchemeMap g) p sq P.complex ≫
      (derivedDirectImage f').map e.hom ≫ Q.trace =
    (spaceDerivedPullback (traceSchemeMap g)).map P.trace ≫
      traceDerivedStructureMap (traceSchemeMap g)

/-- Composition with a trace, followed by the normalized affine identifications,
is the actual map from derived Hom to Hom over the affine coordinate ring.
Source: Stacks, Tag 0E5X, second remark; Tag 071Q
(blueprint: def-sfb-relative-dualizing-trace-pair). -/
def affineDualizingTraceHom (A : Type u) [CommRing A] (Y : Over S)
    (a : Y.left ≅ Spec (.of A)) {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (K : X.DerivedModules)
    (t : (derivedDirectImage f).obj K ⟶ (schemeSpace Y).derivedStructure)
    (E : X.DerivedModules) (h : E ⟶ K) :
    (affineDerivedSections A Y a X f).obj E ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
  (affineDerivedSectionsComposition A Y a X f).hom.app E ≫
    (affineDerivedSections A Y a (schemeSpace Y) (𝟙 _)).map
      ((derivedDirectImage f).map h ≫ t) ≫
    (affineStructureDerivedIso A Y a).hom

/-- The affine-test definition of a relative dualizing trace pair. The source remarks
permit omission of relative perfectness here: it follows from this universal property.
Every affine scheme over the target, every cartesian realization of its fibre product,
and every unbounded quasi-coherent complex are tested. Bijectivity of the displayed
composition maps is the natural Hom isomorphism; the maps themselves fix its naturality.
Source: Stacks, Tag 0E5X and its first two remarks
(blueprint: def-sfb-relative-dualizing-trace-pair). -/
def IsRelativeDualizingTracePair {Y : Over S} {X : AlgebraicSpace S}
    {f : X ⟶ schemeSpace Y} (P : RelativeDualizingTracePair Y f) : Prop :=
  X.derivedQCohProperty P.complex ∧
  ∀ (A : Type u) [CommRing A] (Y' : Over S) (a : Y'.left ≅ Spec (.of A))
    (g : Y' ⟶ Y) (X' : AlgebraicSpace S) (p : X' ⟶ X)
    (f' : X' ⟶ schemeSpace Y') (sq : IsPullback p f' f (traceSchemeMap g)),
    ∃ t : (derivedDirectImage f').obj ((spaceDerivedPullback p).obj P.complex) ⟶
        (schemeSpace Y').derivedStructure,
      TraceBaseChangeCompatible P ⟨(spaceDerivedPullback p).obj P.complex, t⟩ g p sq.w
        (Iso.refl _) ∧
      ∀ E : X'.DerivedModules, X'.derivedQCohProperty E →
        Function.Bijective
          (affineDualizingTraceHom A Y' a f' ((spaceDerivedPullback p).obj P.complex) t E)

end AlgebraicGeometry.AlgebraicSpace
