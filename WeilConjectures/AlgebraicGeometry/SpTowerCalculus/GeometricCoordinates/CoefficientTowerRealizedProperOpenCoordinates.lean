/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerProperOpenCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore

/-! # Proper/open coordinates in the original coefficient-tower category

Source: blueprint gluing proof, Local pairs, fixed realization conjugation.
(blueprint: lem-sp-realized-proper-open-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The two canonical section presentations have equal exact open functors.
Source: the fixed section comparison
(blueprint: lem-sp-realized-proper-open-coordinates). -/
theorem semilinear_open_eq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    SemilinearProperOpen.J (graphRings l E) (graphTransitions l E) j =
      VaryingRing.J (graphRings l E) (graphTransitions l E) j := by
  exact SemilinearProperOpen.J_eq _ _ j

/-- The two canonical section presentations have equal total direct-image functors.
Source: the fixed section comparison
(blueprint: lem-sp-realized-proper-open-coordinates). -/
theorem semilinear_proper_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SemilinearProperOpen.R (graphRings l E) (graphTransitions l E) f =
      VaryingRing.P (graphRings l E) (graphTransitions l E) f := by
  exact SemilinearProperOpen.R_eq _ _ f

/-- The actual support word in the varying-ring presentation.
Source: Local pairs, canonical coordinate transport
(blueprint: lem-sp-realized-proper-open-coordinates). -/
def varyingSupportCoordinates (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    SpTowerShriek.F l E b o c ⋙ (g.presentation Y).functor.mapDerivedCategory ≅
      (g.presentation X).functor.mapDerivedCategory ⋙
        VaryingRing.J (graphRings l E) (graphTransitions l E) c.i ⋙
        VaryingRing.P (graphRings l E) (graphTransitions l E) c.g :=
  graphSupportCoordinates l E b o g c ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (eqToIso (semilinear_open_eq l E c.i)) _ ≪≫
        Functor.isoWhiskerLeft _ (eqToIso (semilinear_proper_eq l E c.g)))

/-- The original tower coordinates followed by the fixed section presentation.
Source: Local pairs, canonical coordinate transport
(blueprint: lem-sp-realized-proper-open-coordinates). -/
def nativeCoordinate (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    (g : GraphCoordinates l E b o) (X : Scheme.{u}) :
    spDerivedCoefficientTowers l E X (q.abelian X) ≌
      VaryingRing.Derived (graphRings l E) (graphTransitions l E) X := by
  let := (q.abelian X).hasDerived
  let := b.realizationAdditive X
  exact (realization l E b X (q.abelian X)).trans (g.presentation X).mapDerivedCategory

/-- The supplied compact-support functor is compared to the canonical proper/open
word by cancelling precisely the recorded realization counit.
Source: Local pairs, canonical coordinate transport
(blueprint: lem-sp-realized-proper-open-coordinates).

Proof: expand compact support as realization, open extension, proper image and
inverse realization. Compose with the target coordinate. Its adjacent inverse
realization and realization cancel by their specified counit. The remaining open
and proper word is the ordinary section comparison descended termwise and by
right derivation. Whisker that comparison by the source realization. This
constructs the comparison on whole derived categories before coefficient evaluation. -/
def nativeSupportCoordinates (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    (g : GraphCoordinates l E b o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    F l E b o q c ⋙ (nativeCoordinate l E b o q g Y).functor ≅
      (nativeCoordinate l E b o q g X).functor ⋙
        VaryingRing.J (graphRings l E) (graphTransitions l E) c.i ⋙
        VaryingRing.P (graphRings l E) (graphTransitions l E) c.g := by
  let := (q.abelian X).hasDerived
  let := (q.abelian Y).hasDerived
  let := b.realizationAdditive X
  let := b.realizationAdditive Y
  let eX := realization l E b X (q.abelian X)
  let eY := realization l E b Y (q.abelian Y)
  exact Functor.isoWhiskerLeft (eX.functor ⋙ SpTowerShriek.F l E b o c)
      (Functor.isoWhiskerRight eY.counitIso (g.presentation Y).functor.mapDerivedCategory ≪≫
        Functor.leftUnitor _) ≪≫
    Functor.isoWhiskerLeft eX.functor (varyingSupportCoordinates l E b o g c)

/-- The original exact open extension in the fixed varying-ring coordinates.
Source: Local pairs, open adjunction uniqueness
(blueprint: lem-sp-realized-proper-open-coordinates). -/
def nativeOpenCoordinates (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    (g : GraphCoordinates l E b o) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    openExtension l E b o q j ⋙ (nativeCoordinate l E b o q g X).functor ≅
      (nativeCoordinate l E b o q g U).functor ⋙
        VaryingRing.J (graphRings l E) (graphTransitions l E) j := by
  let := (q.abelian U).hasDerived
  let := (q.abelian X).hasDerived
  let := b.realizationAdditive U
  let := b.realizationAdditive X
  let eU := realization l E b U (q.abelian U)
  let eX := realization l E b X (q.abelian X)
  exact Functor.isoWhiskerLeft (eU.functor ⋙ SpTowerShriek.openD l E b (o.openOp j))
      (Functor.isoWhiskerRight eX.counitIso (g.presentation X).functor.mapDerivedCategory ≪≫
        Functor.leftUnitor _) ≪≫
    Functor.isoWhiskerLeft eU.functor
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (graphForward l E b o g _ _ (graphOpenCoordinates l E b o g j)) ≪≫
        Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.isoWhiskerLeft _ (eqToIso (semilinear_open_eq l E j)))

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
