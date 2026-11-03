/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerRealizedProperOpenCoordinates
public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.ProperOpenCalculus
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerCompactificationGeometry
public import WeilConjectures.AlgebraicGeometry.VaryingRing.CoefficientTowerUnboundedSupport
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenModel
public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRealization.CompactificationRealization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # The actual compactification operations on the supplied coefficient towers

Source: Stacks 0F7J--0F7K, Local pairs of the geometric gluing proof.
(blueprint: lem-sp-geometric-operation-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual quotient-ring calculus on unbounded derived systems.
Source: Stacks 0F7B (blueprint: lem-sp-geometric-operation-assembly). -/
def model (b : SpTowerShriek.Base l E) : ProperOpenCalculus NoetherianAmbient.{u} := by
  let := b.finite
  refine VaryingRing.properOpenModel (graphRings l E) (graphTransitions l E)
    NoetherianAmbient ?_
  intro U V W Z k r p i _ _ _ _ _ _ h
  exact VaryingRing.quotient_gamma_isIso (fun n ↦ SpTowerShriek.R l E n)
    (graphTransitions l E) k r p i h

attribute [local implicit_reducible] model VaryingRing.properOpenModel
  VaryingRing.assembleProperOpen VaryingRing.actualProperOpenInputs

/-- Coordinates for the supplied native support functors in one fixed model.
Source: Local pairs (blueprint: lem-sp-geometric-operation-assembly). -/
structure NativeCoordinates (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    (M : ProperOpenCalculus NoetherianAmbient.{u}) where
  coordinate (X : {X : Scheme.{u} // NoetherianAmbient X}) :
    spDerivedCoefficientTowers l E X.val (q.abelian X.val) ≌ M.obj X
  comparison (X Y : {X : Scheme.{u} // NoetherianAmbient X})
    {f : X.val ⟶ Y.val} [QuasiCompact f]
    (c : Compactification f) (hc : NoetherianAmbient c.Z) :
    F l E b o q c ⋙ (coordinate Y).functor ≅
      (coordinate X).functor ⋙ M.H X Y c hc

/-- The fixed native functors, with abstract coordinate data.
Source: Local pairs (blueprint: lem-sp-geometric-operation-assembly). -/
def nativeFor (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (M : ProperOpenCalculus NoetherianAmbient.{u})
    (d : NativeCoordinates l E b o q M) :
    ProperOpenCalculus.CompactificationRealization M where
  obj X := spDerivedCoefficientTowers l E X.val (q.abelian X.val)
  category X := by
    let := (q.abelian X.val).hasDerived
    infer_instance
  coordinate X := d.coordinate X
  H := by
    intro X Y f _ c _
    exact F l E b o q c
  comparison := by
    intro X Y f _ c hc
    exact d.comparison X Y c hc

/-- The actual coordinates, retaining the supplied normalization.
Source: Local pairs (blueprint: lem-sp-geometric-operation-assembly). -/
def actualNativeCoordinates (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    (g : GraphCoordinates l E b o) : NativeCoordinates l E b o q (model l E b) where
  coordinate X := by
    dsimp only [model, VaryingRing.properOpenModel, VaryingRing.assembleProperOpen,
      VaryingRing.actualProperOpenInputs]
    exact nativeCoordinate l E b o q g X.val
  comparison := by
    intro X Y f _ c hc
    exact nativeSupportCoordinates l E b o q g c

/-- Fixed realization of every native compact-support functor in the actual model.
Source: Local pairs (blueprint: lem-sp-geometric-operation-assembly). -/
def native (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (g : GraphCoordinates l E b o) :
    ProperOpenCalculus.CompactificationRealization (model l E b) :=
  nativeFor l E b o q (model l E b) (actualNativeCoordinates l E b o q g)

/-- A finite-type quasi-compact scheme over a field lies in the geometric ambient class.
Source: Noetherian finite-type theorem
(blueprint: lem-sp-geometric-operation-assembly). -/
theorem ambient_field (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] : NoetherianAmbient X :=
  ⟨LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k)),
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))⟩

/-- Restrict the native operations on whole derived categories to the given input C.
No preservation witness enters this construction.
Source: Local pairs (blueprint: lem-sp-geometric-operation-assembly). -/
def operationsFor (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (M : ProperOpenCalculus NoetherianAmbient.{u})
    (coords : NativeCoordinates l E b o q M) : CompositionOperations l E k b o q z where
  identity := by
    intro X _ _ _ _ i
    exact Functor.isoWhiskerLeft (inclusion l E b q X)
      ((nativeFor l E b o q M coords).identity noetherian_compactification_geometry
        ⟨X, ambient_field k X⟩ i (ambient_compactification (ambient_field k X) i))
  refinement := by
    intro X Y _ _ _ _ _ _ _ _ f _ _ _ _ c d
    exact Functor.isoWhiskerLeft (inclusion l E b q X)
      ((nativeFor l E b o q M coords).refinement noetherian_compactification_geometry
        ⟨X, ambient_field k X⟩ ⟨Y, ambient_field k Y⟩ f c d
        (ambient_compactification (ambient_field k Y) c)
        (ambient_compactification (ambient_field k Y) d))
  composition := by
    intro X Y Z _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ _ g' _ _ _ _ fg w c d e
    have : QuasiCompact fg := by rw [← w]; infer_instance
    exact Functor.isoWhiskerLeft (inclusion l E b q X)
      ((nativeFor l E b o q M coords).composition noetherian_compactification_geometry
        ⟨X, ambient_field k X⟩ ⟨Y, ambient_field k Y⟩ ⟨Z, ambient_field k Z⟩
        f g' fg w c d e (ambient_compactification (ambient_field k Y) c)
        (ambient_compactification (ambient_field k Z) d)
        (ambient_compactification (ambient_field k Z) e))

/-- The actual operations, obtained by specializing the fixed-coordinate construction.
Source: Local pairs (blueprint: lem-sp-geometric-operation-assembly). -/
def operations (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (g : GraphCoordinates l E b o) : CompositionOperations l E k b o q z :=
  operationsFor l E k b o q z (model l E b) (actualNativeCoordinates l E b o q g)

-- Keep these conditions in field types: a definition body would abstract the
-- nested sheafification proofs and make conversion with the interface expensive.
set_option genInjectivity false in
set_option genSizeOfSpec false in
attribute [local irreducible] Iso.trans NatTrans.vcomp
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

set_option linter.defProp false in
/-- On an open arrow compare with its trivial proper compactification, then use pId.
Source: Stacks 0F7J (blueprint: lem-sp-geometric-operation-assembly). -/
def modelOpenComparison (b : SpTowerShriek.Base l E)
    {U X : Scheme.{u}} (hU : NoetherianAmbient U) (hX : NoetherianAmbient X)
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (a : Compactification j) :
    (model l E b).H ⟨U, hU⟩ ⟨X, hX⟩ a (ambient_compactification hX a) ≅
      VaryingRing.J (graphRings l E) (graphTransitions l E) j :=
  (model l E b).comparison noetherian_compactification_geometry
    ⟨U, hU⟩ ⟨X, hX⟩ j a (Compactification.ofIsOpenImmersion j)
      (ambient_compactification hX a) hX ≪≫
    Functor.isoWhiskerLeft _ (VaryingRing.pId (graphRings l E) (graphTransitions l E) X) ≪≫
      Functor.rightUnitor _

/-- Canonical native comparison with the recorded exact open extension.
Source: Stacks 0F7J (blueprint: lem-sp-geometric-operation-assembly).

Proof: compare the prescribed compactification to the trivial open compactification
in the model calculus. Its proper factor is the identity, so its specified proper
identity comparison gives open extension. Conjugate by the supplied support and
open coordinates, and take the unique inverse image under the fully faithful
target coordinate. Thus this is a constructed comparison before any finite-level
normalization or preservation witness. -/
def openComparison (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (g : GraphCoordinates l E b o)
    {U X : Scheme.{u}} (hU : NoetherianAmbient U) (hX : NoetherianAmbient X)
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (a : Compactification j) :
    F l E b o q a ≅ openExtension l E b o q j :=
  ((nativeCoordinate l E b o q g X).fullyFaithfulFunctor.whiskeringRight _).preimageIso
    (nativeSupportCoordinates l E b o q g a ≪≫
      Functor.isoWhiskerLeft (nativeCoordinate l E b o q g U).functor
        (modelOpenComparison l E b hU hX j a) ≪≫
      (nativeOpenCoordinates l E b o q g j).symm)

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates

end
