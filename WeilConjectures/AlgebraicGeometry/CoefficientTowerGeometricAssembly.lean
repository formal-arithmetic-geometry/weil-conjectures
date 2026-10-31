/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientTowerRealizedProperOpenCoordinates
public import WeilConjectures.AlgebraicGeometry.CoefficientTowerCompactificationGeometry
public import WeilConjectures.AlgebraicGeometry.CoefficientTowerUnboundedSupport
public import WeilConjectures.AlgebraicGeometry.VaryingRingProperOpenModel
public import WeilConjectures.AlgebraicGeometry.CompactificationRealization
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
/-- Exactly the two finite equations in the original interface. Their field types
retain the same coefficient-category and derived instances as CompositionCoherence.
Source: Levels (blueprint: lem-sp-geometric-operation-assembly). -/
structure FiniteWordCompatibility (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (finiteData : FiniteNormalization l E k b o q z)
    (opsData : CompositionOperations l E k b o q z) : Prop where
  refinement_finite : ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (K : C l E b q X) (n : ℕ),
    (fixedLevel l E b q Y n).map ((opsData.refinement f c d).hom.app K) ≫
      (fixedEvaluation l E b o q z d n (finiteData.evaluation d n)).hom.app K.obj =
    (fixedEvaluation l E b o q z c n (finiteData.evaluation c n)).hom.app K.obj ≫
      (fixedRefinement (ULift.{u + 1} (SpTowerShriek.R l E n)) c d).hom.app
        ⟨(fixedLevel l E b q X n).obj K.obj, finiteData.finite_origin K n⟩
  composition_finite : ∀ {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [Z.Over (Spec (.of k))] [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] (c : Compactification f) (d :
      Compactification g)
    (e : Compactification (f ≫ g)) (K : C l E b q X) (n : ℕ),
    (fixedLevel l E b q Z n).map ((opsData.composition f g (f ≫ g) rfl c d e).hom.app K) ≫
      (fixedEvaluation l E b o q z e n (finiteData.evaluation e n)).hom.app K.obj =
    (fixedEvaluation l E b o q z d n (finiteData.evaluation d n)).hom.app ((F l E b o q c).obj
      K.obj) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) d).map
        ((fixedEvaluation l E b o q z c n (finiteData.evaluation c n)).hom.app K.obj) ≫
      (finiteCanonicalComposition (ULift.{u + 1} (SpTowerShriek.R l E n)) f g c d e).hom.app
        ⟨(fixedLevel l E b q X n).obj K.obj, finiteData.finite_origin K n⟩

/-- Exact open extension and total right-derived proper image are triangulated.
Source: derived-functor triangulatedness
(blueprint: lem-sp-geometric-operation-assembly). -/
theorem native_triangulated (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    ∃ (_ : (F l E b o q c).CommShift ℤ), (F l E b o q c).IsTriangulated := by
  let := (q.abelian X).hasDerived
  let := (q.abelian Y).hasDerived
  let := b.realizationAdditive X
  let := b.realizationAdditive Y
  change ∃ (_ : ((b.realization X).functor.mapDerivedCategory ⋙
    (o.openOp c.i).extension.mapDerivedCategory ⋙
    (o.geometry c.g).push.rightDerivedFunctor ⋙
    (b.realization Y).inverse.mapDerivedCategory).CommShift ℤ), _
  refine ⟨inferInstance, ?_⟩
  change ((b.realization X).functor.mapDerivedCategory ⋙
    (o.openOp c.i).extension.mapDerivedCategory ⋙
    (o.geometry c.g).push.rightDerivedFunctor ⋙
    (b.realization Y).inverse.mapDerivedCategory).IsTriangulated
  infer_instance

attribute [local irreducible] Iso.trans NatTrans.vcomp
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

/-- A component of the constructed geometric coherence.
Source: Stacks 0F7J--0F7K (blueprint: lem-sp-geometric-operation-assembly). -/
theorem operation_refinement_identity
    (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (M : ProperOpenCalculus NoetherianAmbient.{u})
    (coords : NativeCoordinates l E b o q M) (_h : Preservation l E k b o q) :
    ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f),
    (operationsFor l E k b o q z M coords).refinement f c c = Iso.refl _ := by
  intro X Y _ _ _ _ _ _ _ _ f _ _ _ _ c
  simp only [operationsFor, ProperOpenCalculus.CompactificationRealization.refinement_refl]
  exact Functor.isoWhiskerLeft_refl _ _

/-- A component of the constructed geometric coherence.
Source: Stacks 0F7J--0F7K (blueprint: lem-sp-geometric-operation-assembly). -/
theorem operation_refinement_transitive
    (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (M : ProperOpenCalculus NoetherianAmbient.{u})
    (coords : NativeCoordinates l E b o q M) (_h : Preservation l E k b o q) :
    ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d e : Compactification f),
    (operationsFor l E k b o q z M coords).refinement f c d ≪≫
      (operationsFor l E k b o q z M coords).refinement f d e =
        (operationsFor l E k b o q z M coords).refinement f c e := by
  intro X Y _ _ _ _ _ _ _ _ f _ _ _ _ c d e
  simpa only [operationsFor, Functor.isoWhiskerLeft_trans] using
    congrArg (Functor.isoWhiskerLeft (inclusion l E b q X))
      ((nativeFor l E b o q M coords).refinement_trans noetherian_compactification_geometry
        ⟨X, ambient_field k X⟩ ⟨Y, ambient_field k Y⟩ f c d e
        (ambient_compactification (ambient_field k Y) c)
        (ambient_compactification (ambient_field k Y) d)
        (ambient_compactification (ambient_field k Y) e))

/-- A component of the constructed geometric coherence.
Source: Stacks 0F7J--0F7K (blueprint: lem-sp-geometric-operation-assembly). -/
theorem operation_identity_left
    (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (M : ProperOpenCalculus NoetherianAmbient.{u})
    (coords : NativeCoordinates l E b o q M) (_h : Preservation l E k b o q) :
    ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (i : Compactification (𝟙 X)) (K : C l E b q X),
    ((operationsFor l E k b o q z M coords).composition
      (𝟙 X) f f (Category.id_comp f) i c c).hom.app K =
      (F l E b o q c).map (((operationsFor l E k b o q z M coords).identity i).hom.app K) := by
  intro X Y _ _ _ _ _ _ _ _ f _ _ _ _ c i K
  exact (nativeFor l E b o q M coords).composition_left noetherian_compactification_geometry
    ⟨X, ambient_field k X⟩ ⟨Y, ambient_field k Y⟩ f c
    (ambient_compactification (ambient_field k Y) c) i
    (ambient_compactification (ambient_field k X) i) K.obj

/-- A component of the constructed geometric coherence.
Source: Stacks 0F7J--0F7K (blueprint: lem-sp-geometric-operation-assembly). -/
theorem operation_identity_right
    (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (M : ProperOpenCalculus NoetherianAmbient.{u})
    (coords : NativeCoordinates l E b o q M) (h : Preservation l E k b o q) :
    ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (i : Compactification (𝟙 Y)) (K : C l E b q X),
    ((operationsFor l E k b o q z M coords).composition
      f (𝟙 Y) f (Category.comp_id f) c i c).hom.app K =
      ((operationsFor l E k b o q z M coords).identity i).hom.app
        ((restrictedSupport l E k b o q h f c).obj K) := by
  intro X Y _ _ _ _ _ _ _ _ f _ _ _ _ c i K
  exact (nativeFor l E b o q M coords).composition_right noetherian_compactification_geometry
    ⟨X, ambient_field k X⟩ ⟨Y, ambient_field k Y⟩ f c
    (ambient_compactification (ambient_field k Y) c) i
    (ambient_compactification (ambient_field k Y) i) K.obj

/-- Renaming the target composite leaves the native binary comparison unchanged.
Source: equality transport (blueprint: lem-sp-geometric-operation-assembly). -/
theorem native_composition_copy
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (M : ProperOpenCalculus NoetherianAmbient.{u})
    (coords : NativeCoordinates l E b o q M)
    (G : ProperOpenCalculus.Geometry NoetherianAmbient.{u})
    (X Y Z : {X : Scheme.{u} // NoetherianAmbient X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val) (fg fg' : X.val ⟶ Z.val)
    (wfg : f ≫ g = fg) (hfg : fg' = fg)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact fg] [QuasiCompact fg']
    (c : Compactification f) (d : Compactification g) (e : Compactification fg)
    (hc : NoetherianAmbient c.Z) (hd : NoetherianAmbient d.Z)
    (he : NoetherianAmbient e.Z) :
    (nativeFor l E b o q M coords).composition G X Y Z f g fg'
      (wfg.trans hfg.symm) c d (e.copy hfg) hc hd he =
    (nativeFor l E b o q M coords).composition G X Y Z f g fg wfg c d e hc hd he := by
  subst fg'
  rfl

/-- A component of the constructed geometric coherence.
Source: Stacks 0F7J--0F7K (blueprint: lem-sp-geometric-operation-assembly). -/
theorem operation_associativity
    (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (M : ProperOpenCalculus NoetherianAmbient.{u})
    (coords : NativeCoordinates l E b o q M) (h : Preservation l E k b o q) :
    ∀ {X Y Z W : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [Z.Over (Spec (.of k))] [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [W.Over (Spec (.of k))] [IsSeparated (W ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))] [QuasiCompact (W ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] (t : Z ⟶ W) [t.IsOver (Spec (.of k))]
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    (c : Compactification f) (d : Compactification g) (e : Compactification t)
    (cd : Compactification (f ≫ g)) (de : Compactification (g ≫ t))
    (cde : Compactification ((f ≫ g) ≫ t)) (K : C l E b q X),
    (F l E b o q e).map
      (((operationsFor l E k b o q z M coords).composition f g (f ≫ g) rfl c d cd).hom.app K) ≫
      ((operationsFor l E k b o q z M coords).composition
        (f ≫ g) t ((f ≫ g) ≫ t) rfl cd e cde).hom.app K =
    ((operationsFor l E k b o q z M coords).composition g t (g ≫ t) rfl d e de).hom.app
        ((restrictedSupport l E k b o q h f c).obj K) ≫
      ((operationsFor l E k b o q z M coords).composition f (g ≫ t) ((f ≫ g) ≫ t)
        (Category.assoc f g t).symm c de cde).hom.app K := by
  intro X Y Z W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ _ g' _ _ _ _ t _ _ _ _
    c d e cd de cde K
  have ht := (nativeFor l E b o q M coords).composition_associativity
    noetherian_compactification_geometry
    ⟨X, ambient_field k X⟩ ⟨Y, ambient_field k Y⟩ ⟨Z, ambient_field k Z⟩
    ⟨W, ambient_field k W⟩ f g' t c d e cd de (cde.copy (Category.assoc f g' t).symm)
    (ambient_compactification (ambient_field k Y) c)
    (ambient_compactification (ambient_field k Z) d)
    (ambient_compactification (ambient_field k W) e)
    (ambient_compactification (ambient_field k Z) cd)
    (ambient_compactification (ambient_field k W) de)
    (ambient_compactification (ambient_field k W) cde) K.obj
  rw [native_composition_copy l E b o q M coords noetherian_compactification_geometry
    ⟨X, ambient_field k X⟩ ⟨Z, ambient_field k Z⟩ ⟨W, ambient_field k W⟩
    (f ≫ g') t ((f ≫ g') ≫ t) (f ≫ g' ≫ t) rfl (Category.assoc f g' t).symm
    cd e cde (ambient_compactification (ambient_field k Z) cd)
    (ambient_compactification (ambient_field k W) e)
    (ambient_compactification (ambient_field k W) cde)] at ht
  rw [native_composition_copy l E b o q M coords noetherian_compactification_geometry
    ⟨X, ambient_field k X⟩ ⟨Y, ambient_field k Y⟩ ⟨W, ambient_field k W⟩
    f (g' ≫ t) ((f ≫ g') ≫ t) (f ≫ g' ≫ t)
    (Category.assoc f g' t).symm (Category.assoc f g' t).symm
    c de cde (ambient_compactification (ambient_field k Y) c)
    (ambient_compactification (ambient_field k W) de)
    (ambient_compactification (ambient_field k W) cde)] at ht
  exact ht

/-- A component of the constructed geometric coherence.
Source: Stacks 0F7J--0F7K (blueprint: lem-sp-geometric-operation-assembly). -/
theorem operation_refinement_composition
    (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (M : ProperOpenCalculus NoetherianAmbient.{u})
    (coords : NativeCoordinates l E b o q M) (h : Preservation l E k b o q) :
    ∀ {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [Z.Over (Spec (.of k))] [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c c' : Compactification f) (d d' : Compactification g)
    (e e' : Compactification (f ≫ g)) (K : C l E b q X),
    (F l E b o q d).map (((operationsFor l E k b o q z M coords).refinement f c c').hom.app K) ≫
      ((operationsFor l E k b o q z M coords).refinement g d d').hom.app
        ((restrictedSupport l E k b o q h f c').obj K) ≫
      ((operationsFor l E k b o q z M coords).composition f g (f ≫ g) rfl c' d' e').hom.app K =
    ((operationsFor l E k b o q z M coords).composition f g (f ≫ g) rfl c d e).hom.app K ≫
      ((operationsFor l E k b o q z M coords).refinement (f ≫ g) e e').hom.app K := by
  intro X Y Z _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ _ g' _ _ _ _ c c' d d' e e' K
  exact (nativeFor l E b o q M coords).composition_refinement
    noetherian_compactification_geometry
    ⟨X, ambient_field k X⟩ ⟨Y, ambient_field k Y⟩ ⟨Z, ambient_field k Z⟩
    f g' c c' d d' e e' (ambient_compactification (ambient_field k Y) c)
    (ambient_compactification (ambient_field k Y) c')
    (ambient_compactification (ambient_field k Z) d)
    (ambient_compactification (ambient_field k Z) d')
    (ambient_compactification (ambient_field k Z) e)
    (ambient_compactification (ambient_field k Z) e') K.obj

/-- A component of the constructed geometric coherence.
Source: Stacks 0F7J--0F7K (blueprint: lem-sp-geometric-operation-assembly). -/
theorem operation_triangulated
    (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (_z : FiniteCoordinates l E)
    (M : ProperOpenCalculus NoetherianAmbient.{u})
    (_coords : NativeCoordinates l E b o q M) (_h : Preservation l E k b o q) :
    ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f), ∃ (_ : (F l E b o q c).CommShift ℤ),
      (F l E b o q c).IsTriangulated := by
  intro X Y _ _ _ _ _ _ _ _ f _ _ _ _ c
  exact native_triangulated l E b o q c

set_option linter.defProp false in
/-- Assemble the finite and algebraic equations over an abstract operation record.
The result annotation is inside the body so Lean infers the field hypothesis types
from the original constructor, retaining its exact elaborated instances.
Source: Stacks 0F7J--0F7K (blueprint: lem-sp-geometric-operation-assembly). -/
def assembleOperationsCoherence (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (h : Preservation l E k b o q)
    (finiteData : FiniteNormalization l E k b o q z)
    (opsData : CompositionOperations l E k b o q z)
    (hn : FiniteWordCompatibility l E k b o q z finiteData opsData)
    (hRefinementIdentity : _) (hRefinementTransitive : _)
    (hIdentityLeft : _) (hIdentityRight : _) (hAssociativity : _)
    (hRefinementComposition : _) (hTriangulated : _) :=
  (show CompositionCoherence l E k b o q z h finiteData opsData from {
    refinement_identity := hRefinementIdentity
    refinement_transitive := hRefinementTransitive
    refinement_finite := hn.refinement_finite
    composition_finite := hn.composition_finite
    identity_left := hIdentityLeft
    identity_right := hIdentityRight
    associativity := hAssociativity
    refinement_composition := hRefinementComposition
    triangulated := hTriangulated })

/-- The geometric equations for the constructed operations; the two finite word
normalizations are the only additional premises.
Source: Stacks 0F7J--0F7K (blueprint: lem-sp-geometric-operation-assembly).

Proof: restriction along the full inclusion preserves the comparison identities
and cocycles. At an object, the native left and right unit, associativity and
refinement equations are exactly their transported counterparts. Preservation
only certifies that the intermediate objects belong to C, and changes no map.
Triangulatedness is inherited from the exact and total right-derived factors. -/
theorem operations_coherenceFor (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (M : ProperOpenCalculus NoetherianAmbient.{u})
    (coords : NativeCoordinates l E b o q M)
    (finiteData : FiniteNormalization l E k b o q z)
    (hn : FiniteWordCompatibility l E k b o q z finiteData
      (operationsFor l E k b o q z M coords)) (h : Preservation l E k b o q) :
    CompositionCoherence l E k b o q z h finiteData (operationsFor l E k b o q z M coords) :=
  assembleOperationsCoherence l E k b o q z h finiteData
    (operationsFor l E k b o q z M coords) hn
    (operation_refinement_identity l E k b o q z M coords h)
    (operation_refinement_transitive l E k b o q z M coords h)
    (operation_identity_left l E k b o q z M coords h)
    (operation_identity_right l E k b o q z M coords h)
    (operation_associativity l E k b o q z M coords h)
    (operation_refinement_composition l E k b o q z M coords h)
    (operation_triangulated l E k b o q z M coords h)

/-- Specialize algebraic coherence to the actual coordinate data.
Source: Stacks 0F7J--0F7K (blueprint: lem-sp-geometric-operation-assembly).

Proof: the generic fixed-coordinate coherence is specialized without unfolding
its component proof terms. The finite equations are precisely the supplied two
normalization hypotheses, and all other fields are already proved. -/
theorem operations_coherence (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (g : GraphCoordinates l E b o)
    (finiteData : FiniteNormalization l E k b o q z)
    (hn : FiniteWordCompatibility l E k b o q z finiteData
      (operations l E k b o q z g)) (h : Preservation l E k b o q) :
    CompositionCoherence l E k b o q z h finiteData (operations l E k b o q z g) :=
  operations_coherenceFor l E k b o q z (model l E b)
    (actualNativeCoordinates l E b o q g) finiteData hn h

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
