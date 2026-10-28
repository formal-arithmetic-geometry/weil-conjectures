/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.VectorTraceGeometry

/-! # Degree-one coordinates of a linear bundle map

Source: the symmetric-algebra generator calculation in the proof of vector-bundle purity.
(blueprint: lem-pur-vector-bundle-map-frame-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.VectorBundleZeroSection

/-- Pull a frame to an arbitrary scheme, using the canonical module pullback comparisons.
Source: blueprint vector-bundle purity, paragraph 2.
(blueprint: lem-pur-vector-bundle-map-frame-coordinates). -/
def pulledFrame (S : Scheme.{u}) (r : ℕ) (F : S.Modules)
    (V : S.Opens) (e : Trivialization S r F V)
    {W : Scheme.{u}} (g : W ⟶ V.toScheme) :
    (Scheme.Modules.pullback (g ≫ V.ι)).obj F ≅
      SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin r)) :=
  (Scheme.Modules.pullbackComp g V.ι).symm.app F ≪≫
    (Scheme.Modules.pullback g).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app F ≪≫ e) ≪≫
    Scheme.Modules.pullbackFreeIso g (ULift.{u} (Fin r))

/-- The map of free modules obtained by expressing a pulled-back linear map in two frames.
No invertibility of the linear map is required.
Source: blueprint vector-bundle purity, paragraph 2.
(blueprint: lem-pur-vector-bundle-map-frame-coordinates). -/
def framedPullbackMap {S T : Scheme.{u}} (f : T ⟶ S) (r s : ℕ)
    (F : S.Modules) (G : T.Modules) (m : (Scheme.Modules.pullback f).obj F ⟶ G)
    (V : S.Opens) (eS : Trivialization S r F V)
    (U : T.Opens) (eT : Trivialization T s G U)
    {W : Scheme.{u}} (a : W ⟶ U.toScheme) (g : W ⟶ V.toScheme)
    (h : (a ≫ U.ι) ≫ f = g ≫ V.ι) :
    SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin s)) :=
  (pulledFrame S r F V eS g).inv ≫
    (Scheme.Modules.pullbackCongr h.symm).hom.app F ≫
    (Scheme.Modules.pullbackComp (a ≫ U.ι) f).inv.app F ≫
    (Scheme.Modules.pullback (a ≫ U.ι)).map m ≫
    (pulledFrame T s G U eT a).hom

/-- A linear bundle map acts on each forward coordinate by the corresponding column
of the matrix of its module map in the pulled-back frames. This is a generator equation;
it asserts neither existence nor invertibility of a matrix, nor equality of inverse charts.
Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2; Stacks Tags 01M2 and 01LX.
(blueprint: lem-pur-vector-bundle-map-frame-coordinates).

Proof: the inverse target chart sends the degree-one image of its i-th frame section to
its i-th polynomial variable. Pull both module frames to W. The pullback adjunction and
its composition comparison identify the image of a source basis section with its image
under framedPullbackMap. Expand that image in the target free basis; its coefficients
are freeMatrix. The generator equation in MapSpec sends this expansion to the identical
linear combination of degree-one functions. Restriction along the chart inclusion and
its topIso converts these functions to coordinate. Finally the affine tower comparison
sends its standard coordinates to affineTraceCoordinate. This argument uses only linearity
and the unit of the pullback adjunction, so applies to rectangular matrices, empty schemes,
and rank zero without any affine or nonemptiness hypothesis.
-/
theorem map_frame_coordinates
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r s : ℕ) (F : S.Modules) (G : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (m : (Scheme.Modules.pullback f).obj F ⟶ G)
    (v : VectorBundleZeroSection.scheme T s G ⟶ VectorBundleZeroSection.scheme S r F)
    (hv : VectorTraceGeometry.MapSpec f r s F G
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ m) v)
    (V : S.Opens) (eS : Trivialization S r F V)
    (U : T.Opens) (eT : Trivialization T s G U)
    (W : Scheme.{u}) (a : W ⟶ U.toScheme) (g : W ⟶ V.toScheme)
    (h : (a ≫ U.ι) ≫ f = g ≫ V.ι)
    (k : affineTraceTower W s ⟶ ((π S r F) ⁻¹ᵁ V).toScheme)
    (hk : k ≫ ((π S r F) ⁻¹ᵁ V).ι =
      (affineTraceMap a s ≫ Etale.vectorIntegrationChart T s G U eT) ≫ v)
    (j : Fin r) :
    (k ≫ trivializationMap S r F V eS).appTop (AffineSpace.coord V.toScheme (ULift.up j)) =
      ∑ i : Fin s, (affineTraceProjection W s).appTop
        (Scheme.Modules.freeMatrix (framedPullbackMap f r s F G m V eS U eT a g h)
          (ULift.up i) (ULift.up j)) * affineTraceCoordinate W s i := by sorry

end AlgebraicGeometry.VectorBundleZeroSection
