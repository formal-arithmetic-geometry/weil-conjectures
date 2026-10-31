/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PbcActualRingedExchange
public import WeilConjectures.AlgebraicGeometry.CompletedBaseChangeMap

/-! # Comparison of the actual and strict-tower completed exchange

Source: Stacks Tags 0D6D and 099N; blueprint completed-exchange coherence,
ordinary-to-completed unit normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The actual ambient-mate construction and the ordered strict-tower construction
are the same arrow under their unit-normalized coefficient comparisons.
Source: Stacks Tags 0D6D and 099N; blueprint completed-exchange coherence,
proof paragraphs on the ordinary unit and completed exchange
(blueprint: lem-weil-pbc-actual-completed-exchange-transport).

Proof: identify the actual coefficient map with the datum's integral coefficient
isomorphism by its finite projections. This identifies ordinary direct image and
ordinary module pullback. Their tensor-unit normalization identifies the ordinary
adjunctions. Universal derived counits identify the two ordinary derived pullbacks;
the ordinary section formula and the resolving normalization identify their
composition comparisons. Taking mates therefore identifies the two ordinary
exchange maps, with the direct-image identifications on both endpoints.
For complete inputs, the actual strict-tower comparison followed by the datum
strict-tower comparison identifies actual completed pullback with datum completed
pullback. Properness is not used: direct image preserves intrinsic completeness
because its direct-image/completion comparison preserves the unit. Apply the
completed-pullback comparison at the direct image of K for the source, and apply
direct image to the completed-pullback comparison at K for the target.
Precompose the asserted square with the actual ordinary-to-completed unit.
Naturality of completion and the unit equation for direct image reduce its left
side to ordinary exchange followed by the target completion unit. The two
strict-tower unit equations and completedExchange_unit reduce its right side to
the same arrow. The reflection property into the intrinsically complete target
cancels the unit and proves the square. These comparisons apply also to zero
objects and empty schemes, and require no dimension or constructibility bounds. -/
theorem pbcActualCompletedExchange_transport
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (K : PbcCompletedDerived X d) (hK : PbcIsIntrinsicallyComplete X d K) :
    ∃ (source : (pbcActualCompletedPull g d).obj ((pbcActualDerivedPush f d).obj K) ≅
        (d.completedPull g).obj ((d.push f).obj K))
      (target : (pbcActualDerivedPush f' d).obj ((pbcActualCompletedPull g' d).obj K) ≅
        (d.push f').obj ((d.completedPull g').obj K)),
      (pbcActualCompletedExchange d sq).app K ≫ target.hom =
        source.hom ≫ d.completedExchange sq K := by
  sorry

end AlgebraicGeometry.Scheme
