/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D9
-/
module

public import Sheaf.Paper.FiniteForwardProductCoordinates
import Sheaf.Paper.FiniteProperProductTranspose
import Sheaf.Paper.FiniteOpenProductSwap

/-! # Signed swap of the compactified ordinary external product

Source: lem-sf-kunneth-coherence.proof.md, symmetry paragraph.
(blueprint: lem-pur-finite-forward-compactified-swap).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The ordinary-product/open-extension normal form commutes with signed interchange.
Only the ordinary normal form occurs on both sides; no compact-support forward product
is used in this assertion.
Source: the proper counit calculation and open-product square in the symmetry paragraph
of lem-sf-kunneth-coherence.proof.md; Steps 2--3 of the parent node.
(blueprint: lem-pur-finite-forward-compactified-swap).

Proof: apply finiteProperProductTranspose to the two proper compactification maps and
the two extended input objects. Its last clause identifies the two ordinary products
by signed symmetry and the actual scheme-factor swap. Use the canonical intrinsic to
fixed-scalar equivalence: its tensor, pullback, direct-image, adjunction and compositor
comparisons preserve the specified counit-defined maps, so this is the equality for
finiteProductOrdinary. Apply finiteOpenProductSwap to the two compactification opens.
Convert exact pullback to total-left-derived pullback through the canonical comparison.
The two-stage open tensor maps are equal since their restrictions are the identity
under the same open units and extension by zero is fully faithful. Thus its final
signed-swap clause is exactly the square for finiteProductOpenTensor.
Apply ordinary direct image to that square and paste with the proper-product equality.
Naturality of tensor symmetry moves the two source compactification comparisons to
the left. The cocycle law and naturality of compactification comparison move the
output comparison to the right. The structure-map equality is sq.w, so its residual
transport is exactly finiteForwardProductSwap on the common Cartesian cone.
All auxiliary proper tensor objects are unbounded; only endpoint comparisons use the
supplied origin conditions. No compact-support product symmetry or forward-product
comparison is used here. -/
theorem finiteForwardCompactifiedSwap
    (C : WeilConjectures.PurityFiniteSetting.{u})
    {B X Z : Scheme.{u}}
    [B.Over (Spec (CommRingCat.of C.field.k))]
    [X.Over (Spec (CommRingCat.of C.field.k))]
    [Z.Over (Spec (CommRingCat.of C.field.k))]
    [IsSeparated (B ↘ Spec (CommRingCat.of C.field.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of C.field.k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (B ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of C.field.k))]
    (f : X ⟶ B) (g : Z ⟶ B)
    [f.IsOver (Spec (CommRingCat.of C.field.k))]
    [g.IsOver (Spec (CommRingCat.of C.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (M : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C.Coefficient)))
    (N : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} C.Coefficient)))
    (wM : Scheme.FixedEtaleOriginWitness X C.Coefficient M)
    (wN : Scheme.FixedEtaleOriginWitness Z C.Coefficient N) :
  letI : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace
    (B ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated
    (B ↘ Spec (CommRingCat.of C.field.k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (CommRingCat.of C.field.k))
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated
    (Z ↘ Spec (CommRingCat.of C.field.k))
  let sq := IsPullback.of_hasPullback f g
  let cf := HasCompactification.compactification f
  let cg := HasCompactification.compactification g
  let G := finiteForwardCartesianGeometry cf cg sq
  let G' := finiteForwardCartesianGeometry cg cf sq.flip
  letI : HasCompactification (G.q ≫ g) := finiteProductGeometry_h_hasCompactification G
  letI : HasCompactification (G'.q ≫ f) := finiteProductGeometry_h_hasCompactification G'
  ∀ (d : FiniteForwardProductDomain (ModuleCat.{u + 1} C.Coefficient) sq M.obj N.obj)
    (d' : FiniteForwardProductDomain (ModuleCat.{u + 1} C.Coefficient) sq.flip N.obj M.obj),
    let hm : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} C.Coefficient) X M.obj :=
      ⟨wM.complex.obj, wM.complex.property, ⟨wM.iso⟩⟩
    let hn : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} C.Coefficient) Z N.obj :=
      ⟨wN.complex.obj, wN.complex.property, ⟨wN.iso⟩⟩
    let out := (finiteForwardCompactificationComparison C.Coefficient
      (HasCompactification.compactification (G.q ≫ g))
      (finiteProductCompactification G)).hom.app ⟨_, d.external⟩
    let out' := (finiteForwardCompactificationComparison C.Coefficient
      (HasCompactification.compactification (G'.q ≫ f))
      (finiteProductCompactification G')).inv.app ⟨_, d'.external⟩
    finiteProductOrdinaryInCoordinates G C.Coefficient cf cg M.obj N.obj hm hn =
      finiteForwardTensorSymmetry (ModuleCat.{u + 1} C.Coefficient) B _ _ ≫
        finiteProductOrdinaryInCoordinates G' C.Coefficient cg cf N.obj M.obj hn hm ≫
        out' ≫ finiteForwardProductSwap (ModuleCat.{u + 1} C.Coefficient)
          sq M.obj N.obj ≫ out := by sorry

end AlgebraicGeometry.ProEtale
