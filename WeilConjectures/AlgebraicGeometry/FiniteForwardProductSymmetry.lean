/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteForwardProductDefinitions
import WeilConjectures.AlgebraicGeometry.FiniteForwardCompactifiedSwap

/-! # Symmetry of the finite forward compact-support product

Source: Stacks Tag 0E48 and the compactification argument of
lem-sf-kunneth-coherence.proof.md, symmetry paragraph.
(blueprint: lem-pur-finite-forward-product-symmetry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem pasteNormalForms {D : Type*} [Category* D]
    {I I' O O' T T' : D} (x : I ⟶ O) (y : I' ⟶ O')
    (σ : I ⟶ I') (S : O' ⟶ O) (e : O ≅ T) (e' : O' ≅ T')
    (n : I ⟶ T) (n' : I' ⟶ T')
    (hx : x ≫ e.hom = n) (hy : y ≫ e'.hom = n')
    (hn : n = σ ≫ n' ≫ e'.inv ≫ S ≫ e.hom) : x = σ ≫ y ≫ S := by
  apply (cancel_mono e.hom).1
  rw [hx, hn, ← hy]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

attribute [local irreducible] derivedTensor upperStar lowerStar
  finiteForwardTensorSymmetryNat finiteForwardCompactificationComparison
  originCompositionAmbient finiteProductOrdinaryInCoordinates finiteForwardProduct

/-- The actual forward maps are symmetric, with the stated bounded-below origin domain.
Source: Stacks Tag 0E48 and the agent-formulated forward-product consequence in the node
(blueprint: lem-pur-finite-forward-product-symmetry).

Proof: apply the product-compactification theorem in both orders. Transport the
comparison to the common Cartesian cone by finiteForwardCartesianCoordinates.
Form its six-field domain from the five ordered fields and the opposite input field.
The chosen-compactification forward map is exactly finiteForwardProduct: the extra
self-comparisons are identity by etale reflexivity and full faithfulness of the site
comparison. Substitute finiteForwardCompactifiedSwap for the ordinary-product/open
normal form, then the reversed compactification equality. Cancel the reversed target
comparison against its inverse and cancel the forward target comparison on the right.
The signed source symmetry and finiteForwardProductSwap are the ones in the conclusion.
No exchange or projection transformation is inverted. -/
theorem finiteForwardProduct_symmetry
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
    FiniteForwardPurityProductSymmetry C f g M N wM wN := by
  let : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace
    (B ↘ Spec (CommRingCat.of C.field.k))
  let : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated
    (B ↘ Spec (CommRingCat.of C.field.k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (CommRingCat.of C.field.k))
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (CommRingCat.of C.field.k))
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (CommRingCat.of C.field.k))
  let : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated
    (Z ↘ Spec (CommRingCat.of C.field.k))
  let sq := IsPullback.of_hasPullback f g
  let cf := HasCompactification.compactification f
  let cg := HasCompactification.compactification g
  let G := finiteForwardCartesianGeometry cf cg sq
  let G' := finiteForwardCartesianGeometry cg cf sq.flip
  change FiniteForwardProductEquation C.Coefficient sq M.obj N.obj
  intro d d'
  have h := finiteForwardCartesianCoordinates C f g M N wM wN
    (finiteProduct_compactification C f g M N wM wN) sq d d'.input
  have h' := finiteForwardCartesianCoordinates C g f N M wN wM
    (finiteProduct_compactification C g f N M wN wM) sq.flip d' d.input
  have hs := finiteForwardCompactifiedSwap C f g M N wM wN d d'
  exact pasteNormalForms _ _ _ _
    ((finiteForwardCompactificationComparison C.Coefficient
      (HasCompactification.compactification (G.q ≫ g))
      (finiteProductCompactification G)).app ⟨_, d.external⟩)
    ((finiteForwardCompactificationComparison C.Coefficient
      (HasCompactification.compactification (G'.q ≫ f))
      (finiteProductCompactification G')).app ⟨_, d'.external⟩)
    _ _ h h' hs

end AlgebraicGeometry.ProEtale
