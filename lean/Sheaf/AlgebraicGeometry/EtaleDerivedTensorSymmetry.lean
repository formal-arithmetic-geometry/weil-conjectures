/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# The canonical symmetry of the etale derived tensor product

Source: Stacks Project, Tag 06YU, symmetry of the derived tensor product
(blueprint: lem-kun-tensor-sym).

The recorded existence theorem forgets the canonical map. This interface exposes the actual
braiding descended from the signed braiding of cochain complexes, without choosing an arbitrary
isomorphism from that existence theorem.

## Main definitions

- `CategoryTheory.DerivedMonoidal.canonicalBraidingNatIso`: the natural braiding before
  specializing to etale sheaves.
- `AlgebraicGeometry.Etale.derivedTensorSymmetry`: its canonical etale specialization.
-/

@[expose] public section

universe v₁ v₂ u' u

open CategoryTheory Limits

namespace CategoryTheory.DerivedMonoidal

/-- The canonical natural symmetry induced on the derived tensor bifunctor by a braiding.
Source: Stacks Project, Tag 06YU (blueprint: lem-kun-tensor-sym).
This packages the existing `braiding` and its two existing naturality identities before
specializing to etale sheaves, avoiding repeated reduction of their monoidal instances. -/
noncomputable def canonicalBraidingNatIso
    {C : Type u'} {D : Type u} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [BraidedCategory C] (F : C ⥤ D) (W : MorphismProperty C)
    [F.IsLocalization W] [W.ContainsIdentities] [F.HasDerivedMonoidalCategory W] :
    bifunctor F W ≅ (bifunctor F W).flip :=
  NatIso.ofComponents (fun K ↦
    NatIso.ofComponents (fun L ↦ braiding F W K L)
      (fun f ↦ braiding_naturality_right F W K f))
    (fun f ↦ NatTrans.ext (funext (fun L ↦ braiding_naturality_left F W f L)))

end CategoryTheory.DerivedMonoidal

namespace AlgebraicGeometry.Etale

/-- The canonical symmetry of the unbounded derived tensor bifunctor, natural in both variables.
Source: Stacks Project, Tag 06YU (blueprint: lem-kun-tensor-sym).

Construction: the homotopy-category braiding is the signed swap in bidegree `(p,q)`, with
sign `(-1)^(p*q)`. Descend that braiding through the K-flat localization using
`DerivedMonoidal.braiding`, and assemble its natural isomorphism of curried bifunctors.
The characterization `DerivedMonoidal.braiding_hom_μ` identifies the descended map on K-flat
representatives with precisely that signed swap. -/
noncomputable def derivedTensorSymmetry
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) : derivedTensor A T ≅ (derivedTensor A T).flip :=
  DerivedMonoidal.canonicalBraidingNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf T.smallEtaleTopology A) (ComplexShape.up ℤ))

end AlgebraicGeometry.Etale
