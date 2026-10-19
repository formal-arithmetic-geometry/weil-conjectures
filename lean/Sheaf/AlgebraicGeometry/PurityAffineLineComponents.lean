/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.Basic

import Mathlib.Topology.Connected.Clopen

/-!
# Connected components of the affine and punctured affine lines

Source: blueprint sec-smooth-purity/sk-prop-a1-inv/lem-pur-a1-components.md;
Stacks Project, Tags 01UA, 01M0, 01K1 and 0377 (blueprint: lem-pur-a1-components).

The affine line and its open complement of the zero section have connected components
pulled back from the base; the unit section meets every such component.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- The connected components of the relative affine line and of the open complement of its
zero section are pulled back from the base, and every component meets the unit section.
Source: blueprint sec-smooth-purity/sk-prop-a1-inv/lem-pur-a1-components.md;
Stacks Project, Tags 01UA, 01M0, 01K1 and 0377 (blueprint: lem-pur-a1-components).

Proof:
1. The affine-space projection is open by `AffineSpace.isOpenMap_over`. Its composite
   with the open immersion `j` is open too. The unit section and its supplied lift give
   sections of both projections, so both maps are continuous open surjections.
2. The affine-space projection is geometrically irreducible. Its fibres are therefore
   irreducible and connected. The fibres of the restricted projection are inverse images
   under an open embedding, so are preirreducible; the lifted unit section makes them
   nonempty, hence connected.
3. A continuous open surjection is a quotient map. Apply the connected-fibre component
   formula `Topology.IsCoinducing.preimage_connectedComponent` to both projections.
4. For any point `x`, the unit point over its image lies in the same component by the
   component formula. In the affine line use both the unit section and its factorization
   through `j`; in the open subscheme use the lifted unit section. -/
theorem affineLine_connectedComponents
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) [Nonempty B]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    {G : Scheme.{u}}
    (j : G ⟶ AffineSpace (ULift.{u} (Fin 1)) B) [IsOpenImmersion j]
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ)
    (i₁ : B ⟶ G)
    (hi₁ : i₁ ≫ j = AffineSpace.oneSection (ULift.{u} (Fin 1)) B) :
    (∀ x : AffineSpace (ULift.{u} (Fin 1)) B,
      connectedComponent x =
        (AffineSpace (ULift.{u} (Fin 1)) B ↘ B).base ⁻¹'
          connectedComponent ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B).base x)) ∧
    (∀ x : G,
      connectedComponent x =
        (j ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).base ⁻¹'
          connectedComponent ((j ≫ (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).base x)) ∧
    (∀ x : AffineSpace (ULift.{u} (Fin 1)) B,
      (connectedComponent x ∩ Set.range j.base).Nonempty) ∧
    (∀ x : AffineSpace (ULift.{u} (Fin 1)) B,
      (connectedComponent x ∩
        Set.range (AffineSpace.oneSection (ULift.{u} (Fin 1)) B).base).Nonempty) ∧
    (∀ x : G,
      (connectedComponent x ∩ Set.range i₁.base).Nonempty) := by
  have _ := hj
  let p := AffineSpace (ULift.{u} (Fin 1)) B ↘ B
  let q := j ≫ p
  have hpopen : IsOpenMap p := AffineSpace.isOpenMap_over B
  have hqopen : IsOpenMap q := hpopen.comp j.isOpenEmbedding.isOpenMap
  have hsection : i₁ ≫ q = 𝟙 B := by
    dsimp [q, p]
    rw [← Category.assoc, hi₁, AffineSpace.oneSection_comp_over]
  have hsection_apply (y : B) : q (i₁ y) = y := by
    change (i₁ ≫ q) y = y
    rw [hsection]
    rfl
  have hunit (y : B) : p (AffineSpace.oneSection (ULift.{u} (Fin 1)) B y) = y := by
    change (AffineSpace.oneSection (ULift.{u} (Fin 1)) B ≫ p) y = y
    exact congrArg (fun f : B ⟶ B ↦ f y)
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)
  have hpirr (y : B) : IsIrreducible (p ⁻¹' {y}) :=
    p.isIrreducible_preimage hpopen isIrreducible_singleton
  have hqconn (y : B) : _root_.IsConnected (q ⁻¹' {y}) := by
    refine ⟨⟨i₁ y, hsection_apply y⟩, ?_⟩
    exact ((hpirr y).isPreirreducible.preimage j.isOpenEmbedding).isPreconnected
  have hpcomp (x : AffineSpace (ULift.{u} (Fin 1)) B) :
      connectedComponent x = p ⁻¹' connectedComponent (p x) :=
    ((hpopen.isQuotientMap p.continuous p.surjective).isCoinducing.preimage_connectedComponent
      (fun y ↦ (hpirr y).isConnected) x).symm
  have hqcomp (x : G) : connectedComponent x = q ⁻¹' connectedComponent (q x) :=
    (Topology.IsCoinducing.preimage_connectedComponent
      (hqopen.isQuotientMap q.continuous (fun y ↦ ⟨i₁ y, hsection_apply y⟩)).isCoinducing
      hqconn x).symm
  refine ⟨hpcomp, hqcomp, ?_, ?_, ?_⟩
  · intro x
    refine ⟨j (i₁ (p x)), ?_, ⟨i₁ (p x), rfl⟩⟩
    rw [hpcomp x]
    change q (i₁ (p x)) ∈ connectedComponent (p x)
    rw [hsection_apply]
    exact mem_connectedComponent
  · intro x
    refine ⟨AffineSpace.oneSection (ULift.{u} (Fin 1)) B (p x), ?_, ⟨p x, rfl⟩⟩
    rw [hpcomp x]
    change p (AffineSpace.oneSection (ULift.{u} (Fin 1)) B (p x)) ∈ connectedComponent (p x)
    rw [hunit]
    exact mem_connectedComponent
  · intro x
    refine ⟨i₁ (q x), ?_, ⟨q x, rfl⟩⟩
    rw [hqcomp x]
    change q (i₁ (q x)) ∈ connectedComponent (q x)
    rw [hsection_apply]
    exact mem_connectedComponent

end AlgebraicGeometry
