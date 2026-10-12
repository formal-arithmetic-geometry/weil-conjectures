/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover
public import Mathlib.GroupTheory.Index
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
/-!
# Open stabilizers of connected finite étale fibres

Source: SGA 1, Exposé V, Proposition 6.13 and §7
(blueprint: lem-galois-pi1-finite-etale-image-stabilizer-open-index).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.PreGaloisCategory
namespace AlgebraicGeometry.Scheme.FiniteEtale
/-- The marked-point stabilizer is open and has index the fibre cardinality.
Source: SGA 1, Exposé V, Proposition 6.13 and §7, p. 116; the index follows by
orbit–stabilizer from transitivity, Exposé V, §5.3
(blueprint: lem-galois-pi1-finite-etale-image-stabilizer-open-index).

Proof: The cover `P` has underlying scheme `X`, so its connectedness makes `P` a
connected finite étale object by `isConnected_of_connectedSpace`. The fundamental
group acts transitively on the fibre of this object (Mathlib's
`IsFundamentalGroup` instance). Its action is continuous on this finite discrete
fibre, so `stabilizer_isOpen` gives openness. The coset map `gU ↦ g • a` is a
bijection with the fibre: stabilizer membership gives well-definedness and
injectivity, and transitivity gives surjectivity. Thus
`MulAction.index_stabilizer_of_transitive` gives the asserted index. -/
theorem fundamentalGroupMap_stabilizer_open_and_index
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (GX GY : Type u) [Group GX] [TopologicalSpace GX] [IsTopologicalGroup GX]
    [CompactSpace GX] [∀ Q, MulAction GX ((fiber s).obj Q)]
    [IsFundamentalGroup (fiber s) GX]
    [Group GY] [TopologicalSpace GY] [IsTopologicalGroup GY] [CompactSpace GY]
    [∀ P, MulAction GY ((fiber (s ≫ f)).obj P)]
    [IsFundamentalGroup (fiber (s ≫ f)) GY] :
    let P : Y.FiniteEtale := ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩
    let a : (fiber (s ≫ f)).obj P := fiberMk (s ≫ f) P s rfl
    let U := MulAction.stabilizer GY a
    IsOpen (U : Set GY) ∧ U.index = Nat.card ((fiber (s ≫ f)).obj P) := by
  let P : Y.FiniteEtale := ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩
  let a : (fiber (s ≫ f)).obj P := fiberMk (s ≫ f) P s rfl
  have : ConnectedSpace P.obj.left := ‹ConnectedSpace X›
  have : IsConnected P := isConnected_of_connectedSpace P
  exact ⟨stabilizer_isOpen GY a, MulAction.index_stabilizer_of_transitive GY a⟩
end AlgebraicGeometry.Scheme.FiniteEtale
