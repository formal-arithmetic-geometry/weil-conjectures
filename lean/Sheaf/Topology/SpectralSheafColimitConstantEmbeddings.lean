/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.Topology.SheafDirectedColimitFiniteCoequalizers
import Sheaf.Topology.SpectralFiniteCoequalizerEmbedsConstant

/-!
# Directed presentations of sheaves on spectral spaces

Source: Stacks Project, Modules, Tags 0CAI and 0CAL, combined in the proof of
Étale Cohomology, Tag 09ZG.
(blueprint: lem-weil-pbc-spectral-sheaf-colimit-constant-embeddings)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat

/-- Every sheaf of sets on a spectral space is a directed colimit of sheaves admitting
sectionwise injections into finite products of finite constant sheaves pushed forward
from constructible closed subsets. Source: Stacks Project, Modules, Tags 0CAI and 0CAL,
combined in Étale Cohomology, proof of Tag 09ZG.
(blueprint: lem-weil-pbc-spectral-sheaf-colimit-constant-embeddings)

The functor `D` includes the transition maps and their identity and composition laws.
The natural transformation `ι` includes compatibility of the cocone maps. For each term,
`e` gives the components of the embedding into the sectionwise product; its last clause
is precisely naturality with respect to restriction. The factor at `k` over `U` is
`LocallyConstant {x : X // x ∈ U ∧ x ∈ Z k} (S k)`, the closed direct image specified
in the node. Thus no choice of an alternative constant-sheaf model is involved.

Proof:
1. The quasi-compact opens form a basis by `def-weil-spectral-space`.
2. Apply `lem-weil-pbc-sheaf-directed-colimit-finite-coequalizers` (Tag 0CAI) to this
   basis and `F`. Its directed diagram consists of coequalizers of two maps between
   finite coproducts of extensions by the empty set of finite constant sheaves on
   quasi-compact opens (`def-weil-pbc-sets-extension-by-empty`). Its cocone with vertex
   `F` is a colimit (`def-weil-pbc-category-colimit`).
3. For each term apply `lem-weil-pbc-spectral-finite-coequalizer-embeds-constant`
   (Tag 0CAL). It supplies finitely many constructible closed subsets
   (`def-weil-constructible-subset`), finite coefficient sets and a sectionwise injective
   morphism to the product of their closed direct images. Take its components as `e`;
   the morphism's naturality is the displayed restriction identity. -/
theorem spectral_sheaf_colimit_constant_embeddings
    (X : TopCat.{u}) [SpectralSpace X] (F : X.Sheaf (Type u)) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ X.Sheaf (Type u)) (ι : D ⟶ (Functor.const I).obj F),
      Nonempty (IsColimit (Cocone.mk F ι)) ∧
      ∀ i : I, ∃ (n : ℕ) (Z : Fin n → Set X) (S : Fin n → Type u),
        (∀ k : Fin n, IsClosed (Z k) ∧ Topology.IsConstructible (Z k) ∧ Finite (S k)) ∧
        ∃ e : ∀ U : Opens X, (D.obj i).obj.obj (op U) →
            ((k : Fin n) → LocallyConstant {x : X // x ∈ U ∧ x ∈ Z k} (S k)),
          (∀ U : Opens X, Function.Injective (e U)) ∧
          ∀ (U V : Opens X) (f : V ⟶ U) (s : (D.obj i).obj.obj (op U)) (k : Fin n),
            e V ((D.obj i).obj.map f.op s) k =
              LocallyConstant.comap
                ⟨fun x : {x : X // x ∈ V ∧ x ∈ Z k} ↦
                    ⟨x.1, f.le x.2.1, x.2.2⟩,
                  continuous_subtype_val.subtype_mk _⟩ (e U s k) := by
  let B : Set (Opens X) := {U | IsCompact (U : Set X)}
  have hBasis : IsTopologicalBasis ((fun U : Opens X ↦ (U : Set X)) '' B) := by
    have hB : (fun U : Opens X ↦ (U : Set X)) '' B =
        {U : Set X | IsOpen U ∧ IsCompact U} := by
      ext U
      constructor
      · rintro ⟨V, hV, rfl⟩
        exact ⟨V.isOpen, hV⟩
      · rintro ⟨hOpen, hCompact⟩
        exact ⟨⟨U, hOpen⟩, hCompact, rfl⟩
    rw [hB]
    exact PrespectralSpace.isTopologicalBasis
  obtain ⟨I, hOrder, hNonempty, hDirected, D, ι, hColimit, hTerms⟩ :=
    exists_directedColimit_finiteCoequalizers X B hBasis (fun _ h ↦ h) F
  let : Preorder I := hOrder
  let : Nonempty I := hNonempty
  let : IsDirected I (· ≤ ·) := hDirected
  refine ⟨I, hOrder, hNonempty, hDirected, D, ι, hColimit, ?_⟩
  intro i
  obtain ⟨m, n, U, V, S, T, hU, hV, hS, hT, β, γ, q, hq, hcoeq⟩ := hTerms i
  let generators : Fin n → CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) :=
    fun a ↦ extensionByEmptyConstant (U a) (S a)
  let relations : Fin m → CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) :=
    fun b ↦ extensionByEmptyConstant (V b) (T b)
  exact spectral_finite_coequalizer_embeds_constant X (D.obj i) m n U V S T
    hU hV hS hT
    (Cofan.mk _ (Sigma.ι generators))
    (Cofan.mk _ (Sigma.ι relations))
    ⟨coproductIsCoproduct generators⟩ ⟨coproductIsCoproduct relations⟩ β γ q hq hcoeq

end TopCat
