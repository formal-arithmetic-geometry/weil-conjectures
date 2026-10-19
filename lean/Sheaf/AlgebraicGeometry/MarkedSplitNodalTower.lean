/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveNodalTower
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Equivariant marked split nodal towers

Source: ILO, Travaux de Gabber, Expose X, Lemma 2.5 and proof, p.153,
and Expose IX, Theorem 1.2, p.131
(blueprint: def-per-marked-split-nodal-tower).

The strict split convention requires smooth fibre components. Hence a branch at a node
is specified by its incident component, and fixing components and nodes fixes both ends.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Strict splitting: reduced fibre components are smooth and geometrically irreducible,
and every nonsmooth fibre point has the base residue field. Smooth components exclude
self-nodes, so rational nodes have two rational branches, one on each incident component.
Source: ILO X 2.5, p.153, with the strict split convention in the tower modification input
(blueprint: def-per-marked-split-nodal-tower). -/
def HasStrictSplitNodalFibres {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : Prop :=
  ∀ y : Y,
    (∀ C : irreducibleComponents (f.fiber y),
      Smooth ((Scheme.IdealSheafData.vanishingIdeal
        ⟨C.1, isClosed_of_mem_irreducibleComponents _ C.2⟩).subschemeι ≫
          f.fiberToSpecResidueField y) ∧
      GeometricallyIrreducible ((Scheme.IdealSheafData.vanishingIdeal
        ⟨C.1, isClosed_of_mem_irreducibleComponents _ C.2⟩).subschemeι ≫
          f.fiberToSpecResidueField y)) ∧
    ∀ x : f.fiber y, f.fiberι y x ∉ f.smoothLocus →
      IsIso ((f.fiberToSpecResidueField y).residueFieldMap x)

/-- A length `d` marked split nodal tower with an action on every level, allowing an action
on the base. Boundaries are closed sets; their recursion includes all markings. The graph
condition fixes each component, node and marked point over a fixed base point. Because
components are smooth and geometrically irreducible, these are exactly the vertices,
edges, ends and legs of the geometric dual graph, including semilinear base actions.
The structure also allows `d = 0`; consumers may require positive length.
Source: ILO X 2.5, proof, p.153; IX 1.2, p.131
(blueprint: def-per-marked-split-nodal-tower). -/
structure MarkedSplitNodalTower (T : Scheme.{u}) (S : Set T)
    (G : Type v) [Group G] (d : ℕ) where
  Y : Fin (d + 1) → Scheme.{u}
  base : Y 0 ≅ T
  f : ∀ i : Fin d, Y i.succ ⟶ Y i.castSucc
  toBase : ∀ i : Fin (d + 1), Y i ⟶ T
  toBase_zero : toBase 0 = base.hom
  toBase_succ : ∀ i : Fin d, f i ≫ toBase i.castSucc = toBase i.succ
  integral : ∀ i, IsIntegral (Y i)
  projective : ∀ i, IsHProjective (f i)
  flat : ∀ i, Flat (f i)
  fp : ∀ i, LocallyOfFinitePresentation (f i)
  connected : ∀ i, GeometricallyConnected (f i)
  reduced : ∀ i, GeometricallyReduced (f i)
  geometric_fibres : ∀ (i : Fin d) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Y i.castSucc),
    (pullback (f i) s).IsPureDimension 1 ∧
    ∀ x : ↥(pullback (f i) s),
      (∃ U : (pullback (f i) s).Opens,
        x ∈ U ∧ Smooth (U.ι ≫ pullback.snd (f i) s)) ∨
      IsGeometricOrdinaryDoublePoint Ω (pullback (f i) s) x
  split : ∀ i, @HasStrictSplitNodalFibres _ _ (f i) (fp i)
  marks : Fin d → ℕ
  sectionMap : ∀ (i : Fin d), Fin (marks i) → (Y i.castSucc ⟶ Y i.succ)
  section_eq : ∀ i j, sectionMap i j ≫ f i = 𝟙 (Y i.castSucc)
  disjoint_sections : ∀ i, Pairwise (fun j k ↦
    Disjoint (Set.range (sectionMap i j)) (Set.range (sectionMap i k)))
  smooth_sections : ∀ i j, Set.range (sectionMap i j) ⊆
    (@Scheme.Hom.smoothLocus _ _ (f i) (fp i) : Set (Y i.succ))
  boundary : ∀ i, Closeds (Y i)
  boundary_zero : (boundary 0 : Set (Y 0)) = base.hom ⁻¹' S
  boundary_succ : ∀ i : Fin d, (boundary i.succ : Set (Y i.succ)) =
    (f i) ⁻¹' (boundary i.castSucc : Set (Y i.castSucc)) ∪
      ⋃ j, Set.range (sectionMap i j)
  smooth_off_boundary : ∀ i : Fin d,
    Smooth ((f i) ∣_ (⟨(boundary i.castSucc : Set (Y i.castSucc))ᶜ,
      (boundary i.castSucc).isClosed.isOpen_compl⟩ : (Y i.castSucc).Opens))
  action : ∀ i, G →* Aut (Y i)
  equivariant : ∀ (i : Fin d) (g : G),
    (action i.succ g).hom ≫ f i = f i ≫ (action i.castSucc g).hom
  stable_markings : ∀ (i : Fin d) (g : G),
    (action i.succ g).hom '' (⋃ j, Set.range (sectionMap i j)) =
      ⋃ j, Set.range (sectionMap i j)
  fixed_components : ∀ (i : Fin d) (g : G) (y : Y i.castSucc),
    (action i.castSucc g).hom y = y →
    ∀ C : Set ((f i).fiber y), C ∈ irreducibleComponents ((f i).fiber y) →
      (action i.succ g).hom '' ((f i).fiberι y '' C) = (f i).fiberι y '' C
  fixed_nodes : ∀ (i : Fin d) (g : G) (y : Y i.castSucc),
    (action i.castSucc g).hom y = y →
    ∀ x : (f i).fiber y,
      (f i).fiberι y x ∉
        (@Scheme.Hom.smoothLocus _ _ (f i) (fp i) : Set (Y i.succ)) →
      (action i.succ g).hom ((f i).fiberι y x) = (f i).fiberι y x
  fixed_legs : ∀ (i : Fin d) (g : G) (y : Y i.castSucc),
    (action i.castSucc g).hom y = y →
    ∀ j, (action i.succ g).hom (sectionMap i j y) = sectionMap i j y

end AlgebraicGeometry
