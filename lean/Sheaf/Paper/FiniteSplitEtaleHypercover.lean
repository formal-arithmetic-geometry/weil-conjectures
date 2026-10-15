/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicTopology.SimplicialObject.Split
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Finite split étale hypercovers

Source: blueprint `def-weil-pbc-finite-split-hypercover`, order 946;
Stacks Project, Hypercoverings, example `example-hypercovering-in-C`, and
Simplicial Methods, definitions `definition-split` and `definition-homotopy`.
(blueprint: def-weil-pbc-finite-split-hypercover)

The matching universal property is tested on all schemes over the base, not just étale
ones. Mathlib's splitting uses the canonical degeneracy maps in its coproduct cofan.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A split étale hypercover over a qcqs scheme.
Source: blueprint definition of finite split étale hypercovers, order 946;
Stacks Hypercoverings `example-hypercovering-in-C`, Simplicial Methods `definition-split`.
The matching projections run over all lower simplices. The universal property is exactly
that of the finite matching diagram (including degenerate lower simplices does not change
its limit). In degree zero it is the terminal object over `X`; in degree one it is the
product of the two vertices over `X`. All structure maps are over `X`, including the
augmentation and simplicial identities. No choices of matching maps are unconstrained.
(blueprint: def-weil-pbc-finite-split-hypercover) -/
structure SplitEtaleHypercover (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] where
  simplicial : SimplicialObject X.Etale
  splitting : simplicial.Splitting
  matching : ℕ → X.Etale
  projection : ∀ (n : ℕ) (Δ : SimplexCategory), Δ.len < n →
    (Δ ⟶ SimplexCategory.mk n) → (matching n ⟶ simplicial.obj (op Δ))
  projection_naturality : ∀ (n : ℕ) (Δ Δ' : SimplexCategory)
    (h : Δ.len < n) (h' : Δ'.len < n) (α : Δ' ⟶ Δ)
    (θ : Δ ⟶ SimplexCategory.mk n),
    projection n Δ h θ ≫ simplicial.map α.op = projection n Δ' h' (α ≫ θ)
  matching_universal : ∀ (n : ℕ) (T : Over X)
    (p : ∀ (Δ : SimplexCategory), Δ.len < n → (Δ ⟶ SimplexCategory.mk n) →
      (T ⟶ (Scheme.Etale.forget X).obj (simplicial.obj (op Δ)))),
    (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
      p Δ h θ ≫ (Scheme.Etale.forget X).map (simplicial.map α.op) =
        p Δ' h' (α ≫ θ)) →
    ∃! f : T ⟶ (Scheme.Etale.forget X).obj (matching n),
      ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
        f ≫ (Scheme.Etale.forget X).map (projection n Δ h θ) = p Δ h θ
  matchingMap : ∀ n, simplicial.obj (op (SimplexCategory.mk n)) ⟶ matching n
  matchingMap_projection : ∀ (n : ℕ) (Δ : SimplexCategory) (h : Δ.len < n)
    (θ : Δ ⟶ SimplexCategory.mk n),
    matchingMap n ≫ projection n Δ h θ = simplicial.map θ.op
  matching_cover : ∀ n, Surjective (matchingMap n).left

/-- A split étale hypercover finite in each degree. Source: blueprint order 946.
(blueprint: def-weil-pbc-finite-split-hypercover) -/
structure FiniteSplitEtaleHypercover (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] extends SplitEtaleHypercover X where
  finite_each_degree : ∀ n, ∃ (k : ℕ) (V : Fin k → X.Etale)
    (ι : ∀ i, V i ⟶ splitting.N n),
    Nonempty (IsColimit (Cofan.mk (splitting.N n) ι)) ∧
      ∀ i, CompactSpace (V i).left ∧ QuasiSeparatedSpace (V i).left ∧
        LocallyOfFinitePresentation (V i).hom ∧ QuasiCompact (V i).hom ∧
          QuasiSeparated (V i).hom

end AlgebraicGeometry
