/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.DimOneQuasiProjective
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Dense projective completion of a scheme of dimension at most one

Source: Stacks Project, Varieties, Tag 0BXV, `lemma-dim-1-projective-completion`
(blueprint: lem-weil-pbc-curve-projective-dense-completion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated finite type scheme of dimension at most one over a field admits an
H-projective completion with dense, scheme-theoretically dense open image and finite
boundary of closed points. The completion is reduced when the source is reduced and
empty when the source is empty.
Source: Stacks Project, Varieties, Tag 0BXV, `lemma-dim-1-projective-completion`.
(blueprint: lem-weil-pbc-curve-projective-dense-completion)

Proof:
1. By `lem-weil-pbc-finite-type-over-noetherian`, X is Noetherian. The minimal-closed-subset
   assertion `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` shows every open is
   quasi-compact (take a maximal finite union in any cover). Every morphism out of X
   is therefore quasi-compact.
2. Use `lem-sc-dim-one-quasi-projective` to immerse X into a finite projective space.
   Its scheme-theoretic image C and factor map a are supplied by
   `lemma-nagata-scheme-image-ideal-qc`. By
   `lemma-nagata-immersion-open-in-scheme-image`, a is an open immersion with both density
   properties. The closed image inclusion makes C H-projective over k.
3. By `lem-pc-projective-proper` and `def-weil-proper-morphism`, C is finite type;
   `lem-weil-pbc-finite-type-over-noetherian` then makes it Noetherian.
4. Decompose C into finitely many irreducible components using
   `lem-sc-noetherian-closed-subset-finite-components`. Each has a generic point by
   `lem-weil-pbc-scheme-sober`. The open dense image meets the open part of each
   component outside all the others, hence contains each component's generic point.
5. For each component Z, Z intersect X is a nonempty irreducible closed subset of X.
   The generic residue fields in X and C agree because a is an open immersion.
   Apply `lem-sc-closed-irreducible-dimension-trdeg` twice: Z and Z intersect X have
   the same dimension, at most one. Every irreducible closed chain in C lies in a
   component, proving the dimension bound, also for mixed dimensions.
6. A boundary point is not a component's generic point. A further strict specialization
   would give a chain of length two, contradicting the dimension bound and sobriety
   (`lem-weil-pbc-scheme-sober`). Thus boundary points are closed. The closed boundary
   has finitely many irreducible components by
   `lem-sc-noetherian-closed-subset-finite-components`; their closed generic points
   show these components are singletons, so the boundary is finite.
7. If X is reduced (`def-pc-reduced-scheme`), any nilpotent section on C restricts to
   zero on X. Scheme-theoretic density makes restriction injective, so C is reduced.
8. If X is empty, its dense image forces C empty. All bounds and boundary claims
   allow this case. -/
theorem exists_projective_dense_completion_of_dim_le_one
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (C : Scheme.{u}) (g : C ⟶ Spec (.of k)) (a : X ⟶ C),
      IsHProjective g ∧ topologicalKrullDim C ≤ 1 ∧ IsOpenImmersion a ∧
      a ≫ g = X ↘ Spec (.of k) ∧ DenseRange a ∧
      (∀ U : C.Opens, Function.Injective (a.app U)) ∧
      (Set.range a)ᶜ.Finite ∧ (∀ c : C, c ∉ Set.range a → IsClosed ({c} : Set C)) ∧
      (IsReduced X → IsReduced C) ∧ (IsEmpty X → IsEmpty C) := sorry

end AlgebraicGeometry
