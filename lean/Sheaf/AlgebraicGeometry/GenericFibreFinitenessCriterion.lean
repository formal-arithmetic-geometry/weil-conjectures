/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import Sheaf.TraceFormula.FiniteResiduePointClosedInFibre
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField

/-!
# Generic residue extensions and finite generic fibres

Source: Illusie–Laszlo–Orgogozo, Exposé II, Proposition 1.1.7 (printed p. 24);
the finite generic-fibre consequence is the restriction of the finite map there.
(blueprint: lem-per-generic-fibre-finiteness-criterion)

## Main statements

* `AlgebraicGeometry.generic_fibre_finiteness_criterion`: for a maximally dominant morphism
  of finite type to a Noetherian scheme, finite residue extensions at the generic points of
  the components of `X` are equivalent to finiteness over a dense open of `S`, and then the
  fibres over the generic points of `S` are finite.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/--
**Generic residue extensions and finite generic fibres.** Let `S` be Noetherian and
`f : X ⟶ S` of finite type, with every component generic point mapping to a component
generic point. Finite residue field extensions at those points are equivalent to finiteness
of `f` over a dense open of `S`; either condition implies finite scheme-theoretic fibres
over component generic points. Source: Illusie–Laszlo–Orgogozo, Exposé II, Proposition
1.1.7 (printed p. 24), together with the finite generic-fibre consequence there.
(blueprint: lem-per-generic-fibre-finiteness-criterion)

Proof (the node's steps):

1. Finite type is local finite type plus quasi-compactness. As `S` is Noetherian, `X` is
   Noetherian (lem-weil-pbc-finite-type-over-noetherian, Stacks 01T6), so it has finitely
   many irreducible components (lem-weil-pbc-noetherian-finitely-many-components, 0BA8),
   each with a unique generic point (lem-sc-scheme-sober, 01IS). `X` is quasi-separated
   (lem-weil-pbc-locally-noetherian-quasi-separated, 01OY), hence so is `f` by clause (1)
   of lem-weil-pbc-qcqs-morphism-permanence. No separatedness or reducedness is used.
2. Assume (i); fix a component generic point `s` of `S` and `x ∈ f⁻¹(s)`. Choose a
   component `C ∋ x` of `X` (lem-sc-irreducible-components-cover) with generic point `ξ`
   (lem-sc-scheme-sober). Continuity gives `s ∈ closure {f ξ}`; `f ξ` is a component
   generic point by maximal dominance, so maximality and uniqueness of generic points give
   `f ξ = s`. By (i), `κ(ξ)/κ(s)` is finite, so `ξ` is closed in `X_s`
   (lem-trf-finite-residue-point-closed-in-fibre, 01TE); as `x` is a specialization of
   `ξ` in `X_s` (def-pc-scheme-fibre), `x = ξ`. Hence `f⁻¹(s)` lies in the finite set of Step 1.
3. With Step 1 (`f` quasi-compact, quasi-separated, locally of finite type, `S`
   Noetherian) and the finite fibres of Step 2,
   lem-weil-pbc-generic-finite-morphism-open-neighborhood (Stacks 02NW) gives a dense open
   `V` containing every component generic point with `f⁻¹(V) → V` finite: (i) ⇒ (ii).
4. Assume (ii). Every component generic point `s` of `S` lies in `V`: `S` has finitely
   many components (lem-weil-pbc-noetherian-finitely-many-components); the complement `W`
   of the union of the other components is open, contains `s` and lies in
   `C = closure {s}`; density gives `v ∈ W ∩ V`, and `v ∈ closure {s}` forces `s ∈ V`
   (def-weil-irreducible-components, def-sc-generic-point).
5. For such `s ∈ V`, `X_s → Spec κ(s)` is the base change of the finite `f⁻¹(V) → V`
   along `Spec κ(s) → V` (universal property of the fibre product, def-pc-scheme-fibre),
   hence finite by clause (a) of lem-weil-pbc-finite-morphism-permanence (01WL). This is
   the last assertion under (ii), and under (i) by Step 3.
6. Let `x` be a component generic point of `X`, `s = f x`, a component generic point. By
   Steps 4 and 5, `X_s = Spec B` with `B` finite-dimensional over `k = κ(s)`
   (def-weil-finite-integral-morphism). The point given by `x` is a prime `q` of `B`;
   `B/q` is a finite-dimensional domain, hence a field
   (lem-weil-pbc-finite-dimensional-domain-is-field), the residue field of that point.
   lem-weil-pbc-fibre-product-point-residue-field (01JT) identifies it with `κ(x)` over
   `k`, since `κ(x) ⊗_k k ≅ κ(x)` has only the prime zero. So `κ(x)/κ(f x)` is finite:
   (ii) ⇒ (i).
-/
theorem generic_fibre_finiteness_criterion (f : X ⟶ S) [IsNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hdom : ∀ ⦃C : Set X⦄ ⦃x : X⦄,
      C ∈ irreducibleComponents X → IsGenericPoint x C →
        ∃ D : Set S, D ∈ irreducibleComponents S ∧ IsGenericPoint (f x) D) :
    ((
        (∀ ⦃C : Set X⦄ ⦃x : X⦄,
          C ∈ irreducibleComponents X → IsGenericPoint x C →
            letI := (f.residueFieldMap x).hom.toAlgebra;
            Module.Finite (S.residueField (f x)) (X.residueField x)) ↔
          ∃ V : S.Opens, Dense (V : Set S) ∧ IsFinite (f ∣_ V)) ∧
      ((
          (∀ ⦃C : Set X⦄ ⦃x : X⦄,
            C ∈ irreducibleComponents X → IsGenericPoint x C →
              letI := (f.residueFieldMap x).hom.toAlgebra;
              Module.Finite (S.residueField (f x)) (X.residueField x)) ∨
          (∃ V : S.Opens, Dense (V : Set S) ∧ IsFinite (f ∣_ V))) →
        ∀ ⦃D : Set S⦄ ⦃s : S⦄,
          D ∈ irreducibleComponents S → IsGenericPoint s D →
            IsFinite (f.fiberToSpecResidueField s))) := by
  sorry

end AlgebraicGeometry
