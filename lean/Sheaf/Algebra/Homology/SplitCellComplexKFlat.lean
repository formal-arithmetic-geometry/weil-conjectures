/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor

/-!
# K-flatness of complexes built from split free cells

Source: Stacks Project, More on Algebra, Tags 0BYH and 06Y3, and the proof of
lemma-resolution-filtered-complex (Tag 0H7X).
(blueprint: lem-kun-split-cell-complex-kflat).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- An exhaustive increasing sequence of subcomplexes, starting at zero, whose inclusions
split in each degree and whose successive quotients have zero differential and free terms,
has K-flat union. The monomorphisms `ι` identify `F m` with the subcomplexes of `C`;
`step` and `hcompat` express their increasing order. The quotient is the categorical
cokernel, which is the degreewise module quotient. Retractions are only degreewise,
not morphisms of complexes. No boundedness or finite-rank condition is imposed.
Source: Stacks Project, More on Algebra, Tags 0BYH, 06Y3 and 0H7X, proof of
lemma-resolution-filtered-complex, part (2).
(blueprint: lem-kun-split-cell-complex-kflat).

Proof:
1. Fix an acyclic complex `A`. For `Q = cokernel (step m)`, choose a basis of each
   `Q.X q` using def-weil-pbc-free-module. The signed direct-sum total tensor construction
   def-pc-tensor-complex-sheaves identifies degree `n` of `A ⊗ Q` with the direct sum,
   over degrees `q` and their basis elements, of `A.X (n-q)`. Because `Q` has zero
   differential, the coordinate differential is that of `A`. A cycle has finite support;
   choose a boundary preimage in each nonzero coordinate and zero elsewhere. This proves
   acyclicity without restricting degrees or ranks.
2. For each inclusion `i` choose the assumed degreewise retraction `r`. For the quotient
   map `π`, the formula `s(π x) = x - i(r x)` is well-defined, linear, and satisfies
   `π s = 1` and `i r + s π = 1`. Tensoring these identities with each term of `A`, then
   taking direct sums, gives a degreewise short exact sequence of total tensor complexes.
   Inclusion and quotient are chain maps, so commute with both signed differential terms;
   the splitting maps themselves need not be chain maps.
3. Induct on `m`. The initial tensor complex is zero by `hzero`. In the successor step,
   the long exact cohomology sequence lem-weil-pbc-complex-ses-homology-long-exact of
   the short exact sequence in step 2 has zero outer terms by induction and step 1.
   Hence `Tot(A ⊗ F m)` is acyclic at every finite stage.
4. Compatibility, monicity and exhaustion identify `C` with the degreewise filtered
   colimit of `F`. Apply lem-pc-module-filtered-colimits-tensor on the one-object site
   with only the maximal covering sieve and ring sheaf `R`. Ordinary modules are exactly
   its module sheaves. Its tensor comparison for the varying first factor gives the
   varying second-factor comparison using signed symmetry `a ⊗ c ↦ (-1)^(p*q) c ⊗ a`.
   Symmetry is a chain isomorphism and commutes with the stage maps. Thus `Tot(A ⊗ C)`
   is the filtered colimit of the finite-stage tensor complexes. Exact filtered colimits
   preserve the short exact sequences from cycles to terms to the next cycles, showing
   directly that the colimit's boundaries equal its cycles in every degree.
5. Since `A` was arbitrary, this is K-flatness in def-pc-module-kflat-complex, equivalently
   preservation of quasi-isomorphisms under tensoring on either side, the recorded
   predicate `(HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat`.
-/
theorem kFlat_of_split_free_cells {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (ι : ∀ m : ℕ, F m ⟶ C) (step : ∀ m : ℕ, F m ⟶ F (m + 1))
    (hzero : IsZero (F 0))
    (hmono : ∀ m : ℕ, Mono (ι m))
    (hcompat : ∀ m : ℕ, step m ≫ ι (m + 1) = ι m)
    (hexhaustive : ∀ (n : ℤ) (x : C.X n),
      ∃ (m : ℕ) (y : (F m).X n), (ι m).f n y = x)
    (hsplit : ∀ (m : ℕ) (n : ℤ),
      ∃ r : (F (m + 1)).X n ⟶ (F m).X n,
        (step m).f n ≫ r = 𝟙 ((F m).X n))
    (hquot_d : ∀ (m : ℕ) (n : ℤ), (cokernel (step m)).d n (n + 1) = 0)
    (hquot_free : ∀ (m : ℕ) (n : ℤ), Module.Free R ((cokernel (step m)).X n)) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).kFlat C := by
  sorry

end CochainComplex
