/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q61, NE
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.IndConstructibleExtensions
import Sheaf.Paper.IndHeartKernelsCokernels
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Shift.ShiftSequence
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# The ind-constructible ambient derived category is triangulated

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ambient-ind-derived,
node `det-ambient-ind-derived-triangulated` (blueprint: det-ambient-ind-derived-triangulated).

## Main statements

- `indConstructibleDerived_isTriangulated`: zero, integer shifts, and triangle closure.
- `indConstructibleDerived_isClosedUnderIsomorphisms`: the explicit repleteness clause.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The full subcategory of the ordinary derived category whose cohomology objects are
ind-constructible in every degree is triangulated, for each of the two canonical coefficient
rings. `ObjectProperty.ind` uses small filtered colimits in the ambient module category.
Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ambient-ind-derived,
`sk-cor-ambient-ind-derived-triangulated.md` and its proof, steps 1--7 of the DAG node.

Proof, separately for the canonical coefficients `E` and `Q̄_ℓ`:

1. The zero module is constructible: on each affine open use the single stratum and the zero
   finitely presented scalar module (`sk-def-sfb-constructible`). Its constant diagram on the
   one-object filtered category makes it ind-constructible. Since every cohomology of the
   zero complex is zero (`def-weil-abstract-derived-category`), the derived predicate contains
   zero. An isomorphism of complexes induces isomorphisms on every cohomology object; transport
   the filtered-colimit presentation along these isomorphisms to obtain isomorphism closure.
2. For any integers `n,r`, the cohomology-shift isomorphism identifies `Hⁿ(K[r])` with
   `Hⁿ⁺ʳ(K)` (`lem-sp-derived-cohomology-shift`). Thus the predicate is stable under every
   integer shift, including both `[1]` and `[-1]`.
3. For a distinguished triangle `K → L → M → K[1]` with `K,L` in the predicate, apply the
   long exact cohomology sequence in the abelian category of module objects
   (`lem-sf-derived-homology-long-exact`, `pur713-def-module-category`). In each degree it
   gives the exact segment `Hⁿ(K) →α Hⁿ(L) →u Hⁿ(M) →v Hⁿ⁺¹(K) →β Hⁿ⁺¹(L)`.
4. Exactness identifies `ker u` with `im α`, hence `coker α` with the coimage of `u`.
   The coimage map is monic (`lem-weil-pbc-coimage-mono`) with image `ker v`. Apply the same
   result to `v` in the opposite abelian category (`def-sp-abelian`); taking opposites gives
   an epimorphism from `Hⁿ(M)` to `im v = ker β`. Its kernel is `ker v`, since the inclusion
   of `ker β` in `Hⁿ⁺¹(K)` is monic. Therefore these maps form the ambient short exact
   sequence `0 → coker α → Hⁿ(M) → ker β → 0`.
5. The four outer cohomology objects belong to `IndCons`. Fullness makes `α,β` morphisms
   between its objects. Closure under ambient kernels and cokernels
   (`det-ind-heart-kernels-cokernels`) puts `coker α` and `ker β` in `IndCons`. Closure under
   extensions (`det-ind-heart-extensions`) puts `Hⁿ(M)` there too. Since `n` was arbitrary,
   `M` satisfies the derived predicate.
6. If instead `L,M` satisfy the predicate, rotate to the distinguished triangle
   `L → M → K[1] → L[1]` (`def-weil-triangulated-category`). Steps 3--5 give `K[1]` in the
   predicate; shift by `[-1]` and use `(K[1])[-1] ≅ K` and steps 1--2 to obtain `K`.
   If `K,M` satisfy it, first shift `K` and rotate twice to
   `M → K[1] → L[1] → M[1]`. Steps 3--5 give `L[1]`; shifting back and using the shift
   isomorphism gives `L`. The rotation maps carry the usual signs, which do not change
   the vertex predicates. This proves all three cases of two-out-of-three.
7. The predicate defines a full subcategory of the ordinary triangulated derived category
   (`def-weil-abstract-derived-category`). Steps 1--6 give zero, all shifts, isomorphism
   closure and the middle-vertex condition. Apply `def-weil-triangulated-subcategory`:
   the inherited shifts and distinguished triangles make this full subcategory triangulated.

(blueprint: det-ambient-ind-derived-triangulated). -/
theorem indConstructibleDerived_isTriangulated
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    ObjectProperty.IsTriangulated (fun K : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)) ↦
      ∀ n : ℤ,
        ObjectProperty.ind.{u + 1}
          (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
          ((DerivedCategory.homologyFunctor _ n).obj K)) ∧
    ObjectProperty.IsTriangulated (fun K : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicAlgClRingObj X ℓ)) ↦
      ∀ n : ℤ,
        ObjectProperty.ind.{u + 1}
          (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
          ((DerivedCategory.homologyFunctor _ n).obj K)) := by
  sorry

/-- The ind-constructible cohomology condition is closed under ambient derived
isomorphisms for both canonical coefficient rings. This supplies the isomorphism-closure
clause separately, since Mathlib's `ObjectProperty.IsTriangulated` does not include it.
Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ambient-ind-derived/
sk-cor-ambient-ind-derived-triangulated.md, first sentence
(blueprint: det-ambient-ind-derived-triangulated).

Proof: this is the isomorphism argument in step 1 of the node's proof. Apply each
`DerivedCategory.homologyFunctor` to the given isomorphism. A filtered constructible
presentation of its source cohomology becomes a presentation of its target by composing
the cocone legs with this cohomology isomorphism. The colimit universal property is
preserved by this composition, exactly as in `ObjectProperty.ind`'s isomorphism-closure
instance. Do this for every integer degree and for each canonical coefficient ring. -/
theorem indConstructibleDerived_isClosedUnderIsomorphisms
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)) ↦
      ∀ n : ℤ,
        ObjectProperty.ind.{u + 1}
          (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
          ((DerivedCategory.homologyFunctor _ n).obj K)) ∧
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicAlgClRingObj X ℓ)) ↦
      ∀ n : ℤ,
        ObjectProperty.ind.{u + 1}
          (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
          ((DerivedCategory.homologyFunctor _ n).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale
