/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixTensorHom

/-! # Coefficient comparisons for tensor product and internal Hom

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/,
sk-prop-scalar-six-hom.md (blueprint: det-sfb-coefficient-comparisons-hom).

Both comparisons use the existing ordinary unbounded derived scalar extension on
internal modules over the pulled-back condensed coefficient rings. The internal-Hom
comparison is the evaluation mate of the canonical tensor comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- For a listed coefficient map, tensor product and internal Hom commute with
coefficient change on bounded constructible complexes of finite Tor amplitude.
The first arrow is the forward map of the canonical K-flat tensor comparison.
The second is the canonical evaluation-transpose map: scalar-extend evaluation,
use the inverse tensor comparison, and transpose. The library's left evaluation
and the blueprint's right evaluation correspond under the symmetric braiding.
Source: latest blueprint sec-smooth-purity/sk-lem-sp-tower/sk-prop-scalar-six-hom.md
(blueprint: det-sfb-coefficient-comparisons-hom).

Proof:
1. Apply clause (1) of det-prop-scalar-six-tensor-hom to the standing scheme and
listed coefficient map. Its symmetric monoidal comparison, restricted to K and M
in Dctf, is precisely scalarSixTensorIso, with the displayed forward direction.
2. Apply clause (2) of that theorem to K and M. Its evaluation-transpose comparison
is scalarSixHomComparison, so this gives the second isomorphism. The finite-ring
parenthetical in the source refers to thm-coef-finite-hom; it adds no hypothesis. -/
theorem coefficientComparisonsTensorHom (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K M : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    IsIso (scalarSixTensorIso a X.left K.obj M.obj).hom ∧
      IsIso (scalarSixHomComparison a X.left K.obj M.obj) := by
  have h := scalarSixTensorHom ell k a _ha X
  exact ⟨by infer_instance, (h.2 K M).1⟩

end AlgebraicGeometry.ProEtale.CondensedRing
