## Worker report

The module `Sheaf.RingTheory.PerfectScalarsReducednessComparison` states
`Algebra.isReduced_tensorProduct_iff_of_perfectField`, with its sole proof `sorry`.
It introduces no definitions and changes only the item's `lean` record.
The docstring gives all five DAG proof steps, including the canonical tensor
isomorphisms and both nilpotent descents. The sources read are
`literature/stacks-project/algebra.tex`, lemma-perfect-reduced (Tag 00I4,
lines 10580–10597), and `fields.tex`, lemma-common-extension-field (Tag 0H7K,
lines 394–424).

Hypotheses and clauses, matched individually:

- A field k: `(k : Type u) [Field k]`.
- Extensions E/k and F/k: `(E : Type w) (F : Type z) [Field E] [Field F]`
  and `[Algebra k E] [Algebra k F]`. These are the recorded field-extension
  encoding, with structure maps `algebraMap k E` and `algebraMap k F`.
- Both extension fields are perfect: `[PerfectField E] [PerfectField F]`.
  Mathlib's perfect-field class uses separability of irreducible polynomials.
  Its `PerfectField.ofCharZero`, `PerfectField.toPerfectRing`, and
  `PerfectRing.toPerfectField` identify this with the node's characteristic-zero
  or surjective-Frobenius description. No prime or characteristic is fixed.
- An arbitrary commutative k-algebra A: `(A : Type v) [CommRing A] [Algebra k A]`.
  There is no reducedness, finite-generation, domain, or nontriviality assumption.
- The algebra tensor product and the stated multiplication are Mathlib's existing
  `TensorProduct k A E` and `TensorProduct k A F`, with their
  `Algebra.TensorProduct.instCommRing` instances. The multiplication is exactly
  `Algebra.TensorProduct.tmul_mul_tmul`: `(a ⊗ e) * (b ⊗ e') = (a*b) ⊗ (e*e')`.
- Both implications of the reducedness comparison are the conclusion
  `IsReduced (A ⊗[k] E) ↔ IsReduced (A ⊗[k] F)`.
  `IsReduced.eq_zero` says that every nilpotent element is zero. Its definition
  allows exponent zero, which is equivalent to the node's positive-exponent
  definition: exponent zero can annihilate an element only in the zero ring,
  where all elements are zero already.
- No embedding E → F or F → E, algebraicity, or perfectness of k is assumed.
  The four explicitly declared universes are independent; no size equality is imposed.

Statement dependencies, read at their recorded declarations:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` (line 95)
  and `RingHom.toAlgebra` (line 197). The fields plus their algebra structures
  supply exactly the recorded notion.
- `def-weil-pbc-module-tensor-product`: its mathlib_match is `TensorProduct`
  in `Mathlib.LinearAlgebra.TensorProduct.Defs` (line 81), not a missing Lean record.
  Read also `TensorProduct.mk` (Defs:376), `TensorProduct.lift`, `lift.tmul`,
  `TensorProduct.ext'` (Basic:123–139), and `LinearMap.rTensor`/`rTensor_tmul`
  (Map:331–346). The statement uses this tensor product, with the standard
  algebra multiplication from `Mathlib.RingTheory.TensorProduct.Basic`.

Proof dependencies are imported without `public` when they are not already
statement imports:

- `WeilConjectures.FieldTheory.CommonExtensionFields`:
  `Field.exists_common_extension`, allowing arbitrary field extensions and universes.
- `Mathlib.RingTheory.TensorProduct.Maps`:
  `Algebra.TensorProduct.cancelBaseChange` and its two pure-tensor formulas;
  `Algebra.TensorProduct.productMap`, `productMap_apply_tmul`, and `ext` from
  Basic/Maps implement the recorded pushout algebra structure.
- `Mathlib.RingTheory.Flat.Basic`:
  `Algebra.TensorProduct.includeLeft_injective`, requiring only flatness of the
  left algebra and injectivity of the field structure map, not nonzeroness of A.
- `WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced`:
  `isReduced_tensorProduct_of_perfectField`, with arbitrary reduced algebras.
- The module tensor-product definition is already a public statement import.

Edge cases checked mathematically before writing:

- A = 0: both tensor products are zero rings and reduced. The binders admit this.
- A = k[epsilon]/(epsilon^2): the nonzero nilpotent remains nonzero under either
  field extension by scalar-extension injectivity, so both sides are false.
- E = F: the conclusion specializes to the identical proposition on both sides.
- Characteristic zero: all extension fields are perfect; no characteristic-zero
  binder was added, so positive characteristic is also included.
- Imperfect k, e.g. F_p(t), and A = k(t^(1/p)): after extension to a perfect
  field the inseparable polynomial acquires a repeated root; both tensors
  are nonreduced. Thus the statement does not incorrectly reduce to reducedness of A.
- Transcendental extensions and infinitely generated A: none of the binders adds
  algebraicity or finite generation; the common-overfield and ascent/descent proof
  remains valid. Tensor products accommodate all four independent universes.

Searches actually run via the prescribed msearch.py wrapper on 2026-10-24:

- LeanFinder: “For a commutative k algebra A and perfect field extensions E F of k,
  A tensor E is reduced if and only if A tensor F is reduced”. Eight hits,
  principally `Algebra.isGeometricallyReduced_iff`, the algebraic-closure test,
  and the reducedness instance requiring an algebraic field extension. No exact match.
- Loogle: `IsReduced, TensorProduct`. Six hits, including the geometric-reducedness
  characterization, an algebraic-extension instance, and
  `IsReduced.tensorProduct_of_flat_of_forall_fg`. None compares two arbitrary perfect fields.
- Grep (Mathlib RingTheory):
  `[Rr]educed.*[Pp]erfect|[Pp]erfect.*[Rr]educed|isReduced.*tensorProduct|tensorProduct.*isReduced`.
  Six hits in Flat/Basic and Nilpotent/GeometricallyReduced. Read the latter's
  full field section; its results are not this comparison.
- LeanSearch: “Reducedness of a commutative algebra after extension of scalars to
  either of two perfect fields is equivalent”. Eight hits about geometric
  reducedness and algebraic-closure scalar extension; no exact match.
- Local `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `perfect.*[Rr]educed|[Rr]educed.*perfect|perfect_scalars|perfectScalars`
  finds the existing perfect-base reduced-tensor theorem and geometric reducedness
  statements, not this comparison. The exact item-id grep over WeilConjectures
  finds no declaration. Exact-name `rg` over both libraries, Mathlib and
  `dag/lean_names_upstream.json` finds no existing
  `isReduced_tensorProduct_iff_of_perfectField` declaration.

No statement correction, dependency repair, new node, or STATEMENT-DISPUTED issue.

## Second reading by Q23

A separate rereading by the same dispatcher worker (the task forbids starting
other agents) compared the node JSON and final module. Independent maintainer
review remains separate from this self-check. Every binder matches the listed
hypotheses above: three fields, one arbitrary commutative ring, three k-algebra
structures, and perfectness of E and F only. The conclusion uses A as the left
tensor factor on both sides, the same base k, and the same IsReduced predicate.
The biconditional preserves both directions. In particular the zero algebra,
imperfect base field, nonalgebraic extensions, and unequal universes are not
excluded. The tensor ring structure is canonical, not an arbitrary multiplication.
The docstring includes every cited proof dependency and both explicit nilpotent
descents. No mismatch was found, so no statement or dependency edits were made.
