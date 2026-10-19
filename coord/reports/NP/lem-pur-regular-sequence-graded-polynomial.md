## Worker report

The module `Sheaf.RingTheory.RegularSequenceGradedPolynomial` constructs
`Ideal.regularSequenceGradedPolynomialMap` by `MvPolynomial.aeval` and states
`Ideal.regularSequence_gradedPolynomial` with one `sorry`. Its statement is unchanged.
There are no new nodes and no dependency repairs. The previous attempt left no delivery
files; this delivery supplies the missing module, node copy and report.

Hypothesis and clause correspondence:

- A commutative ring is `{R : Type u} [CommRing R]`, with arbitrary explicitly bound universe.
- The finite sequence of length c is `{c : ℕ} (f : Fin c → R)`. Its order is the increasing
  order on `Fin c`; regularity is exactly
  `hf : RingTheory.Sequence.IsRegular R (List.ofFn f)`, the recorded dependency definition.
  No reordering or additional Noetherian, local, domain or field hypothesis is imposed.
- J is written directly as `Ideal.span (Set.range f)` everywhere; B is the quotient
  `R ⧸ Ideal.span (Set.range f)`. No ideal or quotient structure is chosen independently.
- The associated graded algebra is the recorded `Ideal.associatedGraded J`, with its
  existing `CommRing` and `Algebra (R ⧸ J)` instances. Its degree n piece is the recorded
  `Ideal.associatedGradedPiece J n`, and the inclusion is `DirectSum.of ... n`.
- The source is `MvPolynomial (Fin c) B`; `MvPolynomial.IsHomogeneous p n` is Mathlib's
  total-degree grading, including the zero polynomial in every degree.
- The canonical B-algebra map theta is the actual definition
  `regularSequenceGradedPolynomialMap f`. Evaluation sends each `X j` to
  `DirectSum.of ... 1 (Submodule.Quotient.mk ⟨f j, ...⟩)`. Its membership proof uses
  `Ideal.subset_span`, not a postponed theorem or a choice of generators. Since evaluation
  is a B-algebra homomorphism and the existing algebra structure is the degree-zero
  inclusion, it is the identity on B in degree zero. Polynomial algebra extensionality
  (`MvPolynomial.algHom_ext`) characterizes this map uniquely.
- Being an algebra isomorphism is `Function.Bijective` of this B-algebra homomorphism.
  The second conjunct says, for every n and polynomial p, that `p.IsHomogeneous n` iff its
  image equals the inclusion of an element of the exact piece `J^n/J^(n+1)`. Together
  with bijectivity this says both the map and its inverse preserve each degree.
- The displayed formula is the third conjunct. A finitely supported family
  `a : {α : Fin c →₀ ℕ // α.sum (fun _ k ↦ k) = n} →₀ R` supplies all coefficient lifts.
  The existential x is an element of the actual ideal power, whose underlying value is
  `a.sum (fun α r ↦ r * α.val.prod (fun j k ↦ f j ^ k))`. The second equality sends the
  polynomial with quotient coefficients to precisely the class of this representative
  in degree n. The existence of x asserts membership in the ideal power rather than
  adding a membership hypothesis. Every homogeneous polynomial over B has such lifts,
  since its support is finite and `Ideal.Quotient.mk J` is surjective.
- The final conjunct is exactly the unique finite expansion definition of a basis in
  `def-weil-pbc-free-module`: for each element x of the actual degree-n quotient there
  exists exactly one finitely supported B-coefficient family a whose monomial expansion
  equals x. Equality is tested after the injective canonical `DirectSum.of` inclusion,
  and scalars act through the recorded B-algebra structure. The preceding formula makes
  these monomials exactly the classes of the products of the f_j. This uses the node's
  basis criterion without defining another action on the quotient pieces, and it
  retains the prescribed monomial basis, rather than merely asserting freeness.

Dependency declarations read and used:

- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`, extending
  `IsWeaklyRegular` with the nonzero final-quotient condition; its full signature and
  docstring were read. `List.ofFn` packages the ordered sequence without changing it.
- `Mathlib.Algebra.Algebra.Hom` and `Mathlib.RingTheory.Ideal.Quotient.Operations`:
  `AlgHom`, `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`, and `Ideal.Quotient.mk`;
  algebra homomorphisms and quotient-algebra structures agree with their recorded match.
- `Sheaf.RingTheory.AssociatedGradedRing`: `Ideal.associatedGradedPiece`,
  `Ideal.associatedGraded`, `Ideal.associatedGradedAlgebra`, and `DirectSum.of` for its
  homogeneous inclusions. The complete source was read, including its multiplication
  and scalar formulas. This is imported publicly.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `MvPolynomial.aeval`,
  `MvPolynomial.monomial` and `MvPolynomial.algHom_ext`; their signatures and relevant
  docstrings were read. The homogeneous module import exposes these.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free` and the underlying
  `Module.Basis` notion, read in their sources; the statement uses the finite unique
  coefficient characterization expressly permitted in the dependency's statement.
- The stated proof dependency `Sheaf.RingTheory.AssociatedGradedRingStructure`,
  `Ideal.associatedGraded_ring_structure`, is imported without `public`. Its full
  signature and docstring were read. All other proof dependencies are statement
  dependencies covered above.

Edge cases checked before writing:

- c = 0: J = 0, the map is the constant-ring identification in degree zero. There is one
  empty multi-index of degree zero and none of positive degree. The latter case gives
  the unique empty expansion of the zero positive-degree piece.
- n = 0 at any length: the sole multi-index is zero; the coefficient formula is the
  degree-zero quotient inclusion, and the basis is the singleton class of 1.
- The zero polynomial belongs to every homogeneous degree, and its image is zero in
  each corresponding summand, as required by the degree equivalence.
- The zero ring and an ideal equal to the unit ideal are excluded exactly when regularity
  excludes them through the nonzero final quotient; no extra nontriviality is added.
- Arbitrary characteristic, non-Noetherian rings, and ordered nonpermutable regular
  sequences remain covered. Coefficient families are finitely supported, so no infinite
  sums or finiteness assumptions on R are introduced.

Searches made on 2026-10-16:

- `msearch.py leanfinder`: "The associated graded algebra of an ideal generated by a
  regular sequence is a polynomial algebra over the quotient ring". Eight hits:
  `Ideal.span_pow_eq_map_homogeneousSubmodule`, `adjoin_monomial_eq_reesAlgebra`, regular
  sequence component lemmas, and homogeneous-localization lemmas. None asserts the
  required coefficient independence or the polynomial isomorphism.
- `msearch.py loogle`: `RingTheory.Sequence.IsRegular, MvPolynomial`: zero hits.
- `msearch.py grep`: `associated.?graded|quasi.?regular` in `RingTheory/Regular`: the
  TODO in `RegularSequence.lean:21`, which lists quasi-regular sequences as missing.
- `msearch.py leansearch`: "The associated graded algebra of a regular sequence ideal
  is a polynomial algebra": service returned Internal Server Error; recorded unavailable.
- `rg` over the upstream `WeilConjectures` tree for `associatedGraded|gradedPolynomial|
  quasi.?regular|normal.?cone|conormal` and the node id found no matching theorem.
  The required id search and the new declaration-name search also found no duplicate.
- `rg` over `lean/Sheaf` found the associated graded definition and structure modules,
  associated-graded finite-type and completion results, and unrelated conormal modules;
  none states this regular-sequence polynomial theorem.
- `dag/lean_names_upstream.json` contains neither proposed declaration name.

Source check: the local `literature/stacks-project/algebra.tex` is absent, so the source
was read directly at [Stacks 00LN](https://stacks.math.columbia.edu/tag/00LN), part (1),
with [061N](https://stacks.math.columbia.edu/tag/061N) and
[061P](https://stacks.math.columbia.edu/tag/061P). These give precisely the map and
regular-to-quasi-regular conclusion in the node. No statement fault or dispute was found.

Validation: the module is checked only through the prescribed `scompile.py`; the
`deliver2.py --no-push` result is recorded after the dry run. No proof is supplied for
the main theorem; the map has genuine evaluation data.

## Second reading by NP

I read the current node, its Stacks source (00LN(1), 061N, 061P), and the complete
Lean file independently. The item-by-item rendering is as follows.

- The commutative ring and its universe are `{R : Type u} [CommRing R]`; this is
  exactly the node's arbitrary commutative ring, with no Noetherian, local, domain,
  field, or characteristic assumption.
- The finite ordered sequence is `{c : ℕ} (f : Fin c → R)`, and its hypothesis is
  exactly `hf : RingTheory.Sequence.IsRegular R (List.ofFn f)`. `List.ofFn` preserves
  the increasing `Fin c` order used by the source; no permutation is assumed.
- The ideal and quotient are definitionally `Ideal.span (Set.range f)` and
  `R ⧸ Ideal.span (Set.range f)` everywhere in the statement. No independently
  chosen ideal or quotient occurs.
- The target is the recorded `associatedGraded` and its degree piece is
  `associatedGradedPiece`; `DirectSum.of ... n` is the canonical homogeneous
  inclusion. The imported `Ideal.associatedGradedAlgebra` and the structure theorem
  provide the stated quotient-algebra structure.
- `regularSequenceGradedPolynomialMap` is the canonical quotient-algebra map
  `MvPolynomial.aeval`, sending `j` to the degree-one class of `f j`. Its type is an
  `AlgHom` over the quotient ring, so it fixes quotient coefficients in degree zero,
  as required by the node's identity-on-constants clause. The map is characterized
  by evaluation and polynomial extensionality, not by a choice.
- The first conclusion conjunct is `Function.Bijective` of this map, matching the
  isomorphism assertion. The second is the exact degree condition: for every `n`
  and polynomial `p`, `p.IsHomogeneous n` iff its image is `DirectSum.of` of an
  element of the exact `associatedGradedPiece ... n`.
- The third conjunct quantifies every finitely supported coefficient family on the
  exact-degree multi-indices. It supplies `x : (J ^ n : Ideal R)`, identifies its
  underlying value with the lifted monomial sum, and identifies the evaluated
  quotient-coefficient polynomial with `Submodule.Quotient.mk x` in degree `n`.
  This is precisely the displayed Stacks formula, including arbitrary coefficient
  lifts and its degree requirement.
- The final conjunct says that every degree-`n` target element has a unique finite
  family of quotient coefficients whose monomial images sum to it. This is exactly
  the node's degree-`n` monomial basis criterion, including the scalar action through
  the quotient algebra.

I checked the edge cases directly against these binders and terms. For `c = 0`, the
range ideal is zero and the only degree-zero multi-index is the empty one; positive
degrees have empty index support and the corresponding piece is zero. For `n = 0`,
the empty multi-index gives the singleton constant basis. The zero polynomial is
homogeneous in every degree and maps to zero in every summand. The regularity
hypothesis excludes exactly the zero final quotient, as in the source, while allowing
arbitrary characteristic and non-Noetherian rings. No independent or undersized
universe is introduced.

I repeated the existing-definition searches: `msearch.py` LeanFinder and LeanSearch
queries for the regular-sequence associated-graded polynomial theorem, Loogle queries
for `RingTheory.Sequence.IsRegular` with `MvPolynomial`, and `rg` over Mathlib,
`WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`. They found only
the generic associated-graded and regular-sequence infrastructure (and Mathlib's
quasi-regular TODO), with no declaration of this map or theorem. The recorded
dependency declarations were opened: `RingTheory.Sequence.IsRegular`,
`Ideal.associatedGraded`/`associatedGradedPiece`,
`Ideal.associatedGraded_ring_structure`, `MvPolynomial.aeval` and
`MvPolynomial.algHom_ext`, and `Module.Free`. Each supplies the notion used here;
there are no new nodes or dependency repairs.

No mismatch was found, so no Lean or node statement was changed. The module was
recompiled with the required `scompile.py` wrapper and completed without errors or
warnings other than the permitted theorem `sorry`.
