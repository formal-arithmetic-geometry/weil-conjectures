## Worker report

The module `Sheaf.RingTheory.GradedStabilizerStrongProducts` states
`GradedRing.exists_sum_mul_eq_one_of_stabilizer_eq_augmentation` with one `sorry` proof.
It introduces no definitions or helper theorems. The natural-language statement, dependency
lists and proof of the DAG node are unchanged. Its docstring retains all five proof steps.

The source read was Stacks Project, `groupoids.tex`, Tag 0EKK,
`lemma-complete-reducibility-Gm`, including its coefficient-decomposition proof. As the node
explicitly says, that tag supplies the grading interpretation, not the augmentation-ideal
implication. I also read the complete independent argument in the Q112 stage-1 report
for this item and the current five-step DAG proof. The attribution in the module preserves
that distinction; it does not claim this auxiliary is a verbatim Stacks result.

Hypothesis and clause correspondence:

- The arbitrary additive abelian group is `{M : Type u} [AddCommGroup M]`.
  The independent coefficient-ring universe is `{A : Type v} [CommRing A]`.
  There is no nonzero, characteristic, finite generation, torsion-free, reduced or
  Noetherian assumption. `[DecidableEq M]` supplies the computational equality parameter
  of Mathlib's grading API, exactly as in the recorded proof dependency. Classical equality
  supplies it for any group, so it imposes no mathematical restriction.
- The additive subgroups are `𝒜 : M → AddSubgroup A`. The unique finite homogeneous
  decomposition, unit in degree zero, and multiplication of degree m and n into degree
  m+n are exactly `[GradedRing 𝒜]`: this extends `DirectSum.Decomposition 𝒜` and
  `SetLike.GradedMonoid 𝒜`.
- The formal group ring is `AddMonoidAlgebra A M`, Mathlib's finite coefficient functions
  with convolution multiplication. The symbol t^m is `AddMonoidAlgebra.single m 1`.
  The coefficient a is embedded as `AddMonoidAlgebra.single 0 (a : A)`.
  This formal exponent zero is independent of the degree m of the coefficient a.
- The first ideal is `Ideal.span {x : AddMonoidAlgebra A M | ∃ (m : M) (a : 𝒜 m),
  x = AddMonoidAlgebra.single 0 (a : A) * (AddMonoidAlgebra.single m 1 - 1)}`.
  Subtype membership of a is precisely the requirement a belongs to A_m.
- The second ideal is `Ideal.span (Set.range (fun m : M ↦
  (AddMonoidAlgebra.single m 1 - 1 : AddMonoidAlgebra A M)))`.
  The equality assumption is the binder `hIdeals`.
- The conclusion quantifies `∀ m : M`, followed by a finite length `n : ℕ`,
  `a : Fin n → 𝒜 m`, and `b : Fin n → 𝒜 (-m)`.
  The final equation `∑ j : Fin n, (a j : A) * (b j : A) = 1` is the requested sum
  in A. Every finite family can be indexed by some `Fin n`; `n = 0` is allowed.

Dependencies and interfaces read:

- `def-weil-pbc-algebra-hom-quotient` is a Mathlib leaf, with no Lean record required.
  Its recorded `AlgHom` in `Mathlib.Algebra.Algebra.Hom` and `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ`, surjectivity and kernel declarations in
  `Mathlib.RingTheory.Ideal.Quotient.Operations` were opened. The statement uses the
  same Mathlib `Ideal` notion and its generated ideal `Ideal.span` from
  `Mathlib.RingTheory.Ideal.Span`. The quotient module is imported without `public`
  for the quotient and kernel argument of the recorded proof.
- The proof dependency `lem-sfb-homogeneous-maximal-graded-field-quotient` is imported
  without `public` from `Sheaf.RingTheory.HomogeneousMaximalGradedFieldQuotient`.
  Its full current server source was read using `scompile.py --source`, since the local
  source checkout did not yet contain it. Its recorded theorem
  `Ideal.exists_homogeneous_maximal_gradedField_quotient` applies to the same arbitrary
  additive abelian-group grading, gives a proper homogeneous H above L, a nonzero
  quotient with the image grading, and inverses in opposite degrees. This is exactly
  what proof steps 2, 3 and 5 use.
- Public imports provide only the statement's monoid algebra, grading, and generated
  ideal notions. No dependency was replaced by a private definition.

Edge cases checked mathematically before drafting:

- For the zero ring, `n = 0` gives the empty family and sum 0 = 1. No `Nontrivial A`
  assumption excludes it.
- For m = 0, the single pair a = b = 1 works. For the trivial group this is every degree.
- For a nontrivial group with the trivial grading over a nonzero ring, I is zero and J
  is nonzero: coefficients distinguish t^m from 1 for m nonzero. Thus the equality
  hypothesis correctly fails when the opposite components vanish.
- A Laurent ring with its usual integer grading has the pair t^m and t^(-m), giving 1.
  A polynomial ring with its usual integer grading does not satisfy the ideal equality;
  the missing negative-degree units are not silently assumed.
- Torsion groups and positive characteristic are retained. For example the canonical
  C2 grading of k[C2] has homogeneous units even in characteristic 2; neither the
  statement nor the quotient proof assumes that the quotient is a domain.
- The group and coefficient ring have independent universes u and v. There is no
  restriction on the cardinality of the group or on the length of a witness family.

Searches actually run, through the prescribed `msearch.py` wrapper with this group and item:

- LeanFinder: "In an abelian group graded commutative ring equality of the ideal generated
  by homogeneous coefficients times t^m minus one and the augmentation ideal implies finite
  sums of products of degrees m and -m equal one". Eight hits concerned homogeneous
  localization, irrelevant ideals and finite-type homogeneous algebra generators; none
  has the ideal-equality hypothesis or this conclusion.
- Loogle: `GradedRing, AddMonoidAlgebra, Ideal.span`. Zero hits.
- Mathlib grep: `strongly.?graded|strongGrading|stabilizerIdeal|augmentationIdeal`.
  Zero hits returned by the wrapper.
- LeanSearch: "The ideal generated by homogeneous elements a times t^m minus one equals
  the augmentation ideal only if each opposite graded component pair generates one".
  Eight hits were `Ideal.homogeneousCore'`, `Ideal.homogeneous_span`,
  `Ideal.homogeneousCore`, `Ideal.IsHomogeneous.mem_iff`,
  `Ideal.isHomogeneous_iff_forall_subset`, `Ideal.IsHomogeneous.iff_exists`,
  `HomogeneousIdeal`, and `Ideal.IsHomogeneous.iff_eq`. These concern homogeneous
  ideals rather than the implication here. The query and result names are retained
  in the sandbox search log.
- Direct `rg` over both `lean/WeilConjectures` and `lean/Sheaf` with the preceding pattern
  and `graded.stabilizer` found only unrelated relative Hopf and polynomial augmentation
  constructions and the affine split-torus consumer's proof docstring. The mandatory
  item-id grep of `lean/WeilConjectures` found no declaration. A search in
  `dag/lean_names_upstream.json` found no attachment for this item.
- Direct searches for `GradedStabilizer` and
  `exists_sum_mul_eq_one_of_stabilizer` across Mathlib and both project source trees
  found no existing declaration. The selected full declaration name is fresh.

No statement correction, new node, dependency repair or statement dispute was needed.
The only postponed theorem is the main theorem, whose source and full proof are in its
docstring and whose DAG node is this item. All writes are confined to the assigned sandbox;
compilation and delivery use only the prescribed wrappers.

## Validation

The prescribed `scompile.py` compiled the sandbox and library module separately against
the live published library. Both passed, with no errors or non-sorry warnings.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
