## Worker report

The module `Sheaf.RingTheory.HomogeneousMaximalGradedFieldQuotient` states
`Ideal.exists_homogeneous_maximal_gradedField_quotient`, with its single proof `sorry`.
It introduces no definition and changes only the item's `lean` field. No statement
correction, missing dependency interface, new node, or statement dispute was found.

Source read: Stacks `algebra.tex`, Tag 00JM, `section-proj`, opening paragraph
(lines 13365 onward), for componentwise homogeneity, and
`coord/reports/Q112/lem-sfb-graded-stabilizer-strong-products.md`, section
"Complete proof retained for the new node", for the independent group-graded argument.
The module docstring distinguishes that auxiliary argument from Stacks' convention.
The theorem docstring includes all five proof steps: chain bounds (including the
empty chain), Zorn maximality, the quotient grading and nonzero quotient, the
homogeneous ideal H+(a), and degree-zero extraction of the inverse.

Hypothesis and clause correspondence:

- Abelian grading group M: `{M : Type u} [AddCommGroup M]`, with no order,
  finiteness or torsion-freeness assumption.
- Commutative unital ring A: `{A : Type v} [CommRing A]`. The independent universes
  u and v allow all sizes of grading groups and rings.
- Additive subgroups A_n: `(𝒜 : M → AddSubgroup A)`.
- Unique finite homogeneous expansion, unit in degree zero, and multiplication
  into summed degrees: `[GradedRing 𝒜]`. Its `DirectSum.Decomposition` parent
  gives the inverse to the canonical finite-sum map, and its
  `SetLike.GradedMonoid` parent gives the unit and multiplication conditions.
  `open Classical in` supplies decidable equality internally; no decidability
  hypothesis restricts M.
- L an ideal: `(L : Ideal A)`; componentwise homogeneity:
  `(hL : L.IsHomogeneous 𝒜)`; properness: `(hL_proper : L ≠ ⊤)`.
- Existence of the containing ideal: `∃ H : Ideal A, L ≤ H ∧ ...`.
- H proper and homogeneous: `H ≠ ⊤ ∧ H.IsHomogeneous 𝒜`.
- Maximal among proper homogeneous ideals:
  `∀ J : Ideal A, H ≤ J → J ≠ ⊤ → J.IsHomogeneous 𝒜 → J = H`.
  J need not have a separately stated condition containing L: H already does.
- Actual quotient D=A/H and canonical q: `A ⧸ H` and `Ideal.Quotient.mk H`.
  There is no arbitrary ring or arbitrary quotient map parameter.
- Nonzero quotient: `Nontrivial (A ⧸ H)`.
- The degree-n quotient subgroup is exactly q(A_n):
  `(𝒜 n).map (Ideal.Quotient.mk H).toAddMonoidHom`.
  `Nonempty (GradedRing (fun n : M ↦ ...))` asserts these actual image subgroups
  form a grading, including directness, finite expansions, unit, and products.
  `GradedRing` carries decomposition data and is therefore a type; `Nonempty`
  expresses existence of that grading. The decomposition is uniquely determined
  by the inverse to the fixed finite-sum map, as Mathlib's
  `DirectSum.Decomposition` docstring and subsingleton instance record.
- Every nonzero homogeneous element: `∀ (n : M) (d : A ⧸ H), d ∈ ... → d ≠ 0 → ...`.
- Opposite-degree inverse with the stated product:
  `∃ e : A ⧸ H, e ∈ (𝒜 (-n)).map ... ∧ d * e = 1`.
  No assertion that every nonzero element of the whole quotient is invertible,
  or that H is an ordinary maximal or prime ideal, has been added.

Dependency declarations read and used:

- `def-weil-pbc-algebra-hom-quotient` is a Mathlib leaf, without a `lean` record.
  Its `mathlib_match` records `AlgHom`, `Ideal.Quotient.algebra`, and
  `Ideal.Quotient.mkₐ`, in `Mathlib.Algebra.Algebra.Hom` and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`. I read their full signatures
  and docstrings. The item concerns an unadorned commutative ring, so uses the
  underlying canonical ring quotient `A ⧸ H` and `Ideal.Quotient.mk H`, whose
  full definition and quotient-map docstring were read in
  `Mathlib.RingTheory.Ideal.Quotient.Defs`. The recorded
  `Ideal.Quotient.mkₐ_toRingHom` says precisely that the underlying ring map of
  `mkₐ` is `mk`. The recorded quotient dependency is usable unchanged.
- `GradedRing` in `Mathlib.RingTheory.GradedAlgebra.Basic` and
  `DirectSum.Decomposition` in `Mathlib.Algebra.DirectSum.Decomposition`.
- `Ideal.IsHomogeneous` in
  `Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal`; its componentwise
  definition and `mem_iff` were read.
- `AddSubgroup.map` in `Mathlib.Algebra.Group.Subgroup.Map` for actual images.
- Proof dependency `lem-weil-pbc-zorn-lemma`: Mathlib leaf `zorn_subset`, whose
  signature was read in `Mathlib.Order.Zorn`. That module is imported privately
  as a proof dependency; the statement dependencies are public imports.

Edge cases checked before writing and during rereading:

- Zero ring A: it has no proper ideal, so the hypotheses cannot hold; no
  `Nontrivial A` assumption is added.
- Trivial grading group M: the statement reduces to an ordinary maximal quotient
  field, including the n=0 inverse assertion.
- Any n, including n=0: the inverse lies in degree -n, which is degree zero for n=0.
- Torsion grading groups: translation is still injective. The group algebra
  F_2[C_2] with its C_2 grading has invertible nonzero homogeneous elements but
  can have nonhomogeneous nilpotents. The statement correctly permits H=0 and
  makes no domain or ordinary-field assertion.
- Laurent polynomials k[t,t^-1] with their Z-grading: H=0 is homogeneous maximal
  but not an ordinary maximal ideal; the conclusion is the graded inverse
  condition, not `Field (A ⧸ H)`.
- Empty chain in the retained proof: L is its upper bound. A group is nonempty,
  so there is no excluded empty grading index case.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder` query "Every proper homogeneous ideal in an abelian
  group graded commutative ring is contained in a maximal homogeneous ideal with
  graded field quotient": 8 hits, including homogeneous-ideal lattice operations
  and `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem`; no exact theorem.
  The prime criterion also requires an ordered grading and does not give this
  group-graded conclusion.
- `msearch.py ... loogle` query `"HomogeneousIdeal", "maximal"`: OK, 0 hits.
- `msearch.py ... grep` query
  `homogeneous.*maximal|maximal.*homogeneous|graded.?field|graded.?division`:
  OK, 0 hits.
- `msearch.py ... leansearch` query "Every proper homogeneous ideal of an abelian
  group graded commutative ring admits a graded field quotient": 8 hits,
  homogeneous ideals, hulls, and a radical criterion; no exact statement.
- `rg -n` with the homogeneous-maximal/graded-field/graded-division patterns and
  the item id across `lean/WeilConjectures` and `lean/Sheaf`: no upstream theorem
  for this item. The Sheaf hits concerned local-attraction regularity and
  unrelated homogeneous relations, not this existence and inverse assertion.
  The item-id part of this search likewise found no declaration.
- `rg` in `dag/lean_names_upstream.json` for graded quotient names found spectral
  sequence quotient entries only. Reading Mathlib's graded algebra files found
  the existing notions used here, but no maximal homogeneous quotient theorem.
- The already existing `Sheaf.RingTheory.CoordinateQuotientGrading` was also read:
  it constructs gradings for homogeneous polynomial coordinate quotients over a
  field, not arbitrary abelian-group-graded commutative rings.

Validation: the prescribed `scompile.py` compiled the module in sandbox and
library mode against the published live build, with no errors or non-sorry
warnings (7.2 s and 4.3 s respectively). The delivery dry run is recorded below.

## Second reading by Q41

This is the assigned worker's separate rereading of the node and module; no
independent sub-agent was started, as required by the dispatch brief. The
maintainer supplies the independent delivery review.

I reopened the source's retained Zorn argument and compared the node's clauses
against the theorem signature. The input `[GradedRing 𝒜]` gives exactly the
finite unique decompositions and product/unit conditions; `IsHomogeneous`
means closure under all components. Properness is required of both L and H,
and the J quantifier expresses maximality only among proper homogeneous ideals.
The quotient is the actual `A ⧸ H`; its subgroups are the actual images of 𝒜 n,
and `Nonempty (GradedRing ...)` includes the uniqueness of the quotient
expansion, not only a spanning assertion. The inverse conclusion quantifies
all n and all nonzero d in those images and gives e in the -n image with d*e=1.
There is no order, field, Noetherian, or torsion-free hypothesis. All variables
and universes are explicitly bound, and `autoImplicit` is false. No mismatch
was found and no statement or signature change was needed after the first compile.

Delivery validation: `deliver2.py Q41 lem-sfb-homogeneous-maximal-graded-field-quotient
--no-push` printed `OK (dry run): commit fca1c11db5a passes the preflight and compiles;
nothing pushed`. An exact-name search in Mathlib, WeilConjectures, Sheaf, and
`dag/lean_names_upstream.json`, and the prescribed recursive item-id grep in
WeilConjectures, both returned no declaration. No module or node repair was needed.
