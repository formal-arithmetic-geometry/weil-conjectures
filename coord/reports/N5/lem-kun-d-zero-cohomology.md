## Worker report

Existing declaration: `DerivedCategory.isZero_iff`, in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
(lines 26–37, including the ambient variables and docstring). No new Lean module is
needed. The base already records this same declaration; this delivery independently
checks it and updates only the lean record, leaving the mathematical node unchanged.
The current server source was read with `scompile.py --source` and agrees with the
local upstream source.

Source checked: the blueprint node
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-d-zero-cohomology.md`,
order 1701, read from the server because literature is not checked out locally.
Its statement and proof agree verbatim with the DAG node.

Hypothesis and clause correspondence:

- `E ∈ D(T_et)` is `(K : DerivedCategory C)` specialized to
  `C := Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1}`, `K := E`.
  This is the unqualified D(T_et) specified in
  `def-weil-pbc-derived-categories`, not the category with arbitrary ring coefficients.
- `E = 0` is `CategoryTheory.Limits.IsZero K`, categorical vanishing (isomorphism
  to a zero object), rather than literal equality to a chosen representative.
- “if and only if” is `↔`; both implications are present.
- `H^q(E) = 0 for all q` is
  `∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor C n).obj K)`.
  Mathlib's functor is defined on cochain complexes with shape `ComplexShape.up ℤ`,
  so its homology in degree n is precisely the paper's cohomology sheaf H^n.

The full ambient signature binds `{C : Type u}`, `[Category.{v} C]`, `[Abelian C]`,
`[HasDerivedCategory.{w} C]`, with explicit universes `w v u`. These express the
infrastructure of D(C); they impose no geometric or boundedness hypothesis on T or E.
The existing-declaration rule permits this direct specialization of a generic theorem.

There are no statement dependencies on the node. Its sole proof dependency is
`def-weil-pbc-derived-categories`: read the recorded module
`Sheaf.AlgebraicGeometry.DerivedCategories`, including its module docstring identifying
D(T_et), H^i, D^+, and D^b, and its recorded main definition
`AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`. The torsion predicate
is not used by this lemma. The relevant existing declarations are `DerivedCategory`
and `DerivedCategory.homologyFunctor`, from Mathlib's derived-category Basic and
HomologySequence modules. The latter's full signature and cochain-complex factorization
were read. The ring-coefficient abbreviation `AlgebraicGeometry.Etale.DerivedCategoryModule`
in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` was also checked to distinguish
it from the abelian-sheaf specialization required here.

Proof correspondence: the upstream theorem maps a zero object through each homology
functor for the forward implication. Conversely, all homology objects being zero makes
`K ⟶ 0` a quasi-isomorphism, hence an isomorphism by `DerivedCategory.isIso_iff`;
therefore K is zero. This is the blueprint's acyclic-object localization argument.
The existing proof is reused; nothing is proved or restated in this delivery.

Edge cases checked: E already zero; nonzero sheaves concentrated in any integer degree;
negative degrees and degree zero; unbounded complexes; the empty scheme. The universal
integer quantifier omits no degree, and no torsion, finiteness, nonemptiness, characteristic,
or boundedness condition is added. Distinct object, morphism, and localization universes
remain available in the generic theorem.

Searches made:

- LeanFinder via msearch.py: “An object in a derived category is zero if and only if
  all its cohomology objects vanish”. Eight hits, including `DerivedCategory.isLE_iff`,
  `isGE_iff` and `HomotopyCategory.mem_subcategoryAcyclic_iff`; none is the exact theorem.
- Loogle via msearch.py: `DerivedCategory.isZero_iff`. Zero hits, unknown identifier
  (the search index is Mathlib; the exact theorem is in the project's upstream extension).
- Mathlib grep via msearch.py: `isZero_iff|isZero_of_forall_isZero_homology` in
  `Algebra/Homology/DerivedCategory`. Two generic isomorphism-vanishing uses in TStructure;
  no exact object-level criterion there.
- LeanSearch via msearch.py: “An object of the derived category is zero if and only if
  every homology object is zero”. Service unavailable: Internal Server Error.
- Upstream rg: `isZero_iff|isZero_of_forall_isZero_homology|lem-kun-d-zero-cohomology`
  in the derived-category directory found the exact theorem in HomologySequence,
  its corollary, and a use in ExactFunctor. Full signature, docstring and proof inspected.
- Side-library rg: `DerivedCategory\.isZero_iff|lem-kun-d-zero-cohomology` in lean/Sheaf:
  no duplicate declaration or node-tagged statement.
- Upstream declaration-name inventory rg for `DerivedCategory.isZero_iff` and the item
  id: no entry; the actual source and current server source supply the exact match.

No statement correction, new node, dependency module, or STATEMENT-DISPUTED issue.
Validation: the prescribed deliver2.py dry run checks the existing declaration with a
real scompile.py import and #check probe; its outcome is recorded below after the run.

Dry-run result: OK, commit `25498ec89f`; the existing-declaration compile passed,
and preflight passed apart from the independent second-reading section, which the
second reader supplies. Nothing was pushed.

## Second reading by N5

I independently opened the node copy and the source declaration before checking the
existing record.  The node's objects and clauses are rendered as follows:

- The object `E` in `D(T_{\Et})` is the argument `K : DerivedCategory C` of
  `DerivedCategory.isZero_iff`, specialized to
  `C := Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.  This is the abelian
  category of sheaves of abelian groups on the small etale site, exactly the
  coefficient-free convention in `def-weil-pbc-derived-categories`.
- The clause `E = 0` is rendered by `IsZero K`, the categorical meaning of an
  object being zero in a category with a zero object.  This includes the
  isomorphic-to-zero cases and does not choose a representative complex.
- The biconditional in the node is the declaration's `↔`, with both directions.
- The clause `\mathcal H^q(E) = 0 for all q` is rendered by
  `∀ n : ℤ, IsZero ((homologyFunctor C n).obj K)`.  The integer quantifier covers
  every cohomological degree, including negative and zero degrees, and
  `homologyFunctor` is the recorded cohomology-sheaf construction.

The declaration has only the generic ambient assumptions
`{C : Type u}`, `[Category.{v} C]`, `[Abelian C]`, and
`[HasDerivedCategory.{w} C]`; these are infrastructure for the displayed derived
category and add no geometric, boundedness, torsion, finiteness, characteristic,
or nonemptiness hypothesis.  The node has no statement hypotheses, so none are
missing or strengthened.  Its proof dependency is the recorded derived-category
definition; the source module and its docstring identify the same coefficient-free
specialization and the same homology functor.

I checked the empty scheme, the zero object, a nonzero sheaf in one degree, all
integer degrees, and unbounded complexes.  The generic theorem leaves all relevant
universes independent, so these edge cases are covered.

The worker's searches were also checked: upstream `rg` finds the exact declaration
and its full signature in `HomologySequence.lean`; Mathlib grep, LeanFinder, Loogle,
LeanSearch, and side-library searches find no competing exact declaration.  The
source declaration's docstring states precisely the same vanishing criterion.

No mismatch was found.  The node, its existing Lean declaration, its dependency
record, and the worker report agree; no file, statement, dependency, or edge-case
repair is required.
