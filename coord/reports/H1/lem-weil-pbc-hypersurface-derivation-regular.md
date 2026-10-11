## Worker report

The module `Sheaf.RingTheory.HypersurfaceDerivationRegular` states
`IsRegularRing.quotient_span_singleton_of_isUnit_derivation`, with only `sorry` as its proof.
No definition, dependency module, new node, or statement correction is needed.

Hypotheses and conclusion, clause by clause:
- The commutative ring R is `(R : Type u) [CommRing R]`, with an explicitly bound universe.
- R is Noetherian and every prime localization is regular local: `[IsRegularRing R]`.
  This Mathlib class extends `IsNoetherianRing R` and contains
  `isRegularLocalRing_localization (p : Ideal R) [p.IsPrime]`.
- The element f is `(f : R)`.
- The additive derivation satisfying D(ab) = aD(b) + bD(a) is
  `(D : Derivation ℤ R R)`. Every additive map of rings is ℤ-linear, and Leibniz
  forces D(1) = 0 by additive cancellation, so Mathlib's extra structure does not
  restrict the node's absolute derivations. No algebra over a field, characteristic
  restriction, or R-linearity is assumed.
- The image of D(f) is a unit in R/fR:
  `hunit : IsUnit (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (D f))`.
  The singleton-generated ideal is exactly fR; `Ideal.Quotient.mk` is the quotient map.
- The conclusion is `IsRegularRing (R ⧸ Ideal.span ({f} : Set R))`, including
  Noetherianity and regularity at every prime.
- The parenthetical unit case is included without a separate hypothesis: if f is a unit
  this ideal is top, the quotient is the zero ring, and its prime condition is vacuous.

Dependency declarations read and used:
- `def-weil-regular-scheme`: its ring clauses are Mathlib `IsRegularRing` and
  `IsRegularLocalRing`, in `Mathlib.RingTheory.RegularLocalRing.Defs`. The scheme
  clause is irrelevant to this ring statement; no scheme specialization is needed.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, in
  `Mathlib.RingTheory.Noetherian.Defs`, used through the regular-ring class.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`, in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, used through the regular-ring class.
  Its residue-field and fibre-ring clauses are not needed here.
- Additional standard Mathlib notions: `Derivation`, in
  `Mathlib.RingTheory.Derivation.Basic`; `Ideal.Quotient.mk`, in
  `Mathlib.RingTheory.Ideal.Quotient.Defs`.

Edge cases checked: no Nontrivial assumption excludes the zero ring; f a unit gives
zero quotient; f = 0 in a nonzero ring cannot satisfy the unit hypothesis because D(0) = 0;
the zero ring still satisfies that hypothesis and conclusion. All characteristics and all
ring universes are admitted. The unit assumption is substantive: over a field, with f = 0,
the zero derivation does not satisfy it. The source is
[Stacks Tag 07PF](https://stacks.math.columbia.edu/tag/07PF), opened directly because the
local literature source is unavailable. It states the same result and gives the local
Leibniz argument. The declaration docstring includes all three DAG proof steps and names
their proof dependencies; nothing is proved in this stage.

Searches for an existing statement:
- `msearch.py ... leanfinder "quotient of a regular ring by an element whose derivative
  under a derivation is a unit is regular"`: eight hits, standard étale/smooth
  presentations and polynomial-domain statements, none the regular quotient theorem.
- `msearch.py ... loogle "IsRegularRing, Derivation, Ideal.Quotient.mk"`: zero hits.
- `msearch.py ... leansearch "A regular ring modulo f is regular if a derivation sends f
  to a unit modulo f"`: service unavailable, Internal Server Error.
- `msearch.py ... grep "IsRegularRing|derivation.*quotient" RingTheory/RegularLocalRing`:
  ten hits, definitions and polynomial regularity, no quotient theorem.
- `rg` on the source `WeilConjectures` and project `lean/Sheaf` for derivations and
  `IsRegularRing`: found localization/finite-type derivation results and polynomial
  formal-fibre/degree-p regularity modules, not this statement. In particular
  `Sheaf.Paper.DerivationExtendsFiniteType` already uses `Derivation ℤ R R` for
  absolute derivations.
- `rg` for the item id and the proposed declaration name in
  `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures`, and `lean/Sheaf`:
  only docstring references to this item in PolynomialFormalFiber and
  DegreePExtensionRegular; no existing declaration or name collision.

No statement dispute or node fault was found. Server compilation and the delivery dry run
are the final validation steps; the second reader will add the independent reading.

## Second reading by H1

I independently read the item, all three statement-dependency nodes, their Mathlib
sources, and the delivered module. The local literature tree has no Stacks .tex;
I read the upstream `more-algebra.tex` at `section-regularity-derivations` and
`lemma-quotient-regular`, as well as [Tag 07PF](https://stacks.math.columbia.edu/tag/07PF).
The section introduces extensions of absolute derivations along ring maps; it imposes
no standing field, characteristic, finite-type, or local hypothesis on this lemma.
The local-ring reduction belongs to the proof, not to the statement.

Objects, hypotheses, and conclusions of the node, matched individually:

1. A commutative ring R: `(R : Type u) [CommRing R]`. Exact; `universe u` is
   explicitly declared and unrestricted.
2. R Noetherian: `[IsRegularRing R]` extends `IsNoetherianRing R` in
   `Mathlib.RingTheory.RegularLocalRing.Defs`. Exact, not an extra assumption.
   I read `IsNoetherianRing` in `Noetherian.Defs`: it is `IsNoetherian R R`,
   equivalently every ideal finitely generated, exactly def-weil-pbc-noetherian-ring.
3. Every prime localization regular local: the same class has the field
   `isRegularLocalRing_localization (p : Ideal R) [p.IsPrime] :
   IsRegularLocalRing (Localization.AtPrime p)`. Exact. `IsRegularLocalRing`
   extends local and Noetherian and equates maximal-ideal generator rank with
   Krull dimension, as def-weil-regular-scheme states. I read
   `Localization.AtPrime` in `Localization.AtPrime.Basic`: localization at
   `p.primeCompl`, precisely the localization clause of
   def-weil-pbc-localization-at-prime. The dependency's residue-field and fibre
   clauses are not invoked by this item; its recorded Mathlib localization is usable.
4. An element f of R: `(f : R)`. Exact, with no nonzero or nonunit restriction.
5. An additive absolute derivation D satisfying Leibniz:
   `(D : Derivation ℤ R R)`. Exact. I read the structure in `Derivation.Basic`:
   it is a linear map with `map_one_eq_zero'` and `leibniz'`. Additivity makes
   a map between additive groups commute with integer scalar multiplication;
   the canonical integer algebra/module structures require no extra binder.
   Leibniz gives D(1) = D(1) + D(1), hence D(1) = 0 by cancellation.
   Conversely its scalar multiplication by R on R is multiplication, so its
   Leibniz field is exactly the node's formula. No absolute derivation is lost.
6. The image of D(f) invertible in R/fR:
   `hunit : IsUnit (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (D f))`.
   Exact. The singleton span is fR, and the `Ideal.Quotient.mk` definition I read
   in `Ideal.Quotient.Defs` is the canonical ring quotient map.
7. The quotient regular: `IsRegularRing (R ⧸ Ideal.span ({f} : Set R))`.
   Exact, including Noetherianity and every prime localization, not just one local
   regularity or a dimension bound. Binding an arbitrary witness D and then hunit
   is equivalent to the source's existence-of-D formulation because the conclusion
   depends only on R and f.
8. The parenthetical unit case: no `Nontrivial R` or nontrivial-quotient hypothesis
   is present. When f is a unit the quotient is zero; its Noetherianity holds and
   its prime-localization requirement is vacuous. Exact.

Edge cases: the zero ring is admitted, including its unique derivation and unit
condition. For f = 0 in a nonzero ring, D(0) = 0 and the unit hypothesis is false,
as required; for f a unit, the zero quotient is admitted. All characteristics and
all ring universes are covered. There is no index set, scheme, or integer n in
this statement, so empty-index, empty-scheme, and n = 0 cases are inapplicable.

Independent searches (queries differ from the first reader's):

- `msearch.py ... leansearch "Jacobian hypersurface regular quotient absolute
  derivation invertible"`: service unavailable, Internal Server Error; no verdict
  inferred from that failure.
- `msearch.py ... loogle "Derivation, IsRegularRing"`: OK, zero hits.
- `rg` for `IsRegularRing|hypersurface|quotient.*deriv|deriv.*quotient` on Mathlib's
  regular-local-ring and derivation directories, upstream `WeilConjectures`, and
  the project's `lean/Sheaf`; also all-Mathlib search for files using IsRegularRing
  and exact-name searches there and in `dag/lean_names_upstream.json`: no duplicate
  of the delivered statement or declaration. The project has specialized
  polynomial formal-fibre and degree-p quotient statements, not this general lemma.
  Upstream `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs` contains
  `IsRegularLocalRing.quotient_span_singleton`; I opened its signature. It assumes
  R local and f in the maximal ideal but outside its square, and concludes local
  regularity and a generator-rank equality. It is a tool for the local proof,
  not this absolute-derivation statement, so it cannot replace the delivery.

The module and theorem docstrings carry the source and the exact blueprint id.
Its three proof paragraphs match each of the node's three proof steps: prime
quotient localization; extension of D and the Leibniz contradiction followed by
local hypersurface regularity; Noetherian quotient and the regular-ring local
criterion. Each named proof dependency is retained. There is one theorem with
`by sorry`, no definitions (hollow or otherwise), and no proved helper. All imports
serve the statement. No implicit variable/universe is unbound; lines are at most
100 characters and the namespace has no Sheaf prefix. The node's lean.statement
is verbatim the declaration signature, without the proof assignment.

No mathematical or Lean mismatch was found. I preserved the module and node;
only this independent second-reading report was appended. There are no new nodes,
dependency modules, or statement corrections requiring further review.

Validation: `scompile.py H1 lem-weil-pbc-hypersurface-derivation-regular` with the
absolute sandbox module path compiled on the server in 1.5 seconds, exit 0, with
no warnings. `deliver2.py H1 lem-weil-pbc-hypersurface-derivation-regular --no-push`
printed OK: preflight and compilation passed. The first compile invocation used a
relative path from the read-only repository and could not find the sandbox file;
using the absolute sandbox path resolved that invocation error.
