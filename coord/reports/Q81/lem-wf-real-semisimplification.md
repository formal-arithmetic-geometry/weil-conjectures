## Worker report

The module states `AlgebraicGeometry.WeilGroup.isReal_semisimplification`, with `sorry` as
its only proof. The node is unchanged except for its `lean` record. No new notion is defined.

Read the current blueprint main-20261015 lemma and its unit `sk-r-real-linear`, the node's
five proof steps, all three statement-dependency nodes and their recorded source declarations.
The published CompositionSeries source was read through `scompile.py --source` because that
module is absent from the older local source checkout. No repair note exists for this item.

Hypothesis and clause correspondence:

- The finite base field is `{K : Type u} [Field K] [Finite K]`. The curve and its structure
  map are `{C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]`. `W : WeilGroup p` is the
  published genuine Weil-group presentation: it includes the fundamental-group presentation,
  geometric connectedness, degree map and local Frobenius elements. The coefficient prime is
  `{l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]`; coefficients are `PadicAlgCl l`.
- The monodromy representation in the item's parenthesis is `D.asRepresentation`, for
  `D : Monodromy.RepresentedDegreeDatum W.carrier n (PadicAlgCl l)`. This uses the exact
  recorded monodromy structure, not the geometric representation alone. Its carrier is
  `n → PadicAlgCl l`; `[Fintype n]` supplies finite dimension. Allowing every finite index
  type in `Type u` covers every finite rank, including rank zero. `[DecidableEq n]` is the
  existing matrix-coordinate interface, not a restriction on ranks.
- Lisseness is `hLisse : W.IsLisse l D.asRepresentation`: continuity of the geometric action.
  This is the existing representation presentation of lisse Weil sheaves used throughout
  upstream RealSheaves.Basic, LocalSystems and Operations. In particular it is a Weil action,
  not just a geometric action. No arbitrary map or unspecified local operator is introduced.
- Reality is `hReal : W.IsReal l D.asRepresentation ι`, with the fixed embedding
  `ι : PadicAlgCl l →+* ℂ`. Weights.lean:111-113 defines this as conjugation fixing every
  coefficient of every local polynomial. This is the identical coefficient condition of
  `FrobeniusModule.IsReal` and `WeilSheaf.IsReal` in the recorded Stalk module: the latter
  applies it to each closed-point stalk. No surjectivity or continuity is imposed on `ι`.
- A choice of composition series is `s : D.asRepresentation.CompositionSeries`. The resulting
  `s.semisimplification` is exactly the recorded direct sum of successive quotients. This
  quantifies over all choices; no preferred series or independence hypothesis is assumed.
- The conclusion `W.IsLisse l s.semisimplification` retains the lisse category of the result.
  `W.IsReal l s.semisimplification ι` is the asserted preserved reality. The final clause is
  `∀ x : C.finitePoints, W.localPolynomial l s.semisimplification x =
  W.localPolynomial l D.asRepresentation x`. By Weights.lean:78-79, localPolynomial is
  `charpolyRev` of the local Frobenius action, namely det(1 - T F_x), with multiplicities.
  This asserts equality of the polynomials themselves, not just traces or root sets.

Dependency declarations used:

- `WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy`:
  `AlgebraicGeometry.Monodromy.RepresentedDegreeDatum` and `.asRepresentation`.
- `WeilConjectures.RepresentationTheory.CompositionSeries`:
  `Representation.CompositionSeries`, `.factor`, `.semisimplification`, and the proof-plan
  ingredient `Representation.exists_compositionSeries`. Read the full structure and
  construction, including the quotient carriers and direct-sum action.
- `WeilConjectures.WeilSheaf.Stalk`: recorded reality module;
  `AlgebraicGeometry.WeilSheaf.IsReal` and `.IsRealizable`. The recorded declaration names
  IsRealizable, while the same module also contains the IsReal definition this item needs.
  No second definition is needed. The representation-side interface is
  `AlgebraicGeometry.WeilGroup.IsReal` and `.localPolynomial` from the published
  `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights`, imported through Operations.
- `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations` supplies the shared
  representation operations and `WeilGroup.IsLisse` quotient/direct-sum facts.
- The stated proof dependency p-linear-filtration is imported privately through
  `WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic` and
  `WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Basic`, including
  `LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ` and
  `Module.End.hasEigenvalue_of_subquotient`. The composition-series proof dependencies
  share the public CompositionSeries import. The remaining proof nodes
  prop-wf-weil-sheaf-representation-equivalence, p-real-operations and
  def-real-weil-representation-operations have no recorded Lean module, so there is no
  recorded proof-module import to add for them. Their steps remain in the proof docstring.

Edge cases checked mathematically against the definitions: empty `n` gives zero carrier,
length-zero series and the empty direct sum; all local factors are 1 and real. A rank-one
representation has one simple factor. A nonsplit upper triangular extension retains its two
Frobenius eigenvalues with multiplicity. Repeated eigenvalues and nontrivial Jordan blocks do
not require a stable complement. Reality can hold for a pair of conjugate nonreal factors
without holding for each factor individually; the conclusion concerns the whole direct sum.
The theorem assumes neither semisimplicity of the original action nor nonzero rank.
No statement dispute or source correction was found.

Searches run (no exact existing theorem):

- msearch leanfinder, `The semisimplification of a lisse Weil sheaf preserves local
  characteristic polynomials and iota reality`: eight results about semisimple endomorphisms
  and FDRep.simple_iff_char_is_norm_one, none about semisimplification/local factors.
- msearch loogle, `Representation, "semisimplification"`: zero hits.
- msearch grep, `semisimplification|IsReal`, subdirectory RepresentationTheory: zero hits.
- msearch leansearch, `A finite dimensional representation and its semisimplification have
  equal characteristic polynomials at every group element`: eight hits, including
  LinearEquiv.charpoly_conj and FDRep.char_iso, but neither states this assertion.
- rg of `semisimplification|semisimpl|isReal_semisimplification` in upstream RealSheaves,
  upstream WeilSheaf and project lean/Sheaf found only commentary and unrelated mixedness
  lemmas. rg of `semisimplification|isReal_semisimplification` in Mathlib/RepresentationTheory
  found no match. rg for the item id and proposed full declaration name in Mathlib, upstream
  WeilConjectures and project lean/Sheaf found no match. The upstream name table records
  CompositionSeries.semisimplification but no theorem for this item.
- The current published Operations source was checked with `scompile.py --source`; it has
  lisseness of subquotients/direct sums and reality for exterior powers given a polynomial
  equality, but no semisimplification polynomial/reality theorem.

Validation: the final module compiled cleanly through scompile.py, separately as sandbox and
library module (2.6 and 2.8 seconds), under the default 60-second limit. All binders and the
universe are explicit; there are no helper definitions, local instances, hidden lets or
proofs beyond the single requested `sorry`.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
