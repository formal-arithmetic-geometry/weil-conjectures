## Worker report

The module `lean/Sheaf/LinearAlgebra/FrobeniusModuleWeights.lean` defines
`FrobeniusModule.IsMixedOfWeightsAtMost`.  The existing upstream declaration
`FrobeniusModule.IsPureOfWeight` supplies the first (pure) predicate in the
node, so it is not redeclared.  The new definition takes the fixed prime
`p`, exponent `a`, distinct coefficient prime `ell`, an algebraic closure
`Qlb` of `ℚ_[ell]`, a field isomorphism `iota : Qlb ≃+* ℂ`, a finite-dimensional
Frobenius module `M`, and a real bound `w`.

The Lean rendering of each statement clause is as follows.

* `[Fact (Nat.Prime p)]`, `[Fact (Nat.Prime ell)]`, `_hellp : ell ≠ p`, and
  `_ha : 1 ≤ a` render the prime, distinctness, and positive-exponent
  hypotheses; `p ^ a` is the fixed prime power `q`.
* `Qlb : Type v`, `[Field Qlb]`, `[Algebra (ℚ_[ell]) Qlb]`, and
  `_hQ : IsAlgClosure (ℚ_[ell]) Qlb` render the chosen algebraic closure.
  `iota : Qlb ≃+* ℂ` is an unrestricted field isomorphism.
* `M : FrobeniusModule.{u, v} Qlb` renders a finite-dimensional vector space
  with a `Qlb`-linear automorphism, using the recorded upstream structure.
* `∃ m : ℕ` and `V : Fin (m + 1) → Submodule Qlb M.carrier` render the finite
  filtration.  `hzero : V 0 = ⊥` and
  `hwhole : V ⟨m, Nat.lt_succ_self m⟩ = ⊤` are the two endpoints.
  `hincreasing : ∀ r : Fin m, V r.castSucc ≤ V r.succ` renders the increasing
  inclusions, including the vacuous case `m = 0`.
* `hstable : ∀ r : Fin (m + 1), Submodule.map M.frobenius.toLinearMap
  (V r) = V r` renders `F(V_r)=V_r` for every filtration term.
* For every `r : Fin m`, the quotient is
  `↥(V r.succ) ⧸ ((V r.castSucc : Submodule Qlb M.carrier).comap
  (V r.succ).subtype)`, which is exactly `V_{r+1}/V_r`.  The existential
  `G` is a `Qlb`-linear automorphism of this quotient, and the displayed
  equation sends the class of each `x : V r.succ` to the class of
  `M.frobenius x`; the membership proof uses `hstable r.succ`.
* `wr : ℝ`, `wr ≤ w`, and
  `FrobeniusModule.IsPureOfWeight (iota : Qlb →+* ℂ) (p ^ a) {...} wr`
  render the real graded-piece weight and its purity bound.  The upstream
  purity predicate is the eigenvalue condition
  `‖iota α‖ = (p ^ a : ℝ) ^ (wr / 2)`, with no semisimplicity assumption.

The edge cases checked were `m = 0` (the endpoint equalities force the
underlying module to be zero and the quotient condition is vacuous), `m = 1`
(one quotient), equal adjacent filtration terms (zero quotient, permitted by
non-strict inclusions), and non-semisimple automorphisms (the upstream purity
predicate uses eigenvalues only).  No continuity condition is imposed on
`iota`.

Dependency declarations used:

* `sk-def-frobmod`: `WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TraceSeries`,
  declaration `FrobeniusModule` (and its `frobenius`/`carrier` fields); the
  recorded module also documents the associated trace declarations.
* `def-weil-l-adic-numbers`: Mathlib `Padic` in
  `Mathlib/NumberTheory/Padics/PadicNumbers.lean`, rendered by `ℚ_[ell]`.
* `def-weil-algebraic-closure`: Mathlib `IsAlgClosure`/`AlgebraicClosure` in
  `Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean`.
* `def-weil-finite-dimensional-subspace`: Mathlib `FiniteDimensional`.
* `def-weil-complex-absolute-value`: Mathlib complex norm (`Complex.instNorm`).
* `def-weil-pbc-quotient-module`: `Submodule.hasQuotient`, quotient module
  instances, and `Submodule.Quotient.mk` from
  `Mathlib/LinearAlgebra/Quotient/Defs.lean` and `Basic.lean`.
* `def-weil-real-power`: Mathlib `Real.rpow`.

Searches made with `msearch.py` were: leanfinder for a finite-dimensional
Frobenius filtration predicate (eight Lie-module/weighted-polynomial hits,
none matching); leansearch for the same natural-language predicate (eight
weighted-polynomial/Lie-module hits, none matching); loogle for
`FrobeniusModule.IsPureOfWeight`, `FrobeniusModule.HasWeightsAtMost`, and
`Module.End.HasEigenvalue` (no hits from the Mathlib-only search); and grep for
`IsPureOfWeight|HasWeightsAtMost|FrobeniusModule|IsMixedOfWeight` under
Mathlib (zero hits).  Project and upstream searches found the upstream
`FrobeniusModule.IsPureOfWeight` but no finite-filtration Frobenius predicate.

## Second reading by N4

Independent maintainer reading of immutable delivery
`e7d49629e92ec8d8d29b46ce77373ae16029dd09`, group N4, item
`def-weil-frobenius-module-weights`. This reading replaces the worker's placeholder;
it was performed against the extracted snapshot, not a moving delivery branch.
The original Worker report above describes the delivered version; the changes below
supersede its description of the inline membership proof.

Sources read: master blueprint `sec-purity-real-sheaves/sk-p-real-semi/`
`def-weil-frobenius-module-weights.md`, order 2651; the identical mathematical text
in main-20261015, order 2995; and the containing `sk-p-real-semi/_section.md`.
Also read the coefficient convention in `def-weil-finite-field-fiber.md`, order 411,
and the source of `sk-def-frobmod`, main-20261015 order 2731. The node's explicit
linearity, non-strict filtration, image-equality stability, empty filtration and
quotient-action clarifications agree with these sources. Strict versus non-strict
filtrations gives the same predicate after deleting repeated terms; invariant
inclusions are equalities for an automorphism on a finite-dimensional invariant
subspace. No source-based statement correction or citer audit is needed.

Clause-by-clause reading:

* Prime data: `p a ell : ℕ`, both primality Facts, `1 ≤ a`, `ell ≠ p`, and
  `p ^ a` give exactly the fixed positive prime power and distinct coefficient prime.
  Natural positive exponents cover precisely the source's positive integers.
* Coefficients: arbitrary `Qlb : Type v`, Field and Algebra instances, and the
  explicit `IsAlgClosure (ℚ_[ell]) Qlb` proof retain the chosen algebraic closure.
  This proof need not be an instance: the upstream purity predicate does not need
  an algebraic-closedness instance. `iota : Qlb ≃+* ℂ` is a field isomorphism,
  with no topology or continuity assumption.
* Module: upstream `FrobeniusModule.{u,v} Qlb` bundles an AddCommGroup, Module,
  FiniteDimensional instance and `carrier ≃ₗ[Qlb] carrier`. Carrier universe `u`
  and coefficient universe `v` remain independent. Subtypes and quotients retain
  the carrier universe, with finite dimension inferred by the Mathlib submodule
  and quotient instances; no extra finiteness or universe assumption is introduced.
* Purity: upstream `FrobeniusModule.IsPureOfWeight`, at FrobeniusModule.lean:88,
  is exactly `∀ α, HasEigenvalue α → ‖iota α‖ = (q : ℝ) ^ (w / 2)`.
  Its `frobeniusEnd` is the given automorphism's linear map. Mathlib
  `HasEigenvalue`, `hasEigenvector_iff` and `mem_eigenspace_iff` give a nonzero
  vector satisfying `F v = α • v`, exactly as the node specifies. The coercion
  of the field equivalence to a ring homomorphism preserves the same scalar map.
  The existing predicate is reused rather than copied.
* Filtration: `m : ℕ`, `Fin (m+1) → Submodule Qlb M.carrier`, the bottom/top
  equalities and adjacent inclusions give every term and both endpoints.
  The submodule-image equality is precisely `F(V_r)=V_r`, for all indices.
* Quotients: `(V r.castSucc).comap (V r.succ).subtype` is the lower term as a
  submodule of the upper one, since the adjacent inclusion is imposed. Its
  quotient is the required successive quotient, not an ambient-space quotient.
* Induced Frobenius: existential `G` is a linear equivalence, constrained on every
  representative by `G(mk x)=mk(F x)`. The quotient map is surjective, so `G`
  is unique, not an arbitrary action. In the replacement the equation quantifies
  also over a proof `hx : F x ∈ V r.succ`; stability guarantees this proof for
  every x, and proof irrelevance makes its choice immaterial. This is equivalent
  to the original equation and adds no hypothesis on the Frobenius module.
  Stability of both adjacent terms gives the usual induced automorphism.
* Graded weights: `∀ r : Fin m, ∃ wr : ℝ, ∃ G, wr ≤ w ∧ ... ∧ IsPureOfWeight ... wr`
  supplies exactly one bounded real weight and the induced pure quotient per step.
  The source's finite list of weights and these pointwise existentials are equivalent.
  There is no semisimplicity, integer-weight or positivity-of-weight restriction.

Every statement dependency was read, including its recorded declaration:
`def-weil-l-adic-numbers` uses `Padic`, PadicNumbers.lean:531 (Cauchy completion
with notation ℚ_[ell]); `def-weil-algebraic-closure` uses `IsAlgClosure`,
IsAlgClosed/Basic.lean:264 (algebraically closed and algebraic extension);
`def-weil-finite-dimensional-subspace` uses `FiniteDimensional`,
FiniteDimensional/Defs.lean:75 (Module.Finite), with submodule/quotient instances
at lines 132/137; `sk-def-frobmod` records the public TraceSeries module, whose
public import supplies the exact `FrobeniusModule` structure, FrobeniusModule.lean:57.
The item directly imports that owning module and uses the very same declaration.
`def-weil-complex-absolute-value` uses Complex.instNorm, Complex/Norm.lean:26,
the square root of normSq; `def-weil-real-power` uses Real.rpow,
Pow/Real.lean:35, with its positive-base characterization at line 51;
`def-weil-pbc-quotient-module` uses Submodule.hasQuotient, Quotient.mk and mkQ,
Quotient/Defs.lean:55,61,227, with the surjectivity theorem at 236. The relevant
blueprint sources for these leaves and Algebra's cited 05GH quotient expressions
(algebra.tex:23011–23040) were also read. All seven citation ids are exactly the
statement-dependency list. No dependency interface repair or missing DAG prerequisite
is required.

Independent searches used alternative terms: `stable.*filtration`,
`weight.*filtration`, `IsMixed`, `mixed.*weight`, `IsPureOfWeight`,
`HasWeightsAtMost`, and Frobenius/filtration combinations, across upstream
WeilConjectures, the read-only group's lean/Sheaf and Mathlib. They found no
existing finite-filtration Frobenius-module predicate. Upstream HasWeightsAtMost
is an eigenvalue inequality, polynomial weights use a polynomial and reciprocal-root
normalization, and WeilSheaf/WeilComplex weight predicates have different objects.
The worker's LeanSearch, LeanFinder/Loogle and grep search record was read; the
independent filesystem searches confirm the relevant distinctions. No duplicate
notion was introduced.

Edge cases checked mathematically: `m=0` forces bottom=top and hence the zero
module, with a vacuous quotient clause; `m=1` is the single whole-space quotient;
equal adjacent terms give a zero quotient, pure of every real weight; the zero
module is mixed at every bound. A scalar one-dimensional automorphism has its
scalar's exact weight; a nontrivial unipotent Jordan block is pure of weight zero,
so no hidden diagonalizability condition appears. The diagonal operator (1,q)
has pure graded pieces of weights 0 and 2 and is mixed at bound 2, but not at
bound 1. Negative real weights are permitted. The hypotheses rule out q=0 and
q=1 and ell=p. Independent carrier/coefficient universes are retained.

Findings and complete fixes:

1. H8: the module docstring lacked the literal blueprint marker and the declaration
   docstring lacked a precise source place. The replacement names chapter,
   section, node and order, with the required marker in both docstrings.
2. H6 (the requested no-local-proof gate): the original quotient-action expression
   contains an inline `by`/`have`/`exact` membership proof. The replacement uses
   the equivalent universally quantified membership witness described above.
   There is no local proof, theorem, axiom, sorry or choice construction in the
   replacement. Existential endpoint/stability witnesses retain their constraints
   and use underscore names to avoid unused-variable linter warnings.
3. H11/report gate: both headings existed, but the delivered second-reading body
   merely disclaimed a reading. This complete independent reading replaces it.
   The Worker report is preserved. No new-node or dependency-module section is
   needed because neither kind is added.

The public signature is unchanged and matches lean.statement verbatim after the
merge tool's whitespace normalization, in both original and replacement.
The namespace and imports are appropriate, every variable and universe is bound,
and all lines in the replacement module are at most 100 characters. The definition
contains real predicates/data, not a hollow definition. No pro-etale substitute
occurs. No project repository or branch was edited, no direct ssh command was run,
and no global build or delivery/merge command was run.

Compiler evidence: the immutable report and packet supplied no explicit per-file
compiler transcript, so compilation was independently reproduced using the
prescribed `/home/ubuntu/weil-launcher-nt/scompile.py N4
 def-weil-frobenius-module-weights <file>` wrapper. The currently installed wrapper
routes to the server's private side overlay despite its older local-overlay
instructions. Original snapshot: exit 0, sandbox 2.0 s, exact library module
Sheaf/LinearAlgebra/FrobeniusModuleWeights.lean 2.1 s, no warnings/errors.
An intermediate proof-free fix exposed unused witness-name warnings; these were
repaired, without disabling any linter. Final replacement compiled at the exact
library path: exit 0, sandbox 2.1 s and library 5.1 s, no warnings/errors;
overlay `/dev/shm/nt-tmp/nt-local-compile-dcc95lcb/.lbuild`. This is per-file
wrapper verification against published imports, not a global build. The complete
replacement module and report are provided in the maintainer fixes directory,
using the merge tool's documented basename formats.
