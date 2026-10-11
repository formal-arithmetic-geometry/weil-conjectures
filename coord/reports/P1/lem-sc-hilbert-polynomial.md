## Worker report

The node is already stated by `AlgebraicGeometry.Scheme.Hom.exists_polynomial_hilbertFunction` in `WeilConjectures.AlgebraicGeometry.Modules.Ample` (source file `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/AlgebraicGeometry/Modules/Ample.lean`, lines 244--248), so no module is added. Its signature is recorded verbatim in the node's `lean.statement` field.

The field `K : Type u` with `[Field K]` and `X : Scheme.{u}` are the surrounding variables of the source module. The properness hypothesis is `[IsProper f]` for `f : X ⟶ Spec (.of K)`. The ample invertible module is represented by `M : X.Modules` and `hM : IsAmple f M`; `IsAmple` includes invertibility. The conclusion introduces `P : Polynomial ℚ`, bounds `P.natDegree` by `((topologicalKrullDim X).unbotD 0).toNat`, and states for every `m : ℕ` that `P.eval (m : ℚ)` equals `f.hilbertFunction M m`, where the latter is `χ(X,M^{⊗m})`.

The source declaration therefore matches the node's proper-over-a-field, ample-invertible, degree-bound, and Hilbert-function clauses. Empty schemes and infinite Krull dimension use the source's `unbotD 0` convention; `m = 0` is included by `∀ m : ℕ`.

Searches: `msearch.py ... grep "exists_polynomial_hilbertFunction" /home/ubuntu/weil-src-slopmaster2/WeilConjectures` found the exact theorem in `WeilConjectures/AlgebraicGeometry/Modules/Ample.lean` (documentation and declaration, with a use at line 288). Grep of `lean/Sheaf` found no competing declaration. The node's recorded Mathlib searches report no matching theorem.

## Earlier second reading (a previous round; superseded)

The existing declaration was read in full in `Modules/Ample.lean`. Its binders and conclusion match the node: `f` is a morphism to `Spec K` carrying `IsProper`, `M` is an `X.Modules`, `hM` is `IsAmple f M`, and the existential rational polynomial has natural-number degree bounded by the topological Krull dimension and evaluates to the Hilbert function at every natural input. No mismatch was found.

## Second reading by P1

I independently opened the sandbox node and `WeilConjectures/AlgebraicGeometry/Modules/Ample.lean`
(lines 100--125, 174--197, 237--248), then followed its definitions into `Modules/Invertible.lean`,
`ProjectiveSpace/Twist.lean`, and `Cohomology/Defs.lean`. The item's `stmt_deps` is empty; there
are no delivered new nodes, dependency modules, or statement corrections. I also read the existing
DAG records `def-sc-ample` and `def-pc-euler-characteristic`, whose recorded declarations are
precisely the ampleness and Euler characteristic used by the existing theorem.

Source reading: the repository's `literature/stacks-project` is absent on this machine. I fetched
Stacks `varieties.tex` and `tags/tags` into the sandbox scratchpad, verified
`0BEM,varieties-lemma-numerical-polynomial-from-euler`, and read lines 10185--10287 including the
section preamble and full proof. I also read https://stacks.math.columbia.edu/tag/0BEM.
The source asserts the more general coherent-sheaf, multiple-invertible-twist polynomial theorem;
the node deliberately specializes it to the structure sheaf and one ample invertible module.
The section imposes no algebraic-closure, characteristic, smoothness, integrality, connectedness,
or projectivity hypothesis in addition to properness over a field. Properness implies finite type,
Noetherianity, and finite dimension here, and invertible modules are coherent on this scheme.
Thus the specialization needs no additional coherent-module binder.

Object/hypothesis/conclusion checklist:

- Field k: surrounding `{K : Type u} [Field K]`. Verdict: same arbitrary field; no restriction
  on characteristic or algebraic closure.
- Scheme X over k: surrounding `{X : Scheme.{u}}` and explicit
  `(f : X ⟶ Spec (.of K))`. Verdict: the named structure morphism supplies exactly the
  k-scheme structure; the convention permits this existing declaration's explicit-morphism form.
- X proper: `[IsProper f]`. Verdict: exact properness over k, not properness over another base
  and not an added projectivity assumption.
- Dimension g: `((topologicalKrullDim X).unbotD 0).toNat`. Verdict: for a nonempty proper
  k-scheme this is its finite Krull dimension g; g is determined by X, not an independently
  chosen bound. No pure-dimension condition is introduced.
- Invertible O_X-module M: `(M : X.Modules)` and the first conjunct `M.IsInvertible` of
  `(hM : IsAmple f M)`. Verdict: the existing scheme-module notion locally trivializes M
  on open neighbourhoods, exactly rank-one local freeness. No arbitrary vector space replaces M.
- M ample: the other conjunct of `AlgebraicGeometry.IsAmple` is
  `∃ m : ℕ, 0 < m ∧ IsVeryAmple f (M.tensorPow m)`. `IsVeryAmple` asks for a finite-coordinate
  projective closed immersion over k and an isomorphism with its O(1) pullback. Verdict: this is
  exactly the proper-scheme characterization in `def-sc-ample`. The upstream docstring warns
  that it differs from absolute ampleness for nonproper schemes; this theorem assumes properness.
  I read the project's absolute `Scheme.Modules.IsAmple` in `Sheaf/AlgebraicGeometry/Ample.lean`
  too: its affine nonvanishing-cover criterion is equivalent in this proper finite-type case.
  The complete-linear-system wording of `def-sc-ample` is equivalent to the existence of a
  projective embedding, as its recorded lead note also explains. Neither alternative warrants
  replacing this already recorded definition.
- Function m ↦ chi(X,M tensor-power m): `f.hilbertFunction M m`. Verdict: its body installs
  the over-k structure specified by f and uses `Scheme.Modules.eulerChar K (M.tensorPow m)`.
  `tensorPow 0` is the monoidal unit O_X, and its successor is tensor product over O_X.
  `eulerChar` is the integer-valued finite sum of alternating k-dimensions of sheaf cohomology.
  Properness and coherence give finite-dimensional cohomology and eventual vanishing, so the
  finsum/finrank junk-value cases do not occur. The underlying abelian-sheaf cohomology encoding
  is the existing encoding recorded by `def-pc-euler-characteristic`, related to module derived
  cohomology by the project's stage-3 comparison convention.
- Numerical polynomial: `∃ P : Polynomial ℚ` and
  `∀ m : ℕ, P.eval (m : ℚ) = f.hilbertFunction M m`. Verdict: rational polynomial with integer
  values at all natural arguments, because the right side is an integer coerced to ℚ. Integral
  finite differences give its integer binomial-basis coefficients, hence the numerical-polynomial
  condition; this is not a demand for integer monomial coefficients. The node's tensor-power
  Hilbert function is rendered on natural exponents. The source's stronger integer-twist version
  is separately stated by `lem-sc-snapper-numerical-polynomial`; this node does not introduce
  dual powers. Equality is for every natural m, including zero, not merely eventual equality.
- Degree at most g: `P.natDegree ≤ ((topologicalKrullDim X).unbotD 0).toNat`. Verdict: in one
  variable total degree is degree; natural degree also permits the zero polynomial. The
  existential polynomial precedes the universal m, so one polynomial works for every input.
- Name Hilbert polynomial: P is the requested polynomial. Verdict: a mathematical name, not
  an extra choice, uniqueness clause, positivity assertion, or equality-of-degrees assertion.

Edge cases: dimension zero allows constants; m = 0 evaluates chi(X,O_X). The empty scheme has
zero cohomology and Hilbert function, so equality at infinitely many natural arguments forces
P = 0 even though the numerical dimension convention is zero. Thus replacing bottom dimension
by zero does not admit a nonzero answer. The zero module is not invertible on a nonempty scheme,
but is permitted on the empty scheme. No nonempty or connectedness instance is assumed.
Infinite dimension cannot occur for a proper scheme over a field; the worker report's mention
of its default-value convention is not a relevant extra case. There is no variable index family
in this node. The arbitrary universe u covers schemes and fields after putting them in a common
universe; there is no fixed `Type 0` constraint or small test-object quantifier. All variables
and the universe are explicitly bound in the upstream public section.

Independent searches (recorded by `msearch.py` in `searches.jsonl`):

- LeanSearch: `Euler characteristic of powers of an ample invertible sheaf agrees with rational
  polynomial`. Service returned Internal Server Error; recorded unavailable, not a negative result.
- Loogle: `"hilbert"`. Returned Hilbert spaces/bases and related analysis declarations, no
  scheme-cohomology polynomial theorem among the displayed results.
- Mathlib grep: `numerical.?polynomial|Hilbert.*polynomial|polynomial.*Euler`. This found
  `Mathlib/RingTheory/Polynomial/HilbertPoly.lean`; I opened it. Its `Polynomial.hilbertPoly`
  is the eventual coefficient function of a rational power series p/(1-X)^d, not this theorem.
- Independent rg on upstream and `lean/Sheaf`: `hilbertFunction|numerical polynomial|polynomial.*eulerChar`
  found the chosen upstream theorem and the project's broader Snapper theorem. I opened both.
  The latter concerns an arbitrary coherent module, finitely many invertible twists and a
  multivariate polynomial, with no ample hypothesis; it is a stronger tool, not this statement.
  No second definition or theorem is required.

Repairs: no mathematical mismatch was found, so the existing Lean record and its verbatim
signature are retained. I replaced the earlier cursory reading with this independent checklist,
source reading, definition audit, and real searches. Nothing was proved and no module was added.
The upstream theorem's body is `sorry`; its docstring identifies this blueprint node and Tag
0BEM. Its short docstring does not contain the DAG's detailed proof; existing attachments are
reused without editing the read-only upstream module. The node's three detailed proof steps
remain the stage-3 handoff: support-dimension induction and embedded-point removal; reduction
by scheme-theoretic support and regular-meromorphic-section forward differences; the zero-
dimensional base and integration of differences, finally specializing F to O_X.

Validation: a scratch file importing the recorded module and checking the fully explicit theorem,
ampleness, Hilbert function, and Euler characteristic signatures was submitted through `scompile.py`.
No scratch file belongs to the delivery.
The server check completed with exit code 0 in 1.9 seconds, with no warnings; its output confirms
that the theorem has exactly the field, scheme, structure-morphism, properness, module, and
ampleness arguments listed above.
