## Worker report

The module `lean/Sheaf/AlgebraicGeometry/FiniteDenseNormalOpen.lean` states
`AlgebraicGeometry.exists_nonempty_normal_open` with proof `sorry`.
The theorem uses a scheme `X : Scheme.{u}`, a field `k : Type u`, and a
structure morphism `f : X ⟶ Spec (.of k)`. The hypotheses are rendered as
`[LocallyOfFiniteType f]`, `[QuasiCompact f]`, and `[IsIntegral X]`, exactly
expressing finite type over a field and integrality. The conclusion is
`∃ U : X.Opens`, so `U` is an open subscheme of `X`; `Nonempty U` renders
nonemptiness; and `∀ x : X, x ∈ U → IsIntegrallyClosed
(X.presheaf.stalk x)` renders normality of the open by requiring every local
ring on that open to be integrally closed. Since `[IsIntegral X]` supplies
integral-domain stalks, this is the normal-scheme condition. No density clause
was added because the node's statement itself asks only for a nonempty open.

The sole statement dependency is `def-weil-pbc-scheme-conventions`. Its Lean
record is a convention bundle with no declaration, so the module uses the
Mathlib notions directly: `Scheme`, `Spec`, `LocallyOfFiniteType`,
`QuasiCompact`, `IsIntegral`, `Scheme.Opens`, `Nonempty`, and
`IsIntegrallyClosed`.

Edge cases checked: `IsIntegral X` entails nonemptiness, but the existential
open is still required to be explicitly nonempty; no dimension or characteristic
assumption was introduced; arbitrary universe `u` is retained; and the empty
open is excluded by `Nonempty U`. The local-ring condition is vacuous only for
an empty open, which is why that clause is paired with `Nonempty U`.

Searches made:

* `msearch.py ... leanfinder "normal scheme all local rings integrally closed domain"`:
  found Mathlib integral-scheme and stalk-domain declarations, but no theorem
  stating existence of a normal open.
* `msearch.py ... loogle "IsIntegrallyClosed, IsIntegral, Scheme.Opens.toScheme"`:
  no hits (the `Scheme.Opens.toScheme` name is not a Loogle identifier).
* `msearch.py ... grep "IsIntegrallyClosed|normal scheme" RingTheory`:
  found only local-property declarations, not this conclusion.
* `rg` over `WeilConjectures/` and `lean/Sheaf/` for normal-open and
  integrally-closed-stalk statements: no exact existing declaration.

No `STATEMENT-DISPUTED` issue or node fault found.

## Second reading by K1

Independent comparison with `dag/nodes/sec-smooth-purity/lem-fin-dense-normal-open.json`:

* Field over which the scheme is finite type: `{k : Type u} [Field k]` and
  `Spec (.of k)`. Exact; there is no characteristic restriction.
* Scheme: `{X : Scheme.{u}}`. Exact; the universe is arbitrary and shared with
  the field so the structure morphism has the required type.
* Structure morphism: `(f : X ⟶ Spec (.of k))`. Exact; this is the specified
  field-scheme structure, not an arbitrary map of topological spaces.
* Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`. Exact by the
  finite-type convention in `def-weil-pbc-scheme-conventions`, which points to
  `def-weil-finite-type-morphism`. Neither a Noetherian nor a separated
  hypothesis was added.
* Integral: `[IsIntegral X]`. Exact: Mathlib's class includes `Nonempty X`
  and domain sections on each nonempty open; this is a scheme condition,
  not the distinct morphism class `IsIntegralHom`.
* Open subscheme: `∃ U : X.Opens`. Exact: its canonical open subscheme is
  `U.toScheme`; the theorem does not select a closed or locally closed locus.
* Nonempty: `Nonempty U`. Exact: it excludes the empty open explicitly.
* Normal: `∀ x : X, x ∈ U → IsIntegrallyClosed (X.presheaf.stalk x)`.
  Exact: with integrality inherited from `X`, this is normality of every
  local ring on the open. The node's statement contains no separate density
  clause; its proof obtains density from integrality and nonemptiness.

Edge cases: `[IsIntegral X]` rules out the empty scheme and zero coordinate
rings. No index set or natural-number parameter occurs; there is no `n = 0`
case. Any field characteristic is admitted. `u` is arbitrary, with no
small-universe or `CharZero` constraint. The open itself cannot be empty.

Searches independent of the worker report: `msearch.py` LeanFinder for
"integral scheme finite type field contains dense open normal subscheme"
returned only integral-scheme and normalization constructions, no matching
existence theorem. Loogle for `Scheme, IsIntegral, IsIntegrallyClosed, Opens`
returned no hit (its parser did not recognize `Scheme`); `msearch.py` grep
for "normal open subscheme integral finite type field" returned no hit.
`rg` in Mathlib's algebraic-geometry modules, the source repository's
`WeilConjectures/`, and the project's `lean/Sheaf/` found no exact statement.
In particular, `Scheme.exists_isIso_fromNormalization_restrict` in the
source repository concludes an isomorphism over an open, a different claim.

Mismatch found: the original theorem docstring compressed the node's four
proof steps and omitted finite module generators, the common denominator,
and the final nonemptiness/density reasoning. I expanded that docstring.
The Lean signature and the node's `lean.statement` were already verbatim
equal and needed no change. The node cites a blueprint source whose Markdown
file is absent from this checkout; the node's full proof and the recorded
convention dependency supplied the comparison text.
