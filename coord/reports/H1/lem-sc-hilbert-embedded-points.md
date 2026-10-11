## Worker report

The module `Sheaf.AlgebraicGeometry.RemoveEmbeddedPoints` states
`AlgebraicGeometry.Scheme.Modules.exists_maximal_nowhereDense_support_cokernel`.
It has one theorem, with `sorry`, and no new definitions. The node is unchanged except
for its `lean` record. No additional nodes or dependency modules are needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A locally Noetherian scheme: `(X : Scheme.{u}) [IsLocallyNoetherian X]`.
- A coherent O_X-module: `(F : X.Modules)` and
  `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`.
- Coherent subsheaves K of F: `K : Subobject F`, with coherence included in the
  predicate to which `Maximal` applies. A subobject is an isomorphism class of
  monomorphisms, with representative inclusion `K.arrow`; this is precisely a subsheaf.
- Nowhere dense support in Supp(F): `IsNowhereDense` on the subtype
  `{x : X | ¬ Subsingleton (F.presheaf.stalk x)}`, restricting the nonzero-stalk
  condition of the subobject to that subtype. This is relative nowhere density,
  not nowhere density in X.
- Existence of a maximal such K: `∃ K : Subobject F, Maximal (...) K`.
  This includes membership in the predicate and the maximality assertion, without
  asserting a stronger greatest-element conclusion.
- F' = F/K: `cokernel K.arrow`, the quotient by that very inclusion.
- Equality of supports: equality of the sets of nonzero stalks of the cokernel and F.
- No embedded associated points of F': on every affine open V, every prime in
  `associatedPrimes Γ(X, V) Γ((cokernel K.arrow : X.Modules), V)` is minimal among
  the associated primes. For a coherent module over a Noetherian affine ring,
  minimal associated primes are exactly the generic points of its support. This
  is the same inline encoding used in the landed `HilbertDifference.lean`, and
  in the affine removal lemma. The scheme-only `associatedPoints X` definition
  is not applicable to a general module F'. No alternative named predicate is defined.
- A dense open U of X: `∃ U : X.Opens, Dense (U : Set X)`.
- U meets Supp(F) densely: `Dense {x : {x : X | ...} | x.val ∈ U}`, in the
  support's subspace topology.
- F'|U is isomorphic to F|U: `Nonempty ((cokernel K.arrow).over U ≅ F.over U)`.
  These are restrictions of sheaves of modules to U. The source asks for an
  isomorphism, so the statement does not add a condition on its chosen map.
- Strict support-dimension drop when the original dimension is finite and positive:
  `∀ d : ℕ, 0 < d → topologicalKrullDim (support of F) = (d : WithBot ℕ∞) → ...`.
  The conclusion compares the topological Krull dimensions of the two support
  subspaces. The finite positive values of `WithBot ℕ∞` are exactly these casts.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  the recorded declaration of `pqf-def-locnoeth`. Its component_noetherian field
  says every affine open has a Noetherian coordinate ring.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`,
  the recorded declaration of `pqf-def-coherent`. It is finite type plus finite-type
  kernels of every map from finite free modules on any open. It applies to
  `X.Modules` via `X.toRingedSpace`, as its module docstring specifies.
- Mathlib subobjects, cokernels, `SheafOfModules.over`, `associatedPrimes`,
  `IsNowhereDense`, `Dense`, and `topologicalKrullDim` supply the remaining language.

Source check: opened https://stacks.math.columbia.edu/tag/02OL, Lemma 31.4.6
(the node's old lemma number 31.5.8 is stale, but its tag and text are correct).
The local `literature/stacks-project/divisors.tex` is absent on this machine.
The web source confirms the maximality, support, associated-point, and dense-open
clauses and cites Tags 02M6 and 02M7 for the proof. The additional dimension clause
and its complete proof are retained from the node, as required by its consumer's
induction; they are not claimed to be an extra clause of Tag 02OL.

Edge cases checked: the empty scheme and zero module are included; the support
subtype can be empty, the zero subobject is admissible, and density on the empty
support is vacuous. Empty support has dimension bottom, so the positive finite
hypothesis does not apply to F = 0. Dimension zero and infinite dimension remain
covered by the first conclusions but impose no strict-drop conclusion. The zero
kernel has dimension bottom, strictly less than any positive finite dimension.
There is no quasi-compactness, separation, finite-type-over-a-field, characteristic,
or nonemptiness hypothesis. A single explicit universe u covers all schemes and
modules in the recorded dependency's encoding; there are no automatic implicits.

Searches (real tool calls are in searches.jsonl):

- leanfinder: `coherent sheaf maximal subsheaf nowhere dense support quotient no embedded associated points`:
  eight hits about ideal-sheaf supports and zero loci, none about removal for a general module.
- loogle: `associatedPrimes`: found the Mathlib associated-prime definition and basic
  lemmas; no sheaf removal statement.
- msearch grep: `associatedPoints|associatedPrimes|IsNowhereDense`: found associated
  primes and `Mathlib.Topology.GDelta.Basic.IsNowhereDense`, no matching theorem.
- leansearch: `coherent sheaf quotient remove embedded associated points same support`:
  unavailable, Internal Server Error; no result inferred.
- rg over `WeilConjectures` for `associatedPoints|associatedPrimes|IsAssociatedPoint`:
  only unrelated ring-theoretic associated-prime uses; no removal statement.
- rg for `lem-sc-hilbert-embedded-points` in `WeilConjectures`: no matches.
- rg over `lean/Sheaf`: found the affine removal statement, scheme-only associated
  points, and HilbertDifference's affine associated-prime encoding; no theorem for
  the present sheaf statement.
- rg of the chosen full-name suffix in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no collision.

Server validation: scompile.py compiled the module in 2.5 seconds with exit code 0
and no warnings. The docstring supplies all four proof steps of the node, including
its supporting node ids and the additional dimension argument. No statement fault
or disputed assertion was found.

## Second reading by H1

I read the sandbox node and module independently, both statement-dependency nodes,
and their recorded declarations. I read the Stacks TeX for Divisors,
`lemma-remove-embedded-points` and the surrounding associated/embedded-point
definitions. The local Stacks checkout is absent; the TeX was fetched read-only
from https://raw.githubusercontent.com/stacks/stacks-project/master/divisors.tex
into the sandbox scratchpad. Tag 02OL is also available at
https://stacks.math.columbia.edu/tag/02OL. No surrounding section hypothesis
adds quasi-compactness, separation, a base field, or nonemptiness.

The node's objects, hypotheses, and conclusion clauses, in order:

1. Object X, an arbitrary locally Noetherian scheme: `(X : Scheme.{u})
   [IsLocallyNoetherian X]`. PASS. The dependency `pqf-def-locnoeth`
   records Mathlib's class, whose field requires every affine coordinate ring
   to be Noetherian. Its existing affine-cover equivalence gives exactly the
   node's cover definition, without a stronger hypothesis.
2. Object F, a coherent O_X-module: `(F : X.Modules)` and
   `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`. PASS. I opened
   `Coherent.lean`: the recorded predicate is finite type together with finite-type
   kernels of maps from finite free modules on every open. Its carrier is the
   same sheaf-of-modules category as `X.Modules`, with no additional instance.
3. Coherent subsheaves K of F with support nowhere dense in Supp(F):
   `K : Subobject F`, and the predicate inside `Maximal` includes both
   `RingedSpace.IsCoherent ... (L : X.Modules)` and `IsNowhereDense`
   of the nonzero-stalk locus of L in the support subtype of F. PASS.
   I opened Mathlib's subobject implementation: its representative arrow is a
   monomorphism into F and its order is inclusion by factorization. Stalk exactness
   makes the representative's support a subset of Supp(F), so restricting this
   locus to the support subtype loses no points. This is relative nowhere density.
4. Existence and maximality of K: `∃ K, Maximal (...) K`. PASS.
   Mathlib's `Maximal` includes the predicate at K and comparison with every
   larger subobject satisfying it; it does not merely assert maximality without
   coherence/nowhere density, and does not require a greatest element.
5. Object F' is F/K: every subsequent occurrence uses `cokernel K.arrow`.
   PASS. This is the quotient by the same representative inclusion, not an
   unrelated quotient. Choices of representatives give isomorphic sheaves.
6. Supp(F') = Supp(F): the two sets `{x : X | ¬ Subsingleton (...stalk x)}`
   are equal. PASS. For an additive module non-subsingleton means nonzero.
7. F' has no embedded associated points: for every affine V and every ideal p
   associated to its section module, `Minimal` in that set holds. PASS.
   The TeX defines embedded primes as associated primes not minimal among
   associated primes; its affine correspondence (`lemma-associated-affine-open`,
   Tag 02OK) identifies these with the scheme points. Generalizations of a point
   of an affine open remain in that open, so the affine tests detect all embedded
   points globally. Mathlib's associated-prime definition uses radicals of
   annihilators, but its `isAssociatedPrime_iff [IsNoetherianRing R]` proves
   equivalence to actual annihilators over these affine coordinate rings.
   The categorical cokernel of coherent F by coherent K is coherent here; no
   extra coherence hypothesis on F' is needed. The scheme-only
   `associatedPoints`/`NoEmbeddedPoints` declarations concern the structure
   sheaf, not this general module, and are not usable substitutes.
8. Existence of a dense open U in X meeting Supp(F) densely:
   `∃ U : X.Opens, Dense (U : Set X) ∧ Dense {x : Supp(F) | x.val ∈ U}`.
   PASS. The two density clauses use precisely their stated ambient spaces.
9. F'|U is isomorphic to F|U: `Nonempty ((cokernel K.arrow).over U ≅ F.over U)`.
   PASS. Mathlib's sheaf-of-modules `over` is restriction to that same open.
   The source requires an isomorphism, not a selected isomorphism or an equation
   identifying a particular quotient map with it.
10. Strict support-dimension drop when dim Supp(F) is finite and positive:
    `∀ d : ℕ, 0 < d → topologicalKrullDim Supp(F) = (d : WithBot ℕ∞) →
    topologicalKrullDim Supp(K) < topologicalKrullDim Supp(F)`. PASS.
    I opened `Topology/KrullDimension.lean`: it is the chain dimension of
    irreducible closed subsets. Positive finite values are exactly the positive
    natural casts used here. This additional clause is explicitly in the node
    and its fourth proof step, rather than an assertion that it appears in 02OL.
    It follows because every irreducible closed chain in the closed nowhere-dense
    Supp(K) can be extended by an irreducible component of Supp(F) containing
    its largest member. That component cannot be contained in Supp(K): locally
    Noetherian components are locally finite, and the component has a nonempty
    relative open away from the other components. Thus a chain of length e in
    Supp(K) has e+1 ≤ d, giving the strict bound uniformly even without global
    quasi-compactness. The module docstring retains all four node proof steps.

Edge cases: the empty scheme and F = 0 are included; the support subtype and
associated-prime sets may be empty. The zero subobject is admissible. Empty
support has dimension bottom, so the finite positive conditional is inactive
for F = 0. Dimension zero and infinite dimension retain all earlier conclusions
without an extra dimension claim. For K = 0 its dimension is bottom and the
strict bound holds. There is no index set or characteristic restriction. The
explicit arbitrary universe u matches the recorded scheme-module carrier;
there are no independent test-object universes, unbound variables, or inferred
extra hypotheses. There are no definitions or new/dependency modules in this
delivery, hence no hollow data or H12/H13 additions to inspect.

Independent searches, recorded by msearch in searches.jsonl:

- leanfinder: `finite module quotient torsion embedded primes maximal submodule support`.
  Eight hits: support of module quotients, support dimension, torsion decomposition,
  and associated-prime finiteness; none is this sheaf-removal theorem.
- loogle: `IsAssociatedPrime`. Eleven hits including the definition and the
  Noetherian equivalence cited above; no removal theorem.
- msearch grep: `remove.*embedded|embedded.*prime|nowhereDense.*cokernel`.
  Zero hits in its configured search.
- leansearch: `maximal coherent subsheaf quotient no embedded points`.
  Service returned Internal Server Error; recorded unavailable, no inferred result.
- Direct rg on Mathlib, WeilConjectures, and lean/Sheaf, with `embedded`,
  `remove.*associated`, `no.?embedded`, `associatedPoints`, and `maximal.*nowhere`:
  the landed ring-theoretic affine-removal/localization statements and the
  structure-sheaf-only associated-point declarations are different objects;
  HilbertDifference uses the same affine no-embedded-prime expression. I opened
  RemoveEmbeddedPrimes and AssociatedPoints to confirm those distinctions.
- Direct rg of `exists_maximal_nowhereDense_support_cokernel` over Mathlib,
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json: no collision.

No statement mismatch was found; the Lean signature and node record are retained
verbatim. The only edit to the module clarifies in its theorem docstring why
Mathlib's radical-based associated primes and the affine formulation express
exactly the source's condition. One named theorem remains, with proof `by sorry`;
nothing is proved. Imports each supply a used notion, all lines are at most
100 characters, and the source/blueprint docstrings are present.

Validation: scompile.py compiled the edited module with exit code 0 and no
warnings. The dry run and actual delivery below supply the final preflight.
