## Worker report

The module `Sheaf.AlgebraicGeometry.PseudoCoherentTopCohomologyFinitePresentation`
states `AlgebraicGeometry.Scheme.isFinitePresentation_homology_of_isPseudoCoherent`.
Its only theorem has proof `sorry`. No definitions, helper nodes, dependency repairs,
or statement corrections are needed. The item copy changes only `lean`.

Source checked: `literature/stacks-project/cohomology.tex`,
`lemma-finite-cohomology` (Stacks Tag 08DN), both its statement and proof.
Part (2), specialized to m = n - 1, gives exactly the asserted finite presentation,
since a pseudo-coherent object is m-pseudo-coherent for every m. The existing
scheme-local finite-free definition is the characterization specified by the node.

Hypothesis and conclusion correspondence:

- A scheme X: `(X : Scheme.{u})`, with no coherence, quasi-compactness, separation,
  or Noetherian assumption.
- An object K of D(O_X): `(K : schemeDerivedCategory X)`. Its coefficient category
  is exactly `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, as in the recorded
  dependency, not the separately instanced category `X.Modules`.
- K pseudo-coherent: `(hK : X.IsPseudoCoherent K)`, using the recorded declaration.
  The explicit `[HasDerivedCategory.{w} ...]` for X and the pointwise family for
  its localized open sites are exactly the ambient localization infrastructure
  required by that predicate. They are not extra geometric hypotheses. The scheme
  universe u and derived morphism universe w are explicit and independent.
- An arbitrary integer n: `(n : ℤ)`.
- H^i(K) = 0 for every i > n: `hvanish : ∀ i : ℤ, n < i → IsZero
  ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
  (moduleRings X.toRingedSpace)) i).obj K)`. This is vanishing of the cohomology
  sheaf itself, not of its global sections or just nonnegative degrees.
- H^n(K) is a finitely presented O_X-module: the identical derived homology functor
  evaluated in degree n, followed by `.IsFinitePresentation`. Mathlib's class
  means locally the cokernel of a map between finite free sheaves, precisely
  clause (2) of def-weil-pbc-module-finite-type-presentation. It adds no choice
  of a fixed presentation or a global rank.
- The sentence excluding coherence/Noetherian assumptions is realized by their
  absence from the signature; the title's word 'nonzero' is not made a hypothesis,
  since the node's actual statement also applies when H^n(K) vanishes.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`
  signature/docstring were checked. Only Scheme occurs in this theorem.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`. The module also exposes
  `DerivedCategory.homologyFunctor`, whose definition in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` was read: it is
  the functor induced from degree-n homology of cochain complexes.
- `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`, including its full local model
  and both derived-category instance binders.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.IsFiniteType`; and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation`. The latter is the clause used here;
  both modules implement the recorded finite-type/presentation dependency.

The stated proof dependencies are imported privately, and their signatures and
source docstrings were read:
`WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact`
(`AlgebraicGeometry.open_restriction_adjunction_exact`),
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`
(`SheafOfModules.IsFiniteLocallyFree`), and
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeTopCancellation`
(`AlgebraicGeometry.Scheme.Modules.exists_local_finiteLocallyFree_top_cancellation`).
The theorem docstring carries all three DAG proof steps: choose a local bounded-above
finite-free representative; cancel acyclic top degrees finitely many times; trivialize
the last two terms and exhibit the cokernel presentation. Restriction and cancellation
on localized open sites versus actual open schemes use the existing module-category
restriction equivalence when implementing the proof.

Edge cases checked before writing:

- Empty X: local finite presentation is vacuous; no nonempty hypothesis is imposed.
- K = 0 or H^n(K) = 0: the zero sheaf has a rank-zero finite presentation.
- n = 0 and negative n: all complexes and degree quantifiers are indexed by ℤ.
- A local representative whose upper bound N is less than n: start cancellation
  at max(N,n); no descending induction from a negative natural number is needed.
- Unboundedness below: neither the statement nor the local model requires a lower
  bound, and the proof changes only finitely many upper degrees.
- Non-Noetherian/noncoherent schemes and varying local finite ranks: none are
  excluded. Only top cohomology is concluded finitely presented, not all lower
  cohomology sheaves.

Searches for an existing statement (all run through the prescribed tools):

- `msearch.py leanfinder`, query "The top cohomology sheaf of a pseudo-coherent
  complex on a scheme vanishing above degree n is finitely presented": eight
  results, all finite-presentation definitions or related presentation data;
  none states the pseudo-coherent cohomology theorem.
- `msearch.py leansearch`, query "The top cohomology sheaf of a pseudo-coherent
  complex on a scheme is finitely presented": eight results, all finite-presentation
  definitions, constructors, and related data; no theorem match.
- `msearch.py loogle`, query `"PseudoCoherent"`: zero hits.
- `msearch.py grep`, query
  `[Pp]seudo[Cc]oherent.*[Ff]inite[Pp]resentation|[Ff]inite[Pp]resentation.*[Hh]omology`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for pseudo-coherence combined
  with finite presentation/homology, and the item id: hits concerned ring-level
  pseudo-coherence and Noetherian criteria, not the present scheme theorem;
  the item id has no upstream occurrence. A separate search for finite presentation
  and homology found `PerfectNoetherianCohomology.lean`; its helper
  `finitePresentation_homology` was read and assumes a locally Noetherian scheme,
  so it does not match this theorem. The new full declaration name was also checked
  against Mathlib, both project trees, and `dag/lean_names_upstream.json`: absent.

Validation: `scompile.py Q142 lem-sfb-pseudocoherent-top-cohomology-fp` compiled
both its sandbox probe and its library module successfully (19.9 s and 2.2 s).
No errors or unexpected warnings. `set_option autoImplicit false` and explicit
universe declarations prevent implicit unbound variables. All lines are at most
100 characters. The JSON signature is copied verbatim from `theorem` to before `:=`.

No statement dispute or node fault was found. The maintainer provides the independent
review, as required by the current worker-direct-delivery brief.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
