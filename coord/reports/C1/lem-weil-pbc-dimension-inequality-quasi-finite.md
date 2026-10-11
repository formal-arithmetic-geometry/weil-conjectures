## Worker report

The module `Sheaf.RingTheory.QuasiFiniteLocalDimension` states
`Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime`, with its proof left as `sorry`.
The statement agrees with [Stacks Tag 00QF](https://stacks.math.columbia.edu/tag/00QF),
read online because the cited `literature/stacks-project/algebra.tex` is absent on this machine.
No correction, new node, or dependency module is needed.

Hypothesis and conclusion correspondence:

- Commutative rings R and S: `(R : Type u) (S : Type v) [CommRing R] [CommRing S]`.
  The universes are independent and explicitly declared.
- The ring map R → S: `[Algebra R S]`, with map `algebraMap R S`.
  An algebra structure over commutative rings is exactly the data of such a map;
  no injectivity, flatness, or locality is assumed.
- Finite type: `[Algebra.FiniteType R S]`, the recorded Mathlib definition.
- Prime q of S: `(q : PrimeSpectrum S)`, bundling an ideal with its primality proof.
- Its inverse image p in R: `(q.comap (algebraMap R S)).asIdeal`.
  Thus p is defined from q and the given map; there is no extra independent prime
  or extra lies-over hypothesis to impose.
- Quasi-finite at q: `(hq : IsQuasiFiniteAtPrime R S q)`, using the recorded dependency.
- The two local rings: `Localization.AtPrime q.asIdeal` and
  `Localization.AtPrime (q.comap (algebraMap R S)).asIdeal`.
- Their Krull dimensions and the inequality: `ringKrullDim` of those rings, with
  the target-local dimension on the left of `≤` and base-local dimension on the right.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`, `Algebra.FiniteType`: finitely generated algebra.
  Available through the imported dependency module.
- `Sheaf.RingTheory.QuasiFiniteAtPrime`, `Algebra.IsQuasiFiniteAtPrime`: the singleton
  of the canonical corresponding fibre prime is open. Its full definition was read.
- `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`: the order-theoretic
  dimension of the prime spectrum, valued in `WithBot ℕ∞`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`: localization
  at the complement of a prime, available through the fibre-ring dependency imports.
  The other declarations in that dependency record, `Ideal.ResidueField` and
  `Ideal.Fiber`, were also read; they occur within the recorded quasi-finite predicate.

The declaration docstring gives all three proof steps of the node, with dependency IDs:
Zariski Main Theorem and localization identify S_q with T_q'; integral incomparability
contracts strict prime chains; the local dimension suprema give the inequality and
are preserved under the ring isomorphism. No proof is attempted in stage 2.

Edge cases checked before writing: a zero ring S has no q, so the statement is
vacuous; a map from a zero ring likewise gives no q. A field base has local dimension
zero, and a quasi-finite fibre prime is isolated and zero-dimensional as required.
The identity map gives equality. Noninjective maps are allowed. Infinite dimensions
are retained by `WithBot ℕ∞`, rather than converted to natural numbers. There is no
Noetherian assumption, no finiteness assumption on dimension, and no characteristic
restriction. Primes need not be maximal. Both ring universes are arbitrary.

Searches (actual remote-search queries are saved in searches.jsonl):

- `msearch.py leansearch`: “For a finite type algebra quasi-finite at a prime the Krull
  dimension of the localization is at most the dimension of the base localization”.
  Service unavailable (Internal Server Error); no verdict inferred.
- `msearch.py leanfinder`: “quasi-finite algebra local Krull dimension inequality at prime”.
  Eight hits, including `IsLocalization.AtPrime.ringKrullDim_eq_height` and unrelated
  dimension bounds for quotients and localizations; none compares these local rings.
- `msearch.py loogle`: `Algebra.QuasiFiniteAt, ringKrullDim`. Zero hits.
- `msearch.py grep`: `quasiFinite.*(dim|height)|(dim|height).*quasiFinite`, restricted
  to Mathlib/RingTheory. Zero hits.
- `rg` with the same pattern and the item ID in upstream `WeilConjectures` and
  project `lean/Sheaf`: only an existing docstring in `Etale/LocalDimension.lean`
  cites this missing theorem; it does not declare it.
- Broader `rg -i 'quasi.?finite|dimension.*inequality'` over upstream and project
  RingTheory found the existing quasi-finite predicate and unrelated completion
  statements, not this inequality. `grep -rn` of the item ID over upstream found none.
- Exact proposed name `ringKrullDim_le_of_isQuasiFiniteAtPrime` searched in Mathlib,
  upstream, project sources, and `dag/lean_names_upstream.json`: no existing declaration.

Validation: the prescribed single-file server compile and the delivery dry run are
run for this module. The final worker response is READY only after the dry run prints OK.

## Second reading by C1

Read the sandbox node and module independently against Stacks Algebra Tag 00QF,
`lemma-dimension-inequality-quasi-finite`. The local Stacks source is absent; read
the official tag page and the upstream `stacks/stacks-project` algebra.tex online,
including its Conventions section and the surrounding Dimension of fibres section.
The current upstream label is at lines 28520–28541 (the node cites an older numbering).
The conventions explicitly allow the zero ring and noninjective maps. The section
imposes no additional standing hypothesis; Noetherianity is only one branch of the
proof, not a hypothesis of the lemma.

Object, hypothesis, and conclusion checklist (all verdicts: exact):

1. Two commutative unital rings R and S: `(R : Type u) (S : Type v)` with
   `[CommRing R] [CommRing S]`. Independent explicitly bound universes impose no
   size equality or smallness restriction.
2. A homomorphism R → S: `[Algebra R S]`, represented by `algebraMap R S`.
   For commutative rings every unital ring map gives this algebra structure; no
   injectivity, flatness, or local-map condition is imposed.
3. Finite type: `[Algebra.FiniteType R S]`. Opened the dependency node and
   Mathlib/RingTheory/FiniteType.lean:39: finite generation of the top subalgebra
   is precisely finite generation as R-algebra, including zero generators.
4. A prime ideal q in S: `(q : PrimeSpectrum S)`; its underlying ideal is
   `q.asIdeal`. Bundled primality supplies exactly the required hypothesis.
5. The inverse-image prime p in R: `q.comap (algebraMap R S)`, with underlying
   ideal `(q.comap (algebraMap R S)).asIdeal`. It is determined by q and the map,
   as in the node; no separate prime or additional lies-over condition is needed.
6. Quasi-finiteness at q: `(hq : IsQuasiFiniteAtPrime R S q)`. Opened the
   dependency node and the complete landed module QuasiFiniteAtPrime.lean. Its
   definition takes p as this comap and asks for `IsOpen {e ⟨q, rfl⟩}` in
   `PrimeSpectrum (p.asIdeal.Fiber S)`, where e is
   `PrimeSpectrum.preimageHomeomorphFiber R S p`. Opened that Mathlib declaration:
   it is a homeomorphism from the fibre subspace to the fibre-ring spectrum.
   Thus this is exactly the isolated corresponding fibre prime of Stacks 00PL/00PK.
   `Ideal.Fiber` has tensor factors κ(p) and S in the reverse order to the node;
   the canonical tensor commutation identifies the rings and corresponding points.
7. Local rings S_q and R_p: `Localization.AtPrime q.asIdeal` and
   `Localization.AtPrime (q.comap (algebraMap R S)).asIdeal`. Opened the
   localization dependency node and Mathlib/Localization/AtPrime/Basic.lean:57:
   this is localization at the complement of the prime. Also read
   `Ideal.ResidueField` and `Ideal.Fiber`, used by the quasi-finite dependency.
8. The sole conclusion dim S_q ≤ dim R_p: exactly `ringKrullDim` of the first
   localization `≤` `ringKrullDim` of the second. Opened the Krull-dimension node
   and Mathlib/KrullDimension/Basic.lean:30: the value is `WithBot ℕ∞`, retaining
   both empty spectra and unbounded prime-chain lengths. All rings, structures,
   q, and hq precede the conclusion; no conclusion clause or quantifier is lost.

Edge cases: S = 0 has no q; R = 0 forces S = 0 for a unital map, so both cases
are vacuous without adding nontriviality. Empty affine schemes are covered by the
same observation. The identity map permits equality; a field base permits local
dimension zero. Zero algebra generators and prime chains of length zero are
included. There is no index-set binder or integer n in this lemma. Nonmaximal
primes, noninjective maps, arbitrary characteristic, non-Noetherian rings, and
infinite dimensions are all allowed. No variable or universe is unbound.

Independent searches used different wording from the worker:

- LeanFinder via msearch.py: `prime height bound under finite type homomorphism
  isolated fiber point`. Eight hits; opened `Ideal.height_le_height_add_of_liesOver`
  in KrullsHeightTheorem.lean. It assumes Noetherian rings and concludes a bound
  involving a fibre height, so it is not this general statement.
- Loogle via msearch.py: `Localization.AtPrime, ringKrullDim, Algebra.FiniteType`.
  Zero hits.
- `rg -n -i '(height|krulldim|dimension).*(quasi.?finite|isolated)|
  (quasi.?finite|isolated).*(height|krulldim|dimension)'` across all upstream
  WeilConjectures, project lean/Sheaf, and Mathlib/RingTheory. Opened the upstream
  scheme QuasiFinite module: `topologicalKrullDim_eq_of_surjective` concerns whole
  schemes with universally closed, surjective morphisms, while
  `coheight_apply_of_flat` adds flatness; neither is the node's statement.
  Opened `RingHom.QuasiFinite.comp_of_ringKrullDim_le_one`: it concerns a quotient
  of a curve over a field and concludes quasi-finiteness, not a local dimension
  inequality. The project's Etale/LocalDimension module merely cites this node
  in its proof docstring. No matching existing statement was found.
- Exact proposed declaration name in Mathlib, upstream WeilConjectures, project
  lean/Sheaf, and dag/lean_names_upstream.json: absent.

No mismatch found and no Lean or node change made. There are no new definition
nodes, dependency modules, or statement corrections in this delivery. The imports
are used; both docstrings cite 00QF and this blueprint node. The theorem docstring
faithfully carries all three node proof steps: pointwise Zariski Main identifies
the localizations; integral incomparability contracts strict chains below q';
suprema of chain lengths and the ring isomorphism give the stated inequality.
The module contains only this theorem with `sorry`, no new definitions or proved
theorems; every line is within 100 characters. The recorded `lean.statement`
matches the signature verbatim. Validation uses the prescribed server single-file
compile followed by deliver2.py dry run and delivery.
