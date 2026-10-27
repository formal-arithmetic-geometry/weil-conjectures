## Worker report

The module `Sheaf.RingTheory.WeaklyEtaleNormalRing` states
`RingHom.WeaklyEtale.isNormalRing`, with exactly one postponed theorem and no new
definitions. Its proof is `sorry`; its docstring supplies the node's four-step
refinement, etale-stage, colimit and descent proof. The node copy changes only
`lean`. There is no statement correction, dispute, new node or dependency repair.

Clause-by-clause correspondence:

- Arbitrary commutative rings A and B, possibly in different universes, are
  `{A : Type u} {B : Type v} [CommRing A] [CommRing B]`, with `universe u v`
  explicitly declared and `autoImplicit false`.
- The unital ring map is `{f : A →+* B}`. Its weak etaleness is
  `(hf : f.WeaklyEtale)`. I read `RingHom.WeaklyEtale` in
  `WeilConjectures.RingTheory.ProEtale.WeaklyEtale`: it installs precisely
  `f.toAlgebra` and uses `Algebra.WeaklyEtale`. I read that Mathlib class in
  `Mathlib.RingTheory.Etale.Weakly`: its fields are `Module.Flat A B` and
  flatness of `Algebra.TensorProduct.lmul' A (S := B)`. This is exactly the
  two flatness conditions in the node, with no choice of an unrelated algebra.
- Normality of A is `(hA : ∀ (p : Ideal A) [p.IsPrime],
  IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))`.
  This is the dependency's prescribed inline normal-ring form. `IsDomain`
  includes nontriviality; `IsIntegrallyClosed` means integral closedness in
  `FractionRing`; `Localization.AtPrime p` localizes at the prime complement.
- Normality of B is exactly the conclusion `∀ (q : Ideal B) [q.IsPrime],
  IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)`.
  Both the domain and integral-closedness clauses are present for every prime.
- No `IsNoetherianRing`, `IsDomain A`, `IsDomain B`, finite presentation,
  locality, faithful flatness, injectivity or common-universe hypothesis occurs.
- Neither ring has a `Nontrivial` assumption. The zero target has no primes,
  and the conclusion is vacuous. For the zero source, unitality of `f` forces
  the target to be zero, as required; this is explanatory content of the node,
  not an additional conjunct or hypothesis.

Dependency declarations read and used:

- `def-weil-pbc-ind-etale-algebra` records
  `Sheaf.RingTheory.IndEtaleUniverseTransport`; its public dependency
  `Sheaf.RingTheory.IndPrincipalZariski` exposes `Algebra.WeaklyEtale` and the
  upstream `RingHom.WeaklyEtale`. The item imports that recorded module publicly.
  The repaired cross-universe ind-etale predicate does not restrict the
  already universe-polymorphic weakly etale predicate.
- `def-weil-pbc-normal-ring` records
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`,
  and the inline form above using `IsDomain` and `Localization.AtPrime`.
  The integral-closure and prime-localization modules are public imports.
- The following recorded proof modules are ordinary imports, following the
  stage-2 proof-dependency rule. I read each declaration and its docstring:
  `WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale`,
  `RingHom.WeaklyEtale.exists_indEtale_comp` (097Z refinement in a common universe);
  `WeilConjectures.RingTheory.EtaleNormalRing`,
  `RingHom.Etale.isNormalRing` (arbitrary normal base);
  `WeilConjectures.RingTheory.FilteredColimitNormalRing`,
  `CommRingCat.isNormal_of_filtered_colimit` (no transition-map condition);
  `Sheaf.RingTheory.FaithfullyFlatNormalRingDescent`,
  `Algebra.normal_ring_of_faithfullyFlat` (independent universes).

Source check: I opened `literature/stacks-project/more-morphisms.tex`,
`lemma-normal-goes-up` (Tag 0950). It asserts normality ascent for an arbitrary
weakly etale morphism, hence precisely the affine assertion here. I also read
`proetale.tex`, `proposition-weakly-etale` (097Z), which gives the refinement
used by the node's proof. The source route and all four recorded proof
statements agree; no extra hypothesis is needed to state the result.

Edge cases checked before writing: A=B=0; B=0 over a nonzero normal A; identity
maps; projections k×k → k (normal base need not be a domain, map need not be
injective or faithfully flat); Z → Z[1/2] (not faithfully flat); general
non-Noetherian normal bases; independent source and target universes. The
prime-local formulation retains all these cases and excludes ramified maps
through the actual weak-etaleness hypothesis.

Searches actually run for this stage-2 attempt:

- `msearch.py leanfinder`: "A weakly etale algebra over a normal commutative
  ring is normal without a Noetherian hypothesis". Eight hits, including
  `Algebra.Etale`, standard-etale instances and etale finite-generation
  results; none gives arbitrary weakly etale normality ascent.
- `msearch.py loogle`: `Algebra.WeaklyEtale, IsIntegrallyClosed`. Zero hits.
- `msearch.py grep`:
  `(WeaklyEtale|IndEtale).*(normal|IsIntegrallyClosed)|(normal|IsIntegrallyClosed).*(WeaklyEtale|IndEtale)`.
  Zero Mathlib hits.
- `msearch.py leansearch`: "Normality ascends along arbitrary weakly etale
  ring homomorphisms". Eight hits concerning etale maps, their local
  properties, base change, composition and formal etaleness; no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  weakly-etale/normality names. No declaration bears this blueprint id.
  I opened `Algebra.WeaklyEtale.isDomain_localization_of_isIntegrallyClosed`
  in `WeilConjectures.RingTheory.ProEtale.RegularLocalization`: it concludes
  only `IsDomain` of each target localization, omitting integral closedness.
  Thus it is not the item's statement. `RingHom.Etale.isNormalRing` requires
  etaleness and is also not an exact match. No existing declaration was copied.

The prior dispatcher message reported a preflight refusal based on Q157's
review. I read Q157's live report: it explicitly records a stage-1 split with
no Lean files or compilation. The current node has `reviewed` but no `lean`
or `reviewed_lean`. This packet supplies the missing stage-2 statement and
preserves Q157's reviewed split.

Validation: prescribed `scompile.py Q128 lem-sfb-weakly-etale-normal-ring-ascent`
compiled this file in both sandbox and library-module modes, taking 2.0 s and
2.4 s respectively, with exit code 0 and no errors or unexpected warnings.

## Second reading by Q128

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
