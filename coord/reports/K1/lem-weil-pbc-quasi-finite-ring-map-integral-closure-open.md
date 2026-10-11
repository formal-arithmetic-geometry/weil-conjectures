## Worker report

The module `Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen` states
`Algebra.quasiFinite_integralClosure_open`, with a single sorry and the full ten-step
DAG proof in its docstring. Nothing is proved. No new nodes, dependency modules,
or statement corrections are needed.

Hypothesis and clause correspondence:

- Commutative rings and the arbitrary ring map R → S: `(R : Type u) (S : Type v)`
  with `[CommRing R] [CommRing S] [Algebra R S]`; the map is `algebraMap R S`.
  Any commutative ring map defines such an algebra, without injectivity assumptions.
- Finite type: `[Algebra.FiniteType R S]`.
- Quasi-finite at every prime: `hq : ∀ q : PrimeSpectrum S,
  IsQuasiFiniteAtPrime R S q`, using the recorded isolated-fibre-prime definition,
  rather than replacing it by Mathlib's differently presented `QuasiFiniteAt`.
- S′ is the actual integral closure: `integralClosure R S`.
- Clause (1): `Topology.IsOpenEmbedding (PrimeSpectrum.comap
  (integralClosure R S).val.toRingHom)` is precisely a homeomorphism onto an open
  image. This is the underlying map of the inclusion-induced Spec morphism.
- Clause (2): the universal binder `∀ g : integralClosure R S` and the inclusion
  `(PrimeSpectrum.basicOpen g : Set ...) ⊆ Set.range (PrimeSpectrum.comap ...)`
  express exactly the principal-open image condition. `Function.Bijective
  (Localization.awayMap ... g)` says the canonical ring homomorphism between the
  two away localizations is an isomorphism, not merely an unspecified equivalence.
- Clause (3): `∃ T : Subalgebra R S` expresses a subring containing the image of R;
  `T ≤ integralClosure R S` places it inside S′; `Module.Finite R T` gives finite
  generation over R with its inherited action. The next open-embedding and
  localization-bijectivity conjuncts repeat clauses (1) and (2) for T. Finally,
  `IsOpenImmersion (Spec.map (CommRingCat.ofHom T.val.toRingHom))` is the stated
  scheme-theoretic open immersion.

Recorded dependency declarations read and used:

- `Sheaf.RingTheory.QuasiFiniteAtPrime`: `Algebra.IsQuasiFiniteAtPrime`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure` (and its
  carrier `IsIntegral`, read in `IsIntegral/Defs.lean`; the recorded ancillary
  `IsIntegrallyClosedIn` was read in `IntegrallyClosed.lean` but is not needed).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, used through
  `Localization.awayMap` from `Mathlib.RingTheory.Localization.Away.Basic`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` (available through imports).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.

Edge cases: neither R nor S is assumed a domain, reduced, Noetherian, or nontrivial.
For the zero ring S the primewise hypothesis is vacuous and Spec S is empty; the
closure and a finite subalgebra may be the zero ring, so all conclusions still
hold. The zero base forces the zero target and is covered. For g = 0 (and any
nilpotent g), D(g) is empty and both away localizations are zero rings, so (2) is
valid; for a unit g the condition says the entire spectrum is in the image and
asks for exactly the resulting global isomorphism. R and S have independent
universes u and v; T and the integral closure are subtypes of S and have universe v,
so the Spec morphism is well typed without equating u and v. No test-object universe
or nonempty-spectrum condition occurs. All universes and variables are explicit.

Searches (2026-10-11):

- `msearch.py ... leanfinder "For a finite type algebra quasi-finite at every prime
  the spectrum embeds as an open subset of the integral closure and of a finite
  subalgebra"`: eight hits, on quasi-finite fibre criteria and the converse
  integral/localization implication; no global affine theorem.
- `msearch.py ... loogle "Algebra.QuasiFiniteAt, integralClosure"`: two hits,
  `Algebra.exists_notMem_and_isIntegral_forall_mem_of_ne_of_liesOver` and
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux`; neither is this
  theorem.
- `msearch.py ... grep "integralClosure|IsOpenEmbedding|awayMap"
  RingTheory/ZariskisMainTheorem.lean`: five hits, including
  `Algebra.ZariskisMainProperty` and its pointwise canonical away map. No global
  open embedding/finite-subalgebra conclusion.
- `rg` in the project's `lean/Sheaf` and the read-only upstream `WeilConjectures`
  for `integralClosure`, `00QB`, this node id, and subsequently
  `IsOpenEmbedding.*comap|basicOpen.*Set.range|quasiFinite_integralClosure`:
  only unrelated ramification, normalization, and basic-open results, no match.
  The exact node id also has no match in `dag/lean_names_upstream.json`.

The local literature checkout lacks the Stacks TeX files, so the source statement
and proof were read from [Stacks 00QB](https://stacks.math.columbia.edu/tag/00QB)
and its geometric reformulation from [Stacks 03GU](https://stacks.math.columbia.edu/tag/03GU).
They agree with the node; no STATEMENT-DISPUTED issue arose.

Validation: server single-file compile succeeded; its initial two long-docstring-line
warnings were corrected before the final compile and delivery dry run. Independent
second reading is left to the designated second reader.

## Second reading by K1

Independent reading on 2026-10-11, with the node and the complete module open.
Verdict: the statement matches the node hypothesis by hypothesis and clause by
clause; no mathematical or Lean correction is needed. Only this review section
was added. The worker report remains in place.

Source check: the local Stacks checkout is absent. I read the actual TeX lemma
and proof from `https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex`
(label `lemma-quasi-finite-open-integral-closure`, Tag 00QB), and from
`https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex`
(label `lemma-quasi-finite-affine`, Tag 03GU), as well as the rendered tag pages.
00QB has finite type and quasi-finiteness, the integral closure, and all three
clauses; 03GU expressly gives the open immersion reformulation. There is no
Noetherian, domain, reducedness, injectivity, field, or characteristic assumption.

Object/hypothesis/conclusion checklist, in the node's order:

1. Commutative rings R and S: `(R : Type u) (S : Type v)` and `[CommRing R]`
   `[CommRing S]`. Exact; neither is required to be nontrivial.
2. Arbitrary ring map phi: `[Algebra R S]`, whose map is `algebraMap R S`.
   Exact for commutative rings: every ring homomorphism gives this algebra
   structure, with no injectivity or extra condition.
3. Finite type of that map: `[Algebra.FiniteType R S]`. Exact finite generation
   as an R-algebra, not finiteness as a module.
4. Quasi-finite at every prime q of S: `(hq : ∀ q : PrimeSpectrum S,
   IsQuasiFiniteAtPrime R S q)`. Exact. I opened the dependency node and
   `Sheaf.RingTheory.QuasiFiniteAtPrime`: its definition takes the finite-type
   instances already present and asks that the singleton of the corresponding
   fibre prime be open. `PrimeSpectrum.preimageHomeomorphFiber` takes the fibre
   over the contraction of q and identifies it with the spectrum of
   `p.asIdeal.Fiber S`. The tensor factor order is the canonical commuted form
   of the node's fibre ring and does not change its prime or topology.
5. S', the actual integral closure subring of S containing phi(R):
   `integralClosure R S`. Exact: Basic.lean defines its carrier by `IsIntegral`
   and includes `algebraMap_mem'`; IsIntegral/Defs.lean uses the given algebra
   map and a monic polynomial root. No abstract substitute is introduced.
6. Inclusion-induced spectrum map, on primes by contraction:
   `PrimeSpectrum.comap (integralClosure R S).val.toRingHom`, and for T,
   `PrimeSpectrum.comap T.val.toRingHom`. Exact direction Spec S -> Spec T.
   The scheme map in the last clause is `Spec.map (CommRingCat.ofHom
   T.val.toRingHom)`; Scheme.lean defines Spec.map on the same ring map.
7. D(g) and the canonical localization map: `PrimeSpectrum.basicOpen g`
   has carrier `{p | g ∉ p.asIdeal}`. `Localization.awayMap f g` has type
   `Localization.Away g →+* Localization.Away (f g)` and is the localization
   map induced by f. These are precisely the node's opens and fraction maps.
8. Clause (1): `Topology.IsOpenEmbedding` of the inclusion-induced comap.
   Exact: the structure extends an embedding with `isOpen_range`, expressing
   a homeomorphism onto an open image.
9. Clause (2): `∀ g : integralClosure R S, D(g) ⊆ Set.range (...) →
   Function.Bijective (Localization.awayMap ... g)`. Exact universal
   quantification with exactly the image condition; bijectivity of this
   particular ring homomorphism means it is a ring isomorphism, not merely
   existence of some unrelated ring equivalence.
10. Clause (3), choice and containment of S'': `∃ T : Subalgebra R S,
    T ≤ integralClosure R S`. Exact: a subring of S containing phi(R) is
    precisely an R-subalgebra; the order condition puts it inside S'.
11. Finite R-module via phi: `Module.Finite R T`. Exact; the inherited
    subalgebra action is the corestriction of phi. Finiteness/Defs.lean defines
    Module.Finite by finite generation of the top submodule.
12. Clauses (1) and (2) for the same S'': the open-embedding and universally
    quantified awayMap-bijectivity conjuncts follow inside the existential
    binder for T. Exact, with the same image condition and canonical maps.
13. Scheme open immersion for that same S'': `IsOpenImmersion (Spec.map
    (CommRingCat.ofHom T.val.toRingHom))`. Exact. I read the dependency node,
    the scheme abbreviation in OpenImmersion.lean and its locally ringed
    space/presheafed space definition: an open embedding together with
    isomorphisms of the structure sheaf on the corresponding opens.

All six statement dependency nodes and their recorded declarations/signatures
were opened. The used recorded notions are compatible and require no missing
instances. No new definition nodes or dependency modules are delivered. There
is no statement_change and no corrected-statement/citer review is applicable.

Edge cases: if S is the zero ring its spectrum is empty and the primewise
hypothesis is vacuous; its integral closure and any subalgebra are zero rings,
so the conclusions hold, including module finiteness and the empty open
immersion. A zero base forces a zero target. For g = 0 or nilpotent g, D(g)
is empty and both away localizations are zero rings. For invertible g the
image condition is the full-spectrum condition and correctly demands the
canonical global isomorphism. Empty finite choices and n = 0 in the proof
are not ruled out by the statement. There are no indexed families or
characteristic restrictions. The independent explicit universes u and v
cover every pair of rings; the closure and T are subtypes of S in v, so the
scheme morphism uses one universe without restricting R. All variables and
universes are bound by eye.

Independent reuse searches (queries different from the worker's):

- LeanFinder via msearch: "Zariski main theorem an affine quasi finite morphism
  factors through the spectrum of a module finite subalgebra as an open
  immersion". Eight hits, all affine finite-type/quasi-finite criteria and
  finite-morphism section lemmas; none states the global conclusion.
- Loogle via msearch: `integralClosure, PrimeSpectrum.comap`. Zero hits.
- LeanSearch via msearch: "A finite type ring homomorphism quasi finite at all
  primes has spectrum open in the integral closure". Service unavailable
  (Internal Server Error); recorded as unavailable, no verdict inferred.
- Mathlib grep via msearch: `00QB|03GU|exists_fg_and_exists_notMem_and_awayMap_bijective`
  in RingTheory/ZariskisMainTheorem.lean. Five hits for pointwise results.
  I opened lines 660-710: each chooses a subalgebra and an element at one
  fixed prime, not a global open embedding or all principal opens in its image.
- rg on the complete upstream WeilConjectures tree, project lean/Sheaf and
  dag/lean_names_upstream.json for `00QB`, `03GU`, this declaration name,
  `IsOpenEmbedding.*comap` and `integralClosure.*IsOpenImmersion`, and a broader
  integralClosure/open-immersion search in RingTheory. Only unrelated
  normalization, ramification, finite-product closure and the pointwise
  ZariskisMainAway module; no existing realization of this node.

H5/H6/H8/H9: there are no definitions, hence no hollow definition, and only
one theorem with proof `by sorry`. The module and theorem docstrings name
00QB/03GU and the exact blueprint id. The theorem's docstring carries all ten
node proof steps, including their dependency citations; the prose replacements
of two long displayed equations retain their mathematical content. Imports
supply the primewise hypothesis, integral closure, canonical awayMap and scheme
open immersion, with no private replacement definitions or duplicate names.
No line exceeds 100 characters. The node's lean.statement was compared to the
signature through the end of the conclusion and agrees verbatim.

Validation: scompile.py on the absolute sandbox module path compiled cleanly
on the server in 1.7 seconds, with no warnings. The initial relative-path
invocation failed to find the file in the read-only repository; rerunning
with the correct absolute sandbox path resolved it without file changes.
