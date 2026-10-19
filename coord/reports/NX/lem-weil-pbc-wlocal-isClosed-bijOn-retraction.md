## Worker report

Existing declaration: `exists_retraction_of_isClosed_of_bijOn` in
`WeilConjectures.RingTheory.ProEtale.WContractible`, lines 511–523, read in the
read-only group clone (and located in the slopmaster2 source too). No new module
or duplicate statement is supplied. The theorem is already proved upstream.
Its complete signature is recorded verbatim, excluding `:= by`; the surrounding
section binds `universe u`, `{R : Type u}`, and `[CommRing R]`.

Clause correspondence after the recorded source-based correction:

- Commutative rings: section parameters `{R : Type u} [CommRing R]` and
  `{S : Type u} [CommRing S]`.
- Both rings w-local: `[IsWLocalRing R]` and `[IsWLocalRing S]`.
- R-algebra structure on S and its canonical map: `[Algebra R S]`, `algebraMap R S`.
- Bijections on every prime stalk: `hbos : (algebraMap R S).BijectiveOnStalks`.
  The definition quantifies over every prime ideal p of S and requires
  bijectivity of `Localization.localRingHom (p.comap (algebraMap R S)) p ... rfl`.
- Every closed point contracts to a closed point: `hcl`, with membership in
  `closedPoints (PrimeSpectrum S)` and in `closedPoints (PrimeSpectrum R)`.
- Closed subset of the component space: `T : Set (ConnectedComponents
  (PrimeSpectrum S))` and `hT : IsClosed T`.
- The induced contraction map is `(PrimeSpectrum.continuous_comap
  (algebraMap R S)).connectedComponentsMap`.
- Surjectivity of its restriction: `hsurjT`, for every target component a
  preimage t belonging to T. Injectivity of its restriction: `hinjT`, equal
  images of two members of T imply equal components.
- Retraction: `∃ f : S →+* R, f.comp (algebraMap R S) = RingHom.id R`.

Dependency declarations read: `IsWLocalRing` in
`WeilConjectures.RingTheory.ProEtale.WLocal` (prime spectrum a `WLocalSpace`),
`Localization.AtPrime` in `Mathlib.RingTheory.Localization.AtPrime.Basic`,
`Ideal.ResidueField` in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, and
`Ideal.Fiber` in `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`.
The last two belong to the bundled dependency but are not needed by this theorem.
The stalk predicate is the existing `RingHom.BijectiveOnStalks` in
`WeilConjectures.RingTheory.ProEtale.StalkIso`, not a new definition.

Source checked: local Stacks proetale.tex, Tag 09AZ, proof (3) to (1), lines
1075–1086. The image T is closed and maps homeomorphically onto the target
component space. The existing theorem's docstring and full proof were read:
restrict S to T, preserve w-locality, closed-point contraction and stalk
bijections, identify components bijectively, then invert the resulting ring
isomorphism and compose with S → Restriction T.

Edge cases: T empty cannot cover a nonempty target spectrum; this explains the
correction below. Zero rings and empty spectra are allowed, with no Nontrivial
hypothesis added. For the identity map and T the entire component space the
identity retraction works. Arbitrary ring sizes fit the common arbitrary
universe by taking its maximum; no nontriviality, finiteness or countability
restriction is present.

Searches made with msearch.py: LeanFinder, "A stalkwise bijective map of w-local
rings with a closed subset bijective on connected components admits a ring
retraction": eight generic stalkwise/localization hits, no retraction theorem.
Loogle, `RingHom.BijectiveOnStalks, ConnectedComponents`: zero hits (unknown
upstream identifier). Mathlib grep, `BijectiveOnStalks|IsWLocalRing|exists_retraction`
in RingTheory: zero hits. Direct rg in upstream WeilConjectures found the exact
`exists_retraction_of_isClosed_of_bijOn` at WContractible.lean:511; an item-id
search found no blueprint tag there. Direct rg in lean/Sheaf found no duplicate.
The group clone's exact source and coord/pefw-upstream-framework.md were read.

## Statement corrected

Old statement, verbatim:

Let R and S be commutative rings with R and S w-local [def-weil-pbc-w-local], equipped with an R-algebra structure on S. Assume the algebra map R \to S induces bijections on all prime stalks [def-weil-pbc-localization-at-prime], and every closed point of Spec S contracts to a closed point of Spec R. Let T be a closed subset of the connected-component space π₀(Spec S). If the map π₀(Spec S) \to π₀(Spec R) induced by contraction is surjective and injective on T (equivalently, its restriction to T is bijective), then there exists a ring map f:S\to R with f\circ(R\to S)=\mathrm{id}_R.

The global-surjectivity reading of "surjective and injective on T" is not
equivalent to the parenthetical bijectivity of the restriction: take the
identity map of F₂ and T empty. The source explicitly chooses a closed image T
mapping homeomorphically onto the target component space. The correction
therefore requires the restriction to T to be bijective, exactly `hsurjT` and
`hinjT` of the upstream theorem. This auxiliary node is not the unit's own
statement. No dependency or proof fields changed. No STATEMENT-DISPUTED remains.

Complete citer audit (all node files searched for stmt_deps/proof_deps):

- `lem-weil-pbc-wlocal-closed-component-retraction`: holds true; Its hypothesis already requires the restriction h|_T to be bijective; proof step 3 supplies precisely hsurjT and hinjT.

## Second reading by NX

Read the corrected node against proetale.tex, Tag 09AZ, proof (3) to (1),
before comparing the Lean. The source chooses a closed image T mapping
homeomorphically onto the target component space, then restricts the ring to
that union of components. Thus the correction resolves the ambiguous scope of
surjectivity in the old wording; it does not add a source-extraneous hypothesis.
The faithful-flatness and extremal-disconnectedness assumptions of the full
Stacks lemma are used to obtain T, not in the auxiliary restriction argument
once T and its bijection are supplied. The auxiliary theorem's complete proof
at WContractible.lean:524–628 confirms this distinction.

Object/hypothesis/conclusion checklist (all verdicts: exact match):

1. R is a commutative ring: the enclosing `universe u` and
   `variable {R : Type u} [CommRing R]` supply it. These are bound section
   parameters, not free variables in the declaration.
2. S is a commutative ring: `{S : Type u} [CommRing S]`.
3. Both spectra are w-local: `[IsWLocalRing R] [IsWLocalRing S]`.
   Opened the dependency node and WLocal.lean:30, then WLocal/Basic.lean:29.
   The class means `WLocalSpace (PrimeSpectrum R)`: closed closed-point set
   and unique closed specialization in a spectral space. Its component/closed
   point homeomorphism gives the node's unique closed point per component.
   Prime spectra already have the required spectral structure.
4. S is equipped with an R-algebra structure: `[Algebra R S]`. Its specified
   ring map is exactly `algebraMap R S`, with no injectivity or flatness instance.
5. Bijective prime stalk maps: `hbos : (algebraMap R S).BijectiveOnStalks`.
   Opened StalkIso.lean:41: this quantifies over all prime ideals p of S and
   requires `Function.Bijective (Localization.localRingHom (p.comap f) p f rfl)`.
   Opened the localization dependency and Mathlib's `Localization.AtPrime`:
   this is localization at the complement of the prime, exactly the source's
   local ring map. The dependency's residue-field and fibre declarations were
   also read; they are not extra hypotheses of this theorem.
6. Closed points contract to closed points: `hcl` quantifies over every
   `y ∈ closedPoints (PrimeSpectrum S)` and asserts membership of its
   `PrimeSpectrum.comap (algebraMap R S)` image in the closed points of Spec R.
7. T is a subset of the connected-component space of Spec S:
   `T : Set (ConnectedComponents (PrimeSpectrum S))`.
8. T is closed in that quotient topology: `hT : IsClosed T`.
9. The component map is the one induced by contraction:
   `(PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap`.
10. The restriction to T is surjective onto all target components: `hsurjT`
    is `∀ c, ∃ t ∈ T, ... t = c`. The witness must belong to T.
11. That same restriction is injective: `hinjT` quantifies over two members
    of T and concludes their equality when their component images agree.
    Together 10 and 11 are precisely bijectivity of the restriction.
12. A ring retraction exists: `∃ f : S →+* R,
    f.comp (algebraMap R S) = RingHom.id R`. The existential follows all
    hypotheses and the equality has the right composition order.

Edge cases: no Nontrivial, finite-type, Noetherian, characteristic, or
nonemptiness restriction appears. T empty forces the target component space
empty by hsurjT; this is allowed for the zero ring. For R zero the unital
algebra structure forces S zero, so the empty-spectrum case is consistent.
S zero with R nonzero fails hsurjT, as it should. Identity algebras with T the
whole component space are covered. There is no index set, degree, or n.
The shared arbitrary universe u excludes no pair of ring sizes: Lean's
cumulative universes allow both types at their maximum universe. No extra
universe equality on mathematical structures is imposed.

Independent duplicate searches used different wording from the first reader:
LeanFinder, "A ring homomorphism identifying local rings has a left inverse
when it bijects a closed subset of connected components", returned eight
localization/open-immersion hits, none the required theorem. Loogle,
`ConnectedComponents, RingHom`, returned zero hits. LeanSearch with a
retraction/local-ring-isomorphism query returned Internal Server Error;
this is unavailable, not a negative mathematical result. Direct rg for
`retraction|leftInverse|LeftInverse` in Mathlib's localization, local-ring,
and spectrum directories found only unrelated inverse facts. Direct rg in
upstream WeilConjectures found the exact theorem at WContractible.lean:511
and its application at line 663; rg in project lean/Sheaf found no duplicate.
Read the exact group-clone WContractible source and the pro-etale framework
note as required. Retain `existing: true`; no new definitions, dependency
modules, proofs, or hollow constructions are delivered. The existing
upstream proof and docstring explain the closed restriction construction,
stalk/component bijectivity, inversion, and composition; upstream sources
are read-only and their docstrings are not rewritten.

Citer audit: searched every DAG node for the item id. There is exactly one
direct citer, `lem-weil-pbc-wlocal-closed-component-retraction`, so there
cannot be two distinct direct citers to open. Opened its full statement and
four proof steps: its restriction is explicitly bijective, and steps 3–4
provide exactly hsurjT/hinjT and apply this theorem. Its `holds: true` verdict
is correct. No citer is broken and no target unit statement changes.

Mismatches found in this second reading: none. Retained the first reader's
source-based correction and exact existing declaration signature unchanged;
added only this independent review report. Server checking of the existing
declaration is performed by deliver2.py's generated import/#check probe.
