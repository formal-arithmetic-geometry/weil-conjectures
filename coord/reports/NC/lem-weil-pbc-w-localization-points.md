## Worker report

The module `Sheaf.RingTheory.PrincipalWLocalizationPoints` states
`PrincipalWLocalization.points`, with its sole proof `sorry`. It uses the actual
finite-partition/principal-denominator colimit, not upstream's differently constructed
`WLocalization`. No definitions, new nodes, dependency modules, or statement corrections.

Hypotheses and clauses, in signature order:

- A commutative ring: `(A : Type u) [CommRing A]`, with no nontriviality assumption.
- W = A^w: every occurrence is `PrincipalWLocalization.algebra A`.
- Points are pairs (x,y) with y contained in x: the equivalence `e` has codomain
  `{p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal}`.
- The structural map sends (x,y) to y: the first conjunct identifies
  `PrimeSpectrum.comap (algebraMap A (algebra A)) q` with `(e q).val.2`.
- The local ring at q is A_y: the next conjunct gives an A-algebra equivalence
  `Localization.AtPrime q.asIdeal ≃ₐ[A] Localization.AtPrime (e q).val.2.asIdeal`.
  Prime localization is the affine scheme local ring, using the standard affine stalk
  identification cited in the node's proof. The A-algebra structure preserves the
  structural map and gives the canonical identification.
- The first-coordinate map to the patch space is continuous: explicit `@Continuous`
  has target topology `constructibleTopology (PrimeSpectrum A)`.
- Components are the first-coordinate fibres: `connectedComponent q` equals
  `{r | (e r).val.1 = (e q).val.1}` for every q.
- Each component fibre is canonically Spec A_x as an affine scheme: for each x an
  A-algebra homomorphism `ρ : algebra A →ₐ[A] Localization.AtPrime x.asIdeal`
  induces a closed immersion `Spec.map (CommRingCat.ofHom ρ.toRingHom)` whose
  underlying image is exactly `{q | (e q).val.1 = x}`. This realizes the fibre as
  the affine closed subscheme with coordinate ring A_x, rather than merely giving
  a homeomorphism of spaces. For affine schemes this is equivalently a surjection
  W → A_x, or Spec(W / ker ρ) ≅ Spec A_x, as in proof steps 6–7.
- Closed points are precisely diagonal pairs: membership in `closedPoints` is
  equivalent to equality of the two coordinates.
- They form a closed subset: `IsClosed (closedPoints (PrimeSpectrum (algebra A)))`.
- That closed subspace is homeomorphic to the patch spectrum: `h` is an explicit
  `@Homeomorph` with the patch topology on its domain and the subspace Zariski
  topology on its codomain; `(e (h x).val).val = (x,x)` fixes the identification.
- Faithful flatness is `Module.FaithfullyFlat A (algebra A)` for the structural
  algebra, equivalent to faithful flatness of its algebraMap.
- W-locality is the recorded `IsWLocalRing (algebra A)`.

Dependency declarations read and used:

- `Sheaf.RingTheory.PrincipalWLocalization`: `PrincipalWLocalization.algebra`,
  its concrete `Index`, `Stage`, `transition`, and `diagram` were read in full.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
  Also inspected the recorded `Ideal.ResidueField` and `Ideal.Fiber`; neither
  residue fields nor residue-field fibres replace the first-coordinate fibres here.
- `WeilConjectures.RingTheory.ProEtale.WLocal`: `IsWLocalRing`, `WLocalSpace`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`.
  Inspected `RingHom.FaithfullyFlat` and its algebraMap equivalence too.
- Mathlib's `constructibleTopology`, `closedPoints`, `connectedComponent`, and
  `AlgebraicGeometry.IsClosedImmersion` express the remaining standard notions.

Statement dependencies are imported through the two public imports. The stated
proof dependencies `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
and `Sheaf.RingTheory.IndEtaleStability` are imported non-publicly; the stated
`Sheaf.RingTheory.IndPrincipalZariski` is already a public import of
`PrincipalWLocalization`. The remaining proof dependencies have no Lean record.
The docstring carries all eleven proof steps verbatim from the node, wrapped
within the line limit. The blueprint source node was read directly.

Edge cases checked: the zero ring has empty spectrum and empty prime-pair set;
all quantified point and fibre assertions are vacuous, the homeomorphism is empty,
and faithful flatness of the zero ring over itself is allowed. Fields and local
rings still have fibres indexed by all primes, not only maximal primes. Inclusion
is non-strict, allowing the diagonal. No characteristic assumption, finite-spectrum
assumption, or extra universe constraint was imposed. The commutative ring and all
spectra and localizations live in the same arbitrary universe u. The first-coordinate
fibre is not the ordinary fibre of Spec W → Spec A (which uses the second coordinate).

Searches made:

- msearch.py leanfinder: "Points of affine w-localization are pairs of primes with
  one contained in the other, connected components local spectra". Eight hits,
  concerning standard affine stalks and localization spectra; no exact match.
- msearch.py loogle: "PrimeSpectrum, Localization.AtPrime, WLocalization".
  Zero hits; WLocalization unknown to the Mathlib search.
- msearch.py grep: "WLocalization|wLocalization|wlocalization" in RingTheory:
  zero Mathlib hits.
- rg over upstream WeilConjectures and project lean/Sheaf for those names and the
  item id: upstream has WLocalization.Basic and consequences for that different
  construction; the project has PrincipalWLocalization but no points theorem.
  Read upstream's Generalization.submonoid/Generalization definitions: those
  localize at all elements invertible on a locally closed piece, not principal
  denominators. Thus attaching its conclusions would change the statement's W.
- rg for `PrincipalWLocalization.points` and `theorem points` in the upstream-name
  index and both ring-theory source trees found no conflicting declaration.

Validation: scompile.py compiles the module cleanly on the server, nice 19,
two threads, default 60 seconds per file; no local Lean compiler was run.
No statement dispute or node fault found. Independent second reading is pending.

## Second reading by NC

I independently read the item's node, its blueprint source at order 1223,
Stacks `proetale.tex` around `lemma-make-w-local` (Tag 0975), and the delivered
Lean file. The blueprint is the direct source of the prime-pair description;
Stacks supplies the comparison construction and assumes only a commutative
ring, not a domain, nonzero ring, or Noetherian ring. The preceding Stacks
construction uses generalization localizations, so it cannot silently replace
the node's principal-denominator colimit.

The statement inventory, with its Lean rendering and verdict, is:

1. Object A is any commutative ring: `(A : Type u) [CommRing A]`. Exact;
   there are no additional hypotheses or inferred finiteness assumptions.
2. Object W is the specified affine w-localization: `algebra A` in namespace
   `PrincipalWLocalization`. Exact. I opened the dependency node and its module:
   `Index.parts`, `nonempty`, `constructible`, `partition`, `denominator`, and
   `nonvanishing` implement the finite partition and allowed denominators;
   `Refines` includes divisibility; `Stage`, `transition`, `diagram`, and `algebra`
   implement the product rings and their colimit, including the empty partition.
3. Points are all pairs (x,y) with y contained in x: the single existential
   equivalence `e` has codomain the subtype `p.2.asIdeal ≤ p.1.asIdeal`.
   Exact, with non-strict inclusion and both directions of the parametrization.
4. Structural map sends (x,y) to y: the first conjunct is
   `PrimeSpectrum.comap (algebraMap A (algebra A)) q = (e q).val.2`.
   Exact, and all later clauses use this same e.
5. Local ring at q is A_y: the second conjunct is `Nonempty` of the displayed
   `Localization.AtPrime` A-algebra equivalence. Exact. I read the recorded
   `Localization.AtPrime` declaration; it localizes at the prime complement.
   The affine local ring is this prime localization. A-algebra compatibility
   expresses compatibility with A, not merely an abstract ring isomorphism.
6. Map to the patch space is continuous: `@Continuous` explicitly supplies
   `constructibleTopology (PrimeSpectrum A)` on the codomain, retaining the
   Zariski topology on the source. Exact. Mathlib defines that topology using
   compact opens and their complements, equivalent on Spec A to D(f), V(f).
7. Components are precisely the first-coordinate fibres:
   `connectedComponent q = {r | (e r).val.1 = (e q).val.1}`. Exact.
8. Each fibre has its affine scheme identification with Spec A_x:
   `∀ x, ∃ ρ : algebra A →ₐ[A] Localization.AtPrime x.asIdeal`, followed by
   `IsClosedImmersion (Spec.map ...)` and equality of its point image with
   the first-coordinate fibre. Exact. I read `Spec`, `Spec.map`, and
   `IsClosedImmersion`: this gives the scheme structure and its structural
   map, not only a bijection or a homeomorphism. It is the quotient/localization
   realization in proof steps 6–7. The A-algebra map and the structural-map
   clause also fix the second coordinate of every image point.
9. Closed points are exactly the diagonal: the equivalence with
   `(e q).val.1 = (e q).val.2`. Exact; the chosen direction of equality is
   immaterial. `closedPoints` is the set of points with closed singleton.
10. Closed points form a Zariski closed subset: `IsClosed (closedPoints ...)`.
    Exact; there is no change of topology on W.
11. That subspace is homeomorphic to the patch spectrum: the existential
    `@Homeomorph` explicitly uses the patch topology on its domain and the
    closed-point subspace topology on its codomain, and
    `(e (h x).val).val = (x,x)` fixes the identification. Exact.
12. A to W is faithfully flat: `Module.FaithfullyFlat A (algebra A)`.
    Exact. I opened its recorded Mathlib class; it applies to the structural
    A-module and is the standard faithfully flat ring-map condition.
13. Spec W is w-local: `IsWLocalRing (algebra A)`. Exact. I opened its
    recorded upstream class and `WLocalSpace`, together with
    `WLocalSpace.isHomeomorph_connectedComponents_closedPoints`: the spectral
    space structure is automatic for a prime spectrum, and the closed-point
    and component conditions agree with the dependency node.

Edge cases: the zero ring has no primes, so both sides of e are empty and
all point and fibre quantifiers are vacuous; its empty-partition stage is the
zero ring. The closed-point homeomorphism is between empty spaces, and
faithful flatness over the zero ring is permitted by the standard definition.
Fields give one diagonal point; general local rings still include every
prime y contained in x, and no maximality restriction occurs. No assumptions
on characteristic, cardinality, or number of components are present. The
universe u is explicitly bound and arbitrary; all prime sets, finite
partitions, products, and localizations stay in it. There is no auxiliary
index-universe restriction. The empty product case is present in the actual
construction, not excluded by a Nonempty instance.

Independent searches used different queries from the first reader:

- `msearch.py ... leanfinder`: "The prime spectrum of the colimit of finite
  products of principal localizations is parametrized by a prime and a
  generalization, with local spectra as connected components". Eight results:
  PiLocalization, spectra of products, and localization order isomorphisms.
  None states the theorem for the specified colimit. PiLocalization is a full
  product of prime localizations, not this finite-partition colimit.
- `msearch.py ... loogle`: `PrimeSpectrum, "connectedComponent"`. Zero hits.
- `msearch.py ... grep`: `primePair|prime_pair|PrincipalWLocalization`.
  Eight unrelated hits, including order-theoretic PrimePair; no match.
- Direct rg over Mathlib ring theory, upstream WeilConjectures, and project
  lean/Sheaf for `PrincipalWLocalization`, `primePair`, `prime_pair`,
  `WLocalization.*(point|component)`, and
  `closedPoints.*constructibleTopology`. Only the existing principal
  construction and facts about the different upstream WLocalization appeared.
  I opened upstream `Generalization.submonoid`, `Generalization`, `ProdStrata`,
  and the colimit definitions to check the object mismatch. No existing exact
  declaration or duplicate definition was found.

No mismatch was found, and I changed no Lean or node field. There are no new
nodes or dependency modules to audit, and no statement correction or citer
verdicts to revisit. The sole theorem proof remains `sorry`; no definition,
private notation, local instance, or proof was introduced. The module and
statement docstrings name the source and blueprint id; the latter carries
all eleven node proof steps. Imports cover the statement dependencies and
all currently recorded proof-dependency modules, including transitive public
imports. I checked that `lean.statement` is verbatim equal to the file's
signature and that the only universe, u, is explicitly declared.

Validation: independently reran scompile.py on the delivered file. The server
compiled PrincipalWLocalizationPoints in 1.5 seconds, with its side-only
imports compiled separately, nice 19, two threads, 60 seconds per file, no
errors or warnings. No local compiler, Lake build, or live-library write.
