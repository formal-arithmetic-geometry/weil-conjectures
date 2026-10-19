## Worker report

The module `Sheaf.RingTheory.WLocalClosedComponentRetraction` states
`RingHom.exists_retraction_of_closed_component_bijective`. Its entire proof is `sorry`;
no definition or theorem proof is supplied. The node is unchanged except for `lean`.

Clause-by-clause correspondence:

- Commutative rings R and S: `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`.
  The independent explicitly declared universes allow any pair of ring sizes.
- W-local spectra: `[IsWLocalRing R] [IsWLocalRing S]`, exactly the recorded dependency.
- Ring map g:R→S: `(g : R →+* S)`, without imposing an externally chosen algebra structure.
- Bijective on all prime stalks: `(hstalk : g.BijectiveOnStalks)`. The upstream definition
  quantifies over every prime ideal p of S and says that
  `Localization.localRingHom (p.comap g) p g rfl` is bijective. Thus these are precisely
  the maps R_(g⁻¹p)→S_p of the node, using `Localization.AtPrime`.
- Closed points map to closed points: `hclosed` quantifies over
  `y ∈ closedPoints (PrimeSpectrum S)` and requires
  `PrimeSpectrum.comap g y ∈ closedPoints (PrimeSpectrum R)`.
- The induced component map h is written directly as
  `(PrimeSpectrum.continuous_comap g).connectedComponentsMap`. It is not an arbitrary map
  or an additional hypothesis: functoriality of connected components gives this map.
- T is a subset of π₀(Spec S): `(T : Set (ConnectedComponents (PrimeSpectrum S)))`.
- T is closed in the quotient topology: `(hT : IsClosed T)`.
- Bijectivity of h restricted to T: `hbij` is `Function.Bijective` of the function
  `fun t : T ↦ (PrimeSpectrum.continuous_comap g).connectedComponentsMap t.val`.
  Its domain is exactly the subtype T, so surjectivity is onto all components of Spec R
  and injectivity concerns only components in T.
- There exists a ring map s:S→R: `∃ s : S →+* R`.
- s∘g=id_R: `s.comp g = RingHom.id R`. This is equality of ring homomorphisms,
  equivalent to the asserted composition identity.

Dependencies and declarations read and used:

- `def-weil-pbc-w-local`: `WeilConjectures.RingTheory.ProEtale.WLocal`, `IsWLocalRing`.
  Its field supplies `WLocalSpace (PrimeSpectrum R)`; the recorded equivalence with
  the closed-point/connected-component definition is retained. No new w-local predicate.
- `def-weil-pbc-localization-at-prime` (Mathlib leaf):
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`;
  also read `Ideal.ResidueField` in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`
  and `Ideal.Fiber` in `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`. The latter two
  clauses of this bundled dependency are not needed by this statement.
- The stalk predicate is the existing `RingHom.BijectiveOnStalks` in
  `WeilConjectures.RingTheory.ProEtale.StalkIso`, publicly imported by WLocal.
- `Continuous.connectedComponentsMap`, `Mathlib.Topology.Connected.TotallyDisconnected`,
  is the quotient-induced map, not a copied construction.
- Proof dependency `lem-weil-pbc-wlocal-isClosed-bijOn-retraction` has a closed upstream
  audit naming `exists_retraction_of_isClosed_of_bijOn` in
  `WeilConjectures.RingTheory.ProEtale.WContractible`. That module is a proof-only import.
  Its signature and docstring were read: it takes an algebra structure, the algebra map,
  explicit surjectivity/injectivity on T, and rings in a common universe. The new node
  intentionally provides the requested explicit ring-map signature and independent
  universes; its proof docstring explains the algebra conversion and, if needed, universe
  lifting and transport. There is no new canonical map or choice of algebra structure
  in the statement.

Source checked: local `literature/stacks-project/proetale.tex`,
`lemma-w-local-extremally-disconnected` (Tag 09AZ), the proof of (3)→(1), especially
choosing the closed image T, restricting to those components, and obtaining an isomorphism.
The upstream auxiliary theorem supplies exactly this closed-component restriction route.

Edge cases: zero rings are allowed. If T is empty, restricted-map bijectivity forces
π₀(Spec R) to be empty, hence R is the zero ring; the unique map S→R has the stated
composition identity. If S is zero and R is nonzero, the component bijection cannot hold.
For an identity map and T the entire component space, the identity is a retraction.
Nonempty proper closed subsets T are allowed; no surjectivity/injectivity requirement
is imposed on the complement. No finite, Noetherian, reduced, faithfully flat, extremally
 disconnected or characteristic assumption was introduced. All topologies here are the
ordinary Zariski topology and its connected-component quotient, not the patch topology.

Searches performed:

- `msearch.py` LeanFinder: “A ring map between w-local rings bijective on prime stalks
  preserving closed points with closed subset bijective on connected components admits a
  retraction”: eight generic localization/open-immersion hits, no exact theorem.
- `msearch.py` Loogle: `RingHom, ConnectedComponents, Function.Bijective`: zero hits.
- `msearch.py` Mathlib grep: `exists_retraction|BijectiveOnStalks|IsWLocalRing`, RingTheory:
  zero hits.
- `msearch.py` LeanSearch: “w-local ring map identifying local rings closed subset of
  connected components retraction”: unavailable, Internal Server Error; no verdict inferred.
- Source and project `rg`: `exists_retraction_of_isClosed_of_bijOn|bijectiveOnStalks|IsWLocal|
  WLocal` located the upstream notions and auxiliary theorem; project results included
  `ClosedComponentSpectrumRestriction.lean` (a restriction existence statement, not this
  retraction theorem). Searching the exact item id in upstream found no declaration.
- Searching the new declaration name across Mathlib, upstream and `lean/Sheaf` returned
  no collisions. The auxiliary algebra theorem is the proof input, not a duplicate
  definition of any notion used by the statement.

Validation: `scompile.py NU lem-weil-pbc-wlocal-closed-component-retraction` compiled the
only delivered module cleanly on the server in 1.4 seconds, nice 19, two threads,
60-second per-file limit. No local compilation. No statement correction, disputed
statement, new node or dependency repair was needed.

## Second reading by NU

I independently opened the item JSON, its delivered Lean module, both statement-dependency
JSONs and their declarations, and the proof-dependency declaration in WContractible.lean.
I read Tag 09AZ in proetale.tex, from the lemma statement through the (3) to (1) proof.
The initial faithful-flat/ind-Zariski hypotheses serve to obtain the intermediate situation:
a w-local source spectrum, closed points preserved, and a closed component subset T.
The final restriction argument uses precisely the intermediate hypotheses in this node;
faithful flatness and extremal disconnectedness are not extra hypotheses here.

Object/hypothesis/conclusion checklist (all verdicts: exact):

1. Commutative rings R and S: `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`.
   `u` and `v` are explicitly bound, independent universes.
2. Both spectra w-local: `[IsWLocalRing R] [IsWLocalRing S]`, from the recorded WLocal
   module. I read its class field `WLocalSpace (PrimeSpectrum R)`, WLocalSpace's closed-point
   uniqueness and closedness fields, and the connected-components/closed-points
   homeomorphism. On prime spectra this is exactly the node's condition, with no extra
   spectral-space assumption on the rings.
3. Ring homomorphism g:R→S: `(g : R →+* S)`; no algebra structure is assumed separately.
4. Every prime stalk map bijective: `(hstalk : g.BijectiveOnStalks)`. I opened StalkIso:
   this quantifies over every prime ideal p of S and uses
   `Localization.localRingHom (p.comap g) p g rfl`. I also read Localization.AtPrime and
   localRingHom in Mathlib: these are the canonical R_(g⁻¹p)→S_p maps, not residue fields
   or arbitrary isomorphisms. The bundled dependency's residue-field and fibre clauses
   are not used by this item.
5. Closed points preserved in the contravariant direction: `hclosed` quantifies over
   `y ∈ closedPoints (PrimeSpectrum S)` and requires that `PrimeSpectrum.comap g y` belong
   to `closedPoints (PrimeSpectrum R)`. No converse is asserted.
6. The induced h on components: `(PrimeSpectrum.continuous_comap g).connectedComponentsMap`.
   I opened Mathlib's definition and its `_mk` equation: it sends [y] to [g⁻¹y], exactly
   the canonical map requested. No arbitrary component map is substituted.
7. Subset T of components of Spec S: `(T : Set (ConnectedComponents (PrimeSpectrum S)))`.
8. T closed: `(hT : IsClosed T)`, in the Zariski component quotient topology.
9. h restricted to T bijective onto all components of Spec R: `hbij` is
   `Function.Bijective (fun t : T ↦ ...connectedComponentsMap t.val)`. The subtype gives
   exactly the restricted domain, and the codomain is unrestricted. In particular,
   surjectivity is from T, not merely from the whole component space.
10. Existence of a ring map S→R: `∃ s : S →+* R` after all the hypotheses above.
11. Retraction equation: `s.comp g = RingHom.id R`, in the correct order and on R.

Edge cases checked: no Nontrivial or Nonempty assumption excludes zero rings or empty
spectra. Empty T forces Spec R to have no components, hence R to be the zero ring, and
the conclusion is valid. Zero S with nonzero R cannot satisfy restricted surjectivity.
The identity case with T the entire component space works; proper closed T is allowed.
No finite/Noetherian, reduced, characteristic, or extremal-disconnectedness restriction
occurs. There is no n/indexed-family parameter to restrict. Universe-polymorphic stalks
and component maps preserve the independent sizes u and v. The proof docstring explicitly
explains common-maximum-universe lifting before using the one-universe auxiliary theorem.

Independent duplicate searches, using different wording from the first reader:

- LeanFinder via msearch.py: "A homomorphism of commutative w-local rings inducing
  isomorphisms of localizations has a section after choosing a closed component transversal".
  Eight hits, about products of localizations, valuation rings and locally defined
  properties; no matching retraction statement.
- Loogle via msearch.py: `ConnectedComponents, IsClosed, RingHom`: zero hits.
- Mathlib grep via msearch.py: `retraction.*component|component.*retraction`: zero hits.
- Direct rg on Mathlib RingTheory, upstream WeilConjectures/RingTheory, and project
  lean/Sheaf for component/retraction phrases, BijectiveOnStalks and the proposed name.
  Opened the nearby `PrimeSpectrum.exists_closed_component_restriction`: it asserts a
  quotient realization of a closed component union, not the present retraction.
- Opened `exists_retraction_of_isClosed_of_bijOn`: its algebraMap binder, common Type u,
  and separate surjectivity/injectivity-on-T hypotheses differ from the explicit arbitrary
  ring map and independent universes here. It is the recorded supporting theorem, not an
  exact declaration to attach in place of this item. WLocal and StalkIso already provide
  all notions used; none is redefined.

No mismatches found; no Lean, signature, dependency, or mathematical statement changed.
No new definition nodes or dependency modules are present. The sole theorem has proof
`by sorry`; there are no definitions or hidden proofs. The source/blueprint docstrings
and the four-step proof plan agree with the node, and the proof-only WContractible import
is retained. All variables and universes are explicitly bound. The node's lean.statement
is verbatim the delivered theorem signature. Worker report retained above.

Validation: the second reader reruns scompile.py on the only delivered module, then
runs deliver2.py --no-push and deliver2.py; all compilation is server-only under the
required nice 19, two-thread, 60-second-per-file limits.
