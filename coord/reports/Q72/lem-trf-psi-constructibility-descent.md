## Worker report

`Sheaf.Paper.PsiConstructibilityDescent` states
`AlgebraicGeometry.OrientedNearbyCycles.constructibility_descent`, with a `sorry` proof.
Its source is Orgogozo's author draft, Lemma 9.1.5, printed p. 21. I opened the source
PDF and read that lemma and §8.1: the argument reflects coherence along the induced coherent
conservative morphism, using the agreement between constructibility and coherence. The
node's four proof steps are included individually in the declaration docstring. The three
statement-only proof dependencies currently have no Lean records, so no imports for them
are available. The definition dependency is imported publicly.

Clause-by-clause rendering of the item:

* Schemes `X`, `S`, and `T` are `Scheme.{u}`. The Noetherian base is exactly
  `[IsLocallyNoetherian S] [CompactSpace S]`, with no separatedness assumption on S.
* The finite-presentation map is `(f : X ⟶ S)` with the three recorded convention
  classes `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`.
* The coefficient ring is `(Λ : Type v) [CommRing Λ] [Finite Λ]`. The universes `u` and
  `v` are independent. `Coeff.{u, v} Λ` is the existing canonical universe lift, not a
  different ring or a coefficient restriction.
* An arbitrary module sheaf F on V_f is
  `(F : (vanishingDatum.{u, v} f).modules (Coeff.{u, v} Λ))`.
* The proper surjective map is `(p : T ⟶ S) [IsProper p] [Surjective p]`.
* The Cartesian changed family is `pullback.snd f p`, with total space `pullback f p`,
  upper map `pullback.fst f p`, and the equality `pullback.condition`.
* The geometric map is the recorded `squareMorphism`, via its recorded module lift
  `squareModules`. The hypothesis `_hF` applies `IsConstructibleVanishing` to exactly
  the object obtained using that lift's `modulePull (Coeff Λ)`.
* The conclusion is `IsConstructibleVanishing f Λ F`, on the original vanishing datum.
  This is ordinary module-sheaf inverse image; no derived or nearby-cycle restriction
  is imposed on F.

Dependency declarations read and used: `AlgebraicGeometry.IsLocallyNoetherian` in
`Mathlib.AlgebraicGeometry.Noetherian`; `CompactSpace` in `Mathlib.Topology.Defs.Filter`;
`AlgebraicGeometry.LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` in
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `.QuasiCompact`, and
`.QuasiSeparated`; `AlgebraicGeometry.IsProper` in `.Proper`; `AlgebraicGeometry.Surjective`
in `.UnderlyingMap`. The scheme-conventions node has no separate declaration: its finite
presentation convention is the three classes above. The topoi and canonical module pullback
are the `vanishingDatum`, `Coeff`, `squareMorphism`, `squareModules` declarations of
`Sheaf.Paper.OrientedNearbyCycles`. Constructibility is the existing
`AlgebraicGeometry.OrientedConstructibleSheaf.IsConstructible` from
`Sheaf.Paper.OrientedConstructibleSheaf`, through the explicit presentation transport
provided in this delivery (see Dependency modules).

For the dependency's clauses, the general `IsConstructible` remains imported unchanged:
it quantifies over both finite locally closed stratifications, requires each stratum to
be constructible, and uses the recorded `stratumRestriction` and
`SheafOfModules.IsFiniteTypeLocallyConstant`. Finite type over a finite ring is exactly
finite as a set. The new `IsConstructibleVanishing` just applies this existing predicate
at `(f, 𝟙 S)` to `vanishingModuleTransport f Λ F`; it duplicates none of these clauses.
The transport restricts scalars by `realizationRingIso`, uses the recorded
`constantRingModuleRestriction`, precomposes through the concrete normalization of triples,
sheafifies, and uses the inverse of the recorded constant-ring module equivalence.
All its data are constructions. The only postponed proof in this delivery is the item.

Edge cases checked before finalizing: identity p, empty S, empty X over nonempty S, zero F,
the zero coefficient ring, and arbitrary (possibly infinite) F. There is no nonempty or
nonzero binder. The constructibility predicate retains empty stratifications and covers,
and does not assume F is finite before pullback. Neither f nor p is assumed étale, and no
invertibility condition on the ring's cardinality is added. Properness and surjectivity
are both retained; the claim would fail for an empty non-surjective base change.

Searches made through the prescribed `msearch.py Q72 lem-trf-psi-constructibility-descent`:

* LeanFinder: "Constructible module sheaves on a vanishing topos descend along proper
  surjective changes of base" — eight hits about condensed modules and finite-presentation
  sheaves, none about oriented constructibility descent.
* Loogle: `"Constructible", "Sheaf"` — zero hits.
* Mathlib grep: `nearby.?cycle|vanishing.?topos|oriented.?product` — zero hits.
* LeanSearch: "Constructibility of a sheaf on a vanishing topos is reflected by proper
  surjective base change" — ordinary sheaf-forgetful and scheme-base-change facts,
  no statement of this lemma.

Direct `rg` searches over `WeilConjectures` and `lean/Sheaf`, and the upstream name index,
found no declaration stating the item. Searching the item id in the upstream Lean source
also found none. The closest project declarations were the general oriented-product
constructibility predicate and the existing nearby-cycle square-module construction.
The downstream Psi-good strata theorem is a consumer, so its helpers are not imported.
No new DAG notion, statement correction, or disputed statement is needed.

## Second reading by Q72

Author self-check only, as required by direct delivery; no second agent was started.
I reread the item and the two files. An initial draft used helpers from the downstream
Psi-good strata theorem and restricted coefficients to Type (u+1). I removed that import
and restriction: the final helper uses only the recorded general product, the nearby-cycle
site, and the canonical constant-ring coefficient transport, with independent u and v.
The theorem's pullback object, direction of modulePull, finite-presentation convention,
properness, surjectivity, and both constructibility occurrences match the node. The helper
calls the general IsConstructible, retaining its two stratifications and finite local
constant models. Its normalization changes only W → V×_S S into W → V using the first
projection, so projections and orientation are preserved. The maintainer supplies the
independent review of this delivery.

## Dependency modules

`def-trf-oriented-constructible-sheaf`: the recorded `Modules f (𝟙 S) Λ` is not definitionally
`(vanishingDatum f).modules (Coeff Λ)`. The former site uses `etaleBaseChange (𝟙 S)`;
the latter uses the identity functor. Moreover, the first coefficient presentation is a
RingCat constant sheaf and the second forgets commutativity after forming a CommRingCat
constant sheaf. Thus the recorded general predicate cannot take the item’s F or its
canonical square modulePull without a presentation transport.

`Sheaf.Paper.OrientedConstructibleSheafVanishing` repairs precisely that interface. It imports
the original general definition unchanged. `identityBaseChangeProjection` uses the canonical
first projection V×_S S → V; `vanishingNormalization` composes the second triple arrow with
this projection and leaves all three entries fixed. This is an equivalence, with inverse
obtained by composing with the inverse projection; the three generating coverings are
unchanged. `vanishingModuleTransport` transports modules along this normalization and the
existing coefficient comparison. Finally `IsConstructibleVanishing` applies the original
`IsConstructible f (𝟙 S) Λ`. The dependency node changes only its lean record and explains
both presentation mismatches in lean.note. No source clause is weakened or redefined.

Validation: `scompile.py Q72 lem-trf-psi-constructibility-descent` compiled both delivered
modules separately, in dependency order, with no errors or warnings. The helper contains
zero sorries; the item has its single requested sorry proof. A comparison against the
shared node copies confirms that each node changes only in its `lean` field.
