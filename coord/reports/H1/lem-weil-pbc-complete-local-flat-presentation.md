## Worker report

The module `Sheaf.RingTheory.ExistsCompleteLocalFlatPresentation` states
`RingHom.exists_completeLocal_flat_presentation`, with `sorry` as its sole proof.
It gives exactly the flat-presentation consequence selected by the DAG node from
[Stacks Tag 07NN](https://stacks.math.columbia.edu/tag/07NN), Lemma 15.40.3. The local
literature checkout is absent on this machine; the complete statement and proof were
read at the official tag page. The six-step DAG proof is reproduced in the declaration
docstring, naming the nodes for each construction and inference. The source also gives
regularity and parameter assertions, which this node deliberately does not assert.

Hypotheses and clauses, matched individually:

- The two commutative rings are `{A : Type u} {B : Type v}` with `[CommRing A]`,
  `[CommRing B]`; the universes are declared explicitly.
- Noetherianity is `[IsNoetherianRing A] [IsNoetherianRing B]`.
- The rings are local by `[IsLocalRing A] [IsLocalRing B]`; the named maximal ideals
  are `IsLocalRing.maximalIdeal A` and `IsLocalRing.maximalIdeal B`.
- Completeness for those maximal ideals is expressed by the two
  `[IsAdicComplete (IsLocalRing.maximalIdeal ...) ...]` binders.
- The local homomorphism in the hypothesis is `(f : A →+* B) [IsLocalHom f]`.
- The existence of the two commutative rings is `∃ (R S : Type (max u v))
  (rR : CommRing R) (rS : CommRing S)`. The `letI` bindings install their existentially
  quantified structures rather than silently choosing structures in advance.
- Locality of the witness rings is `∃ (lR : IsLocalRing R) (lS : IsLocalRing S)`,
  installed by `letI` so that their maximal ideals are available.
- Noetherianity of the witnesses is `IsNoetherianRing R ∧ IsNoetherianRing S`.
- Completeness of the witnesses is the conjunction of `IsAdicComplete` for each
  witness ring's own maximal ideal.
- The three other arrows are existential ring homomorphisms
  `(g : R →+* S) (q : R →+* A) (b : S →+* B)`.
- Their locality is `IsLocalHom g ∧ IsLocalHom q ∧ IsLocalHom b`; together with the
  hypothesis on `f` this covers all four arrows of the square.
- The two vertical surjections are `Function.Surjective q ∧ Function.Surjective b`.
- Flatness of the upper arrow is `g.Flat`, for the module structure induced by `g`.
- Commutativity is the equality of ring homomorphisms `b.comp g = f.comp q`.

Dependency declarations used, with their full signatures and docstrings inspected:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs`. This is `IsNoetherian R R`, equivalent to finite
  generation of every ideal. The node's existing Lean record is used.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete` from
  `Mathlib.RingTheory.AdicCompletion.Basic`, specialized to the ring as a module over
  itself. Its Hausdorff and precomplete conditions together are equivalent to
  bijectivity of the canonical completion map (`AdicCompletion.of_bijective_iff`).
  This Mathlib dependency needs no separate Lean record or private definition.
- `def-weil-pbc-flat-ring-map`: `RingHom.Flat` from
  `Mathlib.RingTheory.RingHom.Flat`, defined as `Module.Flat R S` using `g.toAlgebra`.
  The general `Module.Flat` notion agrees with tensor preservation of injectivity.
- Auxiliary existing Mathlib notions: `IsLocalRing` (LocalRing/Defs),
  `IsLocalRing.maximalIdeal` (LocalRing/MaximalIdeal/Defs), `IsLocalHom`
  (Algebra/Group/Units/Hom). The latter reflects units, equivalently maps the maximal
  ideal into the maximal ideal for local rings. They are imported through
  `Mathlib.RingTheory.LocalRing.RingHom.Basic`.

Edge cases checked: local rings are nonzero by `IsLocalRing`, exactly the usual
convention of the source, so zero rings are not accidentally included. Fields have
maximal ideal zero and are included, as are maps between fields and identity maps.
No residue characteristic is restricted, including mixed characteristic. There are
no positive dimension, injectivity, finite type or equal residue field hypotheses.
The witness rings are allowed to have dimension zero. Distinct input universes are
allowed; the common witness universe `max u v` is closed under the quotients and
finite-variable power-series constructions in the proof, so it excludes no inputs.

Searches for an existing statement (all via the mandated launcher script unless noted):

- LeanSearch: `local homomorphism complete Noetherian local rings flat presentation
  commutative square` returned unavailable, Internal Server Error.
- LeanFinder: `A local homomorphism of complete Noetherian local rings has a
  commutative square with surjective vertical maps and a flat map between complete
  Noetherian local rings` returned eight hits, including formally smooth flatness,
  adic-completion flatness, formally smooth lifting, and faithfully flat descent;
  none states this presentation theorem.
- Loogle: `IsLocalHom, IsAdicComplete, RingHom.Flat` returned zero hits.
- Mathlib grep: `Cohen|flat.*presentation|presentation.*flat` in `RingTheory` returned
  eighteen hits on finite-presentation descent and flat modules, plus a historical
  Cohen citation; no complete-local flat presentation.
- `rg` over project `lean/Sheaf` and upstream `WeilConjectures` for `07NN`,
  `complete.local.*presentation`, `flat.*presentation`, `Cohen`, `completeLocal`,
  `complete_local`, `exists_complete.*flat`, `exists_flat.*complete`: no matching
  declaration. An upstream geometric `exists_flat_polynomial_presentation` concerns
  a scheme point and polynomial rings, not complete local rings.
- `grep -rn 'lem-weil-pbc-complete-local-flat-presentation'` over upstream
  `WeilConjectures`: no hits. The proposed name was also searched in
  `dag/lean_names_upstream.json` and the project/upstream RingTheory modules.

No missing notions, unusable dependencies, statement corrections, or disputes were found.
No new nodes or dependency modules are needed. Server compilation and the authorized
delivery dry run are the validation; the second reader writes the independent reading.

## Second reading by H1

I independently read the node statement, its Stacks source place (More on Algebra,
Tag 07NN, lemma-embed-map-Noetherian-complete-local-rings), and the Lean declaration.
The object and hypothesis list is as follows, with the corresponding Lean rendering and
verdict:

- The input commutative rings (A,B), in universes (u,v), are the implicit `A`, `B`
  binders with `[CommRing A] [CommRing B]`; this is exact.
- Noetherianity and locality are `[IsNoetherianRing A] [IsNoetherianRing B]` and
  `[IsLocalRing A] [IsLocalRing B]`; this is exact.
- Completeness for the named maximal ideals is expressed by the two
  `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]` and corresponding `B` binders;
  this is the node's adic-completeness clause.
- The given map is `(f : A →+* B) [IsLocalHom f]`, rendering the local homomorphism.
- The witnesses are `R S : Type (max u v)` with explicitly existential commutative-ring
  structures `rR`, `rS`, installed by `letI`; they render the two witness rings.
- Witness locality is existential `lR`, `lS : IsLocalRing`, also installed by `letI`.
- The witness properties are the conjunctions of `IsNoetherianRing`, adic completeness
  at each witness maximal ideal, and the three maps `g`, `q`, `b`; each appears in the
  same conjunction order as the conclusion.
- `IsLocalHom g`, `IsLocalHom q`, `IsLocalHom b` render all three local arrows, while
  `Function.Surjective q` and `Function.Surjective b` render the two vertical
  surjections.
- `g.Flat` renders flatness of the upper arrow, and `b.comp g = f.comp q` is precisely
  commutativity of the square. No clause is omitted or strengthened.

The source assumes exactly a local map of Noetherian local rings complete at their
maximal ideals and concludes the displayed flat square; the Lean binders introduce no
extra finiteness, characteristic, dimension, injectivity, or residue-field hypotheses.
The explicit witness universe `max u v` is sufficient for the constructions in the
source proof and does not restrict the input universes.

Edge cases checked: the source convention that local rings are nonzero is enforced by
`IsLocalRing`; fields (zero maximal ideal), identity maps, mixed characteristic, and
zero numbers of power-series variables are all covered. The empty scheme is irrelevant
to this ring statement, and no index-set or `n = 0` hypothesis is present. Distinct
input universes are allowed.

I searched Mathlib and the project/source with LeanSearch, LeanFinder/Loogle, and `rg`
for Cohen presentations, complete-local flat presentations, and the proposed declaration
name. The searches found no existing declaration with this statement; the imported
notions are the canonical Mathlib declarations `IsNoetherianRing`, `IsAdicComplete`,
`IsLocalRing`, `IsLocalHom`, and `RingHom.Flat`. No missing notion or unusable dependency
was found, and no statement correction was needed. The only worker artifact was already
correct; I made no Lean or node changes. The module compiles cleanly with `scompile.py`.
