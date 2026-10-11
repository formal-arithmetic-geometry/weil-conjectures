## Worker report

The module `Sheaf.AlgebraicGeometry.PicardH1RestrictionCompatibility` states
`AlgebraicGeometry.Scheme.picard_h1_restriction_compatibility`, with proof `sorry`.
The original node statement is unchanged. The delivery adds one definition node and
module supplying the previously unnamed units sheaf map and canonical comparison.
No definition contains `sorry`, and no new theorem is proved.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes `Z` and `X` are `{Z X : Scheme.{v}}`; both are arbitrary schemes, with
  no curve, field, dimension, Noetherian or reducedness assumptions.
- The closed immersion is `(i : Z ⟶ X) [IsClosedImmersion i]`.
- An arbitrary invertible module is `(L : X.Modules) [Modules.IsInvertible L]`,
  using the precise recorded scheme-module notion. `Pic.ofIsInvertible L` is its
  isomorphism class in the recorded `Scheme.Pic`.
- Restriction of modules is `(Modules.tensorPullback i).obj L`, the recorded tensor
  formula, rather than Mathlib's different `Modules.pullback`. The existential
  `h : Modules.IsInvertible ((Modules.tensorPullback i).obj L)` supplies the
  invertibility proof required by `@Pic.ofIsInvertible ... h`. This is not a new
  input hypothesis or a choice of a different line bundle: the underlying module
  is fixed and the witness is proof-irrelevant.
- The first Hilbert-90 identification is `Pic.toH1Units X` (and `Pic.toH1Units Z`),
  the canonical recorded map sending a module to its generator torsor.
- The sheaf map `O_X^* → i_*O_Z^*` is `unitsSheafToPushforward i`; its data is
  `Functor.whiskerRight i.c CommRingCat.unitsAddCommGrp`, so on each open it is
  exactly the map on units of `i`'s structure-sheaf map.
- The induced first cohomology map is `Sheaf.H.map (unitsSheafToPushforward i) 1`.
- The comparison from `H¹(X,i_*O_Z^*)` to `H¹(Z,O_Z^*)` is
  `unitsPushforwardCohomologyComparison i 1`. Its data is the exact inverse-image
  map on Ext, with the canonical constant-integer-sheaf comparison, followed by
  the adjunction counit. Thus this is the canonical comparison, rather than an
  arbitrary choice from the dependency's `Nonempty` isomorphism. For a closed
  immersion it is the inverse of the cohomology identification of Tag 02UV:
  exact pushforward preserves injectives, and the derived adjunction with its
  counit gives this inverse. The recorded dependency theorem asserts existence
  of the isomorphism in the other direction and does not supply a named canonical
  map; it need not be duplicated or modified to construct this map.
- The equality is exactly the commutative-square assertion on `[L]`: the composite
  of the preceding two cohomology maps applied to the class of `L` equals the
  canonical class of the tensor pullback. Every Picard class has an invertible
  module representative, so the pointwise formulation covers the entire square.

Cohomology uses the existing `Sheaf.H` of the Hilbert-90 declaration, i.e.
`Ext^p(Z_const,F)`, not a new cohomology definition. The two cohomology dependency
records use `Sheaf.H' F p ⊤`, i.e. Ext from the sheafified free representable of the
terminal open. That free representable is canonically the constant integer sheaf,
so these are the two existing presentations of the same global abelian-sheaf
cohomology, as explained in those records. No abstract unconstrained cohomology
map or arbitrary isomorphism is a hypothesis of the theorem.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding plus stalk surjectivity).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, its complete tensor formula.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`:
  `CategoryTheory.Sheaf.H'`, `Sheaf.H`, `Sheaf.H.map`.
- `Mathlib.CategoryTheory.Sites.Spaces` and `Mathlib.Topology.Sheaves.Sheaf`:
  `TopologicalSpace.Opens.grothendieckTopology`, `TopCat.Sheaf`.
- `WeilConjectures.CategoryTheory.Sites.Torsor`:
  `CategoryTheory.Sheaf.Torsor`; the units sheaf is the already-defined
  `AlgebraicGeometry.Scheme.unitsSheaf` in
  `WeilConjectures.AlgebraicGeometry.Sites.UnitsTorsor`.
- `WeilConjectures.AlgebraicGeometry.PicardFunctor`:
  `AlgebraicGeometry.Scheme.Pic`; the scheme-invertibility bridge
  `Pic.ofIsInvertible` is in `WeilConjectures.AlgebraicGeometry.Picard.Group`.
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`:
  `AlgebraicGeometry.Scheme.nonempty_equiv_H_one_unitsSheaf`,
  `AlgebraicGeometry.Scheme.Pic.toH1Units`, `Pic.toH1UnitsAddEquiv`.
- `Sheaf.Topology.ClosedImmersionPushforwardCohomology`:
  `TopCat.cohomology_closed_immersion_pushforward`, read for the interpretation
  of the comparison; no redundant import, since the comparison is constructed
  from inverse image and the counit and no term from this theorem is required.
- The new definitions reuse `Sheaf.H.mapFunctor` in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, and
  `Functor.constantSheafsheafPullbackIso` in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`.

The declaration docstring contains all three proof steps of the node: generator
 torsor classification, local transition-function pullback with torsor functoriality,
 and the canonical closed-immersion comparison followed by Hilbert 90 on `Z`.

Edge cases checked mathematically: identity immersion gives the identity map;
empty `Z` gives the unique class and zero first cohomology; empty `X` forces empty
`Z`; a one-point scheme and a nonreduced closed thickening are allowed. The
structure sheaf gives the zero cohomology class. No characteristic or degree-zero
case is excluded by the new definitions (`p : ℕ` includes zero); no finite-type
or separatedness assumptions enter. All universes and variables are explicitly
bound, and the two modules use different universe names for combined compilation.
No node fault, statement correction, or STATEMENT-DISPUTED flag is needed.

Searches performed:

- LeanFinder via msearch: `Picard group restriction closed immersion commutes with
  first cohomology of units` — eight hits on tilde restriction, scheme module
  restriction and ring Picard base change; none is the scheme Picard/H¹ square.
- Loogle via msearch: `Sheaf.H.map, Scheme.Pic` — zero hits, unknown identifier
  `Sheaf.H.map` in the search service.
- Mathlib grep via msearch: `Pic.*H1|H1.*units.*pullback` in AlgebraicGeometry —
  zero hits. `unitsSheaf|H.mapFunctor|cohomologyComparison` — zero hits.
- Source and Sheaf rg: `toH1Units|unitsSheaf.*[Mm]ap|[Hh]1.*[Pp]ullback` — canonical
  Hilbert-90 map found, only special dual-number naturality and the distinct
  étale curve-pullback theorem; no closed-immersion Zariski result. The exact node
  id appears in the PicardLift proof docstring, not as an upstream declaration.
- LeanSearch: `Canonical restriction on Zariski cohomology of units for a scheme
  morphism` — unavailable (Internal Server Error), recorded without claiming a
  successful search.
- LeanFinder: `Map H^p(X, f_*F) to H^p(Y, F) using inverse image and counit` — eight
  hits on sheaf/presheaf adjunctions and pushforward component identities.
- DAG rg and `blueprint_refs.py search units` — 34 blueprint matches; no node
  defining the specialized units map and comparison. Source/Sheaf searches found
  `structureSheafCohomologyPullback` as a model for the Ext/inverse-image
  construction, but it concerns additive structure sheaves rather than units.

Source checked online because this clone does not contain the fetched Stacks TeX:
[09NY](https://stacks.math.columbia.edu/tag/09NY),
[02UV](https://stacks.math.columbia.edu/tag/02UV),
[09NU](https://stacks.math.columbia.edu/tag/09NU), and
[01F7](https://stacks.math.columbia.edu/tag/01F7).
The new dependency module compiled alone using lcompile, with no errors or warnings;
the item module then compiled against it, also with no errors or warnings.

## New nodes

`def-sc-zariski-units-restriction` defines the units map and the canonical
pushforward-cohomology comparison used by the item's square. Source: Stacks Tags
09NY, 01F7 and 02UV. Its module is
`Sheaf.AlgebraicGeometry.ZariskiUnitsRestriction`, with declarations
`AlgebraicGeometry.Scheme.unitsSheafToPushforward` and
`AlgebraicGeometry.Scheme.unitsPushforwardCohomologyComparison`.
It reuses the existing units sheaf, Ext cohomology, exact inverse image,
constant-sheaf comparison and adjunction counit. Its search records contain the
queries and results described above. No DAG node or existing declaration supplies
these specialized maps; the étale and additive-structure-sheaf maps have different
sources and targets. The item gains this node in stmt_deps; no existing dependency
node is modified.

## Earlier second reading (a previous round; superseded)

I independently opened the item node, both delivered modules, every statement
 dependency record, and the signatures and bodies described below. Verdict: the
Lean says precisely the node's commutative square. No statement correction,
dependency replacement, or Lean edit is needed. The only change in this reading
is this independent report section; the worker report remains in place.

Objects, hypotheses and conclusion clauses, matched individually:

1. Arbitrary schemes X and Z: `{Z X : Scheme.{v}}`. The universe `v` is explicitly
   declared and unrestricted. No curve, field, reducedness, finite-type,
   separatedness, dimension or Noetherian assumption is present. Verdict: exact.
2. A closed immersion i from Z to X: `(i : Z ⟶ X) [IsClosedImmersion i]`.
   I read Mathlib's class: a closed embedding with surjective stalk maps, exactly
   def-weil-closed-immersion. Verdict: exact.
3. An isomorphism class of invertible modules on X: `(L : X.Modules)
   [Modules.IsInvertible L]` and `Pic.ofIsInvertible L`. I read the scheme
   IsInvertible class, the skeleton definition of Pic, and the bridge
   Pic.ofIsInvertible in Picard/Group. Every Picard element has such a module
   representative; hence quantifying over L covers the entire square. Verdict:
   exact, including the recorded scheme notion of invertibility.
4. Its pullback class on Z: `((Modules.tensorPullback i).obj L)` and
   `@Pic.ofIsInvertible Z ... h`. I read TensorPullback's ring map, object formula,
   and functor: inverse image of modules followed by change of rings, with O_Z
   the first tensor factor, then sheafification. The existential `h` asserts
   invertibility of this fixed object. It is a proof-irrelevant Prop witness,
   not an additional hypothesis or an arbitrary replacement module. Verdict:
   exact rendering of the implicit well-definedness of the Picard pullback.
5. Hilbert-90 maps on both schemes: `Pic.toH1Units X` and `Pic.toH1Units Z`.
   I opened their definition and `toH1Units_mk`: these are the canonical generator
   torsor maps, not choices of unrelated equivalences. Verdict: exact.
6. O_X^* to i_*O_Z^*: `unitsSheafToPushforward i`. I read unitsSheaf's body,
   `X.sheaf.obj ⋙ CommRingCat.unitsAddCommGrp`; the new map is whiskering `i.c`
   with precisely that functor. Thus at each open it is the structure-sheaf ring
   map on units, additively written. Verdict: exact.
7. Induced H^1 map on X: `Sheaf.H.map (unitsSheafToPushforward i) 1`.
   Mathlib's H.map is Ext postcomposition with the specified sheaf map.
   `Sheaf.H` is Ext from the constant integer sheaf; the recorded `H' ... ⊤`
   presentation represents the same global sections functor via the free
   representable of the terminal open. These existing presentations are already
   used by Hilbert 90; no third cohomology is introduced. Verdict: exact.
8. Closed-immersion identification with H^1 on Z:
   `unitsPushforwardCohomologyComparison i 1`. I opened H.mapFunctor and
   constantSheafsheafPullbackIso, checking their directions. The `.symm` supplies
   Z_Z to i^{-1}Z_X, Ext is transported by exact inverse image, and H.map of the
   adjunction counit finishes the comparison. This is the canonical comparison,
   which is inverse to the exact-direct-image identification for closed
   immersions, not a chosen isomorphism from the dependency's Nonempty.
   I also read TopCat.cohomology_closed_immersion_pushforward and the definition
   of TopCat.Sheaf.pushforward, which is the same site pushforward. Verdict: exact.
9. Commutativity: the displayed equality applies the composite in (7)-(8) to the
   canonical class of L and equates it with the canonical class of i^*L. There
   are no extra conclusion clauses. Verdict: exact, pointwise on all classes.

Source reading: the repository lacks the fetched Stacks TeX, so I fetched the
primary-source varieties.tex and cohomology.tex into this item's scratchpad and
read `lemma-lift-line-bundle-from-reduction-dimension-1` (09NY),
`lemma-cohomology-and-closed-immersions` (02UV), `lemma-h1-invertible` (09NU),
and `section-functoriality` (01F7). Cross-checks:
[09NY](https://stacks.math.columbia.edu/tag/09NY),
[02UV](https://stacks.math.columbia.edu/tag/02UV),
[09NU](https://stacks.math.columbia.edu/tag/09NU),
[01F7](https://stacks.math.columbia.edu/tag/01F7).
09NY's dimension and Noetherian assumptions are needed for its surjectivity
argument, not for the naturality fact extracted here. 02UV itself assumes only
closed immersion, despite its section title. 09NU assumes local stalk rings,
which schemes supply. No source hypothesis is missing.

New node def-sc-zariski-units-restriction: independently read its statement,
source, dependencies and module. Both maps are for arbitrary scheme morphisms;
the degree p is any natural number. Their bodies give the named canonical maps
of the source's functoriality construction. They reuse the existing units sheaf,
site topology, cohomology, inverse-image functor and adjunction. No hollow data or
proof hole occurs inside either definition. All declarations have their own
source and blueprint docstrings; the item docstring includes all three DAG proof
steps and their citations. Its sole theorem remains `sorry` as stage 2 requires.
The node's required fields and search records are present. I checked the ancestry
with blueprint_refs.chain: the full chain through the ample, quasi-projective
and projective nodes is correct. My initial concern that the via field was too
long was resolved by that check; I did not alter it. No dependency module is
part of this delivery.

Edge cases: empty Z gives the unique Picard class and zero H^1; empty X forces
empty Z. The identity immersion, a one-point scheme, and nonreduced closed
subschemes are allowed. The structure sheaf represents the zero class. A zero
module is invertible only where the recorded notion permits it (in particular
on the empty scheme); no Nonempty assumption excludes this. The new comparison
includes p = 0. No characteristic, finite index set or extra universe parameter
is imposed. Scheme morphisms share the standard scheme universe, which can be
raised to a common universe; all module variables and universe names are bound.

Independent searches (different queries from the worker): LeanFinder via msearch
`Naturality of line bundle torsor class under restriction on Zariski sheaf
cohomology` returned eight hits on tilde and scheme-section restriction, none
stating this square. Loogle `"toH1Units"` returned zero hits. LeanFinder
`Cohomology pullback using exact inverse image of abelian sheaves and adjunction
counit` returned eight existing pullback/adjunction API hits, not the units
specialization. msearch grep `Picard.*naturality|units.*restriction|units.*pushforward`
returned zero Mathlib hits. Direct rg in pinned Mathlib, WeilConjectures and
lean/Sheaf found the canonical Hilbert-90 map and dual-number specializations;
I opened GmPicardPullback, which is instead an etale-cohomology theorem for
curves over algebraically closed fields. Neither it nor the dual-number results
state this arbitrary-scheme Zariski square. Searches for the two new names in
the DAG, Mathlib and both source libraries found no declaration. DAG concept
searches reveal no existing node for these two specialized canonical maps.
LeanSearch for the inverse-image adjunction cohomology map returned Internal
Server Error; this is recorded as unavailable, not as a successful negative
search.

Validation: lcompile compiled the new dependency module alone, then compiled the
item module against it, with exit code 0 and no warnings. Both lean.statement records were checked
against the actual signatures; no unbound universe or variable, file-local
notation, private definition, or hollow hypothesis occurs. No mathematical
mismatch was found and no correct code was rewritten.

## Second reading by U1

Independent second reading on 2026-10-12. I opened the delivered item node, new
definition node, both Lean modules, all existing statement-dependency records,
and their recorded source declarations. I read the local Stacks TeX at
varieties.tex lemma-lift-line-bundle-from-reduction-dimension-1 (09NY),
cohomology.tex lemma-h1-invertible (09NU), section-functoriality (01F7), and
lemma-cohomology-and-closed-immersions (02UV). The Noetherian and dimension
assumptions in 09NY concern surjectivity, not the compatibility isolated here;
02UV requires only a closed embedding. Schemes supply the local stalk rings
required by 09NU.

Object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Schemes X and Z: `{Z X : Scheme.{v}}`. Arbitrary schemes, unrestricted
   bound universe, with no extra field, finiteness or regularity assumptions. Exact.
2. Closed immersion Z to X: `(i : Z ⟶ X) [IsClosedImmersion i]`. Mathlib's
   class is a closed embedding with surjective stalk maps. Exact.
3. Every invertible module L: `(L : X.Modules) [Modules.IsInvertible L]`.
   The recorded scheme class requires local triviality on neighbourhoods of every
   point. `Pic.ofIsInvertible L` uses its existing bridge to the Picard skeleton.
   The representative of every Picard element has this class (Picard/Group). Exact.
4. Pullback class: `(Modules.tensorPullback i).obj L`, with the existential
   invertibility witness `h` used by `@Pic.ofIsInvertible Z ... h`. TensorPullback
   changes rings on the abelian inverse image and sheafifies the tensor formula.
   The witness asserts well-definedness of this fixed pullback, with no additional
   input hypothesis or alternative module choice. Proof irrelevance removes any
   dependence on h. Exact rendering of the Picard pullback.
5. Hilbert-90 identifications: `Pic.toH1Units X` and `Pic.toH1Units Z`.
   GmPicard defines these using the generator torsor and torsor classification;
   its toH1Units_mk identifies the class with Isom(O,L). Exact canonical maps.
6. Units sheaf map: `unitsSheafToPushforward i`. Its body whiskers `i.c` by
   `CommRingCat.unitsAddCommGrp`; UnitsTorsor defines unitsSheaf by precisely
   that functor applied to the structure sheaf. Thus every component is the
   structure-sheaf homomorphism on units. Exact.
7. Induced degree-one map: `Sheaf.H.map (unitsSheafToPushforward i) 1`.
   I read H.map: it postcomposes Ext classes with the specified sheaf map.
   H is Ext from the constant integer sheaf, as in Hilbert 90. The dependency
   H' at the terminal open uses the sheafified free representable of that open,
   representing the same global-sections functor; no new cohomology is defined. Exact.
8. Closed-immersion comparison: `unitsPushforwardCohomologyComparison i 1`.
   I read H.mapFunctor and constantSheafsheafPullbackIso. The latter goes from
   pulled-back constant sheaf to constant sheaf, so `.symm.app` has exactly the
   direction required for Ext precomposition. Exact inverse image transports
   the Ext class, then H.map of the adjunction counit gives H on Z. This is the
   canonical restriction, inverse to the exact-pushforward identification of
   02UV for closed embeddings. The dependency theorem offers only Nonempty
   of an iso, not a named canonical map to reuse. Exact.
9. Square commutes: the equality applies (7) followed by (8) to the class of L
   and equates it to the class of the fixed tensor pullback under (5).
   Quantification over all L covers all Picard classes. No conclusion is lost
   or extra mathematical assertion imposed beyond pullback well-definedness. Exact.

New-node review: def-sc-zariski-units-restriction introduces two specialized
canonical maps for arbitrary scheme morphisms and degrees p in N. Its source's
functoriality construction has precisely this meaning, including p = 0; the
closed-immersion comparison specializes it. The node's statement introduces
all objects, cites exactly its three stmt_deps, and has the required definition
node fields, empty proof fields, source places, ancestor/via, searches, creation
record, chapter/unit and lean record. Its module uses existing sheaf, Ext and
adjunction definitions; both new definitions contain actual data and no sorry.
No dependency module or statement correction is delivered.

Edge cases: identity immersion gives the identity restriction; empty Z yields
the unique Picard class and zero H1; empty X forces empty Z. The zero module is
allowed precisely where it is invertible (including empty schemes). The
structure sheaf gives the zero class. Nonreduced schemes and all characteristics
are covered. There is no index set restriction; p = 0 is included in the new
comparison. Universes are explicitly bound; both schemes can live in any common
scheme universe. No variable is auto-implicit.

Independent searches, with queries different from the first worker:

- msearch LeanFinder: `Naturality of the Zariski first Chern class of line
  bundles for closed embeddings`: eight scheme-section naturality hits, none
  the Picard/H1 compatibility.
- msearch Loogle: `"unitsSheaf"`: zero hits.
- msearch LeanFinder: `Canonical map from cohomology of a direct image abelian
  sheaf using the inverse image counit`: eight hits on cohomology presheaves,
  global-section naturality, module pullback and sheaf adjunction; none supplies
  the specialized units comparison.
- msearch grep: `units.*cohomology.*(restriction|comparison)|Pic.*naturality`: zero hits.
- Direct rg of Mathlib, WeilConjectures and lean/Sheaf with
  `units.*(restriction|comparison|pushforward)|picard.*naturality|toH1Units|h1.*restriction`
  found the Hilbert-90 map and special dual-number naturality, not this result.
  I opened the project's GmPicardPullback: it concerns etale cohomology and
  curves over algebraically closed fields, a different statement.
- Direct DAG and source searches for `units.*cohomology` and both delivered
  definition names found no existing node/declaration for these Zariski maps.
  General etale cohomology restriction nodes do not define these specialized
  maps. The worker's unavailable LeanSearch is recorded honestly.

Mismatch/change log: no mathematical, typing, dependency or convention mismatch
found. The two Lean modules and node records remain unchanged. I added this
independent section under the required exact heading; the worker report remains.
All declaration docstrings name their source and blueprint node; the main theorem
docstring follows all three DAG proof steps. Only the theorem proof is sorry;
there are no file-local notations, private copies or hollow definitions.
Normalized source signatures agree verbatim with the lean.statement records.

Validation: lcompile compiled both delivered modules together in dependency order
with exit code 0 in 22.8 seconds, no errors and no warnings.
