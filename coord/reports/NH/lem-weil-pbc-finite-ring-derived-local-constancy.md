## Worker report

The previous prerequisite wait is resolved: def-kun-constant-sheaf now records
Functor.mapHomologicalComplex, with its exact constant-sheaf specialization.
The delivered theorem is AlgebraicGeometry.Etale.finiteRing_derived_local_constancy.
All proofs introduced here are sorry; all definition data are explicit.

Hypothesis and clause correspondence:
- X : Scheme and B : Type (u+1), [CommRing B], [Finite B] render the scheme and
  finite commutative coefficient ring. The small etale category has object
  universe u+1 and morphism universe u; no equality of these sizes is imposed.
- K is in DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat B)).
  hbounded gives integer lower and upper bounds on homologyFunctor K.
  hlisse uses Scheme.IsFiniteLocallyConstantSheaf for each homology sheaf:
  local constancy as a module sheaf and finitely generated module stalks.
  Since B is finite, finite generation is equivalent to finite underlying stalks.
- The first conjunct supplies Cover etalePrecoverage X and, on each member,
  a cochain complex E with bounded terms, all finite, and an isomorphism from
  the restricted K to Q of the termwise constant-sheaf complex E.
- The second conjunct quantifies over L with exactly the same hypotheses.
  Its two predicates apply to presheafToSheaf of derivedHomPresheaf and
  derivedIsoPresheaf. Scheme.IsFiniteLocallyConstantSheafOfTypes says local
  constancy and finite geometric stalks; there is no nonemptiness hypothesis.
- The third conjunct spells out the fibre assertion on constant models E,G:
  their sheafified derived Hom presheaf is isomorphic to the constant sheaf
  with value (Q E ⟶ Q G) in D(B). This universal constant-model statement
  transports along the model isomorphisms furnished by the first conjunct.
- The fourth conjunct assumes ConnectedSpace X and quantifies over every
  algebraically closed geometric point x. It provides a cover with restricted K
  isomorphic to the constant derived object obtained by the exact stalk functor
  at x. The additive structure of this stalk functor is explicitly obtained
  from preservation of binary products rather than postulated. The site point
  is canonically lifted to universe u+1 so the existing AB5 instance applies;
  Point.uliftSheafFiberIso (WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic)
  identifies this fibre with the original geometric stalk. This transport
  changes no coefficient or scheme universe.
- No perfectness, freeness, finite Tor dimension, nonzero ring or nonempty
  scheme hypothesis is introduced.

Dependency interfaces read and used: Mathlib.AlgebraicGeometry.Sites.Etale,
Scheme.smallEtaleTopology; Mathlib.Algebra.Homology.DerivedCategory.Basic,
DerivedCategory and Q; Mathlib.CategoryTheory.Sites.ConstantSheaf,
CategoryTheory.constantSheaf; Mathlib.Algebra.Homology.DerivedCategory.HomologySequence,
DerivedCategory.homologyFunctor; Mathlib.CategoryTheory.Sites.Point.Basic,
Point.sheafFiber; Mathlib.AlgebraicGeometry.Sites.EtalePoint,
Scheme.pointSmallEtale. def-kun-constant-sheaf supplies the existing generic
Functor.mapHomologicalComplex, and def-constructible-locally-constant supplies
Scheme.IsLocallyConstantSheaf. The finite variant is the existing
Scheme.IsFiniteLocallyConstantSheaf in WeilConjectures.ConstructibleSheaf.Defs;
its set-valued variant Scheme.IsFiniteLocallyConstantSheafOfTypes is in
WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets (read through
scompile.py --source). All already recorded proof dependency modules are
imported, retaining the proof plan for stage 3.

Edge cases: the empty scheme admits the empty covering and has no geometric
point; the connected clause then has no x. The zero complex admits a zero
model in any degree interval. The zero ring is allowed. The isomorphism
presheaf and its sheafification can be empty. Integer bounds can be arbitrary,
and no finite projective dimension is demanded: Z/2 over Z/4 is included.
No statement correction or mathematical dispute was found.

Searches: msearch.py LeanFinder query "Bounded finite locally constant
cohomology on the etale site implies finite locally constant sheafified derived
Hom and isomorphisms" returned condensed-category constant-sheaf constructions,
not this theorem. Loogle "DerivedCategory, constantSheaf" returned no results
(unknown identifier constantSheaf). msearch.py grep
"derivedHomPresheaf|derivedIsoPresheaf" returned no hits. LeanSearch query
"Presheaf of derived morphisms on the etale site with restriction by exact
inverse image" returned Internal Server Error, recorded as unavailable.
Direct rg of WeilConjectures and lean/Sheaf for the two presheaf names and
upstream grep for the item id returned no declaration. The retained earlier
searches.jsonl includes the same three search kinds and further concept queries.
The source passages read are sites-cohomology.tex lemma-locally-constant
(Tag 094G) and lemma-locally-constant-map (Tag 09BE). The latter assumes a
perfect source; the present finite-source extension is explicitly identified
as the DAG's agent argument, not attributed to that Stacks lemma.

## New nodes

`def-weil-pbc-etale-derived-map-presheaves` owns the two presheaves and their
canonical restriction construction. Its module defines derivedMapRestrictionIso
using upperStarComp and mapDerivedCategoryCompIso, then conjugates exact
pullback of maps and isomorphisms by that comparison. The named theorem
derivedMapRestriction_laws postpones only the identity/composition coherence
asserted explicitly in the new node; its docstring gives the calculation.
The presheaves use these four proof clauses as their functor laws. There is
no arbitrary choice of restriction map or hollow data. The new node's source
is Tag 09BE's restriction of derived maps. DAG concept searches and
blueprint_refs.py search 'derived Hom' found no node defining this presheaf
(the only blueprint match was def-weil-complex-weights). LeanSearch was
unavailable, LeanFinder returned ordinary sheaf or condensed constructions,
and Mathlib/project grep found no exact presheaf construction. The full
search records are copied into the new node. This is an auxiliary notion,
not a restatement of the local constancy theorem.

Validation: scompile.py compiled both delivered modules separately with no errors
or warnings. The initial exact-stalk instance failure was repaired by the canonical
Point.ulift transport, preserving the original small-site universes. The first
preflight found a signature-record formatting mismatch (noncomputable prefix);
the record now starts at def, as preflight requires. No second-reading section
has been written by the author; that belongs to the independent reader.

## Second reading by NH

I independently read the delivered node and both modules, then the source section
sites-cohomology.tex, "Complexes with locally constant cohomology sheaves",
including lemma-locally-constant (094G) and lemma-locally-constant-map (09BE).
The former assumes a Noetherian coefficient ring and a bounded complex with
locally constant finite-type cohomology; a finite commutative ring is Noetherian,
so the statement has not omitted an extra assumption. The latter assumes a
perfect source. The node explicitly supplies its own finite-free approximation
argument for bounded finite source and target instead of invoking 09BE beyond
its hypotheses. I checked all eight proof steps against the theorem docstring.

Object/hypothesis/conclusion inventory, with Lean correspondence and verdict:

- Arbitrary scheme X: `X : Scheme.{u}`. No quasi-compact, Noetherian, separated,
  nonempty or characteristic assumption is introduced. Pass.
- Finite commutative ring B: `B : Type (u + 1)`, `[CommRing B] [Finite B]`.
  Neither a field, a nonzero ring, nor an invertibility condition is required.
  Pass.
- Small etale site and D(X_et,B): `X.smallEtaleTopology` and
  `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))`.
  I read the dependency records and the signatures of `smallEtaleTopology`,
  `DerivedCategory`, and `DerivedCategory.homologyFunctor`: these are the small
  etale site and the localization of cochain complexes, with its actual
  cohomology functors, not a bounded/perfect subcategory. Fixed-coefficient
  module-valued sheaves are the project's accepted constant-ring realization.
  Pass.
- Bounded K: `hbounded` asserts integer bounds outside which every homology
  object is `IsZero`. The absence of `a ≤ b` allows the zero object, and is
  equivalent to existence of an ordered interval after enlarging bounds. Pass.
- Finite locally constant cohomology in every degree: `hlisse` uses
  `Scheme.IsFiniteLocallyConstantSheaf`. I opened ConstructibleSheaf.Defs:
  its two inherited classes are local trivialization on the localized etale
  site and finite generation of geometric stalks. For B finite, finite
  generation is equivalent to finiteness of the underlying B-module. Testing
  separably closed points in that definition is equivalent to testing
  algebraically closed points, since the corresponding etale stalks agree.
  There is no finite-free or projective-stalk condition. Pass.
- Local bounded finite models: the first conjunct gives a jointly surjective
  etale `Cover`, and on each member an `E : CochainComplex (ModuleCat B) ℤ`,
  bounded in its terms and finite in every degree, with an isomorphism from
  derived restriction of K to `DerivedCategory.Q.obj` of the termwise constant
  complex. I read def-kun-constant-sheaf's new recorded signature and Mathlib's
  `Functor.mapHomologicalComplex`: it maps terms and differentials by the actual
  `constantSheaf` functor. The outer cover exists before its model choices,
  as required. Pass.
- Two inputs with exactly the same assumptions: the second conjunct quantifies
  over L, then its boundedness and finite-lisse cohomology, with no further
  assumption. Both `presheafToSheaf ... (derivedHomPresheaf B K L)` and its
  `derivedIsoPresheaf` counterpart satisfy
  `Scheme.IsFiniteLocallyConstantSheafOfTypes`. I read the live source via
  `scompile.py --source WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets`:
  this means constant on an etale cover with finite geometric stalks. Pass.
- Local Hom fibres: the third conjunct gives, for any bounded finite module
  models E,G on any U, an isomorphism of their sheafified derived Hom with
  `constantSheaf ... (DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj G)`.
  Transport through the model isomorphisms in the first conjunct gives precisely
  the stated local fibre, without choosing an unrelated finite set. U need not
  carry an arrow to X because this is the uniform constant-model calculation;
  applying it to each cover member supplies the node's clause. Pass.
- Isomorphisms possibly empty: the second conjunct uses the actual type of
  derived isomorphisms, not `IsIso` of an arbitrarily chosen morphism, and neither
  it nor the finite-set predicate requires nonemptiness. Pass.
- Connected clause: `ConnectedSpace X → ∀ Ω [Field Ω] [IsAlgClosed Ω] x, ...`
  places the connected assumption only on this clause and quantifies over all
  geometric points, as the scheme-conventions node specifies. It gives a cover
  of the whole X, not merely a neighbourhood of x. The model is the constant
  derived object obtained by applying the exact geometric stalk functor to K.
  I read `pointSmallEtale`, `Point.sheafFiber` and the live point-lifting module:
  `Point.uliftSheafFiberIso` identifies the displayed lifted point's fibre with
  the original stalk. The lift changes only the point's set universe. The
  additive structure is derived from binary-product preservation, not an extra
  hypothesis. Pass.
- No finite Tor dimension: there is no Tor, perfectness, projectivity, flatness
  or finite global dimension hypothesis anywhere. In particular the degree-zero
  module Z/2 over Z/4 is included. Pass.

New-node reading (H12/H13):
`def-weil-pbc-etale-derived-map-presheaves` introduces exactly the two missing
presheaves used by the source's restriction of derived maps. Its statement is
self-contained and cites its site and derived-category dependencies. Its fields
have the specified chapter/unit, worker origin, ancestry, empty proof lists and
null match; the item's dependency list cites it. I searched the DAG independently
by concept and checked the related SiteBoundedConstantModel module: it supplies
only local models, not either presheaf or this combined theorem. There is no
existing DAG node for these presheaves. No dependency repair module is present.

I read all six declarations of EtaleDerivedMapPresheaves. At U its object is
literally Hom (respectively Iso) between the upper-star restrictions to U.
`upperStarComp` is the canonical composition comparison of etale inverse image;
`mapDerivedCategoryNatIso` followed by `mapDerivedCategoryCompIso` gives the
correctly oriented derived comparison. Conjugation by its hom and inv defines
the restriction functions. For f:U→V the maps go from values at V to values at U.
The opposite-category `map_comp` arguments are correspondingly reversed. The
four laws of the sole postponed theorem are explicitly part of the new node's
statement, and its docstring explains unit/composition coherence and cancellation.
All definition data are explicit; only these proof fields are postponed. The
Hom and Iso presheaves are not arbitrary choices from existence assertions.

Edge cases: the empty scheme permits an empty covering, with no geometric point
at which the connected clause could demand a fibre. `ConnectedSpace` itself
includes nonemptiness according to the recorded connected-scheme definition.
Zero complexes and the zero ring are admitted; the model need not have any
nonzero terms. Bounds run over all integers, including degree zero and negative
degrees. An isomorphism sheaf between unequal local models can have empty stalks.
There is no restriction on residue characteristic. Universes use the established
etale convention: site objects u+1, arrows u, coefficient objects and derived Hom
values at u+1; no equality of object and arrow universes has been assumed.
All variables and universes are explicitly bound.

Independent searches (other words than the author's): LeanFinder query
"Finite coefficient etale complexes locally constant derived morphism sheaf bounded
cohomology" returned etale-locus/formally-etale algebra facts, no matching theorem
or presheaf. Loogle `"DerivedCategory", "Presheaf"` returned no hits. LeanSearch
"Sheafification of derived isomorphisms between bounded finite locally constant
etale complexes is finite locally constant" returned Internal Server Error
(unavailable, not evidence of absence). Direct rg across Mathlib, upstream
WeilConjectures and lean/Sheaf for derived Hom/isomorphism presheaves and derived
local constancy found no exact match; related hits were ordinary cohomology
presheaves, local constant models and tensor stability. `blueprint_refs.py search
'derived Hom'` found only the unrelated weights node. I also searched DAG filenames
for derived-map presheaves and finite locally constant nodes and inspected the
existing finite-lisse definitions rather than duplicating them. The wrapper has
recorded the independent service searches in searches.jsonl.

Mismatch repaired: the mathematical signatures, definitions and node records
needed no change. The main module omitted explicit imports for recorded Mathlib
proof dependencies (standard t-structure, orthogonality, derived representatives,
triangulated Hom exactness, connectedness, openness of etale morphisms and stalk
exactness). I added their eight modules as ordinary proof imports, retaining
all signatures verbatim and leaving the correct docstrings unchanged. This makes
the import closure reflect the stage-3 proof plan required by stage-2 rule 7.
No statement correction or citer audit is needed. Both theorem proofs remain
`sorry`; no mathematical assertion was proved during this reading.
