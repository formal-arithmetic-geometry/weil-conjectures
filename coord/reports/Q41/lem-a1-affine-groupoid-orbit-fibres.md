## Worker report

This is stage 2, not a second stage-1 split. Q05's independently reviewed PASS
completed the natural-language split only: the current node has no lean record.
The previous worker's stale-assignment diagnosis confused those two stages.
The delivery retains Q05's statement, ten proof steps and all other node fields;
it adds only lean and the missing groupoid-definition statement dependency.

The module Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres states
AlgebraicGeometry.affineGroupoid_orbit_fibres with proof sorry. Its docstring
carries all ten proof steps verbatim, with their dependency names. The auxiliary
module supplies real proposition data for the groupoid laws, with no sorry.

Hypothesis and clause correspondence:

- U=Spec A and R=Spec B: `{A B : CommRingCat.{u}}` and the explicit `Spec A`,
  `Spec B` in the morphism types. No reducedness, nonemptiness, Noetherian,
  injectivity of the relation, global freeness, or constant rank is assumed.
- The maps s,t,e,i,c are the five explicit binders, with c defined on
  `pullback s t`. The hypothesis `hgroupoid : IsSchemeGroupoid s t e i c`
  states exactly that these operations give groupoids functorially on test
  schemes. It retains the specified composition and inverse, rather than
  replacing the groupoid by a set-theoretic equivalence relation.
- Finite locally free s,t are `[s.IsFiniteLocallyFree]` and
  `[t.IsFiniteLocallyFree]`, the upstream finite + flat + locally finite
  presentation class. Neither projection is required to be etale.
- sigma and tau are `(Spec.homEquiv s).hom` and `(Spec.homEquiv t).hom`.
  C is their `RingHom.eqLocus`, Mathlib's equalizer subring. Its `subtype`
  is exactly C into A. No private invariant-ring definition is introduced.
- The canonical ordinary-point map to Spec C is `PrimeSpectrum.comap` of
  that subtype, exactly the underlying map of `Spec.map` of the inclusion.
  The first conjunct is its `Function.Surjective`.
- The second conjunct quantifies over all `u₀ u₁ : Spec A` and equates
  equality of their contracted primes with `∃ r : Spec B, s r = u₀ ∧
  t r = u₁`, including the source/target order of this node.
- Every algebraically closed field is quantified as `k : Type (max u v)`
  with `[Field k] [IsAlgClosed k]`. The extra universe v allows fields larger
  than the coordinate rings; it does not make the quantification vacuous.
  Affine k-points are unital ring maps `A →+* k`, `B →+* k`, and
  `C →+* k`, using the affine spectrum correspondence rather than an extra
  choice of scheme morphism. This also permits arbitrary characteristics.
- The third conjunct is surjectivity of restriction `a.comp C.subtype`.
- The final conjunct says restrictions of a₀,a₁ agree iff `Relation.EqvGen`
  of the relation `∃ r : B →+* k, r.comp sigma = x ∧ r.comp tau = y`
  holds. EqvGen is precisely the generated equivalence relation, so this
  states the exact fibre clause, not just preservation of orbits.

The dependency declarations and their signatures/docstrings were read:
Mathlib.AlgebraicGeometry.Scheme supplies AlgebraicGeometry.Scheme, its Hom,
Spec and Spec.map; Mathlib.AlgebraicGeometry.GammaSpecAdjunction supplies
Spec.homEquiv, the full ring-map/spectrum-map equivalence;
Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback supplies pullback,
pullback.fst and pullback.snd, with existence for schemes supplied by
Mathlib.AlgebraicGeometry.Pullbacks. The upstream
WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree supplies
Scheme.Hom.IsFiniteLocallyFree, read at lines 778–784. AlgebraicClosure,
IsAlgClosure and IsAlgClosed were read in their recorded Mathlib sources;
the field-point statement uses IsAlgClosed directly, as the node does.
Mathlib.Logic.Relation supplies Relation.EqvGen.
The new def-a1-scheme-groupoid supplies IsSchemeGroupoid.
Recorded proof-dependency modules are imported without public where they
are not already statement imports. Unstated proof prerequisites are retained
as node references and in the full proof docstring, not invented as declarations.

The published downstream finite-flat-affine-relation-quotient module has
helpers affineRelationInvariants and affineRelationQuotientMap. Importing
that theorem's module here would reverse the proof dependency and create
an import cycle once the maintainer adds this theorem's proof import there.
Using Mathlib's eqLocus and comap directly reuses the underlying notions and
does not introduce second helpers or arbitrary maps.

Edge cases checked: A=0 forces B=0 via the source coordinate map; both
spectra and all field-point sets are empty, so both surjectivities hold
vacuously. The identity groupoid has C=A and singleton fibres. The pair
groupoid of two points has diagonal invariant ring and one two-point
orbit. Disjoint unions permit varying source rank. The nonreduced alpha_p
translation groupoid in characteristic p is permitted: no reducedness or
etaleness hypothesis has entered. Empty test schemes cause no failure in
the groupoid axioms. No monomorphism of R into U times U is assumed; this
is the general groupoid statement, including nontrivial stabilizers.

Searches actually made through msearch.py:

- LeanFinder, "A finite locally free affine groupoid has invariant spectrum
  with surjective quotient map and orbit fibres": eight hits about affine
  spectra, finite maps and Galois group actions; no exact statement.
- Loogle, "RingHom.eqLocus, EqvGen, Groupoid": zero hits, with unknown
  identifier EqvGen; the actual Relation.EqvGen was subsequently read.
- Mathlib grep, "GroupoidObject|affine.*[Gg]roupoid|invariant.*[Oo]rbit":
  six hits in ramification and dynamics, no scheme groupoid statement.
- LeanSearch, "A groupoid object in the category of schemes with source
  target identity inverse and composition": eight ordinary Groupoid hits.
- LeanFinder, "An internal groupoid object in a category with pullbacks":
  eight ordinary Groupoid/Grpd hits, not an internal groupoid interface.
- rg of upstream WeilConjectures for this item id and affine groupoids:
  no declarations; rg of lean/Sheaf found downstream relation helpers,
  descent prose and unrelated simplicial groupoids.
- rg of DAG notions and blueprint_refs.py search "groupoid scheme":
  statements using groupoids and five blueprint nodes, no definition node.

No statement correction or STATEMENT-DISPUTED finding is needed. The source
Tag 03BL and the Tag 0231 definition were read in groupoids.tex. The reversed
source/target order relative to Stacks is already in the reviewed node and
is equivalent by inversion; the Lean follows the node exactly.

## New nodes

`def-a1-scheme-groupoid` introduces the previously missing predicate for the
specified scheme morphisms to give a groupoid, following Stacks Tag 0231,
the preceding ordinary groupoid axioms and the following septuple account.
The real-data Prop structure records identity and inverse endpoints,
composition endpoints, both identity laws, both inverse laws and associativity.
The last five laws quantify over arbitrary H and maps to the actual pullback,
checking their two projections. Such maps exist for every composable pair by
the pullback universal property; this presentation avoids a proof-dependent
choice of lift. Thus the laws are neither vacuous nor stronger than the source.
Naturality is automatic from precomposition of scheme morphisms. Absolute
schemes amount to the source definition over Spec Z, with no base structure
needed in the item's statement. The searches above are recorded verbatim
from the search log in mathlib_searches, together with the DAG/source grep
and blueprint search results. Ordinary CategoryTheory.Groupoid does not
encode these specified scheme morphisms, and no prior definition node was
found. This definition has its own module and is cited by the item.

## Validation

The required scompile.py wrapper compiled both delivered modules separately,
in dependency order, against the published library with the private overlay.
Both compiled cleanly, with no errors or non-sorry warnings. The final library
checks took 2.0 seconds for IsSchemeGroupoid and 7.5 seconds for
AffineGroupoidOrbitFibres; no build or compiler limit was changed.

## Second reading by Q41

Independent maintainer reading of immutable delivery aa28bbf3b3b6567dcc4c89605e927be60ef7428e.

Read packet.md first, check-brief2.md in full, the immutable item JSON, all six
statement-dependency JSON files, both delivered modules, their complete docstrings,
and the complete report. Read brief-stage2.md and delivery-errors.md, especially H.
The dependency records used are Scheme/Hom, Spec/Spec.map/Spec.homEquiv, pullback,
Scheme.Hom.IsFiniteLocallyFree, IsAlgClosed, and the delivered groupoid predicate.

Read the source clone's `literature/stacks-project/groupoids.tex`:
lines 2406–2500 (Tag 0231, definition-groupoid, preceding laws and septuple account),
4192–4224 (standing assumptions and equation-invariants), and 4368–4566
(Tag 03BK base change and Tag 03BL, lemma-points, including its proof).
The absolute scheme formulation is the case over Spec Z; no base hypothesis is lost.
The source lists ordinary endpoints in the opposite order in its statement, but
inversion makes the node's endpoint order equivalent. The Lean follows the node.

## Every hypothesis and conclusion

1. Objects: `{A B : CommRingCat.{u}}`, `Spec A`, `Spec B` give arbitrary commutative
   rings and their affine schemes. No domain, reducedness or nonzero assumption.
2. Morphisms: the binders s,t,e,i have precisely the required domains/codomains;
   c has domain `pullback s t`, i.e. the ordered composable-pair fibre product.
3. Groupoid hypothesis: both the delivered IsSchemeGroupoid and the selected landed
   IsGroupoidScheme record the endpoint identities, composition endpoints, both units,
   both inverse laws, and associativity, with c(a,b)=a after b. The delivered version
   quantifies over arbitrary maps into the pullback; the landed version uses its
   universal lift with universally quantified compatibility proofs. Existence and
   uniqueness of pullback lifts make these presentations equivalent. The first six
   equations ensure all required compatibility proofs exist, so the last laws are
   not vacuous. Naturality is precomposition of scheme morphisms. Testing only
   Scheme.{u} suffices to express the diagram equalities (take the pullback and
   triple-pullback as test objects); it does not impose a restriction on the laws.
4. `[s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]` are exactly finite, flat, locally
   of finite presentation, as the recorded FiberDegree class says; no global basis,
   constant degree, etaleness, monomorphism or finite-type-over-a-field is assumed.
5. sigma/tau: `Spec.homEquiv` has inverse `Spec.map`, so its two ring maps are exactly
   s-sharp and t-sharp. `RingHom.eqLocus` is the subring with carrier {a | sigma a=tau a}.
6. Canonical map: `PrimeSpectrum.comap C.subtype` is contraction along the actual
   invariant-subring inclusion, not an arbitrary map. Its surjectivity is conjunct 1.
7. Ordinary fibres: conjunct 2 quantifies all u0,u1 and is the exact iff with one
   r in Spec B and s(r)=u0, t(r)=u1. No equivalence closure weakens this clause.
8. Algebraically closed fields: `k : Type (max u v)` and Field/IsAlgClosed are the
   required generality. v is bound, arbitrary, and allows larger fields; smaller
   carriers can live in the larger universe. A,B share a universe as objects of the
   same Scheme category; there is no extra mathematical size hypothesis.
9. Field-point surjectivity: ring-hom restriction A -> k to C -> k is precisely
   U(k) -> M(k), by the affine spectrum correspondence, for arbitrary characteristic.
10. Field-point fibres: equality of restrictions iff Relation.EqvGen of pairs induced
    by B -> k is exactly the generated equivalence relation. EqvGen has the rel,
    refl, symm and trans constructors; it is not a quotient with extra relations.

## Exact dependency declarations inspected

In `/home/ubuntu/weil-src-slopmaster2`, read Mathlib declarations and docstrings:
- AlgebraicGeometry/Scheme.lean:42,74,470,479 (Scheme, Hom, Spec, Spec.map).
- AlgebraicGeometry/GammaSpecAdjunction.lean:559–590 (preimage, map_preimage,
  homEquiv and contravariant composition).
- CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:95–139 (pullback,
  projections, lift and existence), and AlgebraicGeometry/Pullbacks.lean:481–486
  (scheme HasPullback/HasPullbacks).
- Algebra/Ring/Subring/Basic.lean:853–860 (RingHom.eqLocus and exact membership).
- FieldTheory/IsAlgClosed/Basic.lean:62–80 (IsAlgClosed and roots), with the recorded
  AlgebraicClosure/IsAlgClosure interfaces in the statement dependency JSON.
- Logic/Relation.lean:355–360 (Relation.EqvGen).
- WeilConjectures/AlgebraicGeometry/Morphisms/FiberDegree.lean:778–784
  (IsFiniteLocallyFree extends precisely the three required properties).

Read the landed GroupoidScheme.lean in the Q41 clone, the entire declaration and
its owning def-a1-groupoid-scheme JSON. Read downstream affineRelationInvariants and
affineRelationQuotientMap: they are direct wrappers of eqLocus and Spec.map. Reusing
those Mathlib constructions inline creates no second definition, and avoids importing
a downstream theorem module just to use its wrappers.

The ten proof steps remain in order in the theorem docstring, with their cited nodes.
Line wrapping sometimes splits a hyphenated node id; no proof content was lost.
The proof goes through integrality/lying over (1), residue-field embeddings (2),
base change (3), determinant scalar extension (4), polynomial lifting of the norm
(5), finite geometric source fibre (6), prime avoidance (7), the norm prime criterion
(8), generated equivalence on field points (9), and a common algebraic closure for
ordinary points (10). In particular it does not assume nonflat base change preserves
the invariant ring. The elementary determinant and groupoid-closure steps are
legitimate; the non-elementary tools remain recorded proof dependencies.

## Searches, record checks, and findings

Independent LeanSearch query: “Internal groupoid in schemes with specified identity
inverse and composition” returned eight ordinary Groupoid/SmallGroupoid and Scheme
category hits, no internal scheme-groupoid interface. Independent LeanFinder query:
“Fibres of spectrum of invariants for finite locally free groupoid are orbits” returned
finite/profinite group-invariant orbit results and Galois-category results, not this
scheme-groupoid theorem. Direct rg searched the Q41 lean/Sheaf tree, upstream
WeilConjectures, Mathlib AlgebraicGeometry/CategoryTheory and dag/lean_names_upstream.json.

Finding H4/H12 at landing: the current Q41 clone has the exact same notion under
`def-a1-groupoid-scheme` / IsGroupoidScheme. It was absent from the immutable delivery's
parent and landed in commit c998dfb4b3f11a82afc2f5d13ce4414c6fa9a0d5 after this delivery.
This is a concurrent duplicate, not a mathematical failure. Drop the new duplicate
node and its module; the supplied replacement theorem and record use the landed
interface. The item already states the groupoid laws inline in its unchanged prose;
the replacement record explicitly names the owning landed definition node.

Finding H1/H11: the original “## Second reading by Q41” contains only “No second
reading by a worker ...”. It is not a real reading under the requested gates. The
complete replacement report preserves the worker report and supplies this independent
clause-by-clause reading under the required heading.

The delivered new definition itself agrees with 0231 and has the §1(A) fields,
three kinds of recorded search, source and blueprint docstrings, real Prop fields,
and no sorry. It is dropped only to avoid the concurrent duplicate. There are no
§1(B) dependency repairs or §1(C) statement corrections, no missing genuine DAG
prerequisite, and no source-based citer audit is triggered.

Read-only comparison to the immutable parent found exactly `lean` and `stmt_deps`
changed on the item; the latter only gained the new definition. Both delivered
lean.statement strings occur verbatim as their file signatures (before :=/where).
The corrected record likewise matches the complete corrected signature. Maximum
Lean line widths are 96 and 84. The only delivered proof body is the theorem's
`by sorry`; no local theorem is proved and no definition contains sorry.

The route-pivot dropped list at origin/newtargets-dag has no intersection with any
item stmt_deps/proof_deps. The named route-pivot repair-note path is absent. Neither
module introduces infinity/dg/model machinery or a pro-etale substitute. Historical
blueprint ancestry mentions pro-etale nodes, but those are not proof citations here.

## Edge cases and isolation

A=0 forces B=0 through the unital source coordinate map, so C=0 and both point sets
are empty; both surjectivities and fibre iff clauses hold. Identity groupoids give
C=A and singleton fibres. Finite discrete pair groupoids give the expected single
orbit. Nontrivial stabilizers and nonreduced groupoids (e.g. alpha_p in characteristic
p) are allowed. Varying finite locally free ranks are allowed, and no global rank or
nonempty test scheme is required. All variables/universes are bound.

No branch head or project clone was changed. No direct ssh, claim, merge, delivery,
lake build, global build, or live Lean write was performed. Only review.md and fixes/
are written. Compiles use the prescribed scompile.py wrapper on the exact snapshot
files, and then on the complete corrected theorem.

## Compiler evidence and final disposition

The immutable snapshot command was:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q41 lem-a1-affine-groupoid-orbit-fibres snapshot/lean/Sheaf/AlgebraicGeometry/IsSchemeGroupoid.lean snapshot/lean/Sheaf/AlgebraicGeometry/AffineGroupoidOrbitFibres.lean`.
It exited 0 with no errors or warnings. The wrapper compiled the private helper overlay,
preliminary helper, sandbox checks, and each library-path file separately. Final
library checks: IsSchemeGroupoid 12.1 s, AffineGroupoidOrbitFibres 7.3 s. The wrapper
also reported one sandbox wall time of 88.7 s, but returned success, not a Lean
execution timeout; no compiler limit was changed.

The complete fixed theorem was checked with the same wrapper:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q41 lem-a1-affine-groupoid-orbit-fibres fixes/lean/Sheaf/AlgebraicGeometry/AffineGroupoidOrbitFibres.lean`.
It exited 0 with no errors or warnings: sandbox 5.1 s, library-path file 3.1 s.
This machine's current prescribed scompile.py implementation submits the private
overlay checks to the server (its output says “Checking ... on the server”); it
supersedes the older local-compile implementation described in the brief. These
are wrapper/server confirmations, not a claim that I independently ran a local
Lean compiler. No direct ssh command or build was run.

Fix files accepted by the documented stage-2 merge format:
- `lean/Sheaf/AlgebraicGeometry/AffineGroupoidOrbitFibres.lean`: complete replacement.
- `lem-a1-affine-groupoid-orbit-fibres.lean-record.json`: complete corrected record.
- `lem-a1-affine-groupoid-orbit-fibres.report.md`: complete report replacement.

Use these with `--apply-fixes <this review directory>/fixes --drop-nodes def-a1-scheme-groupoid`.
The latter is essential to omit the concurrent duplicate node and its sole-owned
module. No mathematical correction, arbitrary map, hollow construction, added
assumption, silent universe restriction, or outstanding substantive finding remains.
The independent second-reading text is supplied in the report fix. FIX.
