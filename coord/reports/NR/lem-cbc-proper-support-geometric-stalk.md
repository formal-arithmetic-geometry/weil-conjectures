## Worker report

The delivery states `AlgebraicGeometry.Etale.properSupport_geometricStalk` in
`Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk`. Its proof is `sorry`.
It also defines `AlgebraicGeometry.Etale.SectionHasProperSupport`, with no postponed data
or proofs, in `Sheaf.AlgebraicGeometry.EtaleSectionProperSupport`.
The original mathematical statement is unchanged.

Hypotheses and clauses are rendered as follows.

- The arbitrary commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`.
  This is the recorded ModuleCat encoding of module etale sheaves, not the alternative
  constant-ring-sheaf/SheafOfModules encoding.
- Schemes are `{X Y : Scheme.{u}}`; the specified morphism is `(f : X ⟶ Y)`.
  Separatedness and local finite type are `[IsSeparated f] [LocallyOfFiniteType f]`.
  No quasi-compactness, noetherian, torsion, characteristic or finite-type-over-field
  assumption is imposed.
- A geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `(y : Spec (.of Ω) ⟶ Y)`. The geometric fibre is `pullback f y`, its map to X is
  `pullback.fst f y`, and its structure morphism is `pullback.snd f y`.
- F and G are `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and the corresponding
  category over Y. The inclusion of the subsheaf is a morphism
  `i : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F` with `Mono i`.
  A mono together with its image identifies G with precisely a subsheaf; no arbitrary
  extra structure is assumed.
- For every `V : Y.Etale` and every section s of `F` on `f.Etale.obj V`, the hypothesis
  `(∃ t, i.hom.app (op V) t = s) ↔ SectionHasProperSupport ... s` says exactly that
  the image of G(V) is the set of sections with proper closed support.
  The source's base-change object has order `pullback V.hom f`, so its map to V is
  `pullback.fst V.hom f`, as used by the support predicate. This is canonically the
  source's X times_Y V with reversed factors, not an assumption on V.
- The support predicate quantifies over points of V and geometric lifts v into V,
  tests the actual `toPresheafFiber` germ of s at `v ≫ V.hom`, and uses `≠ 0`.
  Its closed set Z is required to equal that locus exactly. Its properness is the
  dependency's `Scheme.IsClosedSubsetProperOver p Z`, using the reduced induced
  closed subscheme. Thus this is section support, not support of the whole sheaf.
- The source stalk is `(Scheme.pointSmallEtale y).sheafFiber.obj G`.
  Inverse image on the fibre is `upperStar ... (pullback.fst f y)`.
  Global sections are evaluated at the terminal etale object
  `op (Scheme.Etale.mk (𝟙 (pullback f y)))`, using `sheafSections`.
- The existential `S : Submodule Λ (...)`, with its membership iff, is exactly
  H^0_c: its underlying elements are all and only the fibre sections with proper
  support over Spec Omega. The statement asserts that this set is a submodule,
  rather than assuming closure or postponing a proof needed for a definition.
- The isomorphism `e : ... ≅ ModuleCat.of Λ S` is a Lambda-linear isomorphism.
  The equation `e.hom ≫ ModuleCat.ofHom S.subtype = sheafFiber.map i ≫ c.app F`
  is the required agreement after inclusion with ordinary restriction from the
  stalk of the direct image.
- The ambient restriction `c` is a natural transformation on ALL module sheaves F.
  Its first conjunct characterizes every component on every pointed neighbourhood
  `(V,v)` by the existing `geometricFibreSectionRestriction`. This explicitly says
  to pull a representative back with the inverse-image unit and restrict along
  its pointed fibre lift. Thus the factorization specifies the actual restriction,
  rather than some abstract isomorphism.
- Naturality in F is encoded by the natural transformation c. For a sheaf map F to F'
  and induced map G to G', the square for the displayed e commutes after the injective
  inclusions S and S' into their global-section modules, by naturality of c and i.
  Hence it commutes already in the support submodules. The membership iff uniquely
  determines S, and the factorization through its subtype uniquely determines e.
  The existential choices of these presentations therefore do not weaken naturality.

Dependency declarations used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, its morphisms.
- Mathlib.AlgebraicGeometry.Morphisms.Proper and FiniteType:
  `AlgebraicGeometry.IsSeparated`, `IsProper`, `LocallyOfFiniteType`; base-change instances.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`.
  Their full generic coefficient-category signatures and docstrings were read in
  the read-only slopmaster2 source. They accept ModuleCat, as the recorded convention says.
- Mathlib.CategoryTheory.Sites.Point.Basic: `GrothendieckTopology.Point.sheafFiber`,
  `toPresheafFiber`; Mathlib.AlgebraicGeometry.Sites.EtalePoint:
  `Scheme.pointSmallEtale`. The fibre is the set of actual lifts and the stalk is the
  colimit over pointed neighbourhoods, with no choice of another stalk construction.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`; the geometric point is inline,
  as in its node's record. Mathlib's `Scheme.SpecToEquivOfField` signature was inspected.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  `pullback`, `pullback.fst`, `pullback.snd`; their declarations were read.
- Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase:
  `Scheme.IsClosedSubsetProperOver`; its full definition and docstring were read.
- Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms:
  `Etale.geometricFibreSectionRestriction` and its defining `geometricFibreSectionLift`.
  Their complete definitions were inspected; no substitute restriction is introduced.
  The already-landed node `lem-sbc-geometric-fibre-exchange-germs` is added to stmt_deps.
- The recorded etale-sheaf module `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
  is publicly imported. That recorded upstream source file is absent in both local
  source locations; the existing local EtaleSheaves statement module and the node's
  explicit ModuleCat convention were inspected instead. The recorded import is
  available on the server and compiled successfully, without a replacement module.

The stated proof dependencies' recorded modules are imported without `public`:
InverseImageStalkGerm, EtaleSectionZeroOpen, NagataCompactification, Compactification.Defs,
OpenClosed.Complex, OpenImmersion.FiniteComparison, ProperGeometricPointExchange,
and GeometricPointPullbackStalk. Properness, reduced closed subschemes, geometric
stalks and underived exchange are already imported through the public dependencies.
Nodes with no recorded module contribute no invented imports.

Edge cases checked before drafting: X empty, V empty and empty geometric fibre give
zero section modules and the zero support submodule. The zero section has empty support;
the zero coefficient ring and zero sheaf are allowed. Non-quasi-compact X is allowed:
there is no CompactSpace or QuasiCompact binder. Omega need not be algebraic over the
residue field, and arbitrary schemes and coefficient rings in their recorded universes
are allowed. All universe parameters and variables are bound explicitly; no local notation,
private definition, local instance or statement-level let is used.

Searches for the item: msearch leanfinder, query "Geometric stalk of direct image with
proper support equals compactly supported sections on the geometric fibre", returned eight
structure-sheaf/topological-stalk lemmas, not this small-etale proper-support formula.
Loogle query `AlgebraicGeometry.Etale.lowerStar, CategoryTheory.GrothendieckTopology.Point.sheafFiber`
returned no hits (unknown lowerStar in that search service).
Mathlib grep `properSupport|proper_support|compactSupport` in AlgebraicGeometry gave no hits.
Project rg for those concepts found derived lower-shriek and whole-sheaf support material,
not this statement. `grep -rn` for the item's id in WeilConjectures gave no hits.
Name-collision rg in Mathlib/project/DAG names found no existing declarations under either
new declaration's name. The exact source proof, Stacks more-etale.tex label
lemma-stalk-f-shriek-separated, was read, including the precise ambient restriction map.

Validation: scompile.py compiled EACH delivered module on the server in dependency order,
cleanly, with nice 19, two threads, and the 60-second per-file limit. No local compiler ran.

## New nodes

`def-cbc-etale-section-proper-support` defines proper support of a SINGLE section on an
arbitrary etale object, over a specified locally finite type morphism p. Source:
Stacks 04FT (nonzero-germ support) and 0F76 (proper support). Existing def-kun-support is
support of an entire sheaf; def-weil-pbc-closed-subset-proper-over-base supplies properness
of a closed subset and support of an O_X-module, neither of which is this notion.
The new definition directly reuses that node for properness and the recorded geometric
stalk germ map for its locus.

Searches: blueprint_refs.py search "section support" gave 0 blueprint nodes; the broader
"proper support" search returned only cohomology/constructibility blueprint units.
DAG support definition nodes and project etaleSheafSupport were inspected.
LeanSearch "Support of a section of an etale module sheaf defined by its nonzero geometric
germs" was unavailable (Internal Server Error).
LeanFinder "A section of an etale sheaf of modules has closed support proper over the base"
returned eight hits about algebra etale loci, structure-sheaf vanishing, ideal-sheaf supports
and algebraic-module support, none about small-etale module sections.
Mathlib msearch grep and rg in WeilConjectures and lean/Sheaf for
`SectionHasProperSupport|sectionSupport|supportOfSection` gave no hits.
The new node's mathlib_searches records these results, including the unavailable service.
No dependency module or statement correction was needed. No STATEMENT-DISPUTED fault found.

## Second reading by NR

I read the node and both delivered modules independently against Stacks
more-etale.tex, section "Sections with compact support", especially
lemma-stalk-f-shriek-separated (0F76), its full proof, the definition of compact
support, and the definition of the proper-support subsheaf. I also read
etale-cohomology.tex, lemma-zero-over-image (including its geometric-germ clause),
definition-support and lemma-support-section-closed (04FT). The section-wide
assumptions are separatedness and local finite type; neither torsion nor a
Noetherian base is assumed. The scalar-module version keeps the same argument
and scalar-linear restriction maps.

Object/hypothesis/conclusion checklist (each item passes):

1. Arbitrary commutative coefficient ring Lambda: `(Λ : Type (u + 1))
   [CommRing Λ]`. This is precisely the recorded ModuleCat convention for the
   six-functor chapters, not a finite ring or a field.
2. Arbitrary schemes X,Y and the specified morphism f: `{X Y : Scheme.{u}}`
   and `(f : X ⟶ Y)`. The only geometric conditions on f are
   `[IsSeparated f] [LocallyOfFiniteType f]`, exactly the source's assumptions.
3. F is a Lambda-module sheaf on X_et: `Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} Λ)`. G is a sheaf on Y_et, and
   `i : G ⟶ (lowerStar ... f).obj F` with `Mono i` presents a subsheaf.
   The generality includes arbitrary presentations of that subsheaf.
4. For EVERY etale V and EVERY section s, the image-membership equivalence
   `(∃ t, i.hom.app (op V) t = s) ↔ SectionHasProperSupport ... s`
   identifies G(V) exactly with the proper-support sections. Neither inclusion
   is omitted. Upstream lowerStar evaluates on `f.Etale.obj V`, whose underlying
   scheme is `pullback V.hom f`; hence `pullback.fst V.hom f` is its map to V.
   This reversed-factor presentation is the canonical fibre product, not a
   different base or a condition on V.
5. A geometric point y is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
   and `y : Spec (.of Ω) ⟶ Y`. The geometric fibre and its two projections are
   `pullback f y`, `pullback.fst f y` and `pullback.snd f y`.
6. The coefficient sheaf on that fibre is
   `(upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F`.
   The target global-section module is evaluation at
   `op (Scheme.Etale.mk (𝟙 (pullback f y)))`, the terminal etale object.
7. H^0_c is presented as `∃ S : Submodule Λ (...)` with
   `∀ s, s ∈ S ↔ SectionHasProperSupport ... (pullback.snd f y) s`.
   Thus every properly supported fibre section and only those sections occur;
   closure is asserted, not assumed in a hypothesis or hidden in a definition.
8. The source is `(Scheme.pointSmallEtale y).sheafFiber.obj G` and
   `e : ... ≅ ModuleCat.of Λ S` gives exactly the Lambda-linear isomorphism.
9. The restriction map is specified on EVERY pointed neighbourhood `(V,v)`:
   `toPresheafFiber ... ≫ c.app F = geometricFibreSectionRestriction ...`.
   I read both `geometricFibreSectionRestriction` and `geometricFibreSectionLift`:
   they use the inverse-image unit, then the lift with projections
   `f' ≫ v.left` and `g'`, then restriction to the terminal etale object.
   This is the representative restriction in the first paragraph of 0F76.
10. Compatibility with the ambient inclusion is exactly
    `e.hom ≫ ModuleCat.ofHom S.subtype = sheafFiber.map i ≫ c.app F`.
    It specifies the actual restriction, not an arbitrary linear isomorphism.
11. Naturality in F is encoded by `c` being a natural transformation on ALL
    module sheaves. The support membership clause uniquely fixes S, and the
    displayed factorization uniquely fixes e because S.subtype is injective.
    For a map F -> F', its image on fibre sections preserves proper support:
    its support is closed and contained in the old proper support. The induced
    maps on G and S consequently give the naturality square; after inclusion
    it is the naturality square for c, and injectivity cancels the inclusion.
    Thus the existential presentation does not omit the naturality clause.

Dependency declarations were opened, not identified by their names alone:
Mathlib's Scheme and Hom; LocallyOfFiniteType, IsSeparated and IsProper;
pullback/fst/snd; pointSmallEtale and Point.sheafFiber/toPresheafFiber;
sheafSections; and upstream UpperLowerStar.Defs.lowerStar, upperStar and
upperStarLowerStarAdjunction. The latter are generic in the coefficient
category and accept ModuleCat with its existing instances. I read the project's
ClosedSubsetProperOverBase.IsClosedSubsetProperOver: it uses the vanishing
ideal's reduced closed subscheme followed by the given base morphism. I also
read the existing GeometricFibreExchangeGerms definitions used in item 9.
No dependency module is needed, and no pro-etale framework is used.

New-definition review: def-cbc-etale-section-proper-support has exactly the
objects, germ locus and properness condition of its natural statement.
`SectionHasProperSupport` existentially binds a closed Z EQUAL to the locus
of nonzero germs, over geometric lifts into V, and reuses
`Scheme.IsClosedSubsetProperOver p Z`. In particular it measures the support
of s, not whether the entire stalk module is nonzero. The existential choice
of geometric point matches the source's point-independent zero-germ criterion
in lemma-zero-over-image. No chosen support or other data are postponed, and
the definition contains no sorry. Its local-finite-type binder is the
hypothesis of the recorded proper-over-base notion and holds in both uses in
the main theorem. I checked the new-node schema against brief-stage2 section 5:
chapter/unit, creation and blueprint ancestry, exact dependency citations,
empty proof fields, null match, audit states, three search kinds and Lean
record are present. No existing DAG definition supplies this individual-section
notion: def-kun-support defines support of an entire sheaf/complex, and the
closed-subset-proper-over-base node defines properness and O_X-module support.

Edge cases: empty X, empty etale V and empty geometric fibre give the zero
section module with empty support. The zero section, zero sheaf and zero
coefficient ring are included. Empty Y admits no y, as it should. No index
set or positive-degree n is introduced (this is degree zero). Every field
characteristic is allowed; Omega is not required to be algebraic over the
residue field. Non-quasi-compact X and non-Noetherian Y are included.
All schemes and geometric fields use the same arbitrary universe u, and
coefficient modules the recorded u+1 convention. Every variable/universe is
bound; there is no independent smaller test universe or hidden smallness
hypothesis.

Independent searches (via msearch.py, with queries different from the worker):

- LeanFinder, "Stalk of extension by proper supports is compactly supported
  sections of the geometric fiber": eight hits, including TopCat.stalkToFiber,
  ModuleCat.Tilde.stalkToFiberLinearMap_germ and skyscraper adjunction maps.
  Their returned types concern topological/structure-sheaf stalks, not this
  small-etale proper-support comparison.
- Loogle, `"support" "stalk"`: rejected as an invalid query; this is not
  evidence of absence.
- LeanSearch, "Nonzero germ support of an etale sheaf section proper over a
  scheme": unavailable (Internal Server Error).
- LeanFinder, "The support of a local section of an etale module sheaf is the
  locus of nonzero geometric germs": eight hits about ringed-space germs,
  algebraic etale loci and basic opens; none defines etale section support.
- Independent rg for `proper.?support|compact.?support|support.?section|
  section.?support` in Mathlib AlgebraicGeometry, upstream WeilConjectures
  and project lean/Sheaf finds derived compact-support functors and coherent
  module support results, not either delivered declaration. I inspected
  EtaleSupport.lean's etaleSheafSupport to rule out the closest existing notion,
  and searched DAG definition nodes for section support. No exact reuse found.

No statement mismatch, new-node fault or hollow definition was found. The
original natural statement, both Lean signatures and both module bodies are
unchanged. The theorem has only its intended sorry; its docstring follows
all seven proof steps (support/base change, open extension, quasi-compact
reduction, Nagata, the two compactification comparisons, proper exchange and
naturality). Both module and declaration docstrings contain their source and
blueprint references. There is no local notation, private copy or local instance.
The two node `lean.statement` strings were compared with the file signatures
and match verbatim; all lines are at most 100 characters.

Validation: I compiled BOTH delivered files together through scompile.py on the
server, each separately in dependency order, nice 19, two threads, 60 seconds
per file. EtaleSectionProperSupport took 1.3 s and ProperSupportGeometricStalk
1.7 s; both succeeded with no errors or unexpected warnings. No local compiler
or global build was run. The only change of this second reading is this report
and the automatically recorded independent search log.
