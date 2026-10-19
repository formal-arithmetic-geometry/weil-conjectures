## Worker report

Repair of return L for immutable head edc1171a97e9: the item no longer refers to the
unavailable legacy names `closedUpperShriek`, `sectionsWithSupport`, or
`sectionsWithSupportι`. It imports the currently recorded dependency module
`Sheaf.AlgebraicGeometry.ProEtalePairFlasque` and uses its published finite-coefficient
support construction. The stale `PurFlasqueSupport.lean` and dependency node copy have
been removed from this delivery. No published dependency record is overwritten.

The only delivered module is `Sheaf.AlgebraicGeometry.PurSupportExact`. It defines the
termwise complex `supportedSectionsComplex` using the actual closed supported inverse
image followed by closed direct image. It states `shortExact_sectionsWithSupport`, with
one postponed proof. The support functors are existing definitions with real kernel data;
this delivery introduces no replacement support notion and no extra theorem. The helper
uses the existing `finiteSupportedSections_leftExact` theorem to provide preservation of
finite limits and hence zero morphisms for the closed supported functor, as required
by `mapHomologicalComplex`. Its complement argument and immersion instances are the
same ones already assumed by the main theorem. This is a local proof binding inside a
definition, not a file-local instance or an added assumption on the theorem.

Hypothesis and clause inventory:

1. Schemes and the closed/open maps are `{Z U X : Scheme.{u}}`, `(s : Z ⟶ X)` and
   `(j : U ⟶ X)`, with `[IsClosedImmersion s]` and `[IsOpenImmersion j]`.
2. The complementary condition is
   `hcompl : IsCompl (Set.range s.base) (Set.range j.base)`.
3. The source-based quasi-compactness assumption, retained from the previous corrected
   delivery, is `[QuasiCompact j]`. The statement_change and complete citer audit remain.
4. Finite commutative coefficients are `(R : Type (u + 1)) [CommRing R] [Finite R]`.
   The helper now explicitly binds `[Finite R]` because the published interface requires
   it; the main theorem already had exactly this assumption.
5. An integer cochain complex of all coefficient-module sheaves is
   `I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) ℤ`.
6. Termwise injectivity is `[∀ n, Injective (I.X n)]`.
7. The first object `s_*s^!I` is `supportedSectionsComplex R s j hcompl I`, obtained by
   `mapHomologicalComplex` for `finiteClosedUpperShriek R s j`, then `lowerStar` for s.
8. The middle object is I. The last object is I mapped termwise by
   `upperStar (ModuleCat R) j ⋙ lowerStar (ModuleCat R) j`.
9. The first arrow f is uniquely characterized in each degree by the closed adjunction
   unit on `(finiteSupportedSections R j).obj (I.X n)` followed by `f.f n` equalling
   `(finiteSupportedSectionsι R j).app (I.X n)`. This is the canonical transported kernel
   inclusion. Its transport is invertible by `finiteSupportedClosedComparison_isIso` in
   the recorded dependency, under precisely the complement and quasi-compact hypotheses.
10. The second arrow g satisfies `∀ n, g.f n =
    (upperStarLowerStarAdjunction (ModuleCat R) j).unit.app (I.X n)`.
11. `∃ w : f ≫ g = 0, (ShortComplex.mk f g w).ShortExact` asserts the zero composite,
    exactness in the middle, monicity of f and epimorphy of g, hence the displayed
    sequence with zeros at both ends. No boundedness or K-injectivity is assumed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtalePairFlasque` (def-pur-flasque-support):
  `finiteSupportedClosedComparison`, `finiteSupportedClosedComparison_isIso`,
  `finiteSupportedSections_leftExact`, and its
  public import `Sheaf.AlgebraicGeometry.ProEtaleSupportedSections`, which supplies
  `finiteSupportedSections`, `finiteSupportedSectionsι`, and `finiteClosedUpperShriek`.
  The supported functor is the kernel of the natural open adjunction unit in the functor
  category; its inclusion is kernel.ι. The closed inverse image is its composite with
  upperStar. These are the recorded construction, including its canonical kernel action.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`:
  `upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`. These are also the operations
  used by the recorded `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` module, now imported
  publicly through the pair-flasque dependency. No legacy star interface is imported.
- Mathlib `CategoryTheory.Injective`, `CochainComplex`, and
  `CategoryTheory.ShortComplex.ShortExact`, the recorded injectivity, complex and exactness
  interfaces. The latter is exactness together with Mono f and Epi g.
- The previously delivered usable proof imports (weakly etale localization, module
  sheafification, ringed-site modules) remain in the file. The now-recorded closed
  essential-image module is also imported for proof step 5. The proof docstring carries the
  six-step free-module extension argument, canonical kernel transport, and degreewise
  exactness criterion. No new proof dependency or statement correction is introduced.

Edge cases: the zero ring, zero complex, empty X, empty Z and empty U are allowed.
For empty Z the expected supported kernel is zero; for empty U the open target is zero
and the kernel is the original sheaf. Every integer degree occurs, including negative
ones. No field, characteristic, reducedness, boundedness or constructibility assumption
is added. The explicit u retains site objects in u+1 and morphisms in u; coefficient
modules are in u+1. There are no independent site-universe equalities or auto-bound
variables.

Searches in this repair:

- `scompile.py --source WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersion`
  confirmed the legacy definitions in source; the current DAG instead records the
  compatible finite-coefficient support interface, whose full source and docstrings were
  read in ProEtalePairFlasque.lean and ProEtaleSupportedSections.lean.
- `msearch.py ... leanfinder "short exact sequence canonical supported kernel open
  restriction unit injective pro-etale sheaves"`: eight hits on local injectivity,
  sheafification and Mayer–Vietoris, no theorem for this sequence.
- `msearch.py ... loogle "CategoryTheory.ShortComplex.ShortExact"`: the generic predicate
  and its lemmas, no pro-etale supported-section theorem.
- `msearch.py ... grep "support.*exact|sectionsWithSupport|finiteSupportedSections"
  Mathlib/CategoryTheory`: zero hits.
- `rg` in the upstream source and lean/Sheaf found the existing finite support definitions
  and only the etale `shortExact_supportsShortComplex` near-match. It is a different site,
  so it does not replace this item. Prior LeanSearch service failure is retained as a
  service failure rather than a no-match search.

The previous statement correction is unchanged. Its source was rechecked at
[Stacks Tag 09AH](https://stacks.math.columbia.edu/tag/09AH), which explicitly assumes a
quasi-compact complementary open immersion. No additional statement fault was found.

## Repair validation

Compilation and the dry run are performed with the prescribed wrappers on the final
single module. The second reader must independently check the repaired imports and
finite-coefficient names. The earlier independent review is retained below as historical
content; it does not assert that this repair has already received a second reading.

## Statement corrected

Original statement (verbatim):

For the closed–open pair of
supported sections and a termwise
injective complex $I^\bullet$ of $\Lambda$-module sheaves, there is
a short exact sequence of complexes

$$
0\longrightarrow s_*s^!I^\bullet\longrightarrow I^\bullet
\longrightarrow j_*j^*I^\bullet\longrightarrow0.
$$

The canonical s_*s^! identification was asserted for arbitrary complements, while the
corrected dependency and Stacks 09AH give it for quasi-compact complements. This is a
source error already established by the dependency's explicit counterexample, not a scope
change inferred solely from an inconvenient API. On X=Spec(product_n k), with closed
subscheme defined by the ideal of finite-support sequences, that counterexample supplies
a nonzero F with j^*F=s^{-1}F=0 and G_Z F=F. Embed F into an injective sheaf I. Its induced
map F→G_Z I is monic. Naturality of the closed unit makes its composite with
q_I:G_Z I→s_*s^!I zero because q_F has zero target. Thus no first map can satisfy the
canonical kernel-inclusion equation: that would make the monomorphism F→I zero.
The failure occurs for a termwise injective complex concentrated in degree zero. The
correction states the quasi-compact scope explicitly, as well as all inherited objects
and the canonical arrows. It changes no target unit statement. The A1 Kummer application
uses finite-type pairs and is unaffected.

Complete citer audit: exactly one DAG node has this item in stmt_deps or proof_deps,
`lem-pur-support-localization-triangle`. Opened its entire statement and proof, and the
construction `def-pur-support-triangle` it invokes. The citer is marked `holds: false`:
its current statement allows arbitrary complements and its first proof step needs the
now-explicit quasi-compact scope. The construction also writes the first map as the
inclusion, confirming the canonical-arrow requirement. There is no second DAG citer to
open. The non-node remark `rem-ptr-pur-support-triangle-2` was also read; its unrestricted
cone-to-quotient claim has the same scope issue. Neither citer nor remark was edited.

Source: Stacks proetale.tex Tag 09AH (`lemma-ses-associated-to-open`), read in TeX, and the
current corrected def-pur-flasque-support with its explicit counterexample. The changed
proof step now names the closed-unit comparison and cites
lem-exc-proetale-closed-essential-image; original proof and proof-dependency fields are
preserved in statement_change.

## Historical second reading by NF (before repair L)

This reading supersedes the earlier worker claims about arbitrary sequence maps and the
alias-based dependency interface. I opened the current item and dependency node records,
the Lean files, and the actual blueprint source on the literature mirror. I also read
Stacks proetale.tex `lemma-ses-associated-to-open` (09AH), sites-modules.tex
`remark-localize-presheaves` (03EJ), and homology.tex `lemma-cat-cochain-abelian` (0114).
09AH explicitly assumes a quasi-compact complementary open immersion. The blueprint's
unrestricted support identification was already corrected in the dependency's current
statement; the item's imported text had not inherited that correction explicitly.

Object, hypothesis and conclusion inventory, with the final Lean rendering:

1. Schemes X, Z, U in the chosen size convention: `{Z U X : Scheme.{u}}`.
   Verdict: exact; no Noetherian, separated, finite-type or field assumption.
2. Closed immersion s and complementary open immersion j: `(s : Z ⟶ X) (j : U ⟶ X)`,
   `[IsClosedImmersion s]`, `[IsOpenImmersion j]`, and
   `hcompl : IsCompl (Set.range s.base) (Set.range j.base)`.
   Verdict: precisely disjoint ranges whose union is X; no reducedness imposed on Z.
3. Finite commutative coefficients: `(R : Type (u + 1)) [CommRing R] [Finite R]`.
   Verdict: the inherited finite-coefficient convention, including the zero ring;
   no characteristic or invertibility restriction is imposed.
4. Quasi-compact open complement: `[QuasiCompact j]`.
   Verdict: necessary source-based scope correction, now explicit in the node with a
   `statement_change`; it was previously an unreported extra hypothesis in Lean.
5. All constant-coefficient pro-etale module sheaves:
   `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)`.
   Verdict: all sheaves, no constructibility. I read upstream `upperStar`, `lowerStar`
   and `upperStarLowerStarAdjunction`: they are the actual left Kan extension plus
   sheafification, base-change direct image, and their adjunction. I also read the
   recorded `ProEtaleInverseImage.lean`: its generic inverse/direct image declarations
   are these same canonical operations (the direct image is a transparent alias).
6. Integer cochain complex and injective terms: `I : CochainComplex ... ℤ` and
   `[∀ n, Injective (I.X n)]`.
   Verdict: exact. I opened Mathlib `Injective`, whose `factors` field is precisely the
   mono-extension property in def-sp-injective-resolutions. I read the recorded complex
   and short-exact APIs; no derived-category existence assumption is added.
7. First object s_*s^!I: `supportedSectionsComplex R s j hcompl I` applies the actual upstream
   `closedUpperShriek (ModuleCat R) s j`, then `s_*`, termwise.
   Verdict: exact. Upstream `closedUpperShriek` is literally `sectionsWithSupport ⋙ s^*`,
   and `sectionsWithSupport` is the kernel of the open adjunction unit, with kernel.map
   on morphisms. Neither is a new definition or a chosen unknown object here.
8. Middle object I and third object j_*j^*I: I and the termwise functor
   `(j)^*[ModuleCat R] ⋙ (j)_*[ModuleCat R]`.
   Verdict: correct order, on the same module category.
9. Canonical first arrow: the first new equation says, in each degree, that the closed
   adjunction unit on the supported kernel followed by `f.f n` is
   `(sectionsWithSupportι ...).app (I.X n)`.
   Verdict: this uniquely fixes the transported kernel inclusion, since that unit is an
   isomorphism under the corrected hypotheses. The former bare existential f did not
   specify it. I read `isZero_upperStar_sectionsWithSupport` and the existing
   `isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl`; they give exactly this
   comparison, without a constructibility assumption.
10. Canonical second arrow: the next equation is
    `∀ n, g.f n = (upperStarLowerStarAdjunction ... j).unit.app (I.X n)`.
    Verdict: this specifies restriction; the former bare existential g was weaker.
11. Short exactness: `∃ w : f ≫ g = 0, (ShortComplex.mk f g w).ShortExact`.
    Verdict: the zero composite, monic first map, exact middle and epic last map are
    precisely the displayed 0-to-0 sequence. Mathlib's ShortExact definition was opened.
    The quantifiers first introduce the given pair and I, then their canonical arrows;
    no extra lifting or existence hypothesis appears.

Dependency reading (H12/H13): no new DAG nodes. The copied def-pur-flasque-support is
unchanged outside `lean`. The first worker defined `purSupportedSections` and
`purExceptionalInverseImage` merely as aliases of existing constructions. I removed
both, and the theorem now uses the original upstream names. The dependency record
lists those exact existing declarations together with `IsPairFlasque` and the existing
closed-unit isomorphism theorem. Its module introduces only the missing pair-specific
predicate and the missing joint left-exactness statement
`purSupportFunctors_leftExact`. That theorem matches the dependency's left-exactness
clause and its proof step 3, and has the full sectionwise-kernel argument in its docstring.
The predicate is epimorphy of the open unit, not surjectivity on every object's sections.
The canonical support comparison is the existing closed unit, not an arbitrary map.

Import compatibility: a direct import of the recorded ProEtaleInverseImage wrapper
alongside upstream ClosedImmersion was tested and failed both locally and on the server:
the finite-coefficient and legacy modules redeclare the same upper/lower-star syntax.
The final module therefore uses the actual upstream upper/lower-star declarations already
imported by ClosedImmersion, which I checked against that wrapper's source, without
copying or redefining either functor. The other usable recorded proof interfaces are
imported: ProEtaleWeaklyEtaleLocalization, RingedSiteModules, and Mathlib's module
sheafification. Proof nodes without a recorded module cannot yet be imported.

Edge cases: empty X, empty Z (j is an isomorphism) and empty U (s has full range) are
allowed. Their open units and kernel inclusions give the expected zero and identity
sequences. The zero ring and zero complex are allowed; there is no Nontrivial binder.
Every integer degree, including zero and negative degrees, occurs; the empty-index-set
issue does not arise because there is no arbitrary index family. There is no coefficient
characteristic assumption. The universe u is explicit; scheme site objects and morphisms
retain their usual u+1 and u sizes, with R-modules in u+1, not an extra equality on the site
universes. There are no file-local instances, notation, private definitions or unbound
variables. Both definitions have real data. Both postponed theorems correspond to clauses
of their owning nodes and have source/blueprint and proof docstrings.

Independent searches: ran msearch.py leanfinder with “The canonical kernel inclusion and
open restriction unit form a short exact sequence for a complex of injective sheaves on a
pro-etale site”: the returned Mayer–Vietoris and injective-resolution exactness declarations
have different objects and hypotheses. Ran loogle `CategoryTheory.ShortComplex.ShortExact`
and opened the predicate: generic exactness only. Ran grep
`flabby|support.*exact|injective.*restriction` on Mathlib/CategoryTheory: zero matches.
Separately searched the upstream project and lean/Sheaf for closedUpperShriek,
sectionsWithSupport, support exactness and injective restriction. Opened the main near
match `AlgebraicGeometry.Etale.shortExact_supportsShortComplex`: it concerns the small
etale site, not the pro-etale site, and cannot serve this node. Opened the upstream
pro-etale support functors and reused them; no exact existing theorem for this item was
found. The worker's LeanSearch service failure is retained as unavailable rather than
claimed as a successful no-match search.

Mismatches repaired: unreported quasi-compactness; arbitrary arrows in place of the
canonical sequence; duplicate functor aliases; the dependency's omitted left-exactness
clause; missing blueprint/source docstrings on the module and helper; incomplete proof
steps in the target docstring; missing usable proof imports; and the recorded signature.
The node's lean.statement is generated from the final source declaration by the project's
signature parser. The old worker report above is retained as requested, as historical
content superseded by this reading.

## Second reading by NF

Independent reading of the post-return-L delivery, 2026-10-16. I opened the sandbox
node and module, the five statement-dependency node records and their declarations,
the published ProEtalePairFlasque and ProEtaleSupportedSections modules, the exact
finite-coefficient UpperLowerStar.Defs source in the group clone, and the inverse-image
wrapper and closed-essential-image module. There are no new nodes or dependency
modules in this delivery. The historical reading above predates repair L and is not
my evidence for the present interface.

I checked the corrected natural-language statement first. The original blueprint
lem-pur-support-exact.md was read from the server literature mirror. Its proof uses the
free-module injection for V times_X U into V and injectivity to extend sections. I also
read Stacks proetale.tex, lemma-ses-associated-to-open (09AH), in TeX from the Stacks
source. That lemma explicitly assumes a quasi-compact open complement. Its displayed
sequence is the extension-by-zero/closed-restriction sequence; applying its closed-unit
conclusion to the supported kernel gives the comparison used here. It is not being
mistaken for the injective supported-section sequence itself. The free-module lifting
argument in the blueprint supplies the latter's surjectivity. The correction therefore
follows the source's scope for the closed-unit identification, with no Noetherian,
separatedness or constructibility assumption inserted.

Object, hypothesis and conclusion inventory (each verdict concerns the repaired file):

1. Schemes X, Z and U: `{Z U X : Scheme.{u}}`. Verdict: exact; the ambient scheme
   universe is explicit and no base field or finiteness property of X is assumed.
2. Closed immersion and complementary open immersion: `(s : Z ⟶ X) (j : U ⟶ X)`,
   `[IsClosedImmersion s]`, `[IsOpenImmersion j]` and
   `hcompl : IsCompl (Set.range s.base) (Set.range j.base)`. Verdict: exact disjoint
   complementary images, with no reduced scheme structure imposed on Z. The dependency's
   `Set.range s` and `Set.range j` use the same underlying point maps.
3. Quasi-compactness of the open complement: `[QuasiCompact j]`. Verdict: exactly the
   corrected node and Stacks 09AH. It is an explicit hypothesis, not silently introduced
   by typeclass inference or confused with quasi-compactness of X.
4. Finite commutative coefficients: `(R : Type (u + 1)) [CommRing R] [Finite R]`.
   Verdict: exactly the node's inherited coefficient convention, including the zero
   ring. No field, characteristic or invertibility assumption occurs.
5. All coefficient-module sheaves on the small pro-etale site:
   `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)`. Verdict: the recorded finite
   constant-coefficient presentation, with no restriction to constructible sheaves.
   The dependency's actual support definitions use precisely this category.
6. Integer-indexed complex and termwise injectivity: `I : CochainComplex ... ℤ` and
   `[∀ n, Injective (I.X n)]`. Verdict: all integer degrees, no boundedness or
   K-injectivity hypothesis. I read Mathlib's Injective.factors, which is exactly the
   extension property along every monomorphism; no chosen injective resolution is
   substituted for the supplied complex.
7. First term s_*s^!I: `supportedSectionsComplex R s j hcompl I`. Verdict: its body maps
   I by `finiteClosedUpperShriek R s j`, then by `lowerStar (ModuleCat R) s`, termwise.
   I opened the former definition: it is `finiteSupportedSections R j ⋙ upperStar ... s`.
   I opened finiteSupportedSections: it is the kernel of the actual open adjunction
   unit in the functor category. The helper contains real functor data; its local
   `letI` is the existing left-exactness theorem's second projection, not postponed
   object data or a new theorem. No quasi-compactness is needed to construct this term.
8. Middle and last terms: I and the image of I under
   `(upperStar (ModuleCat R) j ⋙ lowerStar (ModuleCat R) j).mapHomologicalComplex`.
   Verdict: precisely I and j_*j^*I. I read upperStar (left Kan extension followed by
   sheafification), lowerStar (precomposition with base change), and their adjunction
   in the current finite-coefficient source, rather than relying on legacy names.
9. Canonical first arrow: `∃ f : supportedSectionsComplex ... ⟶ I`, with the equation
   `(upperStarLowerStarAdjunction ... s).unit.app
   ((finiteSupportedSections R j).obj (I.X n)) ≫ f.f n =
   (finiteSupportedSectionsι R j).app (I.X n)` for every n. Verdict: exactly iota q
   equals the kernel inclusion, in Lean's composition order. The dependency's
   finiteSupportedClosedComparison is this same whiskered closed unit; its isIso
   theorem assumes exactly the complementary pair and QuasiCompact j. Thus the
   equation uniquely determines f in every degree; it does not allow arbitrary arrows.
10. Canonical second arrow: `∃ g : I ⟶ ...`, with
    `∀ n, g.f n = (upperStarLowerStarAdjunction ... j).unit.app (I.X n)`.
    Verdict: precisely the open restriction unit, specified degree by degree.
11. Zero composite and short exactness:
    `∃ (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact`.
    Verdict: all clauses of 0 to s_*s^!I to I to j_*j^*I to 0. I opened Mathlib's
    ShortExact structure: it contains exactness, Mono f and Epi g. The existential
    arrows follow the given schemes, coefficients and I; the equations fix the
    canonical arrows. No extra conclusion such as a chosen splitting is asserted.

Edge cases: the zero ring, zero complex and empty scheme X are admitted. Empty Z and
empty U are admitted: respectively the supported term is zero or the open term is zero,
as expected from the kernel construction and closed comparison. Degree zero and negative
integer degrees are included. There is no arbitrary index family whose empty case could
be lost. There is no characteristic condition. The site retains object universe u+1 and
morphism universe u; module carriers have universe u+1. No equality between the site
universes, hidden EssentiallySmall hypothesis or auto-bound variable was added. Finite
rings in this coefficient universe include every finite ring up to its canonical size
transport, in the inherited convention.

Correction/citer audit: searching all DAG node JSON files for actual stmt_deps or
proof_deps occurrences gives exactly one citer, lem-pur-support-localization-triangle.
I opened its full statement and proof. Its first proof step invokes this sequence for
arbitrary complements, so `holds: false` in statement_change is correct. There is no
second DAG citer to inspect. I additionally opened def-pur-support-triangle, which that
citer uses: its first arrow is expressly the inclusion, reinforcing the need for the
canonical-arrow equations. No citer was edited and no target-unit statement was changed.
The old statement in statement_change agrees with the original blueprint and base node.
Only the corrected statement and forced proof-step/proof-dependency changes accompany
its Lean record.

Independent searches, recorded by msearch.py as well as direct source inspection:

- LeanFinder: `injective proetale sheaf exact kernel open immersion restriction complex`.
  Eight hits concerning local injectivity, stalks and open immersions; none states this
  canonical short exact sequence.
- Loogle: `CategoryTheory.ShortComplex.ShortExact`. Generic predicate and its API;
  opened the structure, no pro-etale supported-sections theorem.
- Grep: `flasque|supported.*complex|injective.*restriction` in Mathlib/CategoryTheory.
  No hits. Direct rg additionally searched the upstream WeilConjectures sources,
  lean/Sheaf, and Mathlib Algebra and CategoryTheory for support and exact-sequence
  variants. It found the published finite support functors, which this delivery uses.
  I opened the nearest upstream theorem, Etale.shortExact_supportsShortComplex in
  SixFunctors/OpenClosed/Supports.lean: it is on the small etale site and cannot replace
  the pro-etale statement. The new helper name has no upstream or Mathlib collision.
- LeanSearch: `For injective pro-etale module sheaves the supported kernel and open
  restriction form a short exact sequence`. The service returned Internal Server Error;
  this is recorded as unavailable, not as a successful no-match result.

Findings and changes: no remaining mathematical or Lean-signature mismatch was found
in repair L. I retained the module and node unchanged and added this independent reading
and search evidence. The obsolete legacy-support interface and duplicate dependency
module are absent from this delivery. All declarations have source/blueprint docstrings;
the theorem's six proof steps follow the node, including canonical kernel transport.
The one theorem remains wholly `sorry`; nothing was proved. No hollow definition,
file-local notation/instance, private alias or extra hypothesis occurs.

Validation: the prescribed scompile.py completed both its sandbox and library-file
checks successfully (11.4 s and 29.4 s), with no errors or warnings. The node's
lean.statement was checked verbatim against the final declaration signature. The final
deliver2.py dry run and delivery perform the current server preflight as well.
