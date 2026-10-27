## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFlatFamiliesCoherentAdjointLocality`
formalizes the corrected node with two postponed theorems and four fully constructed helpers.
All declarations are in `AlgebraicGeometry.ProperFlatFamilies`.
Return H3 is repaired by the explicitly permitted §1(C) sentence-removal alternative.
The correction and complete citer audit appear below. No new node or dependency repair is needed.

Hypothesis and clause correspondence:

- An arbitrary scheme S: `{S X Y : Scheme.{u}}`. The structure maps are `pX`, `pY`.
- Both families flat and locally of finite presentation: `[Flat pX]`,
  `[LocallyOfFinitePresentation pX]`, `[Flat pY]`, `[LocallyOfFinitePresentation pY]`.
- A proper S-map: `(f : X ⟶ Y) [IsProper f] (hf : f ≫ pY = pX)`.
- The full unbounded categories are exactly `schemeDerivedQCohCategory`, not
  derived categories of the abelian categories of quasi-coherent sheaves.
- `directImage f` is the full-subcategory lift of `schemeDerivedDirectImage f`.
  The lift uses the existing preservation theorem for qcqs morphisms; properness
  supplies the morphism properties without any global compactness assumptions.
- Existence of a right adjoint and its counit is `exists_rightAdjoint`:
  `(directImage f).IsLeftAdjoint`, and the same for every `f ∣_ V`.
  `Functor.IsLeftAdjoint` means existence of a right functor with an adjunction.
- The arbitrary open immersion is represented by its image open `V : Y.Opens`
  and `V.ι`. This loses no open immersion: every open immersion identifies its
  source with this open subscheme. The corrected statement uses this standard open-subscheme
  presentation and does not assert a separate geometric transport law.
  Its preimage is exactly `f ⁻¹ᵁ V`, with restricted map `f ∣_ V`.
- Arbitrary choices of the two adjunctions are the universally quantified functors
  `a`, `aV` and values `adj : directImage f ⊣ a`, `adjV : directImage (f ∣_ V) ⊣ aV`.
  These act on all unbounded quasi-coherent derived objects; only K is bounded locally.
- Local boundedness is `hK`: for each point y there is an open W containing y,
  an integer b and zero restricted cohomology for every integer i < b. It uses
  `SheafOfModules.overFunctor` on H^i(K), just as the existing
  `derivedLocallyBoundedBelowGlobal` signature. There is no uniform global bound.
- The specified canonical arrow is `openMate`, defined by `mateEquiv` applied to
  the inverse of `openComparison`. The latter is `ObjectProperty.isoMk` of the
  explicit `schemeMVOpenRestrictionComparison`. Thus it is the sectionwise
  identity of Tag 08FE derived by fixed comparisons, not a `Nonempty` choice.
- The first conclusion of `coherent_adjoint_locality` is `IsIso` of this arrow at K.
- The second conclusion is the counit equation: restricted direct image of that
  arrow followed by the local counit equals inverse openComparison followed by
  restriction of the global counit.
- The third conclusion states uniqueness even among arbitrary component maps
  with that counit equation. It prevents substituting an arbitrary isomorphism.
- Naturality in K is built into `openMate`, a natural transformation.
- No compactness, quasi-separatedness, Noetherian hypothesis or flatness of f appears.
  The shared `HasDerivedCategory` family is the standard localization-size convention;
  it asserts existence of these presentations, not geometric properties of schemes.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` (affine-local, stalkwise equivalent).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, providing qcqs of the map.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, represented by open subschemes.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`: `schemeDerivedDirectImage`.
- `WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps`: `schemeOpenRestriction`.
- `WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh`:
  `schemeDerivedQCoh_openRestriction_iff`.
- `WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`:
  `schemeDerivedDirectImage_preserves_QCoh`.
- `WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData`:
  `schemeMVDerivedRestriction`, `schemeMVOpenRestrictionComparison`.
- Mathlib's `ObjectProperty.lift`, `isoMk`, `hom_ext`, `mateEquiv`, `TwoSquare`.

The last four existing nodes were added to stmt_deps because the statement's canonical
maps and full-subcategory lifts use those interfaces. All recorded proof-dependency
modules are imported. For the retired/duplicate Sheaf interfaces to the support criterion
and perfect derived tensor, the upstream WeilConjectures declaration is imported instead.
Unstated proof nodes (levelwise Brown, the Kiehl input and Zariski total descent) have
no module to import. Their complete proof roles remain in the theorem docstring and DAG.

Sources inspected locally: duality.tex, lemma-twisted-inverse-image (0A9E),
lemma-proper-noetherian (0A9P) with the Kiehl footnote, and more-morphisms.tex,
lemma-flat-finite-presentation-pseudo-coherent (0695),
lemma-permanence-pseudo-coherent (0683). The arbitrary-scheme assertion is explicitly
agent-formulated in the node; it is not misattributed to the qcqs statement of 0A9E.
The main docstring retains the eleven-step existence/locality proof plan and replaces
the old coherence paragraph with the transpose proof of naturality and uniqueness.
The DAG proof remains unchanged: its extra coherence argument is no longer an
exported conclusion and is not represented by substitute categorical identities.

Edge cases checked: empty X or Y, empty and identity opens, zero K, unbounded K with
varying local lower bounds, non-quasi-compact/non-quasi-separated bases and targets,
and proper f which is not flat. Nothing in the binders rules these cases out.
The theorem uses IsZero on module sheaves, never on a bare Type.
The full-subcategory categories use Mathlib's existing abelian structure and shared
localization instances. No new category or abelian structure is chosen.

Searches: msearch.py leanfinder queried the full locality assertion and returned ordinary
module-sheaf adjunctions only, none matching this theorem. Loogle query
`CategoryTheory.Adjunction, AlgebraicGeometry.schemeDerivedDirectImage` returned unknown
project identifier. msearch grep `rightAdjoint.*open|LocallyBoundedBelow|proper.*adjoint`
in AlgebraicGeometry had no hit. The subsequent semantic query for mate compatibility
found the Mathlib laws `mateEquiv_counit`, `mateEquiv_vcomp`, and the two conjugate/mate
transport identities; Loogle `CategoryTheory.mateEquiv` confirmed these. Their types were
read in full. Project rg searches for locallyBoundedBelow, rightAdjointOpen, and
right-adjoint restriction found the qcqs support criterion and qcqs base-change laws;
they do not give arbitrary-family locality. The exact item id has no Lean declaration
in WeilConjectures or Sheaf. Searches for lifted quasi-coherent restriction/direct-image
functors found no reusable named lift; the helpers here are explicit ObjectProperty
lifts, not duplicate constructions of the original derived functors.
The wrapper's exact queries and returned names are also recorded in searches.jsonl.

Validation: scompile.py compiled the repaired sandbox module (29.1 s) and library
module (16.5 s) successfully on the server, with no errors or unexpected warnings.
Every theorem proof is exactly `sorry`; every helper has real data.

## Statement corrected

The independent return H3 explicitly offers removing the coherence sentence through
§1(C). This repair takes that option, deleting exactly:

> These canonical identifications respect identity opens, successive restrictions and isomorphisms of the $S$-diagram.

The previous three declarations were generic categorical identities, not geometric
coherence laws on the canonical open mate: the identity theorem did not mention it,
the pasting theorem did not identify direct restriction with iterated restriction,
and the transport theorem did not specify a second scheme diagram. They are removed.
The sentence did not specify the required geometric comparison cocycles; there is no
claim here that such coherence is false. The source assertion is the invertibility of
the counit-defined mate (duality.tex, equation-sheafy, lemma-when-sheafy, Tags 0A9E and
0A9P with the Kiehl footnote). The existing arbitrary-base extension, all hypotheses,
local lower bound, canonical construction, counit equation and uniqueness are retained.
This is a supporting node, not the blueprint unit's own statement.

Old statement, verbatim:

Let $S$ be any scheme [def-pc-scheme], and let $X\to S$ and $Y\to S$ be flat [def-weil-flat-morphism] and locally of finite presentation [def-sbc-locally-finite-presentation]. Let $f:X\to Y$ be a proper $S$-morphism [def-weil-proper-morphism]. On the full derived categories of modules with quasi-coherent cohomology [def-pc-derived-category], derived direct image [def-pc-derived-direct-image] has a right adjoint $f^!:D_{\mathrm{QCoh}}(Y)\to D_{\mathrm{QCoh}}(X)$ with counit $\varepsilon_f:Rf_*f^!\to\operatorname{id}$. If $j:V\hookrightarrow Y$ is any open immersion [def-weil-open-immersion], put $U=f^{-1}V$, write $j_X:U\hookrightarrow X$ and $f_V:U\to V$, and choose the corresponding adjunction for $f_V$. For every locally bounded-below $K\in D_{\mathrm{QCoh}}(Y)$, the canonical mate
$$j_X^*f^!K\longrightarrow f_V^!(j^*K)$$
is an isomorphism. Here locally bounded below means that each point has a neighbourhood on which $\mathcal H^i(K)=0$ for all sufficiently negative $i$. The mate is the transpose under $Rf_{V,*}\dashv f_V^!$ of the restriction of $\varepsilon_{f,K}$, using the canonical identification $Rf_{V,*}j_X^*\simeq j^*Rf_*$. Thus this isomorphism identifies the restricted counit with $\varepsilon_{f_V,j^*K}$. These canonical identifications respect identity opens, successive restrictions and isomorphisms of the $S$-diagram. No quasi-compactness or quasi-separatedness of $S,X,Y$, no Noetherian hypothesis, and no flatness of $f$ are assumed.

Citer search: `grep -rl '"lem-sfb-proper-flat-families-coherent-adjoint-locality"'
dag/nodes`, followed by parsing every node's `stmt_deps` and `proof_deps`, found
exactly one direct citer. Other textual hits are provenance and search metadata.

- `lem-sfb-relative-nodal-perfect-duality-trace`: holds **true**. Steps 2, 4 and 5
  need existence and invertibility of the canonical mate with its counit equation,
  all retained. Step 2 cites derived pushforward and right-adjoint composition for
  the composite counit, not successive-open coherence of this item. Step 5 cites
  `lem-sfb-coherent-right-adjoint-comparisons` for transport under diagram
  isomorphisms; the open where c is an isomorphism uses the retained counit law.
  Steps 6-11 cite separate horizontal/vertical base-change and mate-pasting results.
  Its statement and proof therefore remain valid; the citer is not edited.

The JSON `statement_change` records the exact old statement, source, reason and this
complete citer list. `old_stmt_deps` preserves the base list because the delivered
statement uses four existing restriction/comparison/lift interface nodes in addition
to the base dependencies. The DAG proof and proof dependencies are unchanged.

## Second reading by Q17

I reread the corrected node against the final file. No second agent was started
(the dispatcher prohibits delegation); this is a worker self-check, not an independent
review. The maintainer's review remains independent.

The returned coherence declarations and all report claims that they state geometric
coherence have been removed. I checked the hypotheses against pX, pY, their four
instances, f, IsProper and hf, and checked local boundedness point by point. Existence
is stated separately. The counit equation uses the inverse canonical comparison in
the required direction; uniqueness is the injectivity of adjV.homEquiv. The lean
record lists exactly the six remaining declarations, and its main signature matches
verbatim. The sole direct citer was read in full and audited above.
