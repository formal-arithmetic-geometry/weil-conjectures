## Worker report

This delivery states `AlgebraicGeometry.OrientedSourceLocalization.sourceLocalization`
in `Sheaf.Paper.OrientedSourceLocalization`. Its only theorem proof is `sorry`.
The helper definitions contain actual data: specializations of recorded module categories,
the recorded restriction followed by identity-composite equality transport, the recorded
geometric square map, Mathlib's abelian structure and standard localization, a structure
packaging the conclusion's four functors, and degreewise counit/unit maps and sequence.
Nothing in the shared library or upstream source is edited directly.

The preserved packet was a reviewed stage-1 split, rather than stage-2 Lean. The required
initial `deliver2.py --no-push` rejected its report because `## Worker report` was absent.
I retained that packet and report, read the current node and dependencies, and wrote the
stage-2 module. The prior claim that Q42's split landing already supplied Lean was incorrect:
its current node has no Lean record. This delivery preserves the node's mathematical
statement and all proof steps.

Hypothesis and clause correspondence:

- Schemes `S`, `X`, `U`, `Z` and the maps are explicit `Scheme.{u}` binders; `f : X ⟶ S`,
  `j : U ⟶ X`, `i : Z ⟶ X`. Independent `v` is the coefficient universe.
- Noetherian `S` means `[IsLocallyNoetherian S] [CompactSpace S]`, following the two
  recorded dependencies, with no separation condition on its topology.
- Finite presentation of `f` is exactly `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`, as the recorded scheme conventions require (Stacks 01TP).
- `Λ` is any `Type v` with `[CommRing Λ] [Finite Λ]`. The inherited construction uses the
  canonical `Coeff.{u,v} Λ` universe lift already fixed in `OrientedNearbyCycles`.
- The complementary immersions are `[IsOpenImmersion j] [IsClosedImmersion i]` and
  `Set.range i.base = (Set.range j.base)ᶜ`. Arbitrary closed scheme structures are admitted;
  no reducedness, flatness, étaleness or coefficient invertibility is imposed.
- The composites `j ≫ f`, `i ≫ f` render `f_U`, `f_Z`. `sourceMap f h` is precisely
  `squareMorphism f (h ≫ f) h (𝟙 S) (Category.comp_id (h ≫ f)).symm`, so these geometric
  maps are induced by the recorded universal square, not quantified arbitrary maps.
- The geometric clause finds `V : VanishingTopos f` with `IsSubterminal V` and an
  equivalence `VanishingTopos (j ≫ f) ≌ Over V`. The isomorphism of the actual open
  inverse image followed by that equivalence with `Over.star V` identifies the map
  itself with the open slice projection. Mathlib's `Over.star` sends `A` to
  `V × A → V`; it is the inverse image here, not the slice forgetful functor.
- The same clause requires the actual closed direct image to be full and faithful and
  its essential image to consist exactly of `A` with `IsIso (prod.fst : V ⨯ A ⟶ V)`.
  This is Stacks 08LY's complementary closed subtopos, over the same `V`.
- `Modules f Λ` is the recorded `OrientedConstructibleSheaf.Modules f (𝟙 S) Λ`, which
  presents the constant-ring module category of `V_f`. The dependency explicitly gives
  this identity-second-map presentation and its canonical identity-base-change
  identification with `VanishingTopos f`; no new constructibility predicate is defined.
- `sourcePull` is the recorded `stratumRestriction f (𝟙 S) h (𝟙 S) Λ`, followed only by
  `Pi.eqToEquivalence` for `𝟙 S ≫ 𝟙 S = 𝟙 S`. This is the canonical inverse image of the
  source map in the chosen presentation, with all site and coefficient universes retained.
- The existential result `r : Operations f j i Λ` fixes its two inverse images by
  `openPull_eq`, `closedPull_eq` to those restrictions. Its adjunctions are exactly
  `openExtension ⊣ openPull` and `closedPull ⊣ closedImage`; thus the two extension
  functors are characterized up to the unique adjoint isomorphism used downstream.
  They are conclusions, never hypotheses or arbitrary maps substituted for canonical maps.
- Its twelve additive/finite-limit/finite-colimit fields express exactness of all four
  operations between the abelian module categories. These are fields of the existential
  result, so no exactness assumption is added to the theorem.
- Four separate implications render constructibility preservation for `j*`, `i*`, `j!`,
  `i_*`, respectively. Every predicate is the dependency's `IsConstructible` on the
  appropriate source/base oriented product, with the same finite-stratification notion.
- For every module sheaf `F`, `ShortComplex.mk` has first map the actual open adjunction
  counit and second map the actual closed adjunction unit. Its `ShortExact` conclusion
  includes zero composite, monomorphism, exactness at `F`, and epimorphism, and therefore
  precisely renders the displayed sequence with zeros at both ends. Naturality comes
  from the counit/unit natural transformations themselves.
- `counitComplex` and `unitComplex` are these same natural transformations applied
  degreewise. The explicit identity-complex isomorphisms remove only the termwise identity
  functor. `complexSequence` packages their zero composite into a short complex.
- The derived clause supplies short exactness of that degreewise sequence and natural
  transformations `ε`, `η`, `δ` between the induced unbounded exact derived functors.
  Their formulas on `DerivedCategory.Q.obj K` fix the first two to the descended counit
  and unit and the third to `DerivedCategory.triangleOfSESδ`. The final `Triangle.mk`
  is distinguished for every derived object. Thus this is the corresponding natural
  localization triangle, including its canonical connecting map; it is not just the
  existence of an unspecified triangle or a bounded-below restriction.

Dependency declarations read and used:

- `Sheaf.Paper.OrientedNearbyCycles`: `EtaleSite`, `VanishingSite`, `vanishingTopology`,
  `VanishingTopos`, `squareMorphism`, `Coeff`, the site projections and universal lift.
  I read their signatures and normalization docstrings in the recorded source.
- `Sheaf.Paper.OrientedConstructibleSheaf`: `ProductSite`, `productTopology`, `Modules`,
  `stratumBaseChange`, `stratumRestriction`, `IsConstructible`; the full definition
  specifies the identity-base-map specialization and canonical presentation comparison.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`; `CompactSpace` from
  `Mathlib.Topology.Defs.Filter`; the recorded scheme-conventions record is a convention,
  not a declaration or additional predicate.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- Proof modules imported as non-public imports: `GeometricMorphism`,
  `OrientedProductLargeSites.universalWithLargeSites`,
  `OrientedProductSliceLocalization.oriented_slice_localization`,
  `OrientedProductPointsConservative.orientedProduct_points_conservative` and constructible
  subset infrastructure. The exact-functor factorization and short-exact-complex triangle
  Mathlib matches are also imported and used in the derived statement.
- The three proof-only prerequisites `lem-trf-etale-closed-complement-sets`,
  `lem-trf-topos-complement-factorization`, `lem-trf-topos-complement-module-stalks`
  currently have no recorded Lean module, so there is no import to add for them.
  They remain named proof prerequisites, as in the unchanged item proof.

Edge cases checked mathematically before finalizing: `U = ∅`, `U = X`, `Z = ∅`, `Z = X`,
empty `X` and `S`, zero coefficient ring and zero module, nonreduced closed complements,
empty constructibility partitions, and complexes with unbounded cohomology. The slice
and closed-support predicates have the correct orientation at `V = 0` and `V = 1`.
The degreewise triangle has no boundedness binder. The open adjunction is `j! ⊣ j*`:
the earlier split's rejected reverse adjunction is not present. All universes are bound;
no site/coefficient universe equality or independent smaller test universe is imposed.

Searches for an existing declaration (actual current searches):

- `msearch.py leanfinder`: "Open and closed source recollement on an oriented vanishing
  topos for finite coefficient module sheaves": 8 hits, all on condensed module categories,
  none on source recollement of oriented vanishing topoi.
- `msearch.py loogle`: "CategoryTheory.Sheaf, CategoryTheory.Adjunction,
  CategoryTheory.IsGrothendieckTopos": 0 hits (last identifier absent from Mathlib).
- `msearch.py grep`: "subtopos|Subtopos|recollement|Recollement" in `CategoryTheory/Sites`:
  0 hits.
- `msearch.py leansearch`: "Complementary open and closed subtopoi classified by a
  subterminal object and its slice": 8 hits including `IsSubterminal` and the subobject
  classifier. None defines the complementary pair or states this source theorem.
- `rg` on project/upstream: `orientedSource|sourceLocalization|ComplementarySubtopoi`:
  no matching declaration; upstream grep of the exact item id: no match.
- DAG search and `blueprint_refs.py search 'complementary subtopoi'`: existing general
  complement statement nodes, no blueprint definition match. The geometric conclusion
  uses Mathlib's existing `Over`, `IsSubterminal`, fullness, faithfulness and essential
  image directly; no second general complement predicate is introduced.
- Read `OrientedProperImageConstructibility` as a potential shared normalization API.
  Its DAG closure reaches this item through `lem-trf-oriented-constructible-subquotients`,
  so importing it would create a cycle. The theorem instead uses the actual recorded
  general-product module presentation and restriction in the statement dependency.

Source check: read Orgogozo's original PDF §§8 and 9.3, and Stacks 08LW and 08LY, including
that the closed part is the full category of objects whose product with the subterminal
is terminal over it. The closed scheme is never used as an object of the étale site.
No statement fault or `STATEMENT-DISPUTED` flag remains. No new nodes, dependency-module
repairs, or statement corrections are needed.

The additive-sheafification compiler failure was traced to the imported successor-universe
Grothendieck-category instance. The module selects Mathlib's concrete plus-construction
instance explicitly at `max (u+1) v`, then supplies that witness directly to the inherited
abelian structure. This is a real Mathlib construction, not a postponed proof or extra
hypothesis. The standard derived localization is selected in its exact object/morphism
universes. No universe equality was added.

Validation: `scompile.py` compiled the delivered module without errors or warnings.
The required `deliver2.py --no-push` passed server preflight and per-file compilation
(dry-run commit `c3719e620b`). The final packet also includes the module documentation's
main-declaration lists and is compiled again by the delivery wrapper.


## Second reading by NQ

Independent second reading of immutable delivery `83e1aea55bb8ce84d97926a87610dcba3cc763eb`.
I opened the item node, its eight proof steps, all seven statement-dependency records, the
source place, the complete delivered module, and this report. The item `statement` is
verbatim equal (modulo whitespace) to the signature recorded in `lean.statement` and to
the declaration before `:= by`.

Hypotheses and objects: `S`, `X`, `U`, and `Z` are arbitrary `Scheme.{u}` objects; `f`,
`j`, and `i` have exactly the node's domains. `[IsLocallyNoetherian S] [CompactSpace S]`
renders Noetherian `S` under the recorded convention, and
`[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]` renders finite
presentation exactly. The open, closed, and range-complement hypotheses are present with
no reducedness, flatness, separatedness, or invertibility additions. `Λ : Type v` has
only `CommRing` and `Finite`; the independent scheme and coefficient universes remain
bound.

Conclusion comparison: `sourceMap f j` and `sourceMap f i` are the canonical square maps,
not arbitrary maps. The first existential supplies a subterminal `V`, the open equivalence
and its inverse-image identification with `Over.star V`, and the closed direct-image
fullness, faithfulness, and exact essential-image condition `IsIso (prod.fst : V ⨯ A ⟶ V)`.
The `Operations` witness has the four required functors, fixes both inverse images to
`sourcePull`, and gives the two adjunctions. Its additive, finite-limit, and finite-colimit
fields express exactness of all four operations as conclusion data. The next four
conjuncts preserve the recorded finite-stratification predicate for open pullback, closed
pullback, open extension, and closed image. For every module sheaf, `ShortComplex.mk`
uses the actual counit and unit and requires `ShortExact`, so it includes the zero
composite and both endpoint conditions. The final existential gives the same maps
termwise on arbitrary (including unbounded) cochain complexes, short exactness, the
canonical descended `ε`, `η`, and `δ`, their representative formulas, and a
`distTriang` membership for every derived object. No clause is weaker, stronger, reordered,
or omitted.

Proof-step and dependency audit: step 1 uses the subterminal inverse image and the
recorded oriented-product and slice-localization interfaces; step 2 uses the étale closed
complement and the universal triple factorization; steps 3--4 use the module complement
stalk formulas and conservative oriented points for adjunctions, exactness, and the
short exact sequence; step 5 derives the restriction comparisons from support rather than
assuming a base-change theorem; steps 6--7 give the Noetherian finite refinements and
zero-valued complementary strata; step 8 uses ordinary exact-functor derived
factorization and the short-exact-complex triangle. I read the declarations and signatures
of `VanishingTopos`, `squareMorphism`, `Modules`, `stratumRestriction`, `IsConstructible`,
`IsLocallyNoetherian`, `CompactSpace`, `IsOpenImmersion`, and `IsClosedImmersion`. The
three proof-only complement prerequisites have no Lean records and are not incorrectly
copied into the statement module. No dropped infinity/dg/model-category node is cited,
and the route uses ordinary derived categories.

Edge cases checked: empty or total `U` and `Z`, empty `X` or `S`, zero coefficient ring
and zero module, nonreduced closed complements, empty finite partitions, `V = 0` and
`V = 1`, and unbounded complexes. The formulas remain meaningful in each case. Searches
for duplicate source-localization/recollement definitions in Mathlib, the project, and
the permitted source clone found none. All helper definitions carry source and blueprint
docstrings and contain real data; the sole theorem proof is `sorry` with a complete
stepwise docstring. No universe variable is implicit or silently identified.

Compiler evidence: I reproduced the exact immutable file with
```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py NQ lem-trf-oriented-source-localization
snapshot/lean/Sheaf/Paper/OrientedSourceLocalization.lean
```.
The wrapper compiled both the sandbox overlay and library module successfully (exit 0,
with no diagnostics beyond the permitted postponed theorem). No lake/global build, live
Lean write, clone edit, branch mutation, claim, delivery, or merge was performed.
No mathematical correction is needed; this replacement repairs only the placeholder
second-reading section required by H11.
