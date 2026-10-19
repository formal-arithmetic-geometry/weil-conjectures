## Worker report

The delivery states `AlgebraicGeometry.Etale.supportRestrictionTriangle` in
`Sheaf.AlgebraicGeometry.SupportRestrictionTriangle`, with one theorem proof `sorry`.
It supplies the previously missing arbitrary-coefficient étale global support-section
functor in `Sheaf.AlgebraicGeometry.EtaleSupportedSections`. All definition data are
actual kernels, the existing right derived functor, or composites of existing adjunction
maps. The additive instance is checked directly through the kernel inclusion; it contains
no postponed proof. No statement correction, dependency-module repair, or statement
dispute is needed. The earlier N8 work was the stage-1 DAG split, not a stage-2 statement;
the current source node has no Lean record, so that review does not finish this assignment.

The master blueprint Markdown was read in the launcher's literature directory, including
its displayed triangle and both original proof paragraphs. The current DAG's repaired
six-step proof was read in full. I also read Stacks `cohomology.tex`, section
`section-cohomology-support-bis` (Tag 0G6Y), which defines derived global sections with
support, and the exact recorded dependency interfaces. The delivered theorem docstring
carries all six current DAG proof steps, including two-open gluing rather than the
original unsupported assertion that the supported subsheaf of an injective is injective.

Hypothesis and clause correspondence:

- The arbitrary scheme is `{T : Scheme.{u}}`. The two closed subschemes are represented
  by `{B C : Scheme.{u}}`, `(b : B ⟶ T)`, `(c : C ⟶ T)`, and their two
  `[IsClosedImmersion ...]` instances. Every closed subscheme has this presentation.
- The fixed commutative module coefficient ring is `(R : Type (u + 1)) [CommRing R]`.
  This is the recorded six-functor size convention of
  `def-weil-pbc-derived-categories`; it does not impose finiteness, torsion,
  invertibility, noetherianity, or separatedness. Small coefficient rings may be viewed
  in this universe by cumulativity. Schemes and coefficients of any size are covered
  by selecting a sufficiently large `u`.
- `V = T \ C` and its open immersion `v` are `c.openComplement` and
  `c.openComplement.ι`, using Mathlib's canonical open complement. Its open immersion
  and étaleness instances are inferred from these constructors.
- A bounded below complex is its class
  `F : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))`.
  Quantification over the whole bounded below derived category includes every such
  complex and expresses independence of its representative.
- `supportedEtaleSections R X W` is the kernel in the functor category of
  `Sheaf.natTransΓRes ... (op (Scheme.Etale.mk W.ι))`. Evaluation preserves this kernel,
  so on `M` it is exactly `ker(Γ(X,M) → Γ(W,M|W))`, naturally as an R-module.
  It is not a sheaf-valued support object or an arbitrary resolution.
- `derivedSupportedEtaleSections` is this functor's
  `rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι`, the specified RΓ object in the
  full derived category of R-modules. Its cohomology is, by definition, cohomology
  with support. No separate equality of unrelated cohomology notions is assumed.
- The first support, `B ∩ C`, has open complement
  `b.openComplement ⊔ c.openComplement`. The first term uses this open in `T`.
  The second term uses `b.openComplement`, again on `T`.
- The third support, `B ∩ V`, is a closed subset of `V` with complement
  `c.openComplement.ι ⁻¹ᵁ b.openComplement`. Its support functor is formed with
  ambient scheme `c.openComplement`, hence on `V.smallEtaleTopology`. It is evaluated
  after `(upperStar (ModuleCat R) v).mapDerivedCategoryPlus`, the exact inverse image
  on bounded below complexes. In particular the third functor is not a support
  functor on `T` disguised by an abstract isomorphism.
- The quantified natural transformation `a` is uniquely specified by its composite
  with `supportedEtaleSectionsι`: that composite is the first support's inclusion
  into global sections. Thus it is the canonical inclusion of support kernels.
- The quantified natural transformation `r` is uniquely specified by its composite
  with the support-kernel inclusion on `V`: that composite is the support inclusion
  on `T`, followed by `etaleGlobalSectionPullback`. The latter is explicitly the
  inverse-image unit whiskered by Γ and the existing `lowerStarCompGlobalSectionsIso`.
  Thus `r` is restriction of supported sections, including its canonical coefficient
  identification. Neither `a` nor `r` is an unconstrained arbitrary morphism.
- The natural isomorphism `e` compares the right derived functor of
  `upperStar v ⋙ Γ_(B∩V)` with `v* ⋙ RΓ_(B∩V)`. Its displayed equality with the derived
  units fixes it uniquely by the universal property of the right derived functor.
  The right side is `rightDerivedFunctorPlusCompUnit`, followed by the existing
  `rightDerivedFunctorPlusIsoMapDerivedCategoryPlus` for the exact inverse image.
  This clause specifies the canonical comparison; it introduces no extra hypothesis.
  The source proof obtains its invertibility because open restriction preserves injectives.
- The first two derived arrows are exactly `rightDerivedFunctorPlusNatTrans a` and
  `rightDerivedFunctorPlusNatTrans r` followed by `e.hom`, mapped through the inclusion
  of the bounded below derived category of R-modules. The connecting arrow is `δ.app F`.
- Membership of this `Triangle.mk` in `distTriang (DerivedCategory (ModuleCat R))`
  states precisely distinguishedness. The codomain of `δ` is the first functor composed
  with `shiftFunctor ... (1 : ℤ)`, giving the last term RΓ_(B∩C)[1].
- `a`, `r`, `e`, and `δ` are natural transformations/isomorphisms of functors. Thus all
  three triangle morphisms commute with every derived coefficient-complex morphism,
  including the connecting arrow; naturality is not merely asserted for chain maps.
  Their existence is quantified before `∀ F`, so the statement supplies one natural
  triangle for the entire bounded below category.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.DerivedCategories` reexports
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory.Plus`, and
  `DerivedCategory.homologyFunctor` in the recorded module-sheaf encoding.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and open complements.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `upperStar` and
  `upperStarLowerStarAdjunction`, exactly the recorded inverse-image dependency.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections`:
  `lowerStarCompGlobalSectionsIso`; the canonical pullback is its composite with the
  preceding unit. `WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections`
  supplies the existing `Sheaf.Γ_additive` instance.
- `Mathlib.CategoryTheory.Sites.GlobalSections`: `Sheaf.Γ` and `Sheaf.natTransΓRes`.
  `Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels` supplies the kernel;
  `FunctorCategory.EpiMono` supplies its monic component inclusions.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  `Functor.rightDerivedFunctorPlus` and its unit. The upstream `PlusComp` module
  supplies `rightDerivedFunctorPlusNatTrans` and `rightDerivedFunctorPlusCompUnit`.
  Upstream `PlusExact` supplies `rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`.
- Proof imports retain the recorded enough-injectives, exact module inverse-image,
  étale restriction, and open-closed exact-sequence modules, as well as Mathlib's
  `DerivedCategory.triangleOfSES_distinguished`, injective-representative and
  K-injective Hom interfaces. These are the plan for stage 3; no theorem is proved here.

Edge cases checked mathematically before drafting: B empty gives three zero terms;
C empty gives a zero first term and identity restriction; C=T gives a zero third term
and identity first arrow; B=T gives ordinary localization. Disjoint supports give a
zero first term. The empty scheme, zero ring, zero complex, and nilpotent structures on
B/C cause no exception: the kernels depend only on the underlying closed supports.
No nonempty-open assumption appears. The unit-normalized comparison also covers the
identity open immersion, and the constructions use every bounded below derived object.

Searches for the item used the prescribed msearch tools: LeanFinder on the two-support
triangle phrasing found scheme ideal-gluing/support lemmas, not this theorem; Loogle
`"support", "triangle"` returned zero hits; Mathlib grep
`sectionsWithSupport|supportRestrictionTriangle|localizationTriangle` returned zero hits.
LeanSearch on supported-section kernels returned Internal Server Error, recorded as
unavailable. Searches by exact item ID and support terminology in slopmaster2 and
`lean/Sheaf` found no exact statement. `Etale.Derived.Supports` was read: it supplies
sheaf-valued supported products and restriction classes, not the global two-support
triangle. The pro-étale `sectionsWithSupport` is on another site and is sheaf-valued.

## New nodes

`def-pur-etale-derived-supported-sections` records the actual arbitrary-coefficient
étale kernel functor, its kernel inclusion, its existing right derived functor, and the
unit-defined global pullback. Its source is the item's own definition of RΓ and proof
step 1, with Stacks Tag 0G6Y for the right-derived terminology. It belongs to the same
chapter and unit and has the item as blueprint ancestor.

The DAG and blueprint searches `sections supported` found the item and
`def-pur-flasque-support`. The latter, `def-pur-support-cohomology`, and
`def-exc-proetale-sections-with-support` were checked: they concern pro-étale sheaf-valued
support or torsion/finite conventions and do not define this arbitrary-coefficient étale
global kernel. The new node therefore introduces a missing notion rather than a copy.
It cites the existing site, open-immersion, derived-category and inverse-image nodes.

For this new notion the recorded searches were run separately:
LeanFinder on the additive supported-global-section kernel returned `Scheme.kerFunctor`,
etale-locus support and ideal-sheaf kernel lemmas; none defines this functor.
Mathlib grep `supportedEtaleSections|sectionsWithSupport|derivedSupported` returned no hits.
Slopmaster2 grep found only the pro-étale `sectionsWithSupport`; project grep found no
étale global support functor. LeanSearch on the exact kernel formulation returned
Internal Server Error. Exact returned outputs are retained in `scratchpad/search-support-*`
and copied into `mathlib_searches`; the unavailable service is not claimed as a negative
mathematical search result. No second copy of a generic kernel, global section functor,
derived category, inverse image, or right derived functor is defined.

## Validation

Both delivery files compiled cleanly through the prescribed scompile.py wrapper,
each separately in dependency order. The wrapper checked both sandbox and library
forms against the live/side overlay. The theorem has one postponed proof; the
support-definition module has none. The final required delivery dry run is now being
run with --no-push. No second-reading section is supplied by this worker, and no
delivery will be pushed.


## Second reading by Q24

I independently opened the live item node, both sandbox nodes, both Lean modules,
the five original statement-dependency nodes and their actual declaration sources.
I read the source blueprint Markdown at
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/lem-pur-support-restriction-triangle.md`,
including the statement and both original proof paragraphs. I read Stacks
`cohomology.tex`, section `section-cohomology-support-bis` (Tag 0G6Y), lines
8444–8500, and the preceding definition of support cohomology at lines 3739–3788.
The blueprint agrees with the unchanged node statement; the fixed commutative ring
is explicit in its current proof step 1. The Stacks discussion defines the support
section functor and its derived cohomology, without extra finiteness assumptions;
it concerns ringed spaces, so it is supporting terminology, not a substitute for
the blueprint's small-etale-site assertion. No statement correction or citer audit
under §1(C) is needed.

Here is my object/hypothesis/conclusion checklist, read against the final Lean:

| Node item | Lean rendering and verdict |
| --- | --- |
| An arbitrary scheme T | `{T B C : Scheme.{u}}`; PASS, no finiteness, separation or nonemptiness instance. |
| Closed subschemes B,C in T | `(b : B ⟶ T) (c : C ⟶ T)` with `[IsClosedImmersion b] [IsClosedImmersion c]`; PASS. Mathlib's class is a closed embedding with surjective stalk maps. |
| V = T minus C, with its open inclusion v | `c.openComplement` and `c.openComplement.ι`; PASS, canonical open subscheme, no arbitrary replacement morphism. |
| Fixed commutative module coefficients | `(R : Type (u + 1)) [CommRing R]`, `ModuleCat.{u + 1} R`; PASS, the exact size convention of the recorded derived-category interface. No torsion or invertibility assumption. |
| F bounded below on the small etale site | `F : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))`; PASS, all bounded-below derived objects, hence every bounded-below complex. |
| RΓ means the derived support-section functor | `derivedSupportedEtaleSections`, literally the right derived functor of the kernel of `Sheaf.natTransΓRes`, followed by `DerivedCategory.Plus.ι`; PASS. Cohomology with support is the homology of this object, not an unrelated sheaf-support construction. |
| First term with support B intersect C on T | Complement `b.openComplement ⊔ c.openComplement` in the support functor on T; PASS by complement of intersection. |
| Second term with support B on T | Complement `b.openComplement` in the support functor on T; PASS. |
| Third term with support B intersect V, ambient V | `supportedEtaleSections R c.openComplement (c.openComplement.ι ⁻¹ᵁ b.openComplement)`, right derived on V, after `(upperStar ... c.openComplement.ι).mapDerivedCategoryPlus`; PASS. This complement is V intersect (T minus B); the support is closed in V. |
| First arrow is support inclusion | `a` is characterized by its composite with `supportedEtaleSectionsι`; first triangle arrow is `rightDerivedFunctorPlusNatTrans a`, mapped through Plus.ι; PASS, kernel inclusions make a unique. |
| Second arrow is restriction | `r` composed with the inclusion on V equals the inclusion on T followed by upstream `globalSectionsUpperStarMap ... v M`; second arrow derives r and composes with e; PASS, canonical restriction and coefficients. |
| Third derived term is the specified derived composite | `e` is a natural isomorphism normalized by the displayed equality of right-derived units; PASS, the right-derived universal property fixes the canonical comparison. Its existence is a conclusion, not an extra preservation hypothesis. |
| Connecting arrow to first term shifted by 1 | Natural transformation `δ` with codomain the first support functor followed by `shiftFunctor ... (1 : ℤ)`; PASS. |
| Distinguished triangle, natural in F | `Triangle.mk ... (δ.app F) ∈ distTriang ...`; a,r,e,δ are quantified before `∀ F`, and are natural transformations/isomorphisms; PASS for all derived morphisms, including the connecting map. |

I checked the actual dependency interfaces, not just names:
`Scheme.smallEtaleTopology` is the topology of jointly surjective etale families;
`Scheme.Etale.mk W.ι` is its etale open object. `IsOpenImmersion` is Mathlib's
locally-ringed-space open immersion. `DerivedCategories.lean` uses the precise
`Sheaf ... (ModuleCat.{u+1} R)` encoding, not a private SheafOfModules category.
`upperStar` and `upperStarLowerStarAdjunction` in the recorded Defs module are the
small-etale inverse-image adjunction; its exactness is already an upstream instance.
I read `lowerStarCompGlobalSectionsIso` and `globalSectionsUpperStarMap` in the
upstream GlobalSections module, and `rightDerivedFunctorPlusNatTrans`,
`rightDerivedFunctorPlusCompUnit`, and the composition comparison characterization
in PlusComp. The latter agrees with the equality imposed on e in the statement.
The proof imports retain the enough-injectives, exact inverse-image, etale
restriction-injectives, open-closed exact-sequence, short-exact-complex triangle,
and K-injective interfaces; the theorem docstring follows all six current node
proof steps, including the two-open gluing repair.

Independent searches used different queries from the worker's first phrasing:

- LeanFinder: `Kernel of the map from global sections of an etale module sheaf to sections on an open subscheme, derived localization triangle for nested closed supports` returned scheme ideal kernels and the etale locus of ring algebras, no support-section functor or support triangle.
- Loogle: `"ΓRes"` returned the existing `Sheaf.ΓRes`, `Sheaf.natTransΓRes`, and their equations. I opened the Mathlib GlobalSections source and verified that the delivery uses this exact restriction map inside its kernel.
- LeanSearch: `The additive left exact functor of global sections supported in a closed subset is the kernel of restriction to the open complement on a small etale site` returned Internal Server Error. This service is unavailable, not a mathematical negative result.
- msearch grep: `ΓRes|localizationTriangle|cohomologyWithSupport` returned the existing global restriction declarations and an unrelated scheme restriction-algebra instance. Direct rg of Mathlib, slopmaster2/WeilConjectures, and project lean/Sheaf additionally used `sectionsWithSupport`, `globalSectionsUpperStarMap`, `cohomologyWithSupport`, and `support.*[Tt]riangle`. I opened Etale/Derived/Supports.lean: its sheaf-valued supported product/restriction and localization machinery is not this global kernel functor or the two-support triangle. The pro-etale supported-section construction has the wrong site and codomain.
- Whole-DAG searches for `kernel.*restriction`, `sections.*closed complement`, `supported global`, and `global sections with support`, plus the existing support nodes named by the worker, found no duplicate arbitrary-coefficient etale global-support kernel definition. Exact delivered names have no preexisting source declaration. Search calls are retained in searches.jsonl by msearch.

The new node `def-pur-etale-derived-supported-sections` was read as a stage-1
addition as well. Its source is the item's own kernel definition/proof step 1,
with Stacks 0G6Y for derived-support terminology. It defines a missing independent
notion rather than changing the site's or derived category's encoding. Its id,
chapter/unit, created record, ancestor/via, split definition kind, null mathlib_match,
empty proof/proof_deps, lean_audit none and complete lean record satisfy §5.
Its final objects are the actual kernel functor and kernel inclusion, together
with the existing right-derived construction. Its additivity and left exactness
are now explicit Lean theorem statements, each matching the corresponding clause
in this node and carrying a complete proof plan. The new node remains directly
in the item's stmt_deps. There are no dependency-module deliveries.

Edge cases: B empty gives zero support terms; C empty gives zero first term and
identity restriction; C=T gives zero third term and identity support inclusion;
B=T gives ordinary localization; disjoint B,C give zero first term. The empty
scheme, empty open, zero ring, zero complex, arbitrary characteristic, nilpotent
closed-subscheme structures, and objects concentrated in degree zero are covered.
There is no index type or nonempty condition. The single universe parameter is
bound explicitly; the ring/sheaf value universe u+1 is the recorded etale
six-functor convention, and no additional universe equality is imposed. All
remaining variables are explicit under autoImplicit false. The normalized e
includes the identity-open case.

Mismatches found and repaired:

1. H4: the worker's `etaleGlobalSectionPullback` duplicated the already defined
   upstream component map `globalSectionsUpperStarMap`. I removed the helper and
   used that existing declaration directly in r's characterization. Its module
   is publicly imported by the triangle module. I removed the now redundant
   final paragraph of the new definition node and its inverse-image dependency;
   the item's original inverse-image dependency remains. No item mathematics changed.
2. H6: the worker had proved additivity with tactics inside an instance body.
   I replaced it with the named theorem `supportedEtaleSections_additive`, marked
   as an instance, whose entire proof is sorry, with the full monic-cancellation
   proof in its docstring. This is the new node's explicit additivity clause.
3. H3 for the new node: its left exactness clause had no corresponding explicit
   Lean statement. I added the named instance theorem
   `supportedEtaleSections_preservesFiniteLimits`, with proof sorry and the
   finite-limits-commute-with-kernels proof docstring. It is listed in the new
   node's lean.declarations and matches its existing left-exactness clause.
4. Removed the now unused EpiMono and inverse-image/global-section imports from
   the support-definition module. Updated the item's lean.statement verbatim from
   the final theorem signature. The worker report above records the initial
   implementation; this section records the final repairs.

No data definition contains sorry. The only postponed proofs are the triangle,
additivity, and left exactness, each named, recorded by its corresponding DAG
statement, and accompanied by its source and natural-language proof. Both files
compiled separately and cleanly through scompile.py after these repairs, including
sandbox and library forms with the sibling overlay; no warning or error was emitted.
The initial path-only scompile invocation was corrected to use the actual lean/
paths; this was not a compiler or tool failure.
