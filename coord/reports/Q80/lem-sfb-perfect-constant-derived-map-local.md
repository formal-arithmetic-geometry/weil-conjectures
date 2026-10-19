## Worker report

The module `Sheaf.CategoryTheory.PerfectConstantDerivedMapLocal` states
`CategoryTheory.exists_perfect_constant_derived_map_local`, with proof `sorry`.
It formalizes Stacks Tag 09BE, `lemma-locally-constant-map`, exactly in the
commutative-ring case specified by the node. I read that source and the paragraph
introducing constant realization immediately before Tag 09BD, as well as 09BD.
The accepted Q129 work is a stage-1 split with no Lean record, so its acceptance
does not supersede this stage-2 task. Its statement, proof, proof dependencies,
review, status, and blueprint metadata are retained.

Clause-by-clause correspondence:

- A small site is `{C : Type u} [Category.{v} C]`, `(J : Precoverage C)` and
  `_hJ : J.IsSiteForCoverings`. The latter is the recorded presieve presentation
  of the site axioms, including covering pullbacks and bind composition. The
  sheaf category uses `J.toGrothendieck`. Object and morphism sizes are independent.
- The final object is `(X : C) (_hX : IsTerminal X)`. No chosen points or
  enough-points assumption is present.
- The commutative ring is `(R : Type (max u v)) [CommRing R]`. The coefficient
  universe contains both site sizes. No Noetherian, finite, nonzero, field,
  torsion or characteristic hypothesis is imposed.
- The constant ring is `(constantSheaf J.toGrothendieck RingCat).obj (RingCat.of R)`.
  Modules over it are precisely the recorded `ringedSiteModules`/`SheafOfModules`
  category. The new derived constant functor uses the recorded ordinary constant
  module functor; it is not an arbitrary functor or merely a chosen map.
- `P L : DerivedCategory (ModuleCat R)` are the two objects of D(R).
  `_hP : DerivedCategory.IsPerfectRingComplex P` is the recorded bounded
  finite-projective-model predicate, with its independent localization universe.
  There is no condition on L.
- `φ` is any morphism between the images of P and L under
  `siteDerivedConstantModuleFunctor J.toGrothendieck R`. Every localization
  choice is explicit: `wR`, `wS` and `wU`. The module-sheaf localization binder
  `siteModuleHasDerivedCategory` is a transparent abbreviation for the ordinary
  `HasDerivedCategory` class, with the module size fixed before inference. It
  adds no mathematical condition.
- The conclusion supplies `I : Type (max u v)`, `U : I → C`,
  `f : ∀ i, U i ⟶ X`, and `Presieve.ofArrows U f ∈ J X`: an actual covering
  family, not just a locally generated predicate.
- For every i it supplies `α : P ⟶ L`. The equality is
  `(ringedDerivedRestrictionSized ... (U i)).map φ =
   (ringedDerivedRestrictionSized ... (U i)).map
     ((siteDerivedConstantModuleFunctor ...).map α)`.
  These maps lie in the actual localized derived category over the restricted
  constant ring. This is exactly φ restricted to U_i equals the restriction
  of the constant realization of α_i. No compatibility between different α_i
  is required or asserted.
- An empty covering is allowed. No boundedness or finiteness is required of L,
  and no finiteness of I or connectedness of the site is imposed.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`:
  the sheafification of the constant presheaf.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  a transparent abbreviation for `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `HasDerivedCategory`,
  `DerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`,
  `DerivedCategory.IsPerfectRingComplex`: an isomorphism to Q of a bounded
  complex with finite projective terms.
- The `mathlib_match` of `def-pur-localized-ringed-site` is used verbatim:
  `J.over U`, `Sheaf.over`, `SheafOfModules.overFunctor`, `SheafOfModules.over`,
  `SheafOfModules.Hom.over`, `SheafOfModules.overMap` and `overFunctorMap` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and Sites.Over.
- The added existing dependency `def-weil-pbc-ringed-derived-restriction` is
  generalized in the dependency module described below. Its original full
  signature, exactness helpers and canonical single-complex comparison were read.
- The new definition depends on the already recorded
  `CategoryTheory.siteConstantModuleFunctorGeneral` and
  `siteConstantModulePresheafGeneral` in
  `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`.
  Its localization is `CategoryTheory.Functor.mapDerivedCategory` and its
  representative normalization is Mathlib's `mapDerivedCategoryFactors`, from
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

The main module imports the stated proof dependencies without `public`: exact
sheafification, underlying-set sheafification, exact-functor factorization,
constant-sheaf restriction, constant morphism local algebraicity, and local
sections after sheafification. The latter's current source was read with
`scompile.py --source WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`.
The local-chain-representative proof dependency has no Lean record or Mathlib
match, so there is no module to import yet. Its four-step use remains in the
item's complete proof docstring. No proof-dependency node is restated.

Edge cases checked before drafting: zero ring, zero source or target, a
one-term projective source, a finite projective module not assumed free,
an unbounded target, disconnected sites and sites without points, and a final
object covered by the empty sieve. The one-point site reduces the conclusion
to local ordinary D(R) maps. A final object excludes an empty category, but an
empty cover of it is allowed. In that case every restricted sheaf is zero
and the existential over i is vacuous. On nondegenerate objects the proof uses
injectivity of constant sections, never global faithfulness on every object.
The source-model predicate includes the support's boundary degrees and allows
the zero model. None of these cases requires an extra hypothesis.

Searches for the item, performed with the prescribed `msearch.py Q80 <item>`:

- LeanFinder: “Every morphism between constant derived complexes with perfect
  source on a small site locally comes from a morphism in the derived category
  of the coefficient ring”. Eight hits, including abstract derived fractions,
  essential surjectivity of Q and HasExt; no local algebraicity theorem.
- Loogle: `constantSheaf, DerivedCategory`. Zero hits; it reported unknown
  identifier `constantSheaf`. This is not treated as evidence of absence alone.
- Mathlib grep: `constantSheaf.*DerivedCategory|perfect.*constant|constant.*perfect`.
  Three unrelated Cantor–Bendixson hits, no match.
- LeanSearch: “Morphisms from a perfect constant derived complex on a site are
  locally induced from module derived morphisms”. Eight hits, including the
  generic exact-functor localization, locally injective presheaves and condensed
  constant functors; no theorem stating this result.
- `rg` in the pinned upstream `WeilConjectures`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id and the declaration names:
  no declaration of the item or any delivered name. Searches by perfect,
  constant, derived and local-chain language found scheme-specific comparison
  results and generic constructions, not this arbitrary-site statement.
- Searches for derived restriction found the existing
  `def-weil-pbc-ringed-derived-restriction`, which is reused and generalized
  rather than replaced by a new notion. The object-only canonical representative
  function in `RingedSiteDerivedRestrictionUniverses` cannot restrict morphisms;
  this item needs the existing functorial restriction node instead.

No source-based statement correction or STATEMENT-DISPUTED finding is needed.
The item's only deltas are `lean` and the two additional definition dependencies.
No targets, proof, status, source or other maintainer fields are changed.

## New nodes

`def-sfb-site-derived-constant-module-functor` defines the canonical exact constant
realization from D(R) into D(C, underline R). Its source is the paragraph immediately
before Stacks 09BD, together with 00WJ and 03CY for exact module sheafification.
The actual object and maps are Mathlib's localization of the already existing
`siteConstantModuleFunctorGeneral`. A named theorem states that functor's
additivity and exactness; the definition uses that theorem, and has real data.
Its complete sectionwise-exactness and sheafification proof is in the docstring.
The transparent localization-size abbreviation just pins the same module category.

The new node cites every notion used in its TeX statement, including the existing
ordinary constant functor, and has the item's chapter, unit and blueprint ancestor
`det-lem-integral-models-stacks`. It serves the local 09BE input in the 09C5/09C6
proof route. `blueprint_refs.py search 'derived constant'` found only a supported
cup-product node, and `search 'constant module'` found six unrelated blueprint
nodes; exact-id DAG search found no derived constant module functor node.
The existing ordinary functor node is used, not duplicated. The scheme-specific
`residueLisseDerivedConstant`, constant twists, and constant tower functors do not
supply this arbitrary-site construction. ModuleCat-valued sheaf realizations use
a different category and do not directly give the required SheafOfModules functor.

The three prescribed searches are recorded in the new node with their actual
output, not fabricated summaries:

- LeanSearch for exact constant modules and unbounded derived categories: eight
  hits, ordinary constant sheaves, condensed functors and adjunctions.
- LeanFinder for sheafifying constant module presheaves then localizing: eight
  hits, including `PresheafOfModules.sheafification`, `sheafificationCompToSheaf`
  and `SheafOfModules.instAbelian`. These are reused, but none is this functor.
- Mathlib grep for `siteDerivedConstantModuleFunctor|siteConstantModuleFunctor.*exact|
  constant.*mapDerivedCategory|mapDerivedCategory.*constant`: zero hits.
  The same regex in upstream and side sources found only constant towers,
  Weil twists, scheme-specific statements and the other sheaf encoding.

## Dependency modules

`def-weil-pbc-ringed-derived-restriction` previously pointed to a module whose
functor requires `C : Type u`, `SmallCategory C` and coefficient universe u.
That interface cannot serve a statement retaining independent site object and
morphism universes. The §1(B) module
`Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral` publicly retains that
module and supplies the same construction for arbitrary `Category.{v} C`,
ring universe r, module universe m and independently chosen derived universes.
Specializing R to the underlying ring sheaf of the node's commutative ring sheaf
gives exactly the node's restriction. The generalized definition also accepts
ring sheaves; no commutativity is used by the restriction construction.

`ringedOverFunctor_exactGeneral` is the named proof obligation for the definition.
Its proof docstring explains sectionwise additivity and kernels and the
covering-local preservation of epimorphisms and cokernels. No exactness hypothesis
is added to the item. `ringedDerivedRestrictionGeneral` is the actual
`overFunctor.mapDerivedCategory`; the rank-one degree-zero comparison is the
canonical `mapDerivedCategorySingleFunctor` comparison, retaining the dependency's
normalization clause. `ringedDerivedRestrictionSized` specializes this construction
to coefficient universe `max u v`, supplying canonical sheafification instances.
The wrapper prevents unresolved universe metavariables in consumer inference;
it neither changes the localization nor identifies the two site universes.
Only this dependency's `lean` field changes, with the required explanatory note.

All three modules have source/blueprint docstrings, explicit universe variables,
`autoImplicit false`, and lines of at most 100 characters. The only new postponed
proofs are the item theorem, the constant-functor exactness theorem in its new
definition node, and the slice exactness theorem needed by its dependency
definition. Every definition is constructed from existing functors.

Validation: all three modules compiled separately through `scompile.py` in
sandbox and library positions. Delivery validation uses
`python3 /home/ubuntu/weil-launcher-nt/deliver2.py Q80
lem-sfb-perfect-constant-derived-map-local --no-push`; the second reader supplies
the independent second-reading section before delivery.

## Second reading by Q80

I independently read the sandbox node, all three delivered modules, every statement
dependency's record and declaration, and the source at `sites-cohomology.tex`,
Tag 09BE (`lemma-locally-constant-map`), the preceding paragraph defining constant
realization, and Tag 09BD. The source introduces an arbitrary site with a final
object and an arbitrary ring; it does not inherit the Noetherian assumption of
neighboring lemmas. This node explicitly specializes to commutative rings.
There is no `statement_change`, and no correction or citer audit is required.

The node's objects, hypotheses and conclusion, in order, with their Lean renderings:

1. A small site C: `{C : Type u} [Category.{v} C]`, `J : Precoverage C`,
   `_hJ : J.IsSiteForCoverings`. I opened `SiteCoveringAxioms.lean`: its three
   clauses are isomorphism covers, bind composition, and existence of pullbacks
   of covering families, with the resulting family covering. This is the recorded
   Stacks 00VH convention, not an extra assumption of arbitrary fibre products.
   Sheaves use `J.toGrothendieck`. Verdict: exact dependency and hypothesis.
2. A final object X: `(X : C) (_hX : IsTerminal X)`. It need not be a chosen
   global terminal object instance. Verdict: exact.
3. A commutative coefficient ring R: `(R : Type (max u v)) [CommRing R]`.
   There is no field, Noetherian, nonzero, characteristic or finite-ring condition.
   The size is the common coefficient universe used by the recorded ordinary
   constant module functor, containing both independent site sizes. Arbitrarily
   large common universes are allowed. Verdict: exact under that size convention.
4. The constant ring and its module sheaves: the actual term is
   `(constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)`.
   I read Mathlib's `constantSheaf`: it is `Functor.const` followed by
   `presheafToSheaf`. I read `ringedSiteModules`: it transparently abbreviates
   `SheafOfModules`, with Mathlib's abelian instance. These are the dependency
   objects, with the sheafified scalar action, not a new category. Verdict: exact.
5. Unbounded derived categories: `HasDerivedCategory` with separately bound
   `wR`, `wS`, `wU`, including the family of slice localizations. I read its
   Mathlib definition as a choice of localization, and `DerivedCategory.Q`.
   `siteModuleHasDerivedCategory` is a transparent abbreviation of that same
   class, fixing module sizes before inference; it adds no proposition about the
   site. The family binder chooses the localization on each slice, not points
   or resolutions. Verdict: exact choice of derived-category universes.
6. Objects P and L of D(R): `(P L : DerivedCategory ... (ModuleCat R))`.
   Only P has a hypothesis, `_hP : DerivedCategory.IsPerfectRingComplex P`.
   I opened `PerfectRingComplexGeneral.lean`: it asserts the existence of a
   complex, integer bounds `a b`, `IsStrictlyGE a`, `IsStrictlyLE b`, projective
   and finite terms in every integer degree, and an isomorphism to its image
   under Q. This is bounded finite-projective perfectness; it does not demand
   free terms or a bounded L. Verdict: exact.
7. The arbitrary morphism phi: its endpoints are the images of P and L under
   `siteDerivedConstantModuleFunctor J.toGrothendieck R`. I followed this
   definition to `siteConstantModuleFunctorGeneral`, and that to the actual
   constant module presheaf and `PresheafOfModules.sheafification`. Its derived
   functor is precisely `Functor.mapDerivedCategory` of this exact functor.
   It is not a quantified or unconstrained functor. Verdict: exact constant
   realization and arbitrary morphism.
8. A covering of X: `exists (I : Type (max u v)) (U : I → C)
   (f : forall i, U i ⟶ X), Presieve.ofArrows U f ∈ J X`. The cover is an
   actual site cover, with no finiteness, nonemptiness or connectedness imposed.
   Its indexing universe contains all site arrows and objects. Verdict: exact.
9. A local algebraic map for each cover member: `forall i : I, exists α : P ⟶ L`.
   The map is allowed to depend on i. It is a morphism in D(R), not a module
   map, chain map on a fixed model, or global map required to work everywhere.
   Verdict: exact quantifier order and object.
10. The local equality: `ringedDerivedRestrictionSized ... (U i)` maps phi to
    the same arrow as it maps `siteDerivedConstantModuleFunctor.map α`.
    Both sides lie between the same two restricted objects in the actual
    derived category of modules over the restricted constant ring. I opened
    Mathlib's `J.over`, `Sheaf.over`, `SheafOfModules.overFunctor` and
    `Hom.over`: these use the slice topology and sectionwise restriction.
    The delivered derived restriction is exactly `overFunctor.mapDerivedCategory`.
    Thus the equality says precisely phi restricted to U_i equals the restricted
    constant realization of alpha_i. It asserts no agreement of the different
    alpha_i on overlaps. Verdict: exact, neither weaker nor stronger.

Edge cases: `I` may be empty; if its empty presieve covers X the conclusion's
memberwise condition is vacuous. There is no `Nonempty` binder. The zero ring,
zero source, zero target, zero finite-projective model, a complex concentrated
in degree zero and arbitrary integer shifts are permitted. A finite projective
module need not be free. There is no hypothesis on L's support or terms. A site
with final object cannot have an empty object type; the empty-scheme site, when
presented with its final empty scheme, is still covered. Disconnected and
pointless sites remain included. On empty-covered objects all restricted module
sheaves vanish; elsewhere the constant-section unit is injective, as the proof
docstring explains. No characteristic or natural-number boundary case is lost.
The declared universe variables are exactly `u v wR wS wU`; the theorem has no
unbound variable and never identifies `u` with `v`.

I also reviewed the extra definition and dependency repair:

- `def-sfb-site-derived-constant-module-functor`: the source paragraph before
  09BD supplies the canonical derived realization; 00WJ and 03CY supply exact
  sheafification and the unique scalar action. The new node cites exactly its
  five definition dependencies. Its field set matches the stage-2 new-node
  contract: definition/split, empty proof fields, null mathlib match, three
  actual search records, worker creation, correct chapter/unit and audits,
  and blueprint ancestor `det-lem-integral-models-stacks` (confirmed with
  `tools/blueprint_refs.py ancestor`). The exactness theorem is explicitly
  included in the node's statement. Its docstring gives the sectionwise and
  sheafification argument. The derived functor contains real construction data,
  with only exactness postponed. Its representative comparison is Mathlib's
  `mapDerivedCategoryFactors` (or its inverse in mathematical composition order),
  whose definition and signature I read. No separate choice of realization occurs.
- `def-weil-pbc-ringed-derived-restriction`: I read the original module, which
  requires `C : Type u`, `SmallCategory C`, and coefficient universe u. It
  cannot accept this item's independently sized site. The repair publicly
  retains the original module, changes only this node's `lean` record, and
  explains the unusable interface in `lean.note`. Its exactness theorem and
  functor operate on the same `SheafOfModules.overFunctor`, with independent
  site, ring, module and localization universes. For the node's commutative
  ring sheaf apply it to the underlying ring sheaf. The rank-one degree-zero
  isomorphism is the actual `mapDerivedCategorySingleFunctor 0` component,
  not an arbitrary isomorphism. I read its Mathlib construction: it composes
  the localization factorization and the termwise single-complex comparison.
  `ringedDerivedRestrictionSized` merely supplies the canonical sheafification
  instances when coefficient sizes contain the site sizes. The exactness
  theorem's docstring explains kernels, local lifts and cokernels; no exactness
  assumption is added to the main theorem.

Independent duplicate searches used different wording from the worker:

- LeanFinder via `msearch.py`: "A map in the unbounded derived category from a
  perfect constant sheaf complex becomes a constant module derived morphism on
  some cover of the terminal object". Eight hits, including derived fractions,
  single functors and maps from projective single complexes; no Tag 09BE theorem.
- LeanSearch via `msearch.py`: "Exact functor sending modules over a ring to
  constant module sheaves induces a functor between unbounded derived categories".
  Eight hits: `constantSheaf` and condensed constant module functors; no exact
  match for the arbitrary-site `SheafOfModules` derived realization.
- Loogle query `Functor.mapDerivedCategory`: unknown identifier and zero hits;
  I did not use this failed name lookup as absence evidence. The actual Mathlib
  declaration was found and read directly in `DerivedCategory/ExactFunctor.lean`.
- `rg` over upstream `WeilConjectures`, Mathlib's site/homology modules and
  side `lean/Sheaf`, using `constant.*[Dd]erived`, `[Dd]erived.*[Cc]onstant`,
  `locally_constant_map`, `constant_derived_map` and exactness variants.
  The broad output is saved in `scratchpad/second-reading-search.txt`.
  Generic localization, condensed and scheme-specific constructions do not
  state this arbitrary-site result. I opened `FiniteFreeEtaleLocalActual.lean`:
  it concerns finite-free chain sources on a small etale site with
  ModuleCat-valued sheaves, and gives local chain representatives/homotopies;
  it is not this perfect-source algebraic derived-map assertion. Searches of
  the DAG and `dag/lean_names_upstream.json` found no competing declaration
  for this item or the new derived constant realization. The existing ordinary
  constant-module node and the existing functorial restriction node are reused.
  The existing `ringedSiteDerivedRestrictionOfUniverses` was also opened: it
  only restricts chosen representatives on objects and provides no map action,
  so cannot replace the required functor.

Mismatches and repairs: I found no mathematical or signature mismatch. I did
find that the restriction dependency module's exactness docstring cited 03DJ
alone, which is the exactness-of-extension-by-zero lemma. I added the direct
reference to Modules on Sites Section 03DH, whose definition describes
restriction sectionwise; the module retains the original 03DJ/08JB context.
Only those source docstrings changed. All signatures, construction data, node
statements, proof plans and target statements were retained. Every delivered
postponed theorem is named, has a matching node clause and a natural-language
proof docstring; every theorem proof remains `sorry`. No hollow data, private
copy, local notation or file-local instance was introduced. The item's
`lean.statement` is verbatim its declaration signature, as are both dependency
records. File widths are at most 100 columns.

Validation: independently compiled all three delivered modules, separately,
with the prescribed `scompile.py` wrapper in sandbox and library positions;
all were clean, including independent localization universes. Recompiled the
three final files after the source-reference repair. Delivery preflight is
run with `deliver2.py --no-push` before the final delivery.
