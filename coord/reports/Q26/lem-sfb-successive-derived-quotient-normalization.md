## Worker report

The module `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization` states
`SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`.
Its only postponed proof is that theorem. Its docstring contains the eight proof
steps of this node, with the K-flat resolution, preservation, tensor descent,
localization and normalized coefficient-adjunction inputs identified.

The statement is packaged as existence of presentations and a `Normalization`
structure so the coherence and representative equations share exactly the same
functors and maps. These structures describe the single comparison notion of
this node; they do not construct a replacement tensor product or introduce an
independent missing notion. The helper declarations are all listed in
`lean.declarations`, each with this node's source and blueprint docstring.
Definitions have real data: `Modules` and `restriction` abbreviate the recorded
categories and functor, `pure` uses the existing sheafification unit,
`sectionTensor` transports solely through the specified object equality, and
`squareComparison` composes the comparison isomorphisms and the equality of the
commuting ring-map square. No definition chooses an arbitrary morphism or uses
an existence-only replacement for a construction.

Hypothesis and clause correspondence:

- The site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`.
  `[EssentiallySmall.{r} C]` expresses smallness relative to the coefficient
  universe. The usual `HasSheafCompose`, `WEqualsLocallyBijective` and
  `HasSheafify` instances supply the sheaf constructions and the abelian module
  category. No equality of u, v and r is imposed.
- Coefficients are arbitrary `Sheaf J CommRingCat.{r}` objects and composable
  arrows `a : R ⟶ S`, `b : S ⟶ T`. There are no flatness, surjectivity,
  Noetherian, characteristic or boundedness hypotheses.
- The module category is the recorded `ringedSiteModules` of the underlying
  ring sheaf `derivedChangeRingIndependentCoefficients J R`; `Modules` is only
  its abbreviation. Derived categories are Mathlib `DerivedCategory`, with
  the chosen `[∀ R, HasDerivedCategory.{w} (Modules R)]`. This simultaneous
  size convention can always be supplied by `HasDerivedCategory.standard` in
  the standard universe; it allows a uniformly chosen smaller morphism
  universe as well. These are presentations of the node's unbounded derived
  categories, not an extra mathematical finiteness assumption.
- `Presentation.ordinary`, `.obj_eq`, `.map_eq`, and `.additive` identify
  exactly the E witness of `derivedChangeOfRingsIndependentCoefficients`.
  `.derived`, `.counit`, and `.universal` are its universal left-derived pair
  for `DerivedCategory.Qh`. Thus neither the functor nor its computation map
  is unconstrained. This packages existing notions without a second definition.
- `Normalization.derived a b` is a natural isomorphism of functors
  `(p a).derived ⋙ (p b).derived ≅ (p (a ≫ b)).derived`. Evaluation at any
  derived object is the desired isomorphism; naturality includes every
  morphism of the unbounded derived category.
- `.ordinary` is the termwise comparison on sheaf modules. In the recorded
  scalar-first convention, `.ordinary_hom` sends `t ⊗ (s ⊗ x)` to
  `(b(s)*t) ⊗ x`, and `.ordinary_inv` sends `t ⊗ x` to
  `t ⊗ (1 ⊗ x)`. These are exactly the paper's formulas with the module
  factor written first. Each tensor appearing here is the sheafification
  image, not a tensor in raw section modules mistaken for the sheaf tensor.
- `.computed` and `.intermediate_computed` assert invertibility of the
  actual computation counits on the flat-term K-flat representatives.
  `.representative` states the commuting equation between the derived
  comparison, the two successive universal computation counits, the direct
  counit, and `Qh` of `mapHomotopyCategoryCompIso ordinary`. The latter is
  literally the termwise ordinary comparison. Its inverse is fixed by the
  ordinary inverse formula and the inverse natural isomorphism. There is no
  choice of a functorial K-flat resolution.
- Flat-term K-flat means the recorded
  `CochainComplex.IsKFlatIndependentCoefficients P` and
  `∀ n : ℤ, IsFlatOnSite (P.X n)`; P is an arbitrary integer-indexed
  cochain complex, with no support restriction.
- `.ordinaryAdjunction` and `.ordinary_unit` fix the ordinary unit to
  `x ↦ 1 ⊗ x`. `.right` and `.right_factors` are restriction of scalars
  descended through Qh; `.adjunction` and `.adjunction_normalization` use
  precisely the normalized derived unit of the dependency, through the
  universal left computation and exact right factorization.
- `.restrictionComp` and `.restrictionComp_sections` identify composite
  ordinary restriction by the identity on underlying sections.
  `.rightComp` and `.rightComp_normalization` fix its derived comparison
  through Qh on every homotopy object. Thus the derived restriction
  identification is not an arbitrary natural isomorphism.
- `.unit_comp` is the claimed equality at every `X : DerivedCategory
  (Modules R)`: first the unit for a, then restriction of the unit for b,
  then the normalized composite-restriction comparison, then restriction
  of the extension comparison, equals the unit for `a ≫ b`.
- `.associative` equates the two collapse maps for three maps at every
  derived input, with only `Category.assoc` transporting the final ring
  composite. This implies agreement of all finite parenthesizations by
  induction, as explained in the proof docstring.
- `.coefficient_naturality` is the pasting equation for a commuting diagram
  `(R → S → T) → (R' → S' → T')`. `ha`, `hb`, and `hab` record the two
  square equalities and their outer rectangle. The latter is determined by
  the first two, not an additional restriction on the diagrams. The square
  comparisons are defined from the same derived composition isomorphisms.
  This expresses naturality after actual derived coefficient change, and
  includes changing the base ring through α.
- Ordinary rings are included by specializing C to the singleton category
  and J to the bottom topology (only maximal/identity coverings). The sheaf
  condition is then automatic, module sheaves are ordinary modules, and the
  same tensor construction is ordinary scalar extension. No nonflat or
  quotient case is excluded.

Dependency interfaces read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: the site convention;
  sheaves use the existing `GrothendieckTopology` presentation.
- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`: arbitrary-site module sheaves.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Qh`: the derived localization.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`,
  `SheafOfModules.derivedChangeRingIndependentCoefficients` and
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`: the
  ordinary extension object/map interface and universal derived pair.
- `Sheaf.Algebra.Homology.KFlat`,
  `CochainComplex.IsKFlatIndependentCoefficients`: total-tensor acyclicity.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
  `SheafOfModules.IsFlatOnSite`: exactness of the canonical tensor functor.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`,
  `SheafOfModules.restrictScalars`: unchanged underlying abelian sheaf.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`,
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`: the exact right
  functor and both unit normalizations used in the structure fields.

The stated proof dependencies are imported without public exposure:
KFlatResolutionIndependentCoefficients, KFlatRingedToposPullback,
WeilSiteDerivedTensorDescent, RingedTopoiTensorSections, and Mathlib's
Localization.Predicate. The actual extension pure sections use the recorded
change-of-rings sheafification, so the single-universe RingedTensor.pure API
is not used to restrict the independent universes of this statement.

Edge cases checked mathematically before writing: the empty site, zero
module/complex, the zero ring, identity maps, arbitrary nonflat quotient
maps, and complexes unbounded in both directions. In each case the same
balanced formulas, unit calculation and coherence identities apply. No
nonemptiness, nonzero or boundedness assumption was introduced. Site object
and morphism universes remain separate, including the pro-etale sizes t+1
and t with coefficients in a larger universe.

Searches for an existing declaration:

- msearch leanfinder, “K flat derived scalar extension transitivity ring
  sheaves”: Module.Flat.trans, Module.FaithfullyFlat.trans,
  RingHom.Flat.comp and other ordinary flatness declarations; no match.
- msearch loogle, `"ModuleCat", "extendScalars"`: ordinary
  ModuleCat.extendScalars, its adjunction and identity comparison; no
  unbounded ring-sheaf derived normalization theorem.
- msearch grep, `changeOfRings.*(comp|assoc)|extendScalarsComp` in
  Algebra/Category/ModuleCat: six ordinary module/pseudofunctor hits,
  including ModuleCat.extendScalarsComp; no match for this statement.
- msearch leansearch, “Associativity of derived extension of scalars for
  sheaves of commutative rings with K flat representatives and units”:
  ordinary ModuleCat.extendScalars_assoc, extendScalars_assoc',
  CommRingCat.moduleCatExtendScalarsPseudofunctor, and underived sheaf
  pushforward/pullback results; none has the required derived statement.
- rg on the upstream WeilConjectures tree and the project's Sheaf tree
  for successiveDerived/successive_derived/SuccessiveDerived and the node
  id found no existing declaration. Searches for changeOfRings composition
  found ordinary tensor and derived change-of-rings input modules only.
  The upstream declaration-name index has no match for this new comparison.

The source Tag 0D6D was read in sites-cohomology.tex: it computes successive
pullbacks on flat-term K-flat representatives and identifies the result
with direct pullback. This delivery retains its full generality while
spelling out the identity-topos tensor formula and the node's requested
normalizations. No statement correction, dependency repair, new independent
node, or STATEMENT-DISPUTED flag is needed.

Compilation and preflight results are recorded below once complete.

Validation: scompile.py accepted both the sandbox and module-name compilations
with no errors or warnings (22.6 s and 18.3 s respectively). The unused name
of the index in the `right` family was renamed `_a`; no linter was disabled.
All source lines are at most 100 characters. A direct JSON comparison found
that `lean` is the only changed node field, and the stored signature matches
the theorem text verbatim. The additional intermediate-computation field
ensures that the second counit used in the representative equation is
explicitly invertible as well as the first and direct counits.

## Second reading by Q26

Independent maintainer second reading of immutable delivery
1108fc4db8def97eee5675697089bdc573332959, performed on 2026-10-17.
This replaces the delivered placeholder; the Lean module and node are unchanged.

I read the item and all eight statement dependencies in the immutable snapshot,
the delivered module, and the exact dependency interfaces in the read-only Q26
clone and pinned Mathlib. I read Stacks sites-cohomology.tex at 06YS
(lemma-K-flat-resolution, line 3207), 0G7E (lemma-pullback-K-flat, line 3508),
06YY (lemma-derived-base-change, line 3585), 0D6D
(lemma-derived-pullback-composition, line 3658), and 07A6 (lemma-adjoint,
line 3990). The source has no coefficient-map flatness or boundedness hypothesis.

Hypotheses and conclusions, checked against the actual fields:

- The site is an arbitrary Grothendieck topology on C. Its object and morphism
  universes u and v stay independent. EssentiallySmall at r is the recorded
  smallness relative to module coefficients, as required by the module-category
  dependency. Sheafification and locally bijective equivalence instances are
  the recorded site infrastructure. The simultaneous HasDerivedCategory family
  is localization size data; standard localizations supply it in a common
  universe. No universe equality, scheme hypothesis or pro-etale replacement
  is imposed.
- Modules unfolds to ringedSiteModules of
  derivedChangeRingIndependentCoefficients, hence exactly SheafOfModules.
  restriction unfolds to Mathlib restrictScalars, with unchanged abelian sheaf.
  Presentation fixes ordinary objects and maps to changeOfRings and
  changeOfRingsHom. Its derived pair has the actual IsLeftDerivedFunctor
  universal property, so it is not an arbitrary chosen functor or arrow.
- Normalization.derived is a natural isomorphism of functors, giving the
  required comparison at every derived object and every derived morphism.
  ordinary_hom and ordinary_inv give exactly the displayed forward and inverse
  formulas, in scalar-first notation. pure uses the actual sheafification unit;
  sectionTensor only transports through obj_eq. This does not identify sheaf
  tensor sections with the generally larger sectionwise tensor product.
- computed and intermediate_computed make the first, direct, and second
  computation counits invertible. representative equates the comparison
  followed by the direct counit with the successive counits followed by Qh of
  mapHomotopyCategoryCompIso. The latter declaration really is induced from
  the termwise ordinary comparison. Thus both inverse and forward derived
  maps are determined on every flat-term K-flat representative.
- ordinary_unit fixes x to 1 tensor x. adjunction_normalization is the
  coefficient-adjunction dependency's unit equation. restrictionComp_sections
  fixes the underlying restriction comparison to the identity;
  rightComp_normalization descends that comparison. unit_comp consequently
  says precisely that the two extension units compose to the unit for a >> b,
  with all intermediate restrictions and their comparison included.
- associative compares both three-factor collapse maps with the required
  Category.assoc transport. Its repeated application gives agreement of
  finite parenthesizations; the representative formula also handles identity
  maps. coefficient_naturality is the correctly typed pasting equation for
  two commuting coefficient squares. hab is a consequence of ha and hb,
  not an extra condition on coefficient diagrams. squareComparison is
  explicitly built from the same derived comparisons and the ring-map equality.
- The one-object identity-cover specialization includes ordinary rings.
  There are no nonzero, nonempty, flatness, surjectivity or boundedness binders.

The proof docstring follows all eight node steps: flat-term K-flat resolution;
preservation under each extension; balanced inverse tensor formulas; homotopy
naturality and localization descent; normalized unit calculation; triple and
finite coherence; commuting coefficient diagrams; and ordinary-ring
specialization. The formulas respect both balancing relations and restrictions.
Both triple collapses yield x tensor c(b(s))c(t)u. The unit sends x through
1 tensor (1 tensor x) to 1 tensor x. No extra mathematical prerequisite is
hidden in the packaging.

I independently searched the project Sheaf tree, upstream WeilConjectures,
and Mathlib for derived composition/scalar-extension and successive-extension
interfaces. ModuleCat.extendScalarsComp and extendScalars_assoc are ordinary
module results, not this ring-sheaf derived statement. The existing derived
change-of-rings and coefficient-adjunction interfaces are used, not redefined.
The worker's three kinds of search are recorded above. All eight helper/main
names occur in lean.declarations. Helpers have actual data; the only sorry is
the main theorem's proof. Every declaration has source/blueprint documentation;
the main theorem has the full proof plan. Lines are at most 100 characters,
autoImplicit is false, and the stored lean.statement is verbatim the theorem
signature before := by. There is no statement correction or new dependency
module in this delivery.

Edge cases: empty site; zero ring, module and complex; identity coefficient
maps; nonflat maps Z -> Z/4 -> Z/2; and complexes unbounded in both directions.
For the nonflat example with input Z/2, use its two-term free Z-resolution:
the successive extension and direct extension both give the two-term complex
[Z/2 --0--> Z/2]. All section formulas and unit equations still apply.
No excluded edge case or silent universe restriction was found.

Compiler reproduction: the prescribed scompile.py was run on the immutable
module. It exited 0, with no errors or warnings: sandbox
Sheaf/Stage2/Sandbox0.lean in 8.9 s, then library
Sheaf/Algebra/Homology/SuccessiveDerivedQuotientNormalization.lean in 10.6 s.
The currently installed wrapper uses the server persistent side overlay,
although the brief describes its earlier local-overlay implementation.
No direct ssh command, global build, live Lean write, repository edit, claim,
delivery or merge was performed.

Finding and correction: H1/H11, the delivered second-reading heading contained
only a sentence saying no reading had occurred. This complete replacement
report supplies the actual independent reading. No Lean or node repair is
needed, and no substantive fault was found.
