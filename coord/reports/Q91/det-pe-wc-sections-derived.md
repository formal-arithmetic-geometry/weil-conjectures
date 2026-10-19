## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsDerived` states
`AlgebraicGeometry.Scheme.ProEt.wContractible_sections_derived`. Its two clauses are
exactly the two assertions of `det-pe-wc-sections-derived`; the natural comparison
is the unit of the recorded unbounded right-derived functor, not a freely chosen
map or an assertion merely that two objects are isomorphic. The natural-language
statement is unchanged. Every theorem has proof `sorry`.

Hypotheses and clauses, matched individually:

- The ambient scheme is `(X : Scheme.{t})`, with no finiteness or separation condition.
- The affine object U = Spec D is represented by `(D : Type t) [CommRing D]` and
  `(f : Spec (CommRingCat.of D) ⟶ X) [WeaklyEtale f]`, hence the original site object
  `ProEt.mk f : X.ProEt`. Weak contractibility is `[IsWContractibleRing D]`, exactly
  the interface in the recorded exact-sections dependency.
- The ring sheaf is `(R : Sheaf (topology X) RingCat.{u})`. No commutativity, field,
  completeness, torsion, or constant-coefficient assumption is imposed on R.
- Module sheaves are the recorded `ringedSiteModules`, transparently Mathlib's
  `SheafOfModules`. Their universe is `max u v (t + 1)`: the common universe contains
  the coefficient rings, the site, and arbitrarily large extra module universe v.
  The small pro-etale site retains object universe t+1 and morphism universe t.
  These universes are not identified. This implements the source's size convention.
- The two `HasDerivedCategory.{wA}` and `HasDerivedCategory.{wB}` binders choose the
  localization and its morphism sizes independently for module sheaves and R(U)-modules.
  They are size choices as in the recorded derived-category definition; standard
  localizations always exist. They add no geometric or coefficient restriction.
- “K arbitrary (possibly unbounded)” is
  `∀ K : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ`.
  There is no boundedness predicate and no sign restriction on complex degrees.
- “The natural map K(U) → RΓ(U,K)” is
  `Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit
    (SheafOfModules.evaluation R (op (ProEt.mk f)))
    (moduleQuasiIsoKInjectiveResolutions X R)`, applied at
  `(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K`.
  This is precisely eta_K in the node proof. Its source is evaluation of K term by
  term in the homotopy category followed by `DerivedCategory.Qh`, identified with
  the localization of the termwise section complex by `quotientCompQhIso` and the
  definition of `mapHomotopyCategory`. Its target is RF applied to Qh of K, likewise
  canonically identified with RF(Q(K)). Thus this states invertibility of the
  specified map, with the standard localization identifications.
- “Is an isomorphism in the derived category of R(U)-modules” is `IsIso` on that
  component; evaluation has target
  `ModuleCat.{max u v (t + 1)} (R.obj.obj (op (ProEt.mk f)))`.
- “In particular H^q(U,F)=0 for every F and q>0” is the second conjunct:
  for every `F : ringedSiteModules ... R` and `q : ℤ`, `0 < q → IsZero ...`.
  The displayed object applies the same recorded right-derived evaluation to
  `(DerivedCategory.singleFunctor _ 0).obj F`, then applies
  `DerivedCategory.homologyFunctor (ModuleCat ... R(U)) q`.
  It is therefore exactly H^q(RΓ(U,F[0])) in R(U)-modules.

The helper `moduleEvaluation_additive` exposes the existing additive structure of
`SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op U)` by
`inferInstanceAs`; it constructs no new notion. The abbreviation
`moduleQuasiIsoKInjectiveResolutions` extracts the arbitrary-quasi-isomorphism
hypothesis from `Abelian.HasKInjectiveResolutions.exists_isKInjective`, forgetting
only the extra monomorphism assertion. It uses the Grothendieck instance supplied
by the repaired dependency. Neither helper assumes the desired conclusion,
chooses module data from a bare existence theorem, or contains a `sorry`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact`:
  `AlgebraicGeometry.Scheme.ProEt.wContractible_sections_exact`; the module case
  provides exactness at section universe `max u v (t + 1)` by instantiating its
  free section universe parameter. The abelian-sheaf clauses need not be repeated.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  also read Mathlib's `SheafOfModules`, its category and abelian-instance signatures.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, `Qh`, `quotientCompQhIso`, and `singleFunctor`;
  `...HomologySequence`: `DerivedCategory.homologyFunctor`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its unit,
  universal property, K-injective unit-isomorphism theorem and resolution iso.
  The helper supplies its exact arbitrary-quasi-isomorphism premise.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`:
  `SheafOfModules.isGrothendieckAbelianOfUniverses`, the dependency repair below.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`:
  `CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`,
  and `HasKInjectiveResolutions.exists_isKInjective` from its public imports.
- `Mathlib.Algebra.Category.ModuleCat.EnoughInjectives`: the recorded
  `ModuleCat.enoughInjectives` and its abelian-module-category imports; this
  proof-dependency import remains private. The argument uses only abelianness.
- `def-weil-size-convention` is the recorded metatheoretic convention; it has
  no module or definition to import. Explicit universes implement it.
- Reused already published transport helpers
  `CategoryTheory.siteAbelianHasSheafify` and
  `CategoryTheory.siteAbelianWEqualsLocallyBijective` from
  `Sheaf.CategoryTheory.Sites.RGammaDerivedLimit`. These supply the canonical
  small-model sheafification/locally-bijective instances for the original site,
  with independent object, morphism and coefficient universes. They do not
  replace module-valued cohomology by abelian-group-valued cohomology.

Sources checked: the current blueprint node and proof files under
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-cor-pe-wc-sections/`, Stacks `injectives.tex` remark-existence-D (079Q)
and theorem-K-injective-embedding-grothendieck (079P), and `derived.tex`
lemma-right-derived-exact-functor (015F). The declaration docstrings give the
four-step proof plan of the node, including naturality identifying the map.

Edge cases checked before writing: the zero complex and zero sheaf give the
zero-to-zero isomorphism and zero cohomology; the empty affine, when admitted by
the weak-contractibility predicate, is not excluded by any nontriviality binder;
q=1 and every positive integer are included, q=0 is correctly outside the
vanishing assertion, and negative complex degrees are unrestricted. Empty ambient
schemes are allowed. R can be a noncommutative or zero ring sheaf. The auxiliary
module universe v is arbitrary, both localization morphism universes are independent,
and the site morphism universe remains t, rather than t+1.

Searches made (no exact existing statement was found):

- `msearch.py ... leanfinder` query “Sections of unbounded complexes on weakly
  contractible pro etale affine schemes compute derived sections”: eight hits,
  all affine-limit/global-section or affine-Zariski-site results; none is this
  unbounded module-valued derived-unit comparison.
- `msearch.py ... loogle` query `"rightDerivedFunctorOfQuasiIsoResolutionsUnit"`:
  zero hits in the service index. The local project declaration was read directly
  and used, as recorded by the dependency node.
- `msearch.py ... grep` query
  `sections.*[Dd]erived|[Dd]erived.*sections|rightDerivedFunctorUnit` in
  `Algebra/Homology`: zero Mathlib hits.
- `rg` in the upstream WeilConjectures tree and `lean/Sheaf` for
  `wContractible.*[Ss]ections|sections.*[Dd]erived|[Dd]erived.*[Ss]ections`:
  the exactness statement, topological-open derived sections, and various etale
  comparisons occur; none supplies this statement over arbitrary ring sheaves on
  the pro-etale site. `grep -rn det-pe-wc-sections-derived` upstream: no hits.
- Narrow `rg` for `wContractible.*(derived|Derived)|wContractible_sections|`
  `det-pe-wc-sections-derived|rightDerivedFunctorOfQuasiIsoResolutions` identified
  the recorded right-derived interfaces and exactness module. The exact-functor
  comparison `rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory` was
  read: it requires exactness and the resolution hypothesis and is not the
  specialized theorem, nor does it include positive cohomology vanishing.
- For the universe repair, `msearch.py ... leansearch` query “Sheaves of modules
  over a sheaf of rings on a small site form a Grothendieck abelian category”:
  eight hits, including `SheafOfModules`, `instAbelian` and ordinary abelian-sheaf
  Grothendieckness; no generic ringed-site theorem with these universes.
  `msearch.py ... grep isGrothendieckAbelian|wContractible.*[Dd]erived` in
  `CategoryTheory/Abelian`: 25 hits on Grothendieck categories and abelian-valued
  sheaves, not this arbitrary ring-sheaf universe interface. Upstream grep and
  source reading found `SheafOfModules.isGrothendieckAbelian`, but it equates the
  site-object, site-morphism, ring and module universes. Local grep found the
  existing generalized K-injective interfaces require commutative coefficients;
  they do not cover arbitrary RingCat coefficients. The existing small-model
  transport helpers above are reused, not restated.
- `rg` on the new full declaration names in Mathlib, upstream, the upstream name
  index and `lean/Sheaf`: no name collisions.

Validation: both delivered modules compiled separately in dependency order through
`scompile.py Q91 det-pe-wc-sections-derived`, with no errors or warnings (1.2 s
for the generic dependency, 1.8 s for the item on the successful local-overlay run).
No global build or direct source-checkout mutation was run. Delivery dry run is
performed after assembling these records and report.

No statement dispute, statement correction, new definition node, or omitted
mathematical clause was required.

## Dependency modules

`lem-weil-pbc-ring-sheaves-grothendieck` is repaired under §1(B). Its upstream
record is genuinely unusable here: the full signature has `C : Type u`,
`[SmallCategory C]`, `R : Sheaf J RingCat.{u}`, and `SheafOfModules.{u} R`.
The small pro-etale site has objects in t+1 and morphisms in t, and the ring-sheaf
universe is independent; forcing these equal would alter the size convention.
The module `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses` states
precisely the original arbitrary-ring, small-site Grothendieck property in the
common universe `max c h r s`. It adds no sheafification or Grothendieck assumptions:
existing small-model transport gives abelianness, and its proof plan transports
the upstream theorem along the equivalent small site and lifted coefficients.
The same category, colimits, exact filtered colimits and generator are retained.
Only the dependency's `lean` field changes. Its id, which already had a published
record and was already a proof dependency, is added to the item's `stmt_deps`
because the resolution abbreviation now uses this interface in its signature.


## Second reading by Q91

I independently read the item node and its four proof steps, the blueprint statement
and proof at main-20261015/sec-proetale-coefficients/sk-cor-pe-wc-sections, and both
submitted Lean modules. I read the signatures and implementations of the recorded
dependencies, rather than relying on their declaration names. No repair note for this
item is present under coord/repair-notes. No statement_change or new definition node
is present or required.

The statement inventory, with its Lean rendering and verdict, is:

1. An arbitrary ambient scheme X: `(X : Scheme.{t})`. There are no geometric
   finiteness, separation, nonemptiness or characteristic hypotheses. MATCH.
2. An affine pro-etale object U = Spec D, with D w-contractible, as in
   det-pe-wc-sections-exact: `(D : Type t) [CommRing D]
   [IsWContractibleRing D] (f : Spec (CommRingCat.of D) ⟶ X) [WeaklyEtale f]`,
   with U represented by `ProEt.mk f`. I read that exactness theorem and the
   upstream w-contractible definition (w-strictly-local and extremally disconnected
   connected-component space). This is the same object and predicate. MATCH.
3. An arbitrary ring sheaf R on the original pro-etale site:
   `(R : Sheaf (topology X) RingCat.{u})`. RingCat allows noncommutative rings.
   No constant-coefficient, commutativity or nonzero hypothesis occurs. MATCH.
4. Sheaves of left R-modules: `ringedSiteModules.{max u v (t + 1)} R`.
   The recorded abbreviation is transparently Mathlib `SheafOfModules`; I read
   its objects, morphisms, evaluation, and abelian-instance hypotheses. No private
   module category or internal-module substitute is introduced. MATCH.
5. K an arbitrary integer-indexed, possibly unbounded complex:
   `∀ K : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ`.
   Neither boundedness nor termwise injectivity is assumed. MATCH.
6. K(U) means termwise sections: `SheafOfModules.evaluation R (op (ProEt.mk f))`
   induces the source of `rightDerivedFunctorOfQuasiIsoResolutionsUnit` through
   `mapHomotopyCategory` and `DerivedCategory.Qh`. I read the unit's full type
   and `quotientCompQhIso`; these identify this source with the localization of
   the termwise section complex. MATCH.
7. The specified natural map, not just existence of an isomorphism:
   `IsIso ((Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit ...
   (moduleQuasiIsoKInjectiveResolutions X R)).app
   ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))`.
   The recorded right-derived pair has precisely the universal unit in node
   def-sfb-right-derived-functor; its target is RF of K localized. The target
   coefficient category is exactly `ModuleCat ... (R.obj.obj (op (ProEt.mk f)))`.
   MATCH.
8. Every module sheaf F and every positive cohomological degree:
   `∀ (F : ringedSiteModules ... R) (q : ℤ), 0 < q → IsZero ...`.
   The object is `DerivedCategory.homologyFunctor ... q` applied to the same
   derived evaluation of `(DerivedCategory.singleFunctor _ 0).obj F`.
   This is exactly H^q(U,F). The conjunction makes the vanishing independent of
   any choice of K and includes all F. MATCH.
9. Size choices: module values lie in `max u v (t + 1)`, with arbitrary v;
   the site keeps object universe t+1 and morphism universe t. The two
   `HasDerivedCategory` binders choose localization morphism universes wA and wB
   independently, as the recorded derived-category definition requires. They
   do not force a site/coefficient universe equality or impose a mathematical
   boundedness condition. MATCH with def-weil-size-convention.

Dependency-module review (H13): I read
lem-weil-pbc-ring-sheaves-grothendieck and the old upstream
`SheafOfModules.isGrothendieckAbelian` signature: C : Type u, SmallCategory C,
R : Sheaf J RingCat.{u}, modules in u. It cannot directly consume the original
small pro-etale category with its different object and morphism universes.
The replacement `isGrothendieckAbelianOfUniverses` quantifies over arbitrary
`C : Type c`, `Category.{h} C`, topology J, and `R : Sheaf J RingCat.{r}`,
and asserts Grothendieck abelianness for modules in `max c h r s`.
All the site and coefficients are small in that common universe, so this is
precisely the dependency node, including all small colimits, AB5 and a separator.
I read Mathlib's IsGrothendieckAbelian fields and its colimit consequence.
The existing small-model instances from RGammaDerivedLimit supply abelianness;
there are no extra sheafification assumptions in the submitted signature.
The already published RingedSiteKInjectiveResolutionsOfUniverses theorem has
commutative coefficients and cannot replace this arbitrary-RingCat assertion.
No new definition node or unrelated dependency statement is hidden here.

Source checks: Stacks injectives.tex 079P explicitly covers every complex of a
Grothendieck abelian category, and 079Q explicitly includes modules on ringed
sites. Derived.tex 015F asserts the canonical comparison for all complexes of
an exact functor; 070K/070Y supply the unbounded K-injective derived pair.
Sites-cohomology.tex Section 07A5 states Grothendieckness for module sheaves
and the induced unbounded derived functor of an additive functor.
Sites-modules.tex definition-sheaf-modules and lemma-abelian identify the
category used here. These places add no commutativity or boundedness assumption.

Mismatch found and repaired: both source docstrings in the dependency module
called 03D1 a section on module sheaves, but the Stacks tag table identifies it
as lemma-pushforward-module. I replaced that citation with Tags 03CV and 03DA
(the sheaf-module definition and abelian-category lemma), retaining 07A5 and
079Q. No Lean signature, natural-language node statement, or dependency field
needed a change. The item proof docstring retains all four node proof steps,
including naturality identifying the specified comparison.

Edge cases: zero complex and zero sheaf are included; the vanishing assertion
correctly omits q=0 (which need not vanish) and includes every positive integer.
Negative complex degrees are unrestricted. Empty ambient schemes and the empty
affine are not excluded by any Nonempty or Nontrivial binder; the upstream
w-contractible predicates are properties of spectra/localizations, not an added
nonzero-ring assumption. Arbitrary coefficient characteristic and the zero and
noncommutative ring cases are retained. There is no index family whose empty
case is silently excluded. Common-universe enlargement covers arbitrary module
sizes without equating site object and morphism universes.

Independent searches: msearch leanfinder, query “Unbounded derived evaluation on
sheaves of modules at a weakly contractible affine has invertible unit and
vanishing higher cohomology”, returned eight derived t-structure/K-projective
results, no match. Loogle query `"SheafOfModules.evaluation"` returned twelve
ordinary evaluation/limit-preservation declarations, which were read against
the required derived-unit statement. LeanSearch for left modules over an
arbitrary ring sheaf being Grothendieck returned generic abelian-sheaf and
constant-ring module results, not the independent-universe ringed-site theorem.
The msearch grep query `IsGrothendieckAbelian|derived.*evaluation|evaluation.*derived`
returned generic sheaf/ModuleCat Grothendieck results. Independent rg searches
in pinned Mathlib, upstream WeilConjectures, and lean/Sheaf for acyclic evaluation,
derived sections, wContractible derived statements, and the new declaration
names found no exact existing item or name collision. I opened the nearby
ringed-site universe theorem and the recorded right-derived interface; neither
is an existing statement of this item.

No hollow data: the additive instance uses the existing composite instance,
and the resolution abbreviation eliminates an existing proof of resolution
existence to obtain a proposition, choosing no object data. The only postponed
proofs in this delivery are the two named theorems, each with its owning DAG
node and source/proof docstring. Both theorem bodies are `sorry`. No file-local
notation, private copy, unbound variable, or line over 100 characters remains.
Both node lean.statement strings were checked verbatim against their file
signatures. Both delivered modules compiled separately through scompile.py
without warnings or errors; final wrapper compilation and server delivery
preflight follow the citation repair.
