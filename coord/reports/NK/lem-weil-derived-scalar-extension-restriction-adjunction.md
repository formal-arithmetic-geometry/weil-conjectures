## Worker report

The module `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` states the
completed-coefficient derived tensor/restriction adjunction. It also supplies the
ordinary tensor adjunction with its sectionwise unit formula and exactness of
restriction, the two clauses needed to construct and normalize the derived pair.
Every new theorem has proof `sorry`; no mathematical theorem is proved here.
All other declarations are actual abbreviations, instances from named assertions,
or projections of the universal derived-change-of-rings witness. The ordinary
extension witness fixes objects AND morphisms; the derived witness includes its
universal counit. These are not arbitrary functors chosen from mere existence.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. Its ring of integers,
  chosen uniformizer and quotients are the existing `Padic.coefficientExtension*`
  declarations. No new valuation ring or uniformizer is chosen.
- The scheme is `(Y : AlgebraicGeometry.Scheme.{t})`. The site is exactly
  `AlgebraicGeometry.Scheme.ProEt Y` with `ProEt.topology Y`. The coefficient/module
  universe is `max u (t+1)`, containing both the field and the small-site model.
  Site object universe `t+1` and morphism universe `t` remain distinct.
- `(n : ℕ)` means the positive exponent `n+1`, bijectively covering every exponent
  in the node. `integralCoefficientSheaf l E Y n` is its constant quotient sheaf.
  Its underlying quotient is `Padic.coefficientExtensionRing l E (n+1)`.
- `completedIntegralCoefficientSheafUnrestricted` is exactly `limit
  (integralCoefficientSheafSystem l E Y)`, with the existing quotient transition
  maps. `completedIntegralCommRingSheafUnrestricted` retains commutativity on
  exactly the same section rings. Its projection is the existing limit coordinate
  map, presented in commutative rings. Forgetting commutativity changes no ring data.
- `scalarReductionSource` and `scalarReductionTarget` are Mathlib module-sheaf
  categories over these ring sheaves. Their standard `HasDerivedCategory`
  instances give unbounded derived categories, without changing abelian structures.
- `scalarReductionRestriction` is `SheafOfModules.restrictScalars` applied to that
  projection. `scalarReductionRestriction_exact` asserts preservation of finite
  limits and colimits, the exactness stated in the node. The definition
  `scalarReductionDerivedRestriction` is the recorded Mathlib
  `Functor.mapDerivedCategory`, hence is termwise restriction, triangulated and
  compatible with localization via `mapDerivedCategoryFactorsh`.
- `scalarReductionExistence` is the recorded
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` applied to the
  actual completed projection. `scalarReductionExtension` selects its ordinary
  functor, whose objects and maps are fixed to `changeOfRings` and
  `changeOfRingsHom`. `scalarReductionDerivedExtension` and
  `scalarReductionCounit` select its universal left-derived pair. The defining
  witness includes exactness and invertibility of this counit at every K-flat
  complex, so this is the required K-flat derived tensor product.
- `derivedScalarExtensionRestrictionAdjunction` supplies an adjunction of these
  very functors. Its `Adjunction.homEquiv` is the displayed Hom bijection, with
  naturality in both variables as part of the adjunction structure.
- `scalarReductionExtension_adjunction` normalizes the ordinary unit sectionwise:
  apply the ordinary module extension/restriction unit (the element `1 tensor x`),
  then the module-sheafification unit, then the fixed object identification.
  The derived adjunction theorem equates its unit, after the K-flat counit and
  exact-restriction factorization, with the localized homotopy adjunction unit.
  The selected ordinary unit is explicitly fixed to the normalized one. Thus the
  unit is induced by the coefficient projection, not an arbitrary adjunction unit.
  Naturality extends this representative equation to any K-flat resolution roof.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`: the pro-etale site, constant
  commutative-ring sheaf forgotten to rings, and module universe convention.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the general module-sheaf category is transparently Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`,
  `SheafOfModules.restrictScalars`: unchanged abelian sheaf and restricted action.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.limit` and
  `limit.π`: inverse limit and its coordinate maps. The module-sheaf limit
  instances and evaluation preservation in `Sheaf.Limits` were also inspected;
  ring-sheaf limits use `Mathlib.Algebra.Category.Ring.Limits` and site limits.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Qh`: unbounded localization.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`,
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` and
  `derivedChangeRingIndependentCoefficients`: the full universal derived tensor
  witness, retaining the canonical ordinary tensor objects and maps.
- `Sheaf.Paper.CompletedIntegralCoefficients`, the existing finite coefficient
  sheaves/system and generalized completed ring/projection (repair below).
- `Sheaf.NumberTheory.Padics.CoefficientExtension`,
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, `coefficientExtensionTransition`: actual coefficients.
- `Sheaf.Algebra.Homology.KFlat`, `CochainComplex.IsKFlat`: acyclic-total-tensor
  definition with independent coefficient universe (supporting overlay below).
- Proof imports retain the ringed-topos module adjunction, exact-functor derived
  factorization, exact-functor derived universal property, derived-adjoint theorem,
  pre-derived Hom formula and upstream termwise homotopy adjunction from the node.

Sources checked: blueprint `def-weil-derived-direct-image`, order 1468; the local
Stacks `sites-modules.tex`, lemma-adjointness-tensor-restrict (03CZ), and
`sites-cohomology.tex`, lemma-derived-base-change (06YY) and lemma-adjoint (07A6).
The latter applies to the identity topos with the actual sheaf coefficient map.
It imposes no restriction on the characteristic of the scheme.

Edge cases checked: `n=0` is exponent one, not the zero quotient; no positive
exponent is lost. The zero complex, empty scheme and zero section rings require
no nonempty or nontrivial assumption. Arbitrary unbounded complexes are allowed;
K-flatness is only used to identify the unit on computing representatives, not
as a restriction on derived objects. There is no constructibility, derived
completeness, coefficient flatness, finite-field datum or `l != char(Y)` hypothesis.
The universes `u` and `t` are independent. No statement correction or
STATEMENT-DISPUTED issue is needed.

Searches made (2026-10-15):

- `msearch.py ... leanfinder`: “Derived extension of scalars for sheaves is left
  adjoint to exact derived restriction of scalars, with unit induced by the ring
  map”. Eight hits, including `SheafOfModules.PullbackConstruction.adjunction`,
  `PresheafOfModules.sheafificationAdjunction`, and sheaf pushforward adjunctions;
  all are underived or different coefficient formalisms, not this statement.
- `msearch.py ... loogle`: `CategoryTheory.Adjunction.derived,
  SheafOfModules.restrictScalars`. No hits for that combined query. The source
  Mathlib abstract derived adjunction API was inspected separately; it requires
  derivability hypotheses and does not give this completed-coefficient instance.
- `msearch.py ... grep`: `derived.*[Rr]estrict|[Rr]estrict.*[Dd]erived` in
  `Algebra/Category/ModuleCat`: no hits.
- `rg` of both upstream `WeilConjectures` and side `lean/Sheaf` for
  `integralDerivedRestrict|derivedRestriction|integral.*[Aa]djunction|` plus the
  item id: only unrelated geometric restriction comparisons, no existing theorem.
- Concept/name searches in the DAG and side sources found the already landed
  completion and derived-reduction declarations. Their finite-field arguments
  are not present in this item's statement, so importing that reduction verbatim
  would add hypotheses. The completion is repaired below, while the same recorded
  general derived-change-of-rings construction supplies this item's tensor.

## Dependency modules

`def-weil-completed-integral-coefficients`: its module required a finite-field
datum `D` and `l != D.p`, although the underlying limit uses neither, and this
consumer explicitly has no such datum. Under §1(B), add the unrestricted
completion, commutative enhancement and projection in the owning module. Rewire
the original completion and commutative wrappers through that shared core while
retaining their original signatures. This is the same finite quotient diagram,
limit and projection, without an irrelevant interface requirement. The one new
postponed theorem is commutativity of that same inverse-limit ring, with its
source and complete proof in the docstring; all data constructions are real.

`def-pc-kflat-complex`: the node already records the independent-coefficient
K-flat module, but compilation resolves an older live artifact whose coefficient
universe is fixed to the maximum of the two site universes. This prevents the
recorded independent-coefficient derived-change-of-rings module from compiling.
Include the recorded generalized source as a sibling overlay, with a lean-only
record explaining why it is required. It retains every definition and statement
unchanged. No equality of site and coefficient universes is imposed.

Validation: `scompile.py NK lem-weil-derived-scalar-extension-restriction-adjunction`
with all three sibling modules returned success without warnings. Individual delivered
files took 2.2 s (KFlat), 3.9 s (CompletedIntegralCoefficients) and 15.4 s (the item's
module), all within the unchanged 60 s file limit. No global build was run.

A final full-name collision search with `rg` for `scalarReduction`,
`derivedScalarExtensionRestrictionAdjunction` and `completedIntegral.*Unrestricted`
in Mathlib, upstream WeilConjectures and side Sheaf sources returned no matches.
All recorded declaration names were checked against the delivered source files.

## Second reading by NK

I independently read the node, its full proof, the three delivered modules, the
recorded dependency signatures and their source declarations. No mathematical
statement or construction needed changing. This reading adds the audit below.
There is no statement_change and no new definition node in this delivery.

Object/hypothesis/conclusion checklist (H3):

1. Prime and finite coefficient extension: `l : ℕ`, `[Fact l.Prime]`,
   `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
   `[FiniteDimensional ℚ_[l] E]` match exactly. I opened CoefficientExtension:
   `coefficientExtensionIntegers` is the valuation subring, its selected
   uniformizer generates the maximal ideal, `coefficientExtensionRing l E m`
   is the quotient by its m-th power, and `coefficientExtensionTransition`
   is the quotient factor homomorphism. Verdict: same coefficient data.
2. Arbitrary scheme and small pro-etale site: `Y : Scheme.{t}` and
   `ProEt.topology Y` use the recorded site, not an etale or large site.
   ProEtaleDerivedCategory confirms the constant CommRingCat sheaf followed
   by forgetting commutativity. Module universe `max u (t+1)` contains both
   the independent coefficient universe and the site model; `scalarReductionSiteSmall`
   is supplied by `essentiallySmallSelf`, not an extra assumption.
   Object universe t+1 and morphism universe t remain distinct. Verdict: exact.
3. Positive exponent: the binder `n : ℕ` denotes n+1, so `n=0` gives the
   first quotient and every positive exponent occurs. Verdict: exact reindexing.
4. Finite constant sheaves, quotient transitions, completion and projection:
   `integralCoefficientSheaf`, `integralCoefficientSheafTransition`,
   `integralCoefficientSheafSystem` use the coefficient quotient maps.
   `completedIntegralCoefficientSheafUnrestricted` is literally `limit`
   of this inverse sequence. I opened Mathlib's `limit` and `limit.π`:
   `completedIntegralCommRingProjectionUnrestricted` is precisely its n-th
   coordinate, retaining the commutative structures on the same section rings.
   This is not the constant sheaf of the discrete valuation ring. Verdict: exact.
5. Abelian module categories and unbounded derived categories:
   `scalarReductionSource` and `scalarReductionTarget` use Mathlib
   `SheafOfModules`, the definition transparently exposed by ringedSiteModules.
   The two standard HasDerivedCategory instances use the recorded unbounded
   localization, not bounded or constructible subcategories. Verdict: exact.
6. Restriction and exactness: `scalarReductionRestriction` is Mathlib's
   `SheafOfModules.restrictScalars` along the same projection. I opened its
   implementation: the sheaf condition is unchanged and only the action is
   restricted. `scalarReductionRestriction_exact` states finite-limit and
   finite-colimit preservation, and the instances project those assertions.
   Additivity is inherited from Mathlib. Verdict: the node's exactness clause.
7. Termwise triangulated restriction: `scalarReductionDerivedRestriction`
   is `mapDerivedCategory`. I read ExactFunctor's construction and
   `mapDerivedCategoryFactorsh`; these descend the termwise homotopy functor
   and give its localization identification. Verdict: exact intended functor.
8. K-flat derived tensor: `scalarReductionExistence` applies the recorded
   `derivedChangeOfRingsIndependentCoefficients` to the actual completed
   projection. I read that theorem in full: its ordinary functor has objects
   `changeOfRings` AND maps `changeOfRingsHom`, its derived pair has the
   universal left-derived counit, triangulatedness, and an invertible counit
   on every K-flat representative. I also opened TensorProduct's sectionwise
   extension, sheafification, and morphism construction. Hence the choices
   used by `scalarReductionExtension`, `scalarReductionDerivedExtension`,
   and `scalarReductionCounit` are determined up to the relevant compatible
   equality/isomorphism; no arbitrary functor or hollow datum is selected.
   Verdict: the tensor functor specified in the node.
9. Bifunctorial Hom bijections: the existential `adj` in
   `derivedScalarExtensionRestrictionAdjunction` has exactly the two functors
   of items 7 and 8 as its left and right sides. `Adjunction.homEquiv` supplies
   the Hom bijection for every K and M with naturality in both. There is no
   K-flat hypothesis on either derived variable. Verdict: all quantifiers match.
10. Unit induced by the coefficient projection:
    `scalarReductionExtension_adjunction` fixes the ordinary unit on every
    section to the module tensor unit followed by sheafification and the fixed
    object identification. The main theorem equates the derived unit, followed
    by restriction of the K-flat counit and `mapDerivedCategoryFactorsh`, with
    the localization of this chosen normalized unit. These composites have
    the correct directions. Invertibility of the K-flat counit gives the
    unit on a representative; naturality gives the resolution roof in node
    proof step 5. Verdict: no unspecified choice of adjunction unit remains.

Source checks: I read sites-modules.tex immediately before and through
lemma-adjointness-tensor-restrict (03CZ): the hypothesis is just a map of ring
sheaves on a site and tensor is sheafified sectionwise extension. I read
sites-cohomology.tex lemma-derived-base-change (06YY) and lemma-adjoint (07A6):
the latter gives bifunctorial Hom bijections on unbounded categories of any
morphism of ringed topoi. Identity topos plus our coefficient projection is
such a morphism, with exact pushforward. No invertibility of l on Y is needed
for this abstract adjunction, although the ancestor's geometric application
assumes it. I also read the ancestor blueprint definition at order 1468.
The main docstring follows all five proof steps of this node, including the
resolution-level unit. All new theorem proofs remain `sorry`.

Dependency modules (H13): I independently read both owning nodes and modules.
The completion repair keeps the original finite-field interfaces and uses one
shared inverse-limit core; the new commutativity assertion concerns that same
limit and its docstring gives the projectionwise proof. All functor and sheaf
data are constructed. The KFlat overlay retains the recorded independent-
coefficient interface: `IsKFlat` tests acyclicity of total tensor against every
acyclic complex, and `IsKFlatResolution` is quasi-isomorphism plus K-flatness,
as in 06YN/06YS. Its infrastructure assertions transport sheafification and
tensor localization through the small model, without equating site universes.
Only lean records change on these dependencies. No private replacement notion
or additional mathematical hypothesis is introduced.

Edge cases: arbitrary empty scheme, zero module/complex and zero section rings
are allowed; no nonempty or nontrivial instance is required. The tower is the
nonempty inverse sequence specified by the node, so no arbitrary index-set
restriction is present. n=0 covers exponent one. All characteristics of Y,
including l, are allowed. Site and field universes are independent. The module
uses bound `t,u` and `autoImplicit false`; no free universe or variable remains.

Independent H4 searches: msearch leanfinder query “Left derived change of
coefficient rings on module sheaves has exact scalar restriction as right
adjoint” returned eight underived module, sheafification, condensed, and
pushforward adjunction hits. Loogle `SheafOfModules.restrictScalars` returned
the construction and its additive/underlying-map lemmas, already used here.
My rg search for derived adjunction and derived restriction in Mathlib's module
sheaf and derived-adjunction files, upstream WeilConjectures, and project Sheaf
found abstract derived-adjunction APIs and geometric restriction results.
I opened upstream Algebra/Category/ModuleCat/Sheaf/RestrictScalars: its
`Sheaf.restrictScalars` concerns constant coefficient rings and cannot serve
as restriction from modules over this completed sheaf of rings. None is this
completed-coefficient adjunction with its K-flat-normalized unit. Existing
primitive notions are reused, so the item's module is retained.

Mismatch/change record: no H3/H4/H5/H6/H8/H9 mismatch found. No Lean, node
statement, dependency field or recorded signature changed in the second reading.
All three modules have lines at most 100 characters. The primary recorded
signature matches the source verbatim. Validation is recorded below.

Second-reader validation: scompile.py compiled every delivered file cleanly:
KFlat 2.2 s, CompletedIntegralCoefficients 3.8 s, and
DerivedScalarExtensionRestrictionAdjunction 15.5 s, with no warnings or errors.
The wrapper also compiled the required side-only import overlays. The default
60-second limit, nice 19 and two threads were retained; no global build was run.
