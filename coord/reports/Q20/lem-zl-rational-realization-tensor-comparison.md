## Worker report

The delivery states `WeilConjectures.RationalTensorRealization.rational_realization_tensor_comparison`
in `Sheaf.Paper.RationalRealizationTensorComparison`. The main module has the item theorem and the equivalent completion-presentation
existence helper, both postponed with proof `sorry`.
The other declarations are transparent constructions or structures unpacking the comparison
asserted by this node. No theorem is proved. No existing source or live-library file is edited.

Hypothesis and clause mapping:

- A prime ell is `(l : ℕ) [Fact l.Prime]`. The finite extension is an arbitrary
  `E : Padic.FiniteCoefficientFields l Ω`, represented by `pbcFiniteField.{u} l Ω E`.
  `Ω` is an arbitrary algebraic closure of `ℚ_[l]`. Every finite extension embeds into
  such a closure; the recorded finite-stage equivalence already uses these size-transported
  fields. All finite stages, inclusions (including reflexive inclusions), and ramification
  indices are retained. The valuation ring and uniformizer are the dependency's
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`.
- The algebraic closure of the finite base field is `D.k`, for `D : FiniteFieldDatum`;
  ell different from its characteristic is `_hl : l ≠ D.p`. The structure map is
  `[X.scheme.Over (Spec (.of D.k))]`; finite type is `LocallyOfFiniteType` together with
  `QuasiCompact` of that map, and separation is `IsSeparated` of the same map.
- `X : ContinuousRational.Base l` records the Noetherian, finite-dimensional, ell-invertible
  consequences required by both existing realization interfaces. These are consequences of
  the preceding geometric assumptions (the node's proof step 1), not a restriction to a
  smaller class of schemes. `CompactSpace` and `QuasiSeparatedSpace` are likewise the qcqs
  consequences; compactness is already inherited from Noetherianity, while separation over
  the affine field gives quasi-separatedness. The small site retains objects in `u+1` and
  morphisms in `u`; the coefficient sheaves/modules live in `u+1`. There is no equality of
  site object and morphism universes.
- B_T and E_T are exactly the coefficient objects in
  `R.realization (pbcFiniteField l Ω E) X`, with its `integralIso`, `localizationIso`,
  finite quotient normalization and localization normalization. The target uses
  `rationalCoefficientSheaf`, not the discrete constant E-sheaf.
- The raw category is `sfRationalConstructibleCategory` and the tensor is precisely
  `rationalDerivedTensor`; the unit is `pullbackTensorRationalUnit`. The source associator,
  both unitors and braiding are the published `pullbackTensorRationalAssociator`,
  `pullbackTensorRationalLeftUnitor`, `pullbackTensorRationalRightUnitor`, and
  `pullbackTensorRationalBraiding`. These are the localized completed maps, not new choices.
- I is `((S.coefficients X.scheme).stage E).rational.functor`, and J_pbc is
  `(R.realization (pbcFiniteField l Ω E) X).J`. `realization` is literally their composite.
  `S` and `R` are arbitrary witnesses of the recorded normalized comparison systems, so
  the theorem applies to the functors introduced by the two dependency statements.
- The bounded stratified locally finite free cohomology assertion is inherited from
  the `image`, `strata_criterion` and `encoding` fields of the recorded continuous
  realization, after the recorded finite-stage equivalence. Its ambient category is
  `DerivedCategory (pbcModules X.scheme (rationalCoefficientSheaf ...))`.
- `At.tensor` is the natural isomorphism J(P tensor Q) to J(P) tensor J(Q), for all P,Q.
  `At.ambient` is the existing `RingedSiteDualityModel`, so the target is ordinary derived
  tensor with the canonical K-flat total-complex, unit, associator and Koszul symmetry
  normalizations. `At.unit` targets its monoidal unit; `At.coefficientUnit` composes this
  with `ambient.unitIso`, giving exactly E_T[0].
- `At.associativity`, `At.left_unit`, `At.right_unit`, and `At.symmetry` spell out the
  four structural comparison equations. They use the specified source maps and the
  normalized target maps, and express symmetric strong monoidality without introducing
  a second monoidal structure on the raw category.
- On integral representatives, `At.integral_normalization` pins its comparison to the
  existing J_pbc integral comparison after I. `completionMap` extracts the very same
  quotient/Roos augmentation supplied by `constructibleTensorCompletion`, with its zero
  shifted coordinate; `completionIso` inverts it only on constructible pairs, using that
  theorem's IsIso proof. `At.integral_tensor` says tau = ordinary comparison composed
  with coefficient extension of chi inverse, conjugated by the prescribed integral
  comparisons and the literal raw tensor-object equality.
- `ordinaryTensor`, `ordinaryModel`, `completionMap`, and `completionIso` all use one
  existing tensor-completion witness. This is not data chosen from an unspecified
  Nonempty object: signed total tensor and its K-flat localization comparison determine
  the ordinary tensor up to the compatible unique isomorphism; the quotient coordinates
  and zero shifted coordinate determine chi. Its descent is fixed relative to that same
  model. Every use below includes these representative identifications.
- `At.balance_sections` fixes the ordinary integral coefficient-extension comparison on
  actual sheafified generators: s tensor (x tensor y) maps to
  (s tensor x) tensor (1 tensor y). `At.ordinary_normalization` is its derived comparison
  equation, using the universal `integralCounit` and the target K-flat representative
  isomorphism. `At.kflat` is the standard coefficient-extension preservation needed to
  type precisely this computation, not a new input assumption. The unit is forced by
  the two unit coherence equations with these normalized tensor maps.
- `At.fractions` states the full localization coefficient equation for every localized
  scalar a, hence in particular f/varpi^n maps to J(f)/varpi^n. The specified source
  tensor is already bilinear on fractions by `rationalDerivedTensor_existsUnique`.
- `System.stage` supplies one comparison for every finite field. `System.fieldChange`
  supplies its compatibility for every E ≤ F. `FieldChange.comparison_normalization`
  fixes the comparison to inverse I-scalar beta, the integral-normalized PBC transition
  comparison, and the existing J_pbc scalar comparison. Thus it retains their identity and three-field
  associator coherence, instead of choosing an unrelated comparison for each extension.
- `fieldMap` is the continuous, section-normalized coefficient map already supplied
  by R; `fieldExtend` is its actual `pbcDerivedExtend`, namely F_T tensor^L_(E_T) -.
  `rawScalar` is the existing completed-integral raw scalar extension.
  `FieldChange.tensor_compatibility` and `unit_compatibility` are exactly the tensor and
  unit squares. The ambient scalar tensor map is pinned by `balance_sections` and
  `ordinary_normalization`; its unit is pinned by `unit_sections` (s tensor a maps to
  s phi(a)) and `unit_normalization` using the actual cochain counit. No quotient map
  is assumed flat and the uniformizers in E and F are not identified.

Recorded dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the publicly imported valuation rings,
  uniformizers and positive quotients from `CoefficientExtension`.
- The scheme-morphism-properties node is explicitly a convention: the actual Mathlib
  `Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` are used.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `ProEt.topology` (the small weakly-etale site, Hom universe u).
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`,
  `sfRationalCoefficientEquiv` (raw localization, unchanged objects).
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralTensor`,
  `rationalDerivedTensor`, `rationalDerivedTensor_existsUnique`,
  `rationalTensorScalarComparison`.
- `Sheaf.Paper.RationalCoefficientCategoryComparison`:
  `rationalCoefficientCategoryComparison`, using its `FdCoefficientComparisonSystem`
  witness and `FdRationalStageComparison`/`FdCoefficientComparison` fields from their
  defining modules. The full signatures and normalizations of these structures were read.
- `Sheaf.Paper.ContinuousRationalDerivedRealization`:
  `ContinuousRational.continuous_rational_derived_realization`, `Base`, `At`, `Family`,
  `FieldChange`; their integral, fraction, image and scalar normalization fields are used.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent `SheafOfModules` specialization used by the module categories.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- Additional already-landed statement dependencies added to the item:
  `lem-pur-derived-pullback-tensor-iso` (`Sheaf.Paper.DerivedPullbackTensorIso`), supplying
  the completed/rational unit, structural maps and scalar-unit map; and
  `lem-fix-constructible-tensor-completion` (`Sheaf.SixFunctors.ConstructibleTensorCompletion`),
  supplying the actual ordinary tensor presentation and quotient-map augmentation.
  The additional canonical scalar-transition comparison and dependency-interface repairs are described below.

Edge cases checked by reading the actual binders and equations: the empty scheme has
bottom dimension and satisfies the geometric assumptions; zero objects and arbitrary
bounded intervals are not excluded; all cochain degrees are integers, including negative
ones (the target symmetry carries the Koszul sign); finite coefficient levels use n+1
through the recorded constructions, avoiding a spurious n=0 positive-level condition;
equal fields/reflexive inclusions occur in `System.fieldChange`; ramified extensions use
the actual normalized coefficient map and never identify uniformizers or require flatness
of finite quotient coefficient maps. Tensor comparisons are natural in arbitrary localized
arrows, not only integral arrows. No node statement is disputed or corrected.

Searches made before writing:

- `msearch.py ... leanfinder "Continuous rational realization of constructible adic sheaves
  preserves completed derived tensor and is symmetric strong monoidal"`: eight hits,
  chiefly the LightCondensed monoidal structures and ordinary AdicCompletion; no match.
- `msearch.py ... loogle "CategoryTheory.Functor.CoreMonoidal,
  CategoryTheory.Functor.Monoidal"`: three generic monoidal-functor transport declarations,
  none specifying this completed-to-continuous realization.
- `msearch.py ... leansearch "Continuous rational coefficient realization of completed
  constructible proetale derived categories is symmetric strong monoidal"`: eight generic
  symmetric-category/monoidal functor hits, no realization comparison.
- `msearch.py ... grep "rational.*realization.*tensor|realization.*monoidal"
  CategoryTheory`: zero Mathlib hits.
- `rg` in the source checkout `WeilConjectures` and in `lean/Sheaf` for
  `rational.*[Mm]onoidal|[Mm]onoidal.*[Rr]ational|rationalTensorUnit|completedTensorUnit|
  integralTensorUnit|integral.*[Aa]ssociator|rational.*[Aa]ssociator|rational.*[Ss]ymmetry`:
  found scalar associators, lisse-only monoidality and the published structural maps
  subsequently reused. There was no matching realization theorem.
- The prescribed item-id search in the source checkout returned no declaration.
  `tools/blueprint_refs.py ancestor` identifies the ancestor as
  `prop-zl-smooth-proper-relative-purity`; the additional scalar comparison and
  existing-model definition nodes are documented below.
- Read BS 6.8.14(2) and 6.8.15 directly from the provided PDF using pdftotext.
  Read the complete node proof and the source/docstrings of the recorded interfaces,
  including the scalar StageSystem interface through `scompile.py --source` where
  the older local upstream checkout lacked its module.

Validation: the prescribed dry run and individual compiles are being repaired
against current published sources; final results are recorded below.

## Second reading by Q20

This is a second pass by the same worker; the dispatcher forbids starting other agents,
and the maintainer performs the independent review after delivery. I reopened the node
and reread the file clause by clause. The prime, finite field, geometric hypotheses and
actual raw categories match the hypothesis mapping above. The composite functor has the
correct order I then J_pbc. The tensor comparison has direction J(P tensor Q) to
J(P) tensor J(Q). The integral square uses chi inverse, as required by the node's formula.
The associativity, left unit, right unit and symmetry equations compare the same fixed
structural maps as the node. The scalar square uses the inverse I-beta, the canonical normalized-to-embedding PBC comparison and the forward
continuous scalar comparison; both its tensor and unit equations have matching endpoints.
The field unit normalization is actual scalar multiplication, and the main coefficient-unit
comparison lands in the actual coefficient complex via ambient.unitIso.

The second pass checked that the ordinary comparisons are fixed by the explicit balanced
cochain map and universal derived counits, not just asserted to exist; these normalization
fields were added during drafting. It also added the public `At.coefficientUnit` composite
so the node's displayed E_T[0] target is directly accessible. The auxiliary Noetherian,
dimension, invertibility and qcqs binders are exactly consequences of the stated geometry.
No extra mathematical condition, discarded case, weakened clause, duplicate raw category,
or replacement of continuous coefficients was found. The report records the lack of an
independent worker reading honestly; the independent delivery review remains required.


## Dependency modules

The saved semilinear dependency repair is already in the current published
`Sheaf.Paper.SemilinearSystemModels`: the generic successor-universe sheafification
instance is disabled there. The current module also has two additional legitimate
imports. Its stale sandbox copy and node record were removed, and the delivery now
uses that current published dependency without modification.

The compiler caught an important identity-index interface detail during drafting:
the PBC StageSystem uses a literally normalized identity transition, whereas the
continuous realization compares the raw scalar tensor. The field normalization
therefore explicitly inserts `pbcFiniteRawScalarComparison.hom` after inverse I-beta.
This retains the prescribed coefficient-multiplication identity comparison when
E = F, rather than treating the two functors as definitionally identical.


The published `lem-fix-constructible-tensor-completion` retains Q36's record and all
8 original declarations, including `constructibleTensorTotal` and
`constructibleTensorTotalSection`. This delivery no longer contains a replacement
node record or completion-facade module. The three presentation helpers now belong
to the item module and its `lean.declarations`: `ConstructibleTensorCompletionNormalized`,
`ConstructibleTensorCompletionPresentation`, and `constructibleTensorCompletionPresentation`.
They package exactly the four clauses of the original existential theorem for efficient
projection. Their source and blueprint docstrings identify the item; the repackaging
theorem remains postponed with its complete proof docstring. The main module imports
`Sheaf.SixFunctors.ConstructibleTensorCompletion` directly and uses its original totals.

## New nodes

`def-zl-pbc-finite-raw-scalar-comparison` defines the unique natural comparison
between the normalized PBC StageSystem transition and the embedding scalar functor
used by continuous realization, on the same canonical small coefficient fields.
Its integral component is precisely `pbcScalarIntegralComparison`, expressed with
HEq to retain the equality of the two quotient-normalized coefficient maps and
integral tensor objects. This fixes all components since every raw object is Q(K).
Its equal-field case is the specified coefficient-multiplication unit. The module
contains its existence/uniqueness theorem with a full source-based proof docstring,
then the definition choosing that unique comparison. This is the missing bridge
between two existing scalar constructions, not a new scalar functor. The source
is BS 6.8.14(2), 6.8.15 and ordinary extension/localization in Stacks 03EK/0D6D.

Searches for this additional node: LeanFinder returned eight integral-norm and
integral-closure localization hits; LeanSearch returned eight ordinary linear-map
localization equivalences; neither provides the bridge. Mathlib CategoryTheory
grep for `pbcScalarExtension|pbcRationalScalarExtension` returned zero hits. Project
source and DAG searches found the two separate constructions and their integral
comparisons, with no connecting declaration. Blueprint search for scalar extension
returned 69 nodes and no such bridge. The invalid-name Loogle search is recorded
verbatim in the new node alongside these successful searches. The new node's
statement dependencies cite exactly the three construction nodes it uses.

`def-zl-ringed-site-duality-model` records the existing definitions
`CategoryTheory.RingedSiteDualityModel`, `ringedSiteDualityUnitComplex`, and
`ringedSiteDualityUnit` in `Sheaf.CategoryTheory.RingedSiteDualityMaps`, with
`existing: true`. It makes no existence claim: the item quantifies over the
normalized model and does not call `ringedSiteDualityMaps_exists`. The data include
the existing closed tensor-Hom representative model, coefficient unit and K-flatness,
Koszul interchange, scalar right unitor, and reassociation on representatives.
The object, morphism, coefficient and derived-category universes remain independent.
The source is Stacks 06YN/08JD/0A97/0A98 and the published definition's docstring.
LeanFinder and LeanSearch each returned eight generic underived/flat/condensed
results; Mathlib grep found no names, and source/DAG/side-library searches identify
these existing definitions, previously listed only under a theorem node. No module
or declaration is duplicated. The item cites this definition node instead of the
existence theorem. `lem-pur-kflat-total-tensor-model` and its unused import were removed.

## Resumed packet self-check (Q20, 2026-10-18)

The resuming worker retained the saved four-module packet and began with the
prescribed dry run. With the item and all four delivered modules open, the
self-check matched the composite I then J_pbc, tensor and coefficient-unit
comparisons, associativity, both unitors, signed symmetry, integral quotient-map
normalization, localized-arrow formula, and finite-extension tensor/unit squares.
The normalized identity-field transition is explicitly bridged to raw scalar
tensor; it is not silently identified with it. The completion presentation retains
all four clauses of the original existential interface. The semilinear module
diff changes only instance selection, preserving all signatures and constructions.
No further mathematical or Lean-source change was needed during this self-check.
The existing search record is retained; validation results follow once returned.


## Resumed compile repair audit

The saved extra `DerivedPullbackTensorHom` overlay differed from its published
source only by six elaboration/compiler options. It did not repair a mathematical
interface, and changing it forced recompilation of its entire consumer closure.
The resumed worker tested the options and residue-field transparency; the module
still timed out. The unnecessary overlay and its lean-only node copy have therefore
been withdrawn from this delivery. The item uses the published dependency unchanged,
retaining all canonical operations, common-stage comparisons and hypotheses.
Validation below records the outcome for the original four-module packet.

## Final resumed self-check (2026-10-18)

The retained packet now contains three Lean modules. The prescribed first dry run
passed preflight and all three per-file compiles, producing dry-run commit
`d928071ed9` without pushing. I read the complete main module and both auxiliary
modules against the item and auxiliary node records. The tensor direction, actual
continuous coefficient unit, four monoidal equations, completed-integral comparison,
fraction formula, and finite-field tensor/unit squares agree with the node. The
completion facade retains all four clauses of the published existential statement.
The scalar bridge retains integral normalization and the equal-field case. No Lean
source change was needed. Only delivery dates and this validation entry were updated.
The final delivery command rechecks the resulting packet before pushing.

## Returned delivery repair (2026-10-19)

1. Retained Q36's original completion record unchanged by withdrawing the sandbox
   dependency node copy. Moved all three completion-presentation helpers into the
   item module and listed them under the item's declarations. Removed the separate
   facade module. Original total-tensor declarations remain owned by Q36's node.
2. Added `def-zl-ringed-site-duality-model` with `existing: true`, owning the
   published model and coefficient-unit definitions used by this statement. Replaced
   the theorem statement dependency `lem-sfb-ringed-site-duality-maps` by this node.
3. Removed the unused `lem-pur-kflat-total-tensor-model` statement dependency and
   `Sheaf.Algebra.Homology.KFlatTotalTensorModel` import. Retained the genuinely used
   `lem-pur-derived-pullback-tensor-iso` and `lem-fix-constructible-tensor-completion`.

Second reading of this repair: reopened both final modules and all three delivered
node records. Helper relocation preserves their four normalization clauses exactly;
completionData still selects the same presentation specification. The new definition
node records the full existing structure, including independent universes and all
three representative equations; it does not assume the existence theorem. Every
geometric hypothesis and tensor/unit/coherence/integral/fraction/extension clause of
the main statement is unchanged. Empty schemes, zero complexes, all integer degrees,
ramification and reflexive coefficient inclusions remain covered. No statement change
or dispute is introduced. Historical validation entries above concern prior packets;
validation of this returned-delivery repair is recorded below.

Repair validation: `scompile.py` compiled both delivered modules separately,
with no diagnostics: scalar bridge 3.7 seconds, main module 46.7 seconds
(the sandbox pass was 46.4 seconds). The repaired-packet dry run returned
`OK (dry run): commit df2e88d216 passes the preflight and compiles; nothing pushed`.
Its staged list contains the item node, two definition nodes, two Lean modules,
and this report. It contains no completion dependency override or facade module.
The existing-model record was also checked by the prescribed wrapper.
