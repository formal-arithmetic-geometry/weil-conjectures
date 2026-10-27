## Worker report

The module `Sheaf.Paper.TraceCorrespondences` defines the complete correspondence
and supported-class data of sk-d-corr. It contains definitions with real data and
no postponed theorem or `sorry`. The item's mathematical statement is unchanged.

Hypothesis and clause correspondence:

- The finite-field base is `F : FiniteFieldDatum.{u}` and the base scheme is
  `Spec (.of F.k)`. The prime, characteristic inequality and finite extension are
  the explicit binders `l`, `[Fact l.Prime]`, `hl : l ≠ F.p`, `E`, `[Field E]`,
  `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`. Level `n + 1`
  covers exactly all positive finite coefficient levels, including level one.
  The coefficient ring is `Padic.coefficientExtensionRing l E (n + 1)`.
- `X`, `Y`, and the support `C` are objects of `Over (Spec (.of F.k))`.
  Thus their structure maps and the two commutation equations are retained,
  not merely an assertion that such maps exist. The ambient categories and
  objects `K`, `L` are the recorded `Scheme.proEtaleDerivedCategory`.
- `TraceCorrespondence.c₁ : C ⟶ Y` and `.c₂ : C ⟶ X` are maps over the base.
  `compactification : Compactification c₁.left` realizes compactifiability by
  its specified open/proper factorization, as in proof step 1.
- `TraceCorrespondenceAdjunction` takes the actual support functor
  `sfIntrinsicCompactSupport` of this compactification. Its `preserves`
  field types its restriction to the supplied full source and target domains;
  `right` and `adjunction` give the supplied right adjoint, unit, counit and
  triangles on exactly those domains. This permits the whole ambient category
  by using the top object property, without requiring it. `target_mem` and
  `pull_mem` state that these domains contain the displayed objects.
- `.u` is the ordinary ambient Hom from
  `(finiteDerivedPullback l E n c₂.left).obj K` to
  `(exceptional.right.obj ⟨L, target_mem⟩).obj`. Ordinary pullback is leg 2.
  There is no constructibility condition on a general correspondence.
- `.product X Y` is `pullback Y.hom X.hom`, with projections the recorded
  `pullback.fst` and `pullback.snd`. `.support` is their universal lift of
  `(c₁.left,c₂.left)`, using `c₁.w.trans c₂.w.symm`. The standard
  `pullback.lift_fst` and `pullback.lift_snd` give precisely p1 c = c1 and
  p2 c = c2. No independent support map is chosen.
- `.exchange` is `pullbackSymmetry X.hom Y.hom`, retaining its inverse.
  `.oppositeSupport d` is `d.support` followed by this exchange; the opposite
  correspondence has the same type with `(X,K)` and `(Y,L)` interchanged.
- `.intersection c d` is `pullback c.support d.oppositeSupport`.
  `.intersectionFst`, `.intersectionSnd`, `.intersectionBase` retain both
  projections and the structure map `e_C ≫ a_C`. Its alternative expression
  through `e_D` agrees by the pullback condition and the equations over s.
- For an endocorrespondence, `.fixed` is literally
  `pullback c.support (pullback.diagonal X.hom)`. `.fixedInclusion`,
  `.fixedProjection`, `.fixedBase` retain both fixed-square maps and the
  structure map. The pullback of the diagonal represents the equalizer of
  the two legs even for nonseparated X: a test map t with equal legs lifts
  using the pair (t,t ≫ c1), uniquely by pullback extensionality.
- `TraceSupportedClass cs P` is exactly the ordinary ambient Hom from
  `(sfIntrinsicCompactSupport cs A).obj A_T` to `P`; `A_T` is
  `(finiteIntrinsicClosed l E T n).monoidal.tensorUnit`. It works for any
  compactifiable specified i, without an immersion condition or a right
  adjoint to i!. It retains the compactification giving the supplied i!.
- The final identification has K and L in the actual full categories
  `TraceClassOperations.Category`, built from the existing
  `finiteTorConstructible` predicate. `TraceClassOperations.Data` records
  compactifications of c, p1, and c p1, their supplied exceptional
  adjunctions on those full categories, and the supplied composition and
  unit-specialized projection comparisons. `ordinary_mem`, `pull_mem` and
  the preservation fields type the displayed operations on those domains,
  as required by the node's explicit operation-domain proviso. The projection
  field is the projection formula followed by the unit isomorphism; it is
  precisely the comparison supplied by the geometric operations, not a
  substitute arbitrary coefficient map or an assumed Hom equivalence.
- `TraceClassOperations.homEquivalence` constructs, rather than assumes, the
  displayed equivalence. It uncurries the existing closed adjunction,
  precomposes with projection plus the unit, uses the fully faithful
  inclusions and the exceptional Hom equivalence, and conjugates by ordinary
  pullback composition and the unique composite right-adjoint comparison.
  Its statement computes both Hom sets in the ordinary ambient categories.
  For the node instantiate Z as `.product X Y`, p1 and p2 as its projections,
  and c as `.support`; their leg equations identify the two composites with
  the original legs. No constructibility of the internal Hom is assumed.
- `TraceClassOperations.supportedClass` uses `.symm` of that very equivalence.
  Its `agreement` is the stipulated agreement at L with the adjoint used in u.
  Equality of objects is the special case `eqToIso`; allowing the canonical
  isomorphism permits the equivalent full-subcategory presentations. Thus
  applying the forward equivalence recovers the coefficient map, and every
  class is recovered by its inverse, by `Equiv.apply_symm_apply` and
  `Equiv.symm_apply_apply` already in Mathlib. No extra supported-class field
  is added to the correspondence.
- `TraceCorrespondenceClass` also provides the specialization directly from
  `GeometricOperations`, so geometric comparison data need not be resupplied.
  `unitCtf` pulls back the base unit, uses the given monoidal-unit comparison,
  and transports membership by repleteness from `TraceFormulaCoefficientSetup`.
  `projectionUnit` is the package's actual projection formula at that unit
  followed by the actual left unitor. `homEquivalence` composes the same
  canonical steps using `O.comparisons.exceptionalComp` and `pullComp`.
  Its `supportedClass` again takes the inverse image, retaining agreement
  at L. This geometric form is a specialization, not a geometric restriction
  on the general definitions above.

Dependencies read and used:

- sk-d-setup: `Sheaf.Paper.TraceFormulaCoefficientSetup`,
  `WeilConjectures.TraceFormulaCoefficientSetup`; its existing ambient category
  and `finiteTorConstructible` are reused, including arbitrary schemes.
- sk-d-six: `Sheaf.Paper.GeometricOperations`,
  `WeilConjectures.GeometricOperations`; full comparison-data signatures and
  coherence read, including `GeometricOperationPackage.pullComp`, `pullCtf`,
  `support`, `supportCtf`, `exceptionalCtf`, `closed`, and
  `Comparisons.exceptionalComp`. No second operation package is introduced.
- def-weil-scheme-over-base: `Mathlib.AlgebraicGeometry.Over`,
  `Scheme.Over` and `Scheme.Hom.IsOver`, in their equivalent bundled
  `CategoryTheory.Over` form.
- def-pc-fibre-product: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift` and
  `pullback.diagonal`, with schemes' existing pullbacks.
- def-nagata-compactifiable: `WeilConjectures.Compactification.Defs`,
  `AlgebraicGeometry.HasCompactification` and the actual `Compactification`
  whose nonemptiness it asserts. No new compactifiability notion is made.
- def-sfb-derived-tensor-hom-adjunction-sheaves:
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom`,
  `AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction₂` and the fixed-parameter
  `derivedTensorHomAdjunction`. The intrinsic module-over-constant-ring
  coordinates of the supplied geometric package use its already recorded
  `CoefficientClosedStructure.transpose`, with the same tensor--Hom adjunction.
  This is reuse of the package's existing intrinsic operations, not another
  definition of derived tensor or Hom in this delivery.
- Proof imports retained: `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
  and `Sheaf.Paper.IntegralFinitePullbackComposition`, the recorded declarations
  `finiteCoefficientInverseImageMap_isIso` and
  `integralTowerGeneralPullbackComposition`. The given package's `pullComp`
  uses the canonical intrinsic realization of this composition, whose defining
  formula was read. `Adjunction.comp` and `Adjunction.rightAdjointUniq` are used
  directly for the exceptional comparison, as required by the proof nodes.

Edge cases checked before writing: empty schemes and empty intersections remain
allowed; no nonemptiness is imposed. Zero K or L and zero coefficient morphisms
are valid. For X=Y=C=s and identity legs the construction reduces by the unit,
projection and adjunction identifications to Hom(A,RHom(K,L)) equivalent to
Hom(K,L). Nonseparated and non-finite-type schemes are allowed by all general
correspondence, intersection, fixed and supported-class definitions; only the
explicit specialization using the geometric package uses geometric schemes.
No properness of the ordinary leg or immersion assumption on a support is added.
All scheme universes are u; the coefficient categories keep the existing pro-etale
object/morphism universe convention. Level n+1 includes every positive n of the
node without permitting its excluded level zero.

Searches (recorded by the prescribed msearch wrapper in searches.jsonl):

- leanfinder, "cohomological correspondence supported class schemes exceptional
  pullback": 8 unrelated derived T-structure hits, no correspondence definition.
- loogle, "SupportedClass, Correspondence, Adjunction.homEquiv": 0 hits,
  unknown identifier SupportedClass.
- grep, "SupportedClass|classEquiv|CohomologicalCorrespondence": 7 unrelated
  homotopy-class equivalence hits, no match.
- leansearch, "Cohomological correspondences finite coefficients supported classes
  exceptional adjunction": 8 unrelated locally constant/representation adjunctions.
- rg in project `WeilConjectures/` and `Sheaf/`, by Correspondence, SupportedClass,
  classEquiv and sk-d-corr: the upstream `TraceFormula.Correspondence` and
  `CorrespondencePair` use condensed rational algebraic-closure coefficients
  and separated finite-type supports, hence do not state this finite-coefficient
  arbitrary-scheme definition. `TrfCohomologicalCorrespondence` also restricts
  to geometric finite-Tor endocorrespondences with its fixed-scalar exceptional
  functor. `PurityFiniteSetting` supported classes use ordinary-etale purity
  settings or closed supports. Their full signatures and relevant docstrings
  were read; none is an exact match. The withdrawn CompactObject example and
  its current upstream attachment were read as instructed.

No new DAG node, dependency repair or statement correction is needed. No
STATEMENT-DISPUTED issue remains beyond the node's already reviewed explicit
functor-domain provisos; the delivery preserves them.

## Second reading by Q11

Clause-by-clause self-check against the node and current blueprint is recorded
above. This dispatcher brief prohibits starting another agent and specifies the
maintainer's independent delivery review; no independent worker is claimed here.
During the check the initial geometric-only Hom equivalence was supplemented by
`TraceClassOperations` on arbitrary schemes with the stipulated full-domain
operations. Both ambient Hom sets, factor order, ordinary leg 2, and the inverse
orientation of the exceptional compositor were checked explicitly. The support
unit membership and the projection comparison in the geometric form are derived
from the recorded operation data, not added as user assumptions. No theorem is
proved and every definition has actual data.
