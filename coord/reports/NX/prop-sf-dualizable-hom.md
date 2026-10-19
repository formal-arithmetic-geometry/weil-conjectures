## Worker report

The module `Sheaf.Paper.SitePerfectDualizableHom` states
`WeilConjectures.sixFunctor_sitePerfect_dualEvaluation_isIso`, with one `sorry`.
Its four conjuncts state exactly the four allowed coefficient choices. The item
statement, dependencies, and proof plan are unchanged. The theorem docstring
reproduces all fourteen proof steps and their cited nodes.

Hypothesis and clause correspondence:

- Distinct primes p and ell, a >= 1, q = p^a, k0 = F_q, and k its algebraic
  closure: `D : FiniteFieldDatum` supplies these fields and their properties;
  `C : D.CoefficientDatum` supplies ell, its primality and `C.different`.
- E/Q_ell a finite extension: `E : Type u`, `[Field E]`,
  `[Algebra (Padic C.l) E]`, `[FiniteDimensional (Padic C.l) E]`.
  The coefficient ring, valuation ring and uniformizer are the recorded
  `Padic.coefficientExtensionRing`, `Padic.coefficientExtensionIntegers`, and
  `Padic.coefficientExtensionUniformizer` used by the dependency categories.
- n >= 1: the Lean natural index is n and the actual exponent is n+1;
  `Nat.succ_pos n` supplies positivity and includes exponent one.
- Fix a six-functor datum: `S : SixFunctorDatum D C E (n+1) ...`.
  The four closed presentations are `S.finiteClosed X`, `S.integralClosed X`,
  `S.rationalClosed X`, and `S.commonClosed X`. They use the recorded internal
  Homs and the datum's evaluation-normalized coefficient models and comparisons.
- X a separated finite-type k-scheme: `X : SixFunctorSpace D` gives the
  over-Spec(k) structure, locally finite type and quasi-compact structure morphism;
  `[IsSeparated X.obj.hom]` supplies separatedness. No properness or smoothness
  is imposed.
- K and M in D^b_ctf: the finite and integral quantifiers use the exact
  `S.toSixFunctorOperationDatum.finiteTorDomain X` and
  `.integralFiniteTorDomain X` full subcategories. Their nested `.obj.obj`
  forgets bounded constructibility and then finite Tor, without changing the
  derived object. At the two field stages the domain is top on the recorded
  constructible category, since finite Tor is the entire field category.
- K locally represented by a bounded complex of finite projectives:
  finite uses `IsFiniteCoefficientSitePerfect C.l E X.obj.left n K.obj.obj`;
  integral uses `IsIntegralCoefficientSitePerfect ... K.obj.obj`;
  rational uses `IsSfRationalCoefficientSitePerfect ... K.obj`;
  common-stage uses `IsGeneralAlgebraicallyClosedCoefficientSitePerfect ... K.obj`.
  These retain an actual site covering, local degree bounds, finite-free
  retractions, and rational retractions only after localization. The common-stage
  condition is existence of a site-perfect finite-field representative up to
  isomorphism, rather than requiring the literal stored representative to be perfect.
- Lambda_X and K^vee = RHom(K,Lambda_X): in each clause Lambda_X is that
  closed domain's `closed.monoidal.tensorUnit`. The evaluation-normalized closed
  structure uses `sixFunctorDomainHom`, the restriction of the recorded Hom.
  Thus `H.obj (op K, tensorUnit)` in the canonical comparison is precisely K^vee.
  `Iso.refl _` identifies this coefficient unit with itself, with no arbitrary map.
- The canonical evaluation comparison, with source K^vee tensor M and target
  RHom(K,M), is the existing `CategoryTheory.ringedSiteDualEvaluationLeft`.
  Its definition is signed symmetry followed by the transpose of evaluation,
  the associator and the coefficient unitor. The conclusion is `IsIso` of
  this particular morphism. It does not assert merely existence of an isomorphism.
- Every M is quantified in each respective category, with no perfectness or
  projectivity assumption on M and no chosen representative of M.

Dependency declarations used:

- `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`,
  `SixFunctorClosedDomain`, `sixFunctorDomainHom`; the four closed fields and
  their normalized finite/integral models and coefficient comparisons.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the actual finite, integral, rational
  and common-stage internal Homs, used by those four closed-domain fields.
  Read the primary recorded `commonStageDerivedInternalHom_existsUnique`
  declaration and its complete representative-map signature and docstring.
- `Sheaf.Paper.SitePerfectComplex`: the three existing predicates listed above
  and the appended common-stage predicate described below.
- `Sheaf.CategoryTheory.RingedSiteDualityMaps` (visible through SixFunctorDatum):
  `CategoryTheory.ringedSiteDualEvaluationLeft` and its full defining formula.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `GeneralAlgebraicallyClosedCoefficients.Stage` and `.inclusion` for the
  common-stage perfectness predicate, using the actual recorded pair category.

Every recorded proof-dependency module is imported without `public`; the three
statement dependency modules are public imports. Mathlib leaves are imported
from their recorded modules. No new proof dependency was invented.

Edge cases checked before stating: exponent one is n=0; zero K and zero M are
allowed, including rank-zero local terms and empty bounded complexes; the empty
scheme and empty covering sieves are not excluded; local bounds and local ranks
need not be globally constant. Rational finite-free splittings may exist only
after inverting the uniformizer. A common-stage representative can be over any
finite subextension and need only be isomorphic to K. No equality between site
object and morphism universes is imposed: the existing small pro-etale site
retains object size u+1 and morphism size u, with coefficients in u+1.
No statement correction or disputed mathematical assertion was needed.

Searches actually run (wrapper search results are in the sandbox search log):

- LeanFinder, `For a complex locally isomorphic to a bounded complex of finite
  projective coefficient sheaves, its coefficient dual tensor M is canonically
  isomorphic to derived internal Hom into M`: eight hits in LightCondensed,
  sheaf cohomology, and the Grothendieck category tensor construction;
  none states this theorem.
- Loogle, `CategoryTheory.IsDualizable, CategoryTheory.ihom`: unknown identifier
  CategoryTheory.IsDualizable; no usable match (it is an upstream extension,
  not a declaration in the searched Mathlib).
- LeanSearch, `perfect complex sheaf dual tensor derived internal Hom`: eight
  hits including `CategoryTheory.ihom.adjunction`,
  `CategoryTheory.MonoidalClosed.internalHomAdjunction₂`, `dualTensorHomEquiv`,
  and `CategoryTheory.tensorRightHomEquiv`; none gives site-perfect derived
  evaluation on these four coefficient categories.
- Wrapper grep, `dualTensorHom|ihomObjIsoTensor|IsPerfectOnRingedSite`,
  subdirectory CategoryTheory: zero hits.
- Direct rg of Mathlib CategoryTheory/Monoidal for `DualEvaluationLeft` and
  perfect evaluation: no match. Direct rg of upstream and Sheaf for dualizable,
  dual tensor and evaluation comparisons found the owning canonical map in
  RingedSiteDualityMaps and the related general-site RingedSitePerfectDuality.
- Upstream node-id search found
  `WeilConjectures/SixFunctors/Etale/Derived/Perfect.lean` and its `Dual.lean`.
  Read `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_tensor`:
  its hypothesis is IsDualizable in a generic etale coefficient category and
  its conclusion is Nonempty of an iso. Its module explicitly explains that
  it does not state site-perfectness or the specified canonical map; it cannot
  serve as an existing exact match for this item.
- rg in upstream, Sheaf and dag/lean_names_upstream.json for both delivered
  declaration names found no existing declaration. The dependency's recorded
  common-stage predicate was read in full and takes the legacy pair category;
  the datum's `commonClosed` takes the general pair category instead.

## Dependency modules

`def-weil-site-perfect-complex`: ownership-preserving section 1(B) extension of
`Sheaf.Paper.SitePerfectComplex`. The recorded
`IsAlgebraicallyClosedCoefficientSitePerfect` has domain
`algebraicallyClosedConstructibleCategory`, while the datum has
`generalAlgebraicallyClosedConstructibleCategory`. Add
`IsGeneralAlgebraicallyClosedCoefficientSitePerfect` to the same owning module:
it says there exist a finite coefficient field E and a rational object P with
`IsSfRationalCoefficientSitePerfect` and `Nonempty (K ≅ inclusion.obj P)`.
This is the dependency node's algebraically closed clause verbatim in the actual
category, preserving rational-only finite-free retractions. All existing
imports, declarations, signatures and bodies are retained; only one public
import and this final definition are appended. The node delta is lean-only,
retaining its primary declaration, statement, file and all previous declarations,
and adding the new declaration and an explanatory note. No new node is needed.

## Second reading by NX

Performed a separate in-thread rereading of the node and both completed modules;
no other agent was started, as required by the worker brief. The maintainer's
independent reading remains the external review. Matched the four coefficient
choices to the four conjuncts, and checked that positive exponent indexing does
not lose level one. Read the nested full-subcategory carriers against finite Tor
and bounded constructibility. Checked the two field domains are top, that the
rational perfectness hypothesis uses the intrinsic predicate, and that the
common-stage condition quantifies some representative up to iso. Opened the
canonical map definition: source order is dual tensor M, codomain is Hom(K,M),
and it is the signed evaluation transpose. No dualizability hypothesis has been
substituted for local perfectness. The dependency extension retains all old
bodies and states the same existential common-stage notion on its new domain.
No mismatch requiring a change to the mathematical statement was found.

Compilation repair: the appended common-stage predicate uses scoped backward
elaboration compatibility settings to avoid unfolding the large stage-system
choice while identifying its rational carrier. No old declaration body changes.

Validation: prescribed scompile.py checked both files individually in dependency
order against the live published build, with no errors or warnings. The dependency
compiled in 37.5 s, the theorem sandbox in 52.8 s, and its library-path check in
15.1 s, all under the fixed 60-second limit. The main module uses the same
backward elaboration transparency settings as SixFunctorDatum.
