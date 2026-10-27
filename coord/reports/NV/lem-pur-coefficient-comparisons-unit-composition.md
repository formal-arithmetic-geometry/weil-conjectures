## Worker report

The module Sheaf.SecSmoothPurity.CoefficientComparisonsUnitComposition states
CategoryTheory.CochainPullback.StrictCoefficient.coefficientComparisonsUnitComposition.
Its only postponed proof is this named theorem. Five real helper definitions collect
multiplication formulas, forward/inverse transition squares, and the composite square
transport. No statement correction, dependency repair, or statement dispute is needed.
The previous worker's stage-1 blocker does not apply: the current node has no Lean
record, and coord/brief-stage2.md section 0 explicitly permits this stage handoff.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The two small sites are C, D with independent object and morphism universes uC,
  vC, uD, vD, topologies J, K, and EssentiallySmall.{w}. The latter allows the usual
  small-site transport; no equality of site universes is imposed. HasSheafCompose
  forgets the commutative-ring structure and is available on these small sites.
- The geometric morphism and its left-exact inverse image are d.inverse, d.direct,
  d.adj and d.finiteLimits in the existing Diagram. Its algebraic and graph fields
  identify the actual inverse-image ring and module operations for every arrow.
- The inverse sequences and coefficient rows are d.R and d.S on
  Index = Fin 3 × ℕᵒᵖ. R denotes the Y row and S the X row. Functor identity and
  composition encode i^{aa}=1 and i^{02}=i^{12}i^{01}. Natural transformation d.phi
  and the graph equation encode both the coefficient and sequence squares.
- F is pull (d.ringed i). Diagram.hobj and hmap make its module functor the actual
  sheafified scalar tensor after algebraic inverse image, rather than an arbitrary
  functor. Its module adjunction and additivity are presentation data available
  for every such ringed pullback (ringedPullbackPresentation_exists). The auxiliary
  k supplies the already existing canonical module comparison/generator interface;
  it adds no flatness or geometric restriction.
- S^{ab} is extend (B.map a). Its objects are SheafOfModules.changeOfRings and its
  maps changeOfRingsHom. The scalar-first convention is extensionTmul.
- T is the existing total P Q = P ⊗ Q on Complex R = CochainComplex (Modules R) ℤ.
  It is precisely CochainComplex.mapBifunctor with the sheaf tensor. Its differential
  has the signed second term and its terms are arbitrary coproducts over p+q=n.
- The given natural isomorphisms are e.kappa, e.sigmaR, e.sigmaS in Comparisons.
  Their cochain lifts are e.kappaC, e.sigmaRC, e.sigmaSC. The hypothesis _normalized
  is e.Normalized k: the existing generalized-generator equation IsScalarAssociation
  fixes k and its inverse, including the inverse-image phi factor. Sigma is already
  a Comparison of the actual scalar extension: its generator and contraction
  normalizations are part of that existing definition, in both directions.
- The strictness hypothesis _strict is KappaTransitionLaws and the two
  TensorTransitionLaws. These quantify over arbitrary scalar-extension adjoint
  chain maps f,g; they neither require invertibility nor specify the transition
  to be a scalar-extension unit. Inverse strictness follows by cancelling the
  component isomorphisms, just as in the node's definition of strictness.
- U and A are the existing diagramUnit and diagramComp. These are natural
  isomorphisms obtained by cochain lifting the concrete left-adjoint-uniqueness
  scalar maps, conjugate to identity-on-sections scalar restriction comparisons.
  Thus their data already exists, without a choice from an undetermined existence.
- UnitMultiplication on each site gives U(c tensor x)=c*x and U^{-1}(x)=1 tensor x,
  in every cochain degree and over every object of the site.
- CompositionMultiplication gives A(c tensor (d tensor x))=c*i(d) tensor x and
  A^{-1}(c tensor x)=c tensor (1 tensor x), again in every degree and on both sites.
  The existing extensionTmul is the actual sheafification-unit image of a tensor;
  this does not replace sheaf tensors by tensors of global sections.
- UnitStrictness and CompositionStrictness on both sites state the forward and
  inverse squares for U,A and every semilinear transition. twiceSquareArrow
  transports through the two coefficient squares using the recorded squareArrow.
  The equality witnesses are products of the two thin-factor equalities, not new
  hypotheses. Restricting these universal squares to coefficient arrows at fixed
  sequence levels is the node's strict-system assertion. Quantifying arbitrary
  arrows is a uniform presentation of the same universal coefficient calculation:
  any composable pair of sequence/coefficient arrows supplies three ring rows.
- TensorLaws on d.R and d.S gives exactly T(U,U)s=UT and
  T(A,A)s12 S12(s01)=s02 A_T, as equalities of chain isomorphisms.
- The penultimate conjunct is k^{aa} followed by F_a(U_Y)=U_X F_a.
  The final conjunct is S_X12(k01), k12, F2(A_Y) equal to A_X, k02 in that order.
  Lean uses left-to-right composition, the reverse of the paper's written product.
- In the successive k equation, the normalized generalized generators and the
  displayed CompositionMultiplication formula give exactly
  d*i12(b)*i02(a) tensor (1 tensor x). For s they give
  (d*i12(b) tensor x) tensor (1 tensor y), on each bidegree inclusion. These are
  the same maps in the displayed equations, not separately chosen comparisons.
- All four equations are equalities using ≪≫ of Iso objects, so both forward and
  inverse components are equal. The U/A inverse generator and transition formulas
  are also explicit conjuncts. No inverses of sequence transitions are used.

Dependency declarations read and used:

- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules, exactly
  Mathlib SheafOfModules, with linear natural transformations as morphisms.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  SheafOfModules.cochainModulesMonoidal, cochainModulesSymmetric,
  cochainModulesPreadditive and both colimit-preservation instances, giving the
  actual localization tensor at independent site universes.
- Mathlib.Algebra.Homology.BifunctorShift: CochainComplex.mapBifunctor, its
  HasMapBifunctor requirement, and its bidegree coproduct inclusion.
- Sheaf.SecSmoothPurity.CochainTensorCoherenceData: Modules, Complex,
  RingedPullback, Comparison, pull, comparison; the full presentation signatures
  and the canonical comparison normalizations were read.
- Sheaf.SecSmoothPurity.CochainCoefficientArrows: extensionFunctor,
  extensionTmul, extensionAdjunction, extend, CoefficientSquare,
  IsScalarAssociation and generator; their docstrings and full signatures were read.
- Sheaf.CategoryTheory.SystemScalarCoherence: systemScalarRestrictionUnit and
  systemScalarRestrictionComposition. Their components are the concrete
  identity-on-sections comparisons that fix diagramUnit/diagramComp uniquely.
- The existing definition interface of
  Sheaf.SecSmoothPurity.StrictCoefficientComparisonCalculus: Diagram, Comparisons,
  Normalized, scalarUnit, scalarComp, diagramUnit, diagramComp, squareArrow,
  TensorLaws, TensorTransitionLaws, KappaTransitionLaws and their cochain lifts.
  No use is made of strictCoefficientComparisonCalculus, its downstream theorem.
- Plain proof imports supply SheafOfModules.tensor_bilinear_universal from
  WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal;
  TensorProduct and its universal property from Mathlib.LinearAlgebra.TensorProduct.Basic;
  PresheafOfModules.sheafification from
  Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification;
  existsUnique_bilinear_sheafification_extension from the recorded upstream
  Presheaf.SheafificationBilinearExtension; and tensorClosed from the recorded
  upstream Sheaf.TensorClosed. These import the existing proof plan, with no
  duplicate library-side module. The definitions and theorem docstrings were read.

Edge cases checked before writing: zero modules; zero coefficient rings; repeated
rows and identity coefficient maps; zero semilinear transitions; nonflat coefficient
maps such as Z→Z/2; complexes unbounded in both directions; empty sites; independent
site object/Hom universes. There is no Nontrivial, flatness, boundedness or transition
isomorphism assumption. The differential never swaps the two factors, so scalar
multiplication introduces no Koszul sign. The generator test is sheafified and the
sum test uses coproduct inclusions; neither assumes global lifting of local sections.

Searches: prescribed msearch LeanFinder with query "Normalized strict coefficient
scalar extension comparisons obey multiplication unit and successive composition
laws for sheaf tensor total complexes" returned eight HomologicalComplex tensor
construction hits, no matching theorem. Loogle "ModuleCat.extendScalarsComp,
ModuleCat.extendScalarsId" returned four ordinary module scalar-unit equations.
Grep "extendScalarsComp|extendScalarsId|pullback_assoc" in Algebra/Category/ModuleCat
returned nine ordinary scalar/pullback hits. LeanSearch "Strict inverse sequences of
sheaves of rings and normalized coefficient pullback tensor comparisons with unit and
associator" returned eight ordinary pullback comparison hits. Searches of the exact
item tag, coefficient comparison names and scalarUnit/scalarComp in WeilConjectures
and Sheaf found the existing general strict-calculus interface but no separate theorem
with exactly this conditional unit/composition statement. The downstream calculus
asserts unique existence of comparisons and additional squares, hence is not an
existing declaration of this item. Full outputs for the interface-node searches are
preserved in its mathlib_searches.

Validation: scompile.py compiled the module cleanly, both in the sandbox and under
its intended library name. The first probe found missing scalar-action elaboration
transparency and product-Hom thinness inference. Both were repaired without changing
hypotheses: enable transparency locally for UnitMultiplication, and explicitly combine
the two component Hom equalities with CategoryTheory.Prod.hom_ext. The next probe
caught docstring/option placement and line width; both were repaired. The final
single-file check had no errors or warnings. The required dry-run and delivery follow.

## New nodes

Added def-pur-normalized-coefficient-diagram as an existing:true definition-only
attachment to the already landed Diagram and companion definitions. No Lean
notion is duplicated and no module is written for it. The sources are the diagram
in the item, Stacks 03EK/03EL, and the existing interface. Whole-DAG searches for
StrictCoefficient.Diagram/Comparisons/scalarUnit/scalarComp locate these helper
attachments only in the downstream theorem node, not a definition node for their
interface. tools/blueprint_refs.py search 'strict coefficient' finds no equivalent
blueprint definition. The three prescribed search kinds are recorded verbatim in
mathlib_searches. This node factors the existing *definitions* from the downstream
*existence assertion* at DAG level, so the item has no dependency on its own citer.

The existing source module also contains the downstream theorem, but importing it
here uses only its definition interface, not that theorem as an assumption or proof
input. When the maintainer adds later proof imports, the parent cannot import this
module without a source import cycle; the explicit cycle-omission rule in
stages/2-statements.md section 3(7) applies. This is reported, not concealed by copying
or privately redefining its interface. No dependency node record is changed.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
