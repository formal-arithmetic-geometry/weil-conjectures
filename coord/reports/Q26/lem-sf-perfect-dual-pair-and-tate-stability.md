## Worker report

The module `Sheaf.Paper.PerfectDualPairAndTateStability` states
`WeilConjectures.sfPerfectDualPairAndTateStability`, with `sorry` as its entire
proof. Its other declarations are transparent constructions or propositions
expanding clauses of this same node. No definition contains postponed data or
an inline postponed proof. The node changes only in `lean`.

Hypotheses and clauses are rendered as follows.

- The fixed finite field, distinct coefficient prime, algebraic closure, and
  finite coefficient extension are `D : FiniteFieldDatum`,
  `C : D.CoefficientDatum`, `E`, its `Field`, `Algebra (Padic C.l)` and
  `FiniteDimensional` instances. `S : SixFunctorDatum D C E (n+1) ...` supplies
  the fixed operation datum and axioms. Using the predecessor `n : ℕ` covers
  exactly every positive quotient exponent, including exponent one.
- `X : SixFunctorSpace D` is a finite-type scheme over the fixed algebraic
  closure. No smoothness, properness, separatedness, orientation, or dimension
  assumption is imposed on X.
- The four copies of `SfPerfectDualPair` use precisely `S.finiteClosed X`,
  `S.integralClosed X`, `S.rationalClosed X`, and `S.commonClosed X`, with each
  record's own monoidal structure and symmetry. These are the actual finite-Tor
  full subcategories. In particular the integral tensor is completed, the
  rational category is raw localization, and the closure category uses common
  finite stages. There is no ordinary discrete-field sheaf substitute.
- In `SfPerfectDualPair`, `P : B` ranges over that finite-Tor category, and
  `@IsDualizable B _ M.monoidal P` is perfectness exactly as in `sk-def-perfect`.
  The first conclusion is dualizability of `H.obj (op P, M.monoidal.tensorUnit)`.
  The site's local-model predicates are publicly imported from their recorded
  dependency; the node uses dualizability as its primary, equivalent convention.
- An arbitrary dual pair is `Q` and `d : ExactPairing P Q`. Its two triangle
  identities are exactly the fields of Mathlib's `ExactPairing`, with evaluation
  `d.evaluation' : Q tensor P → 1` and coevaluation `d.coevaluation' : 1 → P tensor Q`.
  The asserted iso `e : Q ≅ H(P,1)` has hom equal to `M.transpose ... d.evaluation'`.
  The next equation identifies its contraction with `M.evaluation P 1`.
- The canonical bidual arrow is the existing `CategoryTheory.ringedSiteBidual
  M s M.monoidal.tensorUnit P`, whose definition transposes symmetry followed by
  coefficient evaluation. Its `IsIso` clause concerns that actual arrow.
- The induced coevaluation is literally `d.coevaluation'` followed by tensor
  with `e.hom`. `sfCoefficientBidualInverse` inserts the left unitor inverse,
  that coevaluation tensor identity, the associator, identity tensor the
  reversed evaluation of the dual, and the right unitor. The final two
  equations assert that this displayed composite is a two-sided inverse.
- The integers `m s : ℤ` are unrestricted. `sfShiftedLineComplex` is the actual
  signed coefficient line in degree zero shifted by s; its opposite uses
  `(-m,-s)`. `SfFinitePerfectLines` and `SfIntegralRationalPerfectLines` assert
  the existence of these objects in the actual finite-Tor domains, rather
  than adding membership hypotheses.
- `SfNormalizedRingedLinePair` uses the datum's existing ordinary ringed-site
  realization and tensor comparison. Its two object equalities fix the line
  representatives themselves, not arbitrary isomorphic objects. Its unit
  iso must obey `SfLineUnitComparison`, the unitor normalization equation, so
  it cannot rescale evaluation freely.
- Both opposite-line isomorphisms are `e` and `f`, with homs fixed by the
  realization equations and `SfRingedShiftedLineEvaluation`. The latter uses
  the model's actual K-flat comparison and unit iso. It asserts K-flatness of
  the shifted line representatives rather than assuming it. The ordinary
  chain map is specified on the only nonzero tensor bidegree by
  `SfShiftedLineChainEvaluation`: multiplication at m=0, functional evaluation
  at positive or negative m, with scalar `(s*s).negOnePow` from the prescribed
  total tensor shift. The HEq premises there express only the canonical
  degree transports of sections in degrees -s and s; they do not replace
  evaluation by a new arrow. The reverse order uses the same formula with
  (-m,-s), including the canonical double-negation transports.
- `SfPerfectLinePair` supplies the two natural tensor cancellations, with
  every component equal to reassociation, contraction by e or f, and the
  unitor. Hence the two prescribed tensor functors are mutually inverse.
  It explicitly asserts dualizability after tensoring by either line and
  after tensoring the coefficient dual by the first line.
- `SfPerfectLineTransport` pins both scalar-extended evaluation maps to
  the supplied tensor comparison and a unitor-normalized unit comparison.
  `SfIntegralRationalPerfectLines` uses the actual rationalization comparison.
  `SfCommonPerfectLines` uses the completed line over
  `Padic.finiteCoefficientBase C.l C.Qbar`, then that field's actual
  rationalization and `S.commonClosedComparison`. Its image therefore is
  the prescribed common-stage Tate line, with the category's existing
  shift conventions. Both evaluation orders and perfect-object preservation
  survive these specified functors; an arbitrary map or arbitrary Nonempty
  isomorphism is never substituted for the coefficient evaluations.

Recorded dependency declarations used:

- `Sheaf.Paper.SixFunctorOperationDatum`:
  `WeilConjectures.SixFunctorOperationDatum` (publicly imported by the datum).
- `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`,
  `SixFunctorClosedDomain`, `SixFunctorCoefficientClosedModels`,
  `SixFunctorClosedComparison`, `sixFunctorDomainChange`, `sixFunctorRingedModel`.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`:
  `CategoryTheory.IsDualizable`; Mathlib's `CategoryTheory.ExactPairing`.
- `Sheaf.Paper.SitePerfectComplex`: the recorded finite, integral, intrinsic
  rational and general common-stage site-perfect predicates (equivalent
  interpretation of perfectness; used by the proof dependency).
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, publicly importing
  `CoefficientTwistsDetailed`: `coefficientTwistLine`, `purTwistFiniteOne`,
  `purTwistIntegralModule` and the existing completed/rational/common-stage
  twisting constructions. The normalization uses their actual signed lines.
- `Sheaf.CategoryTheory.RingedSiteDualityMaps`, publicly available through
  SixFunctorDatum: `ringedSiteBidual`, `ringedSiteDualityUnitComplex`,
  `RingedSiteDualityModel` and its representative/unit comparisons.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`, through the same imports:
  `CoefficientClosedStructure`, `.evaluation`, `.transpose`,
  `coefficientTotalTensor`, `coefficientTensorGenerator`, `CoefficientTensorModels.iso`.

Every recorded non-Mathlib proof-dependency module is imported, with plain
proof imports except for those also needed by the statement. The generic exact
pairing tensor/swap, braiding naturality, tensor adjunction, and right-adjoint
uniqueness leaves use Mathlib's recorded modules. The natural-language proof in
the theorem docstring follows all eight steps of the node.

Edge cases checked: n=0 represents quotient exponent one; P=0 and P=1;
empty X; m=0 and either sign of m; s=0, negative s and odd s; characteristic two,
where the displayed sign becomes one. The coevaluation/evaluation order was
checked against the two actual `ExactPairing` fields. The displayed bidual inverse
was checked from its source and target at every associator/unitor. There are no
extra finite-Tor, smoothness, orientation, or invertibility hypotheses. The site
object universe is u+1 and morphism universe is u throughout; compilation caught
and repaired the differing universe argument orders of the existing tensor and
unit-complex interfaces.

Searches (before writing):

- msearch leanfinder: "Perfect coefficient duals are perfect, canonical
  biduality is invertible, and shifted Tate line tensor functors are mutually
  inverse". Eight module perfect-pairing hits; none states this node.
- msearch loogle: "CategoryTheory.ExactPairing, CategoryTheory.IsDualizable".
  No hits; the latter is an upstream rather than Mathlib declaration.
- msearch grep: "bidual|exactPairing_swap|tensorRightEquivalenceOfTensorIso"
  under CategoryTheory/Monoidal. Three hits for exactPairing_swap in
  Rigid/Braided.lean, the recorded generic leaf, not the assembled assertion.
- rg in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json for
  PerfectDualPair, SfPerfectLinePair, SfSignedLinePairing, sfSignedLinePairing,
  sfCoefficientBidualInverse: no existing declaration. The item-id search in
  WeilConjectures also finds nothing.
- Broader source searches for biduality, line evaluation, shifted Tate lines,
  coefficient twists and perfect duality located OrientedPerfectDuality,
  SitePerfectCoefficientDual, RingedSiteDualityMaps, SignedLineTensorEquivalence,
  IntegralLineReductionDefinitions and CompletedLineTensorCoherence. These
  provide the definitions and partial results reused here, but none states
  all four stages with the specified maps and arbitrary shifted inverse line.

Source read: the node and its complete eight-step proof; all five statement
nodes and their recorded interfaces; the current blueprint's
sk-thm-sf-dual-perfect/_section.md and sk-thm-sf-dual-perfect.proof.md, plus
thm-sf-dual-perfect.md. No statement correction or disputed claim is needed.

Validation: scompile.py compiled the module in sandbox mode and its actual
library module name, separately, in 12.7 seconds each, without errors or warnings.
All variables/universes are explicit and autoImplicit/relaxedAutoImplicit are false.

## Second reading by Q26

The dispatcher forbids starting other agents. This section records a separate
self-review pass, not an independent worker's review; the maintainer's independent
review remains the delivery review.

Re-read the node against the final file and checked each clause above. Found and
fixed: the unit-complex universe arguments have a different order from the tensor
arguments; anonymous predicates need ObjectProperty.FullSubcategory rather than
Function.FullSubcategory; whitespace in universe levels. The arbitrary dual-pair
quantifier retains both triangle fields. The transpose and coevaluation transport
use the given evaluation and the same iso, and both bidual inverse identities are
present. Line membership is existential in the conclusion; no missing-membership
hypothesis is added. Both contraction orders have their representative formulas,
including the (-1)^(s*s) shift sign. The rational and closure statements use the
actual supplied scalar functors. No changes to the mathematical node were made.
