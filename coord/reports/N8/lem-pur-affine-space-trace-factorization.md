## Worker report

The module Sheaf.Paper.AffineSpaceTraceFactorization states
AlgebraicGeometry.ProEtale.AffineSpaceTrace.affineSpaceTraceFactorization, with its
whole proof postponed. The node statement and accepted three-step proof are unchanged.
The resolved stage-1 repair note was read: its requested split is already reflected
in the current node and is preserved. The returned stage-2 H2 defect is repaired below: definitions formerly recorded only
inside four theorem modules now have their own definition nodes.

Hypothesis and clause correspondence:

- Finite conventions, including the algebraic closure of the finite base field,
  ell distinct from its characteristic, the finite coefficient extension, and every
  positive quotient level: `P : PurityFiniteSetting.{u}`. `AffineLinePurity.Ring P`
  is the existing lifted quotient at index P.level-1, canonically identified by the
  published ringEquiv with P.Coefficient. There is no ramification-divisibility condition.
- Separated finite-type k-scheme: `Y`, `aY`, and the LocallyOfFiniteType,
  QuasiCompact and IsSeparated instances. No affineness or nonemptiness is imposed.
- X_m, p_m, q_m and p_(m+1)=p_m q_m: the existing iteratedAffineLine,
  iteratedAffineLineProj and lastProjection. The square for the product is the literal
  AffineSpace.isPullback_map square, flipped to the order (p_m,T_m),(p_1,T_1).
- T_m=A_X(m)[2m]: published `OrderedAffineTranspose.tate`, the ordered tensor power
  of the compared shifted finite Tate line. `pullTate` uses canonical monoidal
  pullback on each factor and the existing unitPull. `appendTate` cancels the unit
  in the last factor. `externalTateIso` composes precisely these identifications.
  The even shifts are already in shiftedLine; no new orientation is selected.
- V_m=Rp_m! T_m and U=V_1: `(compact P Y m).obj (tate P Y m)` and its m=1 case.
- Actual exceptional transpose I_m: the existing `OrderedAffineTranspose.integration`.
  Reading its source shows that it first maps the inverse tateSourceIso, then maps
  exactly affineSpacePurityComparison, then applies the published exceptional counit.
  It is not a recursion of newly chosen trace maps.
- Normalized t_Y: existing `lineNormalizedIntegration`. Its body uses only the
  fixed source identification, canonical change of compactification, unit
  identification and AffineLinePurity.integration (the actual open counit followed
  by the normalized projective trace). Its domain is V_1 in these same coordinates.
- V_m bounded constructible of finite Tor amplitude for all m>=1: `_hV`, with
  the exact recorded ProEtale.DerivedCategory.constructibleFiniteTor predicate.
- Base change along every v:Y'->Y, and the same assumption over every base Y':
  `_ht : UniversalLineBaseChange P Y aY`. The predicate quantifies over B->Y
  and every X->B, both separated finite type over k. Their over-k equations are
  explicit. Choosing B=Y, b=id gives every original base change. Further B's
  give the iterated assumption. `LineBaseChangeEquation` uses exactly
  BaseChangedLineTrace.TraceCompatible, trace and normalizedPulledTrace. The
  operation-domain QuasiCompact and composite finite-type instances are derived
  internally from the structure maps; they are not additional assumptions.
- Supplied isomorphism kappa_(m,1): `κ d`, where m=d+1; all m>=1 occur.
  `_hκ` is BinaryProductSpecified. This requires its inverse to equal the actual
  native `finiteForwardProduct` followed by the projection equality and
  externalTateIso. The native forward product has exactly the six arrows inverse
  to the specified relative Kunneth construction: symmetry, PF, symmetry under
  compact support, exchange tensor identity, PF, normalized compositor. Thus no
  arbitrary product isomorphism or abstract six-functor datum is substituted.
  The existential h is only a Prop-valued bounded-below etale-origin witness
  required by the compositor's published domain; it supplies no map or object.
- I_1=t_Y: the first conjunct.
- I_(m+1)=(I_m tensor t_Y) kappa_(m,1) for all m>=1: the second conjunct,
  indexed by d:Nat with m=d+1. Tensor on the first arrow then tensor on the
  second is precisely the tensor bifunctor on the pair of maps. The final
  comparedLeftUnit at the coefficient unit restores A_Y tensor A_Y -> A_Y;
  left and right unitors agree on that unit. There is no permutation assertion.

Dependencies read and reused (module; declarations):

- Sheaf.Paper.PurityFiniteSetting; WeilConjectures.PurityFiniteSetting and its
  coefficient data. Mathlib.AlgebraicGeometry.AffineSpace; AffineSpace, over,
  isPullback_map. The iterated model is the recorded affine-space comparison model.
- Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted and its imported intrinsic
  coefficient-twist construction; the finite specialization is the published
  shiftedLine and twistAction of Sheaf.Paper.AffineSpacePurityComparison.
- Sheaf.Paper.AffineLinePurityComparison; integration, Ring, primeUnit and
  affineLinePurityComparison. Sheaf.Paper.AffineSpacePurityComparison;
  affineSpacePurityComparison, orderedSource, tensor, inverseImage,
  inverseImageTensorIso, shiftedLinePullback, actionPullbackIso and projection_geometry.
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients; the recorded
  ConstructibleExceptionalCoefficients.System and its published finite counit
  specialization used by OrderedAffineTranspose.counit.
- Sheaf.Paper.OrderedAffineTransposeProjection; compact, tate, integration,
  transpose, unitPull and lineNormalizedIntegration. Its definitions are now
  recorded by def-pur-ordered-affine-trace-data (existing:true).
- Sheaf.Paper.FiniteForwardProductSymmetry; finiteForwardProduct and its literal
  six-arrow definition, finiteForwardProductPrefix and normalized compositor.
  These maps are recorded by def-pur-finite-forward-product (existing:true).
- Sheaf.Paper.RelativeKunneth; relativeKunnethIso, relativeKunnethMap and
  relativeKunneth. Their six-factor construction fixes the product requested by
  the item; the native map is used without assuming a SixFunctorDatum.
- Sheaf.Paper.ExchangeProjectionSuppliedDomains; ExchangeProjectionStage and
  its projection and compactExchange. The finite native transformations used by
  finiteForwardProduct are their existing fixed-scalar specialization.
- Sheaf.Paper.FiniteTorAmplitudeSites; its public fixed-ModuleCat
  ProEtale.DerivedCategory.constructibleFiniteTor predicate.
- Sheaf.Paper.BaseChangedLineTraceEvaluation; TraceCompatible, trace,
  normalizedPulledTrace, recorded by def-pur-normalized-line-trace-base-change
  (existing:true). Its theorem conclusion is a proof dependency only.
- Sheaf.Paper.AffineLineCompositeTranspose; comparedLeftUnit and composite_transpose.
  The unitor is
  recorded by def-pur-compared-coefficient-left-unitor (existing:true); the
  composite-transpose conclusion is a proof dependency only.
- Sheaf.Paper.TwistPreservesFiniteness; twist_preserves_finiteness, a proof import.

The remaining proof dependency lem-pur-affine-space-last-factor-product has no
recorded Lean declaration in the read snapshot. It is not a notion needed to type
this statement: the native product is explicitly constructed here from existing
operations. Its proof step remains in the theorem docstring for stage 3, rather
than adding an unrelated theorem or copying a future proof result.

Edge cases checked: d=0 in the concluding quantifier is m=1, giving the A^2
formula, so the first nontrivial recurrence is retained. The first conjunct
separately covers I_1. The source's m=0 is not required or accidentally added
as a theorem conclusion. Empty Y and all its coordinate spaces are allowed;
there is no chosen point or finite-dimension maximum. P.level=1 and ramified
coefficient extensions are retained by the published annihilating exponent.
Identity v and b are included in the base-change predicate; arbitrary further
intermediate bases are included. All scheme and coefficient universes retain
Scheme.{u} and ModuleCat.{u+1}; no equality of site object/morphism universes is
introduced. All parameters and universe variables are explicitly bound.

Searches (the prescribed msearch wrapper writes the full results to searches.jsonl):

- LeanFinder: 'Ordered affine space exceptional transpose integration factors as
  tensor product of affine line traces under compact support Kunneth'. Eight
  results on torus/measure integration, including torusIntegral_succ, no match.
- Loogle: 'CategoryTheory.Adjunction, "comp"'. Twelve generic adjunction results,
  including Adjunction.comp and comp_homEquiv; no geometric trace factorization.
- LeanSearch: 'Affine space purity exceptional transpose factors through tensor
  product of affine line integrations'. Eight results on affine equivalences
  and affine-space geometry; no match.
- msearch grep 'trace.*(tensor|affine)|integrat.*kunneth|purity.*comp', Mathlib
  AlgebraicGeometry: zero hits.
- rg of lean/WeilConjectures and lean/Sheaf for the item id, trace factorization,
  affine integration tensor/successor formulas and helper names: no declaration
  of the complete claim. Found and reused the actual transpose in
  OrderedAffineTransposeProjection. AffineSpacePurityComposition's proof docstring
  cites this still-unstated trace factorization, so its broader theorem is not
  used to assert the item as an existing result. The new names were searched for
  in both trees and do not already exist.

No statement correction or disputed statement is needed. The H2 repair adds
definition ownership metadata for existing data, with no duplicate construction. Helpers belong to this node's actual displayed product and
base-change condition and are all listed in lean.declarations. Their data contain
no sorry. The sole new sorry is the whole proof of affineSpaceTraceFactorization,
matching this DAG node, with its complete three-step proof in the docstring.

## Second reading by N8

The dispatcher explicitly forbids starting other agents. This is a separate
self-review against the open node and completed module, not a claim of an
independent reader. The maintainer's independent review follows delivery.

I rechecked the two equalities, all positive dimension indices, the actual
exceptional counit in the reused integration, the two normalized trace sources,
and the native six-arrow product. I replaced the initially extra explicit
QuasiCompact/composite-typing arguments of the universal base-change condition
by internally derived instances, so the condition is exactly on arbitrary
morphisms of the stated finite-type bases. I changed the product specification
from heterogeneous to ordinary equality once its explicit endpoints were
available. The constructor fixes the inverse of kappa, not merely its isomorphism
class. No source hypothesis or conclusion was changed. The base-change
condition is over every intermediate base B, not just the projections p_m.

## New nodes

The returned H2 fault is repaired by removing all four added theorem stmt_deps
and adding the following four definition nodes. All are existing:true records of
exact public declarations in the existing modules. No new Lean file, definition,
choice or theorem is introduced. The original statement, proof, proof_deps and
original nine stmt_deps are preserved against current main.

def-pur-ordered-affine-trace-data: Ordered affine compact supports and actual trace maps. It records `AlgebraicGeometry.ProEtale.OrderedAffineTranspose.compact`, `AlgebraicGeometry.ProEtale.OrderedAffineTranspose.tate`, `AlgebraicGeometry.ProEtale.OrderedAffineTranspose.unitPull`, `AlgebraicGeometry.ProEtale.OrderedAffineTranspose.integration`, `AlgebraicGeometry.ProEtale.OrderedAffineTranspose.lineNormalizedIntegration` in Sheaf.Paper.OrderedAffineTransposeProjection. Its source is the current blueprint Integration on affine space paragraph and its expanded trace-factorization construction. The exact data already exist, but the DAG searches find no definition node recording them; only theorem nodes do. Thus the node uses existing:true instead of copying the definitions. LeanSearch, LeanFinder, Loogle, Mathlib grep, upstream/Sheaf rg and DAG/blueprint searches are recorded verbatim in mathlib_searches, including the wrapper result names and digests. The generic search results do not supply these canonical geometric composites.

def-pur-finite-forward-product: Native finite-coefficient forward compact-support product. It records `AlgebraicGeometry.ProEtale.finiteForwardProduct` in Sheaf.Paper.FiniteForwardProductSymmetry. Its source is the current blueprint Integration on affine space paragraph and its expanded trace-factorization construction. The exact data already exist, but the DAG searches find no definition node recording them; only theorem nodes do. Thus the node uses existing:true instead of copying the definitions. LeanSearch, LeanFinder, Loogle, Mathlib grep, upstream/Sheaf rg and DAG/blueprint searches are recorded verbatim in mathlib_searches, including the wrapper result names and digests. The generic search results do not supply these canonical geometric composites.

def-pur-normalized-line-trace-base-change: Normalized line traces and their base-change equation. It records `AlgebraicGeometry.ProEtale.BaseChangedLineTrace.TraceCompatible`, `AlgebraicGeometry.ProEtale.BaseChangedLineTrace.trace`, `AlgebraicGeometry.ProEtale.BaseChangedLineTrace.normalizedPulledTrace` in Sheaf.Paper.BaseChangedLineTraceEvaluation. Its source is the current blueprint Integration on affine space paragraph and its expanded trace-factorization construction. The exact data already exist, but the DAG searches find no definition node recording them; only theorem nodes do. Thus the node uses existing:true instead of copying the definitions. LeanSearch, LeanFinder, Loogle, Mathlib grep, upstream/Sheaf rg and DAG/blueprint searches are recorded verbatim in mathlib_searches, including the wrapper result names and digests. The generic search results do not supply these canonical geometric composites.

def-pur-compared-coefficient-left-unitor: Left unitor with the compared coefficient unit. It records `AlgebraicGeometry.ProEtale.AffineLineEvaluation.comparedLeftUnit` in Sheaf.Paper.AffineLineCompositeTranspose. Its source is the current blueprint Integration on affine space paragraph and its expanded trace-factorization construction. The exact data already exist, but the DAG searches find no definition node recording them; only theorem nodes do. Thus the node uses existing:true instead of copying the definitions. LeanSearch, LeanFinder, Loogle, Mathlib grep, upstream/Sheaf rg and DAG/blueprint searches are recorded verbatim in mathlib_searches, including the wrapper result names and digests. The generic search results do not supply these canonical geometric composites.

The existing signatures were reread in full, including section-bound coefficient,
scheme and morphism parameters. For ordered trace data, dimension zero is the
identity compact-support functor and canonical zero-fold twist; dimension one
still names two distinct defined maps, whose equality is a theorem conclusion.
For the forward product, only its external coefficient requires the native
bounded-below etale-origin domain; no swapped-domain or symmetry conclusion is
introduced. The normalized trace uses the specified annihilating exponent and
canonical roots pullback, and TraceCompatible is an equation, not its proof.
The compared unitor retains the generic coefficient category's Grothendieck,
closed monoidal, additive and functorial-flat-resolution assumptions. Its
finite-module specialization is exactly the one used twice in this item.

During the second reading I checked each new node against the definition body,
its full signature and docstring, and verified that none includes its old
theorem's conclusion. The existing-data records introduce no sorry.
