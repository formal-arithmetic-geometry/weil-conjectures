## Worker report

The module `Sheaf.AlgebraicGeometry.LogarithmicDifferentialTransform` states the entire
node in eight sorry-only theorems. Its three auxiliary declarations describe finite tests
on the already-defined marked data, extend the geometric tests by open restrictions,
and specify transforms of another ideal on those same supports. No proof or hollow
construction is supplied. No correction of the node statement is needed.

Source read: Bierstone--Milman, *Functoriality in Resolution of Singularities*, Publ.
RIMS 44 (2008), pp. 618--625, Definitions 2.1--2.5, Lemmas 3.1--3.3, Corollaries
3.4--3.6 and 4.1, Exercise 4.4(2), publisher PDF
https://ems.press/content/serial-article-files/41043 . The local ILO citation is a route
reference; the node itself records that its Taylor consequences are an agent formulation.
The proof docstrings reproduce the node's steps 1--12 under their respective conclusions.

Hypotheses and definitions, clause by clause:

* `A : AlgebraicGeometry.MarkedIdeal.{u}` packages the smooth closed pair N -> Z over
  `ULift.{u} ℚ`, the two finite-type structure maps (locally finite type and quasi-compact),
  the positive natural mark d, the coherent ideal I, and the finite ordered SNC boundary
  transverse to N. Its ambient `Embedded` also carries X and a retained level, which are
  unused by the order and differential statements; they impose no restriction on these
  inputs (one can take X=N and any level). There is no presentation, maximal-order,
  irreducibility, dimension, connectedness, nonemptiness or rational-point assumption.
  The packaged effective Cartier and adapted-parameter conditions are precisely the
  node's smooth labelled SNC hypersurfaces and transversality, not extra restrictions.
* `HilbertSamuel.stalkIdeal` and `HilbertSamuel.order` are reused unchanged. The latter
  is the supremum of the natural q with stalk containment in the q-th maximal-ideal
  power, as an extended natural number. Thus zero stalk ideals have order infinity.
  `MarkedIdeal.cosupport` is the inverse image of the existing ambient cosupport,
  hence exactly `{x | d ≤ order I x}` on N.
* `MarkedIdeal.logDifferential` is reused unchanged. Its affine ideals iterate the
  existing `logDerivative`, which retains the original ideal and adjoins derivatives by
  derivations preserving every labelled boundary ideal. This is derivative length at
  most j, with the empty list giving the ordinary differential ideal. Its integer-linear
  derivations are exactly Q-linear derivations on these rational section rings, including
  the zero ring of an empty open. No private differential, ideal-order or boundary
  definition is introduced.
* `DifferentialTestStep.operation = some s` uses the existing
  `HilbertSamuel.Step`, `Step.Admissible`, and `Step.Transforms`. These specify the
  actual global blowup, scheme-theoretic strict N in a controlled blowup, and cartesian
  N for a line or boundary-intersection blowup. The line appends its zero section;
  blowups append the exceptional member after the strict transforms of the old labels.
  The `none` branch is an open immersion with the actual cartesian support, pulled-back
  boundary and ideal, and unchanged mark. The stored support map is pinned by its
  commuting square with the closed immersion; it is not an arbitrary comparison map.
* `DifferentialTestStep.TransformsIdeal` characterizes K by
  `K * exceptional ^ d = J.comap support` exactly for the chosen admissible-blowup
  tag, and by ordinary pullback for every other operation. This is the regular
  controlled quotient by e^d, not a freely chosen map or a hollow quotient construction.
  The exceptional ideal is pulled back from the actual center. Even when one morphism
  admits both blowup descriptions, the operation tag fixes which rule is used.
  A `DifferentialTestSequence n` retains all n+1 marked states and n such steps,
  including n=0, opens between tests, empty centers and empty strict supports. These
  are helper specifications of this node's tests, not a competing test calculus.

Conclusions, clause by clause:

1. `logDifferential_coherent A j` states quasi-coherence and finite type of every
   logarithmic differential ideal. On the smooth (locally Noetherian) support this is
   exactly coherence, using the same `IsQuasiCoherentFiniteType` encoding as `Marked`.
2. `taylor_order_criterion A x q hq` has q>=1 and states precisely
   `q ≤ order I x ↔ stalkIdeal (logDifferential [] I (q-1)) x ≤ maximalIdeal`.
   The point x is arbitrary, not assumed closed. No residue-field condition is imposed.
3. `order_semicontinuous_bounded A` gives closed sets at every natural order threshold.
   This is upper semicontinuity of the extended-natural-valued function, also at infinity
   since that superlevel is the intersection of the finite superlevels. Under nonzero
   stalk at the generic point of each irreducible component, it gives a finite natural
   upper bound on a neighbourhood of each x and a finite range. The range conclusion
   uses the quasi-compact finite-type support already in A; finiteness without excluding
   infinity would not replace the explicitly stated local finite bound.
4. `order_product_sum A J hJ x` uses another coherent J on the same smooth N, and
   states both the product=sum-of-orders and sum=min-of-orders equations in `ℕ∞`.
   Ideal-sheaf addition is the ideal sum; all infinite-value conventions are intrinsic
   to the extended natural arithmetic.
5. `order_logDifferential_smooth_pullback A g` quantifies over every smooth g:Y->N,
   with Y finite type over Q (`QuasiCompact` of its structure map, local finite type
   follows from smoothness). It gives order equality at every y and equality of the
   entire pulled-back differential ideal in every degree j. Its pulled-back boundary
   retains all labels and allows disconnected/split components; the operators include
   every derivation, including relative ones. There is no fixed relative dimension,
   surjectivity, or equality of residue fields. Ambient smooth pullbacks in the node
   induce exactly such a smooth support map by base change.
6. `logDifferential_finite_test T j hj` uses j<d (j is natural, hence j>=0) and every
   finite test word. It supplies the differential-ideal transforms at every prefix,
   starting at exactly D_E^j I, with mark d-j in the exceptional-power identity, and
   gives the inclusion into D_{E_i}^j I_i at every stage, in particular the final t.
   Transform ideals are characterized on the fixed supports by their multiplication
   identity; regularity of the exceptional coordinate gives uniqueness. The conclusion
   includes existence rather than assuming the derivative transform was already defined.
7. `exists_contact_coordinate A hE x hx` assumes empty E and order exactly d at x.
   It gives an actual affine neighbourhood, an actual etale coordinate map to affine
   space, a selected coordinate index, an integer/Q derivation with Kronecker values
   on those coordinates, and a section f of I. The section condition is written as
   `(f) ≤ I|U`, using `ofIdealTop`, on the affine U. The d-th iterate is a unit,
   and the (d-1)-th iterate has principal-ideal order one at x and a smooth zero
   subscheme over Q throughout the chosen neighbourhood. In particular it is the
   required smooth hypersurface, not merely some abstract order-one element.
8. `contact_finite_test T h hmem horder htransverse` starts with the specified section
   h in D_E^(d-1) I, of order one along its zero set, and transverse to E. Section
   membership is `(h) ≤ D`; transversality is the already-recorded simultaneous etale
   coordinate flag on N for the ideal (h) and pulled-back boundary. For every finite
   word it supplies mark-one transforms of the actual principal ideal (h), contained
   in D_{E_i}^(d-1) I_i at every prefix, with transformed cosupport inside their zero
   loci. Around every transformed cosupport point there is an open on which that ideal
   is invertible, has order one along its zero locus, and is transverse to the full
   transformed boundary. These are exactly local equations h_t, up to multiplication
   by a unit, which is the natural chartwise meaning of e^(-1)h. This avoids incorrectly
   demanding a global function on a blowup. All the asserted conditions are local near
   transformed cosupport, so charts with empty cosupport impose no order-one assertion.

Dependency declarations used and checked in their sources:

* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` for finite type. These are publicly available through the marked
  data imports, not copied predicates.
* `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType`, and the recorded coherence interface
  `WeilConjectures.AlgebraicGeometry.Coherent.RingedSpace.IsCoherent` (namespace
  `AlgebraicGeometry.RingedSpace`). The former is used on smooth supports, where
  quasi-coherent finite type is equivalent to the latter. The source declaration of
  `RingedSpace.IsCoherent` includes both finite type and finite-type kernels.
* `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`;
  `WeilConjectures.Compactification.StrictTransform`: `strictTransform`,
  `strictTransformMap`, `strictTransformToSource`, used by the existing test relation.
  This is the scheme-theoretic closure construction, not topological closure.
* Already-landed `Sheaf.AlgebraicGeometry.MarkedIdealData`: `MarkedIdeal`, `cosupport`;
  `Sheaf.AlgebraicGeometry.HilbertSamuelPresentation`: `Embedded`, `Marked`, `Step`,
  `Step.Admissible`, `Step.Transforms`, `TestKind`, `blowupBoundary`, `lineZero`;
  `Sheaf.AlgebraicGeometry.MarkedIdealOrder`: `stalkIdeal`, `order`;
  `Sheaf.AlgebraicGeometry.LogarithmicCoefficientIdeal`: `logDifferential`;
  `Sheaf.AlgebraicGeometry.EtaleCoordinateFlag`: `HasEtaleCoordinateFlag`.
  Added the five existing owning nodes to stmt_deps under the landed-dependency rule.
  There is no added definition node or repaired dependency module.
* All already-stated proof-dependency modules are imported non-publicly. The one
  unstated proof prerequisite `lem-trf-logarithmic-derivative-single-transform` has no
  module to import; this does not prevent recording the current statement. No missing
  statement object is delegated to that future theorem. The existing coefficient-ideal,
  order and test interfaces have full definitions and compile as imported.

Edge cases checked before writing: I=0 (infinite order and full cosupport), I=O
(order zero and empty positive cosupport), J=0 and J=O in both arithmetic laws;
empty N and empty strict transforms; components swallowed by the center; n=0 empty
word and j=0 (identity ideal); d=1 (h=f and mark-one transform); absent boundary labels;
nonclosed points and transcendental residue fields; a line product with new zero section;
the intersection of two boundary coordinates with an independent contact coordinate;
the contact-pivot chart where the transformed equation is 1 and cosupport is empty.
For x^p in characteristic p, the Taylor conclusion fails, explaining the retained rational
base. A positive finite order cannot occur in a zero-dimensional smooth local field.

Searches actually run (2026-10-24):

* msearch.py leanfinder: `Taylor ideal order criterion logarithmic differential ideals
  controlled blowup transforms smooth maximal contact` returned eight Weierstrass
  division declarations; none states this result.
* msearch.py loogle: `"Derivation", "Ideal"` returned
  `LieDerivation.ad_isIdealMorphism` and `LieDerivation.mem_ad_idealRange_iff`;
  neither concerns coherent differential ideals or transformations.
* msearch.py grep: `logarithmic.*ideal|differential.?ideal|maximal.?contact` returned
  18 hits, concerning Kahler relation ideals and Dedekind different ideals; no match.
* msearch.py leansearch: `Order of a coherent ideal at a smooth scheme point is upper
  semicontinuous and is detected by iterated derivations` returned eight hits, including
  analytic vanishing order and the ideal-sheaf order instances; no algebraic theorem match.
* rg in `lean/WeilConjectures` and `lean/Sheaf` for logarithmic/marked-ideal/test-sequence
  and Taylor-order terms found the reused marked-order, marked-data, logarithmic
  coefficient, restricted-equivalence and controlled-blowup interfaces above, but no
  statement of the current node. The node-id search in `WeilConjectures` returned no hit.
  The new helper names and theorem names were absent. No new primitive notion is needed.

Validation: scompile.py compiled the final module in sandbox mode and at its actual library
module name cleanly, in 14.3 and 9.1 seconds respectively. `autoImplicit` is disabled; every
universe and variable is explicit. All eight theorem bodies are `sorry`, all helper data
are complete definitions or structures. No statement is disputed.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
