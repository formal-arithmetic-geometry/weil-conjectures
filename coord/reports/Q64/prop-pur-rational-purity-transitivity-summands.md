## Worker report

Repair of immutable returned head d5f8300932ed, points H3, H9, H13/H5/H6 and H11.
The retained packet passed the initial prescribed dry run mechanically. Reading its
statements against the return showed that it still contained the returned arbitrary
functor formulation, so that formulation has been replaced substantively. This packet
contains one module, `Sheaf.Paper.RationalPurityPresentation`, owned by the item.
The mathematical node statement and every other non-lean field are unchanged.

The theorem `AlgebraicGeometry.Scheme.rationalPurityTransitivitySummands` states
`PbcRationalPurityConclusion l Ω D hl f d`. The definition unfolds to the coefficient
assertion for every compactification of the specified geometric morphism. Its finite
categories are literally `PbcRationalDerivedCategory`; finite fields inside Ω use the
published small field `pbcFiniteField.{u}`, without equating the scheme universe u and
closure universe w. The algebraically closed category is literally `pbcQbarCategory`.
The transition functors and associators are those of `pbcScalarSystem`, identified with
`pbcRationalScalarExtension` by `pbcPurityScalarNormalization`, whose components are
specified by the recorded integral scalar comparison. These are not arbitrary categories,
functors, extensions or associators supplied as hypotheses.

Source hypotheses, one by one:

- The fixed algebraic closure k of a finite field is `D : FiniteFieldDatum.{u}` and
  `Spec (.of D.k)`. The coefficient prime is `(l : ℕ) [Fact l.Prime]`, distinct from
  the characteristic by `hl : l ≠ D.p`. Algebraically closed l-adic coefficients
  are `(Ω : Type w) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
- The schemes are `{X Y : Scheme.{u}}` with `Xbase` and `Ybase` instances of
  `.Over (Spec (.of D.k))`. Their separatedness is `Xsep`, `Ysep` on their structure
  maps. Their finite type is the pairs `Xft`/`Xqc` and `Yft`/`Yqc`, namely
  `LocallyOfFiniteType` and `QuasiCompact` on those maps.
- The geometric map is `(f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]`.
  Its separated finite-type conditions are `fsep`, `fft`, `fqc`. Its pure relative
  dimension is `(d : ℕ) [fsm : SmoothOfRelativeDimension d f]`. Thus d is nonnegative.
  The explicit `include ... fsm hl in` retains all these named instances in the
  theorem even when Lean would otherwise omit a section variable.
- No Noetherianity, dimension bound, stalk invertibility, compactification existence,
  functor-existence, or coefficient-compatibility hypothesis is imposed on the theorem.
  `pbcPurityGeometricBounds` supplies the first three from the source setting.
  `PbcRationalPurityConclusion` installs them and quantifies over every presentation
  `c : Compactification f`; the separated finite-type source setting admits one.

The two functors in purity are identified as follows. `pbcPurityTwistedAmbient` is
`pbcActualCompletedPull f ... ⋙ pbcTateAmbient ... d ⋙ shiftFunctor _ (2*d)`;
`pbcPurityTwisted` is its actual restricted rationalization, hence Lf^*(-)(d)[2d].
`pbcPurityCompactAmbient` is `PurCompactSupport.image ... c`, the specified Rp_* j_!
with the PBC completed coefficient pullback isomorphisms. `pbcPurityCompact` restricts
and rationalizes this construction. `PbcPurityExceptionalSpec` characterizes G as its
right adjoint at each finite stage. This is the actual exceptional inverse image,
determined up to its unique adjunction-compatible isomorphism, rather than an arbitrary
functor. Its b comparison is fixed by the displayed counit-mate equation: application
of compact support to b, followed by the new counit, equals inverse c followed by
scalar extension of the old counit. The compact comparison c is itself the
rationalization of the published proper/open coefficient mate.

Each conclusion clause is rendered explicitly:

1. Purity is a simultaneous natural-isomorphism family
   `γ : ∀ E, pbcPurityStageTwisted ... E ≅ G.Φ E` in the existential conclusion,
   together with the actual exceptional specification. The proof docstring selects
   the compatible adic family before rationalizing it; it never asserts compatibility
   for an arbitrary preassigned family or independently chosen objectwise lifts.
   Both inverse identities are part of NatIso. The construction supplies purity,
   rather than assuming a purity-family input.
2. The coefficient square is the first conjunct after γ in
   `PbcPurityCoefficientConclusion`: `TX(h).map γE ≫ b(h) = a(h) ≫ γF` at every K.
   `pbcPurityTwistedScalarComponent` constructs a from shift/scalar interchange,
   the specified pure-tensor Tate comparison and inverse completed-pullback scalar
   comparison. The ordinary and derived scalar-model bridges are fixed on tensor
   generators and universal counits. `pbcPurityStageA` conjugates these maps by the
   recorded stage normalization. Neither a nor b is a freely selected comparison.
3. `PbcPurityTransitivity` states Step 4 as two equalities of actual morphisms for
   E ≤ F ≤ L. Its first equation identifies direct extension, preceded by the X
   tensor associator, with the successive extensions and the Y tensor associator.
   Its second equation gives the other path through a and γL. It retains both
   associators explicitly; it does not merely restate the single coefficient square.
   `pbcPurityStageA_coherence` states the corresponding associator equation for a.
4. The Qbar conclusion is an actual natural isomorphism between
   `(pbcPurityTwistedSystem ...).functor` and `G.functor`, the recorded descended
   functors on `pbcQbarCategory`. `PbcPurityDescent` includes `DescentSpec` for both,
   the component formula and inverse component formula on every pair-category object,
   and the common-stage naturality equation for every representing arrow u. This
   last equation is written for γ inverse, equivalently the forward purity square.
   `DescentSpec` includes the arrow representative formula and compatible equations;
   the fixed StageSystem quotient supplies independence of representatives/enlargement.
5. Summand restriction ranges over every finite-stage K and every endomorphism e
   with exactly `he : e ≫ e = e`. It asserts `IsIso` of the component at `⟨K,e,he⟩`
   of Mathlib's `Idempotents.functorExtension₂` applied to γ.hom. The same statement
   is asserted for every Qbar K and e after descent. This is the actual projector
   sandwich between the image projectors; its inverse is the sandwich of γ.inv.
   Finite-stage Karoubianity and `pbcIdempotentCompleteTriangulation` identify these
   Karoubi objects with the summands in the stated categories. No integral lift of
   a rational idempotent and no chosen splitting is assumed.
6. The final Step 7 is also explicit: at each finite stage and on Qbar, for every
   i:J→K and r:K→J with i≫r=identity, the restriction H(i)≫γK≫G(r) equals γJ,
   and the inverse restriction equals γJ inverse. Hence the coefficient square and
   associator equations already quantified at J apply to this actual restriction.
   The Qbar formula uses actual morphism classes, so descent and representative
   independence apply to the restriction as well. Naturality at the canonical
   isomorphism between two splittings gives independence of the splitting.

Dependency declarations and reuse:

- `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational`,
  `AlgebraicGeometry.Etale.exists_iso_fromIntegral_realization_twistShiftPullbackLevel`:
  the recorded upstream declaration remains unchanged. It was read through
  `scompile.py --source`; its normalized-tower realization does not by itself give
  this coefficient-square/descent theorem. Its integral-realization role remains
  part of the proof route. The returned `RationalAndQbarPurity.lean` and its dependency
  node copy have been removed, rather than replacing this record by tautological data.
- `Sheaf.Paper.PbcDescentFunctors`, `CategoryTheory.StageSystem.Morphism.DescentSpec`,
  `CategoryTheory.StageSystem.CoherentExactMorphism`,
  `AlgebraicGeometry.Scheme.pbcDescentFunctors`: the actual pair-category descent
  construction and theorem, now used explicitly in the conclusion.
- `Sheaf.Paper.PbcIdempotentCompleteTriangulation`,
  `AlgebraicGeometry.Scheme.pbcIdempotentCompleteTriangulation`, and
  `Sheaf.Paper.PbcFiniteStageKaroubian`, `AlgebraicGeometry.Scheme.finite_stage_karoubian`:
  the proof dependencies interpreting the explicit Karoubi restriction as summands.
- `Sheaf.Paper.PbcScalarExtension`: `pbcRationalScalarExtension`,
  `pbcScalarCoefficientMap`, `pbcScalarCompletedPullIso`; and the normalized
  `pbcScalarSystem`/`pbcScalarIntegralComparison` from the recorded scalar system.
- `Sheaf.Paper.PbcCoefficientTwists`: `pbcTateAmbient`, `pbcTateSheafTensor`;
  `Sheaf.Paper.IntegralTwistDerivedScalarCanonical`: `integralTwistOrdinaryBeta`;
  the existing coefficient model `purCoefficientModel` and `purScalarModel`.
  The module supplies only their necessary normalization bridges, not duplicate twists.
- `Sheaf.Paper.IntegralCompactSupportUniformRestriction` and
  `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`:
  `PurCompactSupport.Coefficients`, `image`, `Change`, `comparison` and scalar shift.
- The explicitly imported recorded proof dependencies also include rational transport,
  semilinear scalar localization, integral stratified-perfect characterization,
  integral residue Tor, finite-type dimension, and the coefficient-category modules.
  Helpers all belong to this item's construction and have source/blueprint docstrings;
  postponed helper proofs are named theorems with natural-language proofs.

Reuse checks specifically requested by the return: `SmoothPurityMap.lean` was opened.
Its `PurityFiniteSetting.smoothPurityMap` is the specified finite-coefficient intrinsic
map; its source uses a positive finite quotient and its target is transported from the
etale exceptional functor. It is not a map on the rational PBC category. Its normalization
is the finite-level input to the adic proof route. `SmoothPurityQbar.lean` was opened in
full. `smoothQbarPurityRightFunctor` and `smoothPurityQbar` use the intrinsic
`generalAlgebraicallyClosedConstructibleCategory`, and conclude an adjunction for a
compact-support action there. They cannot be substituted literally for the recorded
PBC categories and do not state this item's coefficient/associator/summand equations.
The present exceptional specification uses the same universal adjunction principle
on the actual PBC categories, with the coefficient mate explicitly fixed.

Edge cases: identity and repeated extensions retain the scalar unit normalization;
E ≤ F ≤ L retains the actual associators. Ramified extensions are allowed; no flatness
or unramified hypothesis is added. Empty schemes and the zero object remain allowed;
finite dimensionality is an existential bound, so the empty scheme's bottom dimension
is included. Both e=0 and e=identity are included. Rational idempotents with denominators
need no integral idempotent lift. Every Qbar representative and common-stage arrow is
quantified over, with no single common field fixed for the category. Scheme and closure
universes remain independent. The old identity/negative-comparison counterexample cannot
instantiate the theorem: the actual comparisons and counit-mate normalization are fixed.

Searches (prescribed msearch and direct source searches):

- LeanFinder, smooth purity natural isomorphism on rational constructible categories
  commuting with finite scalar extension and idempotent summands: 8 unrelated
  Dold--Kan/Karoubi hits, no statement match.
- Loogle, `CategoryTheory.Adjunction.rightAdjointUniq, CategoryTheory.Idempotents.functor`:
  no match. Earlier packet searches for Karoubi and NatTrans also gave no exact item.
- msearch grep, `pbcPurity|rationalPurityTransitivitySummands`: zero Mathlib hits.
  The earlier purity/twist searches likewise gave no matching theorem.
- Direct rg in upstream WeilConjectures and shared lean/Sheaf located the actual PBC
  scalar, twist, compact-support and descent constructions, plus SmoothPurityMap and
  SmoothPurityQbar described above. No exact item declaration exists. The prescribed
  recursive grep for the item id in upstream WeilConjectures returned no hits.
- Mathlib `CategoryTheory/Idempotents/FunctorExtension.lean` supplies the actual
  functor extension used here, so no private projector or Karoubi notion was invented.

There is no disputed mathematical node statement and no statement correction. The
faults were in the returned Lean formulation, not in the blueprint. There are no new
nodes or dependency node changes in this repaired packet. The theorem remains stage 2:
all theorem proofs are sorry, and all definitions have real construction data.

## Second reading by Q64

I reread the node, its seven proof steps, the dependency signatures, the returned review,
and the replacement module with those texts open. This is the dispatcher's single-worker
second reading; no additional agent was started. The following mismatches were found
in the saved packet and repaired:

- H3: free coefficient categories, extensions and comparisons made a false universal
  assertion. These have been replaced by actual PBC constructions and an existential
  compatible purity family on the specified geometric functors. The exceptional b is
  fixed by the canonical compact mate and counit equation.
- H3: the old composite field repeated compatibility and supplied arbitrary compositors.
  The replacement uses the published scalar associators in the explicit Step 4 equations.
- H3/H9: Qbar descent was missing and its imports had no role. The conclusion now uses
  the descended functors, both component formulas and common-stage naturality;
  finite and Qbar summand restrictions use the actual Karoubi extension.
- H13/H5/H6: the dependency replacement was tautological and omitted the geometry.
  It has been deleted, the upstream record retained, and f, d, l, the base field,
  smoothness, separatedness, finite type and l distinct from p appear in the repaired
  theorem. H is literally completed pullback/Tate/shift, and G has the actual
  compact-support adjunction specification. The final `include` was checked specifically
  to prevent Lean silently dropping the geometric section hypotheses.
- H11: this second reading checks the maps and defining predicates, not just the
  successful compilation or the names. All coefficient-square, associator, descent
  and idempotent clauses above were traced through their definitions. No free
  RationalPurityFamily or RationalPurityDatum remains in this packet.

Local file-only compilation via scompile.py passed cleanly for the repaired module
and the explicit proof imports (31.7 s sandbox / 29.3 s module); preflight also passed.
The final actual-splitting clauses are compiled again through scompile.py, followed by
the final deliver2.py dry run before pushing. All thirteen postponed proofs are named
theorems; all twenty-six definitions supply construction data.

## Timeout-return retry, 2026-10-18

The returned immutable head is 6206c267c96f. Its sole return point is a
60-second timeout compiling `Sheaf/Stage2/Sandbox0.lean`. As instructed for
this retained packet, I first read this report and ran the prescribed
`deliver2.py Q64 prop-pur-rational-purity-transitivity-summands --no-push`.
It passed preflight and both file-only compilations, producing dry-run
commit d80073b3bd. Therefore the saved Lean module is retained unchanged;
the timeout did not recur, and no compiler limit was changed.

The required self-check reread the saved module, the current node and all
three statement-dependency nodes, their recorded declaration signatures and
docstrings, and the main-20261015 proposition. The current upstream rational
purity source was obtained with `scompile.py --source` because it is absent
from the older source checkout. Its realized-lattice packaging is still used
only as described above; it is not substituted for the coefficient conclusion.
The actual `DescentSpec` includes exactness, the representative arrow formula
and compatible transformation equations. The idempotent-completeness theorem
refers to the same raw pair category and its canonical Karoubi inclusion.

I traced the retained definitions again: the geometric hypotheses enter through
the final explicit `include`; the twisted functor is completed pullback, Tate
tensor and shift; the exceptional functor is characterized by adjunction to
the actual compact-support composite with its specified counit mate. The
finite-extension square, both associator equations, Qbar component and
common-stage formulas, finite/Qbar idempotent restrictions, and actual-retract
formulas remain present. Equal stages, zero and identity projectors, empty
schemes, and independent scheme/coefficient universes are still included.
This reading found no new mismatch. Comparing the sandbox node with current
shared main shows that only `lean` differs; no mathematical node field changed.

An additional prescribed `scompile.py Q64
prop-pur-rational-purity-transitivity-summands
lean/Sheaf/Paper/RationalPurityPresentation.lean` passed without diagnostics:
39.3 seconds for the sandbox file and 40.4 seconds for the library module,
each under the unchanged 60-second limit. The final delivery dry run and push
use this same retained module and the updated report.

## Current timeout return fca0dcacce6c, 2026-10-18

As required for this repair, I first inspected the retained report and ran
`deliver2.py Q64 prop-pur-rational-purity-transitivity-summands --no-push`
on the saved packet. It returned `OK (dry run): commit f7e21e56e1 passes the
preflight and compiles; nothing pushed`. Both the sandbox and library
compilations passed under the unchanged 60-second per-file limit. The
reported timeout did not recur. Following the explicit retry instruction,
I retained the saved Lean module and node record unchanged.

For the required self-check I opened the current item statement and all seven
proof steps, the main-20261015 proposition and proof, all three statement
dependency records, the complete current upstream Rational module obtained
through `scompile.py --source`, and the current `DescentSpec`,
`CoherentExactMorphism`, `pbcDescentFunctors` and
`pbcIdempotentCompleteTriangulation` signatures and docstrings. I reread the
entire saved RationalPurityPresentation module. The geometric hypotheses are
retained by the final explicit `include`; actual PBC pullback/Tate/shift and
compact support specify the functors. The counit-mate equation specifies the
exceptional comparison. The finite coefficient square, both associator
transitivity equations, Qbar component and common-stage formulas, and finite
and Qbar Karoubi and actual-retract restrictions remain explicit. Equal
stages, zero and identity idempotents, empty schemes and independent scheme
and coefficient universes remain covered. No additional mismatch was found
in this timeout retry. A parsed comparison with the current shared node
confirmed that only `lean` differs; mathematical node fields are unchanged.
This self-check used no additional agents. The only edit for this retry is
this report entry recording the successful validation of the retained packet.
