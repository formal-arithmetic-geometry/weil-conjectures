## Worker report

The delivery states lem-pur-etale-horizontal-double-counit in
Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit. All declarations use namespace
AlgebraicGeometry.Etale. Every theorem proof is `by sorry`; the two definitions contain
actual mate/conjugate constructions. The node statement and its proof are unchanged.

Hypotheses and objects, clause by clause:

- A finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The coefficient and site sizes follow the existing DerivedCategoryModule interface;
  there is no independent or reduced coefficient universe.
- R, R', T, T' are X, X', Y, Y'. Each has `[IsNoetherian ...]`, the usual scheme
  notion equivalent to the finite affine Noetherian cover in the node.
- The arrows h, h', e, e' have the same endpoints. The section binds separatedness
  of all four. Finite type is locally finite type plus quasi-compactness; etale supplies
  the horizontal locally finite type instances. Every arrow and both composites have
  HasCompactification, exactly the compactifications stipulated in the node.
- The Cartesian data is the recorded `ChosenCartesianSquare e' h' h e`, including
  its chosen fibre-product isomorphism, projection equations, and equality of composites.
  `IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd`
  passes exactly those data to the existing comparison API; no new square is chosen.
- Ordinary unbounded small-etale constant-A module categories are the recorded
  `DerivedCategoryModule A X`, etc. There is no boundedness, constructibility,
  smoothness, or purity hypothesis.
- F_a is the existing `rightDerivedLowerShriek (ModuleCat A) a`. The arbitrary
  right adjoints G and G' and their specified adjunctions are explicit section binders
  `adj` and `adj'`; their counits are t and t'. These are chosen adjunction data, as
  in the node, not an extra existence hypothesis. The recorded exceptional-adjoint
  module is imported for the existence foundation.
- S_e and S_e' are the exact etaleLowerShriek functors descended by mapDerivedCategory.
  The evaluations are precisely the counits of the recorded
  derivedEtaleLowerShriekUpperStarAdjunction, not replacements with identical endpoints.
- N : EtaleCompactSupportNormalization A is the landed graph/derived-normalized
  comparison interface, owned by def-sp-etale-compact-support-normalization. Its
  nonemptiness theorem is not needed to state this item.
  It supplies the canonical d through etaleCanonicalCompactSupportComparison. Its sheaf
  graph equation and homotopy representative equation pin the map uniquely. This is the
  same interface used by the support-mate and ambient-adjoint-locality nodes; it is not
  an arbitrary choice of natural isomorphism, nor a hypothesis that comparisons commute.
- Delta is exactly `etaleHorizontalSupportMateDelta A ... N`, the landed four-factor
  expression from d, the two specified compositors, and the equality of composites.
  C is exactly `etaleHorizontalSupportBaseChangeIso A ...`; its hom is the existing
  compact-support exchange and its inv is the C inverse in the statement.
- etaleHorizontalDoubleCounitIso constructs b as the conjugate of delta inverse under
  `(sumAdj_e').comp adj` and `adj'.comp sumAdj_e`. It is a natural isomorphism by
  construction, not selected from a Nonempty existence theorem.
- etaleHorizontalDoubleCounit_compositors identifies this construction with the node's
  literal formula. Ge, Ge', Gd and ae, ae', ad allow arbitrary specified right adjoints
  for e, e', and their common composite. The first whiskered factor is rho_e' inverse;
  the second is c_h,e' inverse; the third is c_e,h'; the last is G'(rho_e). The third
  compositor is transported across sq.toCommSq.w, so both use the very same composite
  adjunction ad. Rho is conjugateIsoEquiv of d inverse, in exactly the node's direction.
- The first conjunct of etaleHorizontalDoubleCounit is the displayed double-counit
  equation. Lean's `≫` is diagrammatic, so it reads S_e(F_h'(b) ≫ t') ≫ ev_e on the
  left and delta inverse ≫ F_h(ev_e') ≫ t on the right. Its domain is exactly
  S_e F_h' e'^* G K, and its codomain K.
- The second conjunct is F_h'(b) ≫ t' = C inverse ≫ e^*(t), the displayed single
  counit, at every K. The third conjunct states the concluding adjunct assertion via
  adj'.homEquiv. This is the same equality under the bijection, not another condition.
- Naturality in K is carried by the natural isomorphism and by equality of natural
  transformations in etaleHorizontalDoubleCounit_exchange. The helper
  etaleHorizontalCounitRightExchange is exactly mateEquiv of C inverse.
- etaleHorizontalDoubleCounit_refinement states the commuting comparison square for
  proper refinements c -> d and c' -> d'. It allows arbitrary fixed-compactification
  adjunctions on both sides, transports each along rightDerivedLowerShriekIso, and
  uses the conjugates of the inverse canonical refinement comparisons on the right
  adjoints. It also allows different normalization families N and M. The refinement
  normalization theorem identifies these common-refinement maps with the specified
  proper-refinement maps, including noncartesian refinements. Horizontal choices and
  composite compactifications are already absorbed by the canonical alpha and d.
- etaleHorizontalDoubleCounit_openRestriction states the full cube comparison square.
  jX, jX', jY, jY' are open immersions; leftsq and rightsq are Cartesian vertical
  restriction faces; topsq and bottomsq give horizontal compatibility. The barred
  square is itself the recorded chosen Cartesian square. On the first path one uses
  b followed by the right-adjoint restriction mate for h'. On the second path one
  uses the canonical inverse-image square, the restriction mate for h, barred b, and
  the inverse canonical inverse-image square at the target. The restriction maps are
  defined by the same inverse exchange and specified adjunctions, not arbitrary maps.
  Since both counit equations are already asserted for each square, their natural
  comparison square and these counit-preserving mates also transport those equations.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom.
- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing; scheme Noetherian instances
  use Mathlib.AlgebraicGeometry.Noetherian.
- Sheaf.AlgebraicGeometry.ChosenCartesianSquare: ChosenCartesianSquare and its fields.
- The scheme-morphism-properties node is a convention collector, not a new structure:
  use IsSeparated, LocallyOfFiniteType, QuasiCompact, and IsOpenImmersion.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: Etale.
- WeilConjectures.Compactification.Refinement / RefinementCategory: Compactification,
  Compactification.Refinement; the latter is the current source owning Refinement.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients: DerivedCategoryModule.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  rightDerivedLowerShriekOfCompactification and rightDerivedLowerShriek.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint:
  isLeftAdjoint_rightDerivedLowerShriekOfCompactification (existence foundation).
- WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap: etaleLowerShriek.
- Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality, through the current upstream
  EtaleMapProjection declaration: derivedEtaleLowerShriekUpperStarAdjunction.
- Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact:
  quasifiniteCompactSupportExact, the existence/normalization foundation for d.
- Mathlib.CategoryTheory.Adjunction.Mates: conjugateIsoEquiv, conjugateEquiv,
  mateEquiv and mate-pasting identities. Mathlib.CategoryTheory.Adjunction.Basic:
  Adjunction.comp, its counit formula, mkOfHomEquiv and homEquiv.
- Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons:
  unboundedEtaleLowerShriekCompIso, unboundedEtaleLowerShriekCongr, and canonical
  exchange/refinement normalization.
- Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate:
  etaleCanonicalCompactSupportComparison, etaleHorizontalSupportMateDelta,
  etaleHorizontalSupportBaseChangeIso (the three definitions are now owned by
  def-pur-etale-horizontal-support-comparisons); etaleHorizontalSupportMate is a
  proof dependency only.
- Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization:
  EtaleCompactSupportNormalization, cited through the existing definition node
  def-sp-etale-compact-support-normalization. Its nonemptiness conclusion is unused
  in the statement.
- Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility:
  etaleSupportMapCompatibility, used for the open-restriction normalization proof.

The statement dependencies now cite def-sp-etale-compact-support-normalization for N
and the new existing-definition ownership node
def-pur-etale-horizontal-support-comparisons for d, delta, and C. The support-mate
theorem stays in proof_deps only; its conclusion is unnecessary to state the item.
Nothing in the natural-language statement or Lean module changes.

Edge cases checked mathematically before writing: h or e an identity, e an open
immersion, empty schemes, the zero ring, K zero, arbitrary unbounded K, arbitrary choices
of the intermediate right adjoints, identity refinements, noncartesian proper refinements,
and empty further open restrictions. No counit is assumed invertible, and neither S_e
nor e^* is assumed faithful. The domain/codomain and all four factor directions in the
compositor formula were checked separately. All universes and variables are explicitly
bound, with autoImplicit false. No local notation or private instance enters a statement.

Searches on 2026-10-21 (msearch.py, group Q83, this item):

- leanfinder: "etale horizontal cartesian square right adjoint comparison double counit
  compact support exchange" returned 8 general/condensed adjunction results; no exact
  etale derived-category statement.
- loogle: "conjugateIsoEquiv, Adjunction.comp" returned zero hits with an unknown-name
  diagnostic from the remote index. Directly read the pinned Mathlib declarations;
  both exist and are used here.
- grep, CategoryTheory/Adjunction: "conjugateEquiv.*counit|comp_counit_app" returned
  Adjunction.comp_counit_app and conjugateEquiv_counit / counit_symm (6 hits total).
  These provide the categorical identities, not this geometric theorem.
- leansearch: "The mate of the inverse exchange in an etale horizontal square equals
  the composition comparison of right adjoints and satisfies the composite counit
  identity" returned 8 hits including mateEquiv_square, mateEquiv, mateEquiv_counit_symm,
  and bicategorical analogues; no full geometric statement.
- rg in both lean/WeilConjectures and lean/Sheaf for horizontalDouble, doubleCounit,
  double_counit and the item id found no existing statement. The prescribed grep -rn
  of the exact blueprint id in lean/WeilConjectures also found no match. Broader
  conjugate/counit searches found the ambient and support-mate foundations reused above.

No STATEMENT-DISPUTED flag or node fault. Validation uses scompile.py only; the dry-run
and delivery wrapper results are the authoritative compile/preflight records.

## Second reading by Q83

The dispatcher's instruction forbids starting another agent; this is a separate rereading
by the same worker, with independent maintainer review to follow delivery. I reread the
node alongside the complete module and checked every clause in the mapping above.
The first draft used IsPullback directly; the final interface retains the dependency's
ChosenCartesianSquare and passes its recorded identification to IsPullback.of_iso_pullback.
I checked the contravariance order against conjugateIsoEquiv's signature: rho is the
conjugate of d inverse; c maps the common right adjoint to the composite right adjoint.
The compositor equation therefore has rho_e' inverse, c_h,e' inverse, c_e,h', rho_e in
that order. The comparison for equal composites is explicitly inserted. I checked the
open cube paths at their common source G e'^* jX'^* and common target e^* jY'^* H'.
The direct path uses b then r_h'; the other uses topsq, r_h, barred b, bottomsq inverse.
The refinement equation uses conjugates of F_d -> F_c, giving G_c -> G_d, which is the
required direction. Every theorem has only sorry and its proof plan in its docstring;
the two definitions use existing explicit equivalences with no postponed data.


## New nodes

`def-pur-etale-horizontal-support-comparisons` owns exactly the three existing
plain definitions in `Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate`:
`etaleCanonicalCompactSupportComparison`, `etaleHorizontalSupportMateDelta`, and
`etaleHorizontalSupportBaseChangeIso`. It has `existing: true`; the published module
is unchanged and no duplicate declaration is delivered. Clause (1) spells out the
chosen-compactification inverse followed by N.comparison, clause (2) spells out the
two d whiskerings and the two alpha factors with the equality congruence, and
clause (3) is asIso of the canonical exchange. The latter uses the invertibility
conclusion of lem-amb-unbounded-compact-support-comparisons, already a statement
dependency of the item; it does not use the horizontal-support-mate theorem.
The three clauses retain the definitions' separate hypotheses: separated
quasi-compact etale a in (1); quasi-compact f,f', separated quasi-compact etale
v,v', and compactifications of all four and both composites in (2); separated
finite-type f, quasi-compact f', and their compactifications with arbitrary
base change in (3). All schemes are Noetherian and coefficients finite of Type
(u+1). No existence assertion for a normalization family is added.

Sources read: Stacks more-etale.tex Tags 0F7J, 0F7K, 0F7L, and
etale-cohomology.tex Tags 03S6 and 0F4L; the current blueprint co-smooth etale
locality Step 1. The new node records the actual LeanSearch, LeanFinder, and
Mathlib grep responses from searches.jsonl, plus the project/DAG/blueprint searches.
Mathlib has no exact comparison construction. Project grep finds the three exact
definitions in EtaleHorizontalSupportMate.lean at lines 28, 43, and 78.
DAG grep finds only the support-mate theorem node, which does not supply a
separate definition node. Both blueprint_refs searches returned zero matches;
blueprint_refs ancestor returns thm-pur-composition-coherence. The new node
therefore adds definition ownership while reusing the existing Lean code.

## Repair of independent return L (head 9574abe22c2c)

H2 repaired: removed lem-asd-etale-compact-support-normalization and
lem-pur-etale-horizontal-support-mate from the item's added stmt_deps. Cited the
existing def-sp-etale-compact-support-normalization and the new definition node
above instead. The support-mate theorem remains in proof_deps. The Lean module,
its signature, the item statement and all other base fields are unchanged.
The initial saved-packet dry run passed at 3d7579d1f95, but that mechanical check
did not resolve the independent review's H2 finding; these node/report edits do.

Second reading of the repair by Q83: opened all three definitions and their full
signatures, the normalization definition record, and the unbounded comparison
interface. Checked d's inverse direction, delta's five Lean factors (including
congruence), and C.hom as the actual exchange. The new node contains no counit
identity and cites no support-mate theorem. Identity arrows, empty schemes, zero
ring, and arbitrary unbounded complexes introduce no extra condition. Compared
the saved item against current main: before this repair only lean and stmt_deps
differed; after it the same field boundary holds. The returned module is retained
byte for byte. No other agent was started, as the dispatcher requires.


Repair validation: scompile.py compiled the unchanged item cleanly (30.0 s sandbox,
12.9 s library). The first repaired-packet dry run compiled both modules and found
one metadata issue: grouped definition citations were not recognized individually.
Changed them to separate [id] citations. Also recorded the existing delta signature
from the `def` keyword, matching the preflight's declaration reader. No Lean or
mathematical statement changed during these formatting repairs.
