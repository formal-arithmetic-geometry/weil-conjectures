## Worker report

The module defines `AlgebraicGeometry.lerayLowDegree` in
`lean/Sheaf/AlgebraicGeometry/LerayLowDegree.lean`.  It states that for a scheme
morphism `f` and a quasi-coherent module `F` there exist four consecutive maps,
from the zero object through `H^1(Y,f_*F)`, `H^1(X,F)`,
`H^0(Y,R^1f_*F)`, and `H^2(Y,f_*F)`, whose `ComposableArrows.mk₅` is exact.
The final conjunct states that if the first higher direct image is zero (`IsZero`),
then the first two cohomology terms are isomorphic.

The displayed Lean terms use `RingedSpace.moduleCohomology`,
`RingedSpace.moduleDirectImage ... .rightDerived`, and `forget₂` to
`AddCommGrpCat`; the first arrow is from the categorical zero object, and each
of `a`, `b`, `c`, and `d` renders the corresponding arrow in the exact sequence.
The final `∀ hzero` clause renders the `R^1 f_* F = 0` hypothesis and the
`Nonempty` isomorphism conclusion.

Dependency used: `Sheaf.AlgebraicGeometry.LeraySpectralSequence`, declaration
`AlgebraicGeometry.exists_leray_spectralSequence` (the Leray spectral sequence).
The generic five-term statement is imported from
`Sheaf.CategoryTheory.LerayFiveTerm`; its edge-map identification is recorded
in the node proof and is left for stage 3.

Edge cases checked in the statement design: the zero object is explicit, `F = 0`
and identity morphisms are admitted, and `R^1 f_* F` is expressed as a categorical
zero object rather than by an extra nonzero hypothesis.  The index universe is
that of the schemes (`v`).

Searches: `rg -n 'Leray|five.?term|moduleCohomology' lean/Sheaf` found the
existing Leray spectral sequence and generic five-term modules; grep of Mathlib
and `WeilConjectures` found no theorem stating this scheme-cohomology low-degree
sequence.  `msearch.py` leanfinder query “low degree Leray exact sequence for
scheme cohomology” and loogle query “Leray five term spectral sequence” returned
no exact existing declaration.

## Earlier second reading (a previous round; superseded)

The statement was re-read against the blueprint clause by clause.  The four
maps and exactness predicate render exactly the displayed five-term sequence;
the final universal vanishing clause renders the stated isomorphism consequence.
No statement correction or dependency correction was needed.

## Second reading by C1

Read the node copy, the blueprint source paragraph, Stacks `cohomology.tex`
lines 2212–2248 (Tag 01F2, `lemma-Leray` and its following remark), the recorded
`pqf-lem-leray` node and `LeraySpectralSequence.lean`, and the declarations of
`pqf-def-cohomology`, `def-sc-ringed-space-module-cohomology`, and
`def-pc-ringed-spaces-derived-direct-image`. Also read the existing
`def-weil-pbc-module-cohomology-fmap` node and its module, including the
resolution-based definition and the identity-map specialization defining the edge.
Stacks assumes arbitrary ringed spaces and a bounded-below complex; F[0] is such
an object. The blueprint specializes to schemes and quasi-coherent modules.
There is no additional Noetherian, separation, finite-type, or base-field assumption.

Clause-by-clause list and verdicts (after repairs):

- Objects X and Y: `{X Y : Scheme.{v}}`; arbitrary schemes, matching the node.
- Morphism f: `(f : X ⟶ Y)`; no property instance on f. Matches.
- O_X-module F: `SheafOfModules.{v} (moduleRings X.toRingedSpace)`; the recorded
  module-sheaf category, not abelian sheaves or an unrelated coefficient ring.
  Hypothesis `[F.IsQuasicoherent]` is precisely quasi-coherence. Matches.
- Initial zero: `(0 : AddCommGrpCat.{v})` and its unique zero arrow in `mk₄`.
  Matches. The redundant extra zero in the original `mk₅` has been removed.
- H¹(Y,f_*F): `moduleCohomology Y.toRingedSpace 1` applied to
  `(moduleDirectImage f.toLRSHom.toShHom).obj F`, with global-section scalars
  forgotten to abelian groups. Direct image is the shared sectionwise module
  pushforward. Matches the displayed term literally.
- H¹(X,F): `moduleCohomology X.toRingedSpace 1` applied to F, with the same
  forgetful functor. Matches. Cohomology is derived global sections in O-modules.
- First nonzero arrow: `Scheme.Modules.moduleCohomologyEdgeMap f F 1`, defined
  from the identity on f_*F by the recorded h-map construction. It replaces an
  unconstrained existential b, so exactness now applies to the canonical edge.
- R¹f_*F: `((moduleDirectImage f.toLRSHom.toShHom).rightDerived 1).obj F`.
  This is the shared higher-direct-image encoding used by `pqf-lem-leray`.
- H⁰(Y,R¹f_*F): `moduleCohomology Y.toRingedSpace 0` applied to that object,
  forgetting scalars to Ab. Matches; no positive-degree assumption excludes zero.
- H²(Y,f_*F): `moduleCohomology Y.toRingedSpace 2` applied to the ordinary
  direct image, forgetting scalars. Matches.
- Remaining arrows and exactness: existential c from H¹(X,F) to H⁰(Y,R¹f_*F),
  and d from that group to H²(Y,f_*F); `mk₄ 0 (moduleCohomologyEdgeMap f F 1) c d`
  is Exact. Reading Mathlib's `ComposableArrows.Exact` confirms exactness at
  precisely H¹(Y,f_*F), H¹(X,F), H⁰(Y,R¹f_*F), with no surjectivity requirement
  at the terminal H². The source does not separately quantify naturality or a
  formula for these two arrows; the proof constructs them by the Leray left edge
  and transgression. Matches the displayed exact-sequence assertion.
- Vanishing consequence: for every `_hzero : IsZero (R¹f_*F)`, `Nonempty`
  of the isomorphism between the two H¹ groups. Matches; the order of the two
  sides is reversed in the Lean iso, equivalently the stated iso by symmetry.
  The vanishing hypothesis occurs only in this consequence, not in exactness.

Edge cases: empty schemes and F = 0 are allowed, with no nonempty/nonzero
assumption; the identity morphism is allowed. No index family is introduced, so
empty index sets are irrelevant. Degrees 0, 1, 2 are the literal nonnegative
cohomology indices of the source; n = 0 is present in the H⁰ term rather than
excluded by a positivity hypothesis. No characteristic or field is specified.
The universe v is arbitrary and shared by the schemes, their module sheaves and
Ab-valued cohomology as in the dependency. Objects from different small universes
can be viewed in a common larger universe; no independent test universe or
smallness instance restricts the assertion. All binders and v are bound.

Independent searches: `msearch.py` LeanFinder query “five term exact sequence
higher direct image cohomology” returned group-cohomology long-exact-sequence
lemmas, not this statement. Loogle query `CategoryTheory.Functor.rightDerived`
returned the right-derived functor and `rightDerivedZeroIsoSelf`, not the Leray
sequence. LeanSearch query “Leray cohomology exact sequence direct image” was
unavailable (Internal Server Error); no negative verdict inferred from that.
Grep search “transgression|lowDegree|low_degree|fiveTerm|five_term|lerayLowDegree”
in Mathlib found only group (co)homology infrastructure. My separate rg of the
project and WeilConjectures found and opened the generic `LerayFiveTerm`, the
scheme Leray spectral sequence, `OpenCurveEtaleLerayLowDegree`, and the upstream
étale `UpperLowerStar/EdgeMap` and generic Ext `MapBijective` modules. The étale
modules concern abelian étale sheaves and injectivity only; the generic Ext
result requires an exact left adjoint. None states this Zariski O-module
four-arrow sequence for arbitrary scheme morphisms. No exact existing match.
The shared module cohomology, direct image, and canonical bottom edge are reused;
no new definition node or dependency module is needed.

Mismatches repaired: the displayed ordinary direct-image terms had been rendered
as zeroth right-derived objects without explaining their identification; they
now use direct image itself. The first nonzero arrow was existential and is now
the existing canonical edge map. Removed the redundant leading zero arrow and
its existential arrow a, using `mk₄`. Repaired the source docstring's parentheses,
made the natural-language proof include the R⁰ comparison and the injective/
surjective argument, removed the unused generic five-term import, and split the
long vanishing binder. No node statement correction was required: its objects,
hypotheses, displayed sequence, and consequence are right as written. No
`statement_change` or new nodes are present. The worker report above describes
the earlier signature and is retained as requested; this reading supersedes it.

The only proof remains `AlgebraicGeometry.lerayLowDegree := by sorry`; no
hollow definition, new axiom, private copy, local notation, or proved theorem.
The node's `lean.statement` was synchronized verbatim with the repaired signature.
Server single-file compile completed cleanly in 3.8 seconds, without warnings.
