## Worker report

The incoming worker account below is retained. Its dependency-packet and API claims
are historical; the second reading records the final delivery and supersedes them.

The item defines `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedReductionSquare`
in `Sheaf.Paper.CompletedReductionSquare`. This is the square's four edges, with actual
geometric derived objects and canonical maps. Its edge structure asserts no path equality;
commutativity is the subsequent completed-map-reduction theorem. Definitions have real
bodies. Postponed named comparison theorems have `by sorry`, sources, and proof docstrings.

The blueprint definition is order 1341, and its completed-map prerequisite is order 1338.
Stacks Tags 099N, 099M and 0944 were read for completed pullback, reconstruction and the
perfect projection comparison. No statement correction or new mathematical hypothesis is
made. Several unstated prerequisites and unusable universe-specialized interfaces are
included under the user's recursive-dependency instruction and section 1(B).

Each hypothesis and clause is rendered as follows.

- The schemes are `{X' X Y' Y : Scheme.{t}}`; the four morphisms and
  `sq : ChosenCartesianSquare g' f' f g` retain the chosen Cartesian square. `[IsProper f]`
  is precisely properness of its original direct-image arrow.
- `{A : Type (t+1)} [CommRing A]` and `d : AdicCoefficientDatum A` reuse the published
  complete coefficient datum structure: Noetherian ring, finite generating sequence for
  the ideal, additive-torsion first quotient, and finite perfect positive quotients. The
  coefficient ring need not itself be complete. Coefficients stay in universe t+1 while
  site objects and morphisms stay in t+1 and t.
- `K : d.derived X` lies in the derived category over the actual inverse-limit coefficient
  sheaf, not the constant A-sheaf. `hK : d.TowerComplete X K` means the specified quotient
  completion unit is invertible. `koszulReconstruction` identifies this with intrinsic
  completeness; no extra completeness assumption is imposed on ordinary pullback.
- `W : ∀ n, ConstantEtaleOriginWitness X (A ⧸ d.ideal ^ (n+1)) ((d.reduction X n).obj K)`
  retains the separate bounded-below etale-origin witnesses. There is no common lower
  bound and no compatibility condition on the choices of witnesses.
- `d.fourCorners ... K n` lists A_n, B_n, C_n, D_n in that order. They use the actual
  completed and finite coefficient pullback/direct-image functors. `d.fourArrows` supplies
  h_n, h'_n and v'_n from their projection adjuncts and normalized finite exchange.
- S is `(d.completedPull g).obj ((d.push f).obj K)` and T is
  `(d.push f').obj ((d.completedPull g').obj K)`. The upper vertices in the edge structure
  are their actual `d.reduction Y' n` images. The lower vertices are corners 1 and 3.
- `completionDirectImageComparison` is chi: derived limit of `towerProjection`, followed
  by inverse `directImageRlimIso`, then pushforward of inverse
  `completedPullCompletionIso`. This last factor supplies the specified identification
  of completion of ordinary pullback with completed pullback.
- The displayed quotient-transition equality for the projection-formula family is
  represented by the single strict derived tower morphism `d.towerProjection f' E`.
  Its level identification is `d.towerProjection_evaluation`; its construction is the
  adjoint of the normalized strict quotient/pullback comparison followed by the actual
  counit. Consequently quotient transitions are retained before applying Rlim. These
  towers live over the completed ambient coefficient sheaf, after scalar restriction;
  the displayed sigma, tau and square edges live over the finite quotient sheaf.
- `completedReductionSigma` is the canonical `completedPullReduction` of Rf_* K; the
  complete-input hypothesis follows from `d.directImageLimits f K hK`.
- `completedReductionTau` reduces inverse chi and then uses
  `quotientCompletionReduction` for M=Rf'_* Lg'^*K. Its invertibility is stated for that
  arbitrary input by `completedDirectImageReduction_isIso`; M is not assumed complete.
- `upper` is literally `(d.reduction Y' n).map (d.completedBaseChangeMap sq K hK W)`.
  `lower` is literally `(d.fourArrows sq K hK W n).v'`.
  `left` is sigma followed by h_n; `right` is tau followed by h'_n. Thus their order is
  exactly alpha=sigma;h and delta=tau;h'. All four arrows retain quotient ring actions.

The direct imported dependency declarations are
`Sheaf.Paper.CompletedBaseChangeMap` / `AdicCoefficientDatum.completedBaseChangeMap`,
`Sheaf.Paper.CompletedDirectImageLimits` / `AdicCoefficientDatum.directImageLimits`,
`Sheaf.Paper.CompletedPullbackReduction` / `completedPullbackReduction`,
`Sheaf.Paper.KoszulReconstruction` / `koszulReconstruction`, and
`Sheaf.Paper.PerfectProjectionFormula` / `perfectProjectionFormula_locus` (all in
`AlgebraicGeometry.Scheme`). Transitive construction declarations and their owners are
listed below. The existing `ChosenCartesianSquare` and completed coefficient datum are
imported unchanged. The canonical composition comparison is reused from
`Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange`; K-flatness, resolutions and
independent-coefficient derived scalar extension use the published upstream declarations.

Edge cases checked: n=0 denotes exponent one, so no I^0 term is introduced. I=0 gives
identity quotient transitions and a constant tower. I=top allows zero quotient rings,
and the complete subcategory has the expected zero objects. Zero complexes, empty schemes
and identity Cartesian squares impose no nonzero or nonempty assumptions. The definitions
work for every positive level and do not ask for witness compatibility. No division by
an ideal generator occurs. Ordinary pullback and its direct image may be incomplete: rho
for the right edge is justified by arbitrary-input reduction of completion.

Searches: `msearch.py NB ... leanfinder` with "Four edges of the derived completed proper
base change reduction square" returned eight unrelated categorical-square declarations,
including CatCommSqOver and Arrow squares. `loogle` with `"DerivedCategory", "baseChange"`
returned zero hits. Mathlib `grep` with `completed.*[Rr]eduction|completedPullback` in
CategoryTheory returned zero hits. `rg` over WeilConjectures and lean/Sheaf found general
adic coefficient reductions but no declaration of this square. Node-id search found no
upstream implementation. The recorded dependency sources and relevant delivered Q03,
Q06 and Q23 branches were inspected; they supply alternate coefficient presentations but
not the canonical strict-tower interface used here. Source probes used `scompile.py
--source`; branch reads were read-only. The local earlier canonical prerequisite draft
was used as a starting point, with the published composition comparison reused and the
identity-compactification duplicate-docstring defect repaired. No independent second
reading is claimed by this worker.

## Second reading by NB

I independently read the item node, its blueprint definition (order 1341), the fourteen
statement-dependency nodes and their current recorded declarations. I read Stacks
`proetale.tex`, the Noetherian complete-coefficient discussion and pushforward lemma
(Tags 099M/099N, around lines 4260–4395), and `sites-cohomology.tex`, the derived-limit
comparison and canonical projection-formula counit (Tag 0944). These sources assume
the Noetherian adic datum, perfect finite quotients, the chosen Cartesian square with
proper f, and a complete K with a separately retained bounded-below etale-origin pair
at each positive level. They impose no uniform lower bound or completeness of ordinary
pullback. The blueprint deliberately defines four edges without a commutativity claim.

Clause-by-clause list, with the node, source and final Lean open:

1. Coefficients — PASS. `{A : Type (t + 1)} [CommRing A]` and
   `d : AdicCoefficientDatum A` reuse the actual completed coefficient ring
   `d.completedRing T`, the finite function-sheaf quotients `d.finiteRing T n`, and
   their specified projections. The datum supplies Noetherianity, finite generation,
   torsion and finite perfect positive quotients. No field, nonzero, additional
   Noetherian or coefficient-completeness assumption is introduced.
2. Geometry — PASS. `{X' X Y' Y : Scheme.{t}}`, the four named arrows,
   `sq : ChosenCartesianSquare g' f' f g`, and `[IsProper f]` are the given
   chosen Cartesian square and precisely its proper original arrow. No properness
   assumption is added for g or g'.
3. Input — PASS. `K : d.derived X` is over the completed coefficient sheaf.
   `hK : d.TowerComplete X K` is invertibility of the canonical quotient completion
   unit. The current `d.towerComplete_iff_intrinsic` identifies this with intrinsic
   Koszul completeness, without a new mathematical hypothesis. The input need not
   be bounded below.
4. Origin pairs — PASS after API repair. `W : ∀ n : ℕ,
   FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1)) ((d.reduction X n).obj K)`
   retains an actual bounded-below etale complex and its comparison isomorphism after
   the canonical finite-function/constant-ring transport. There is neither a uniform
   lower bound nor a coherence requirement on W. This is the current published
   witness used by `fourArrows` and `completedBaseChangeMap`.
5. Finite corners and arrows — PASS. The current `d.fourCorners ... K n` gives
   A_n, B_n, C_n, D_n at indices 0,1,2,3, with C_n the reduction of
   ordinary Rf'_* Lg'^* K. `d.fourArrows ...` supplies the specified h_n,
   h'_n and finite exchange v'_n. These are canonical projection adjuncts and
   finite proper base change, with their quotient coefficient actions.
6. Completed objects — PASS. S is `(d.completedPull g).obj ((d.push f).obj K)`;
   T is `(d.push f').obj ((d.completedPull g').obj K)`. The first two arguments of
   `CompletedReductionSquareEdges` are exactly their finite reductions. Its remaining
   arguments are `fourCorners ... 1` and `fourCorners ... 3`, namely B_n and D_n.
7. Sigma — PASS after interface repair. `completedPullReduction` is defined by the
   normalized strict tower/pullback comparison, the adjunct of the actual derived
   limit projection, and inverse `d.chi`. `completedReductionSigma` is its asIso
   on Rf_*K. The named `completedReductionSigma_isIso` states exactly this node's
   sigma invertibility, using completeness of Rf_*K from the direct-image lemma
   and finite reduction of completed pullback. No arbitrary map or isomorphism is chosen.
8. Completion and rho — PASS. `d.quotientCompletion` is the strict quotient tower
   followed by the published `completedRlim`. `quotientCompletionEvaluation` uses
   the existing `completedRlimProjection` and normalized K-flat evaluation.
   `quotientCompletionReduction` is its extension/restriction-of-scalars adjunct,
   retaining the finite quotient action.
9. Chi and its tower compatibility — PASS. `completionDirectImageComparison` is
   Rlim of `d.towerProjection f' E`, then the inverse of
   `d.directImageRlimIso f'`, then the pushed inverse identification of the completion
   of E with completed pullback. The current `towerProjection` is a single strict
   derived tower morphism, constructed by the tower adjunction from normalized
   `reductionTowerPullbackIso` and the ordinary counit. Its
   `towerProjection_properties` identifies its evaluations with the canonical finite
   projection maps. Thus the node's displayed transition equality is retained before
   taking Rlim, rather than assumed only levelwise.
10. Tau — PASS. `completedReductionTau` reduces the inverse of chi, then applies
    rho for M=Rf'_* Lg'^* K, in precisely that order. The named
    `completedDirectImageReduction_isIso` covers this potentially incomplete M; it
    does not incorrectly apply the complete-input reconstruction theorem to M.
11. Four edges — PASS. `upper` is reduction of `d.completedBaseChangeMap sq K hK W`;
    `lower` is `(d.fourArrows ...).v'`; `left` is sigma followed by h; `right` is
    tau followed by h'. The structure has exactly these four fields. No path equality,
    weakened conclusion, or additional commutativity assertion is included.

Dependency reading and final scope:

- `AdicCoefficientDatum`, `ChosenCartesianSquare`, `RingedEtaleOriginWitness`,
  `FourCorners`, `FourArrows`, `CompletedBaseChangeMap`, and `CompletedPullback`
  are the current published modules for those dependency nodes. Their signatures and
  actual constructions were read, rather than matched by similar names. In particular
  the tower APIs now take d, not d.ideal, and the witness is `FiniteEtaleOriginWitness`.
- `IntrinsicCompletion` supplies `IsDerivedCompleteIntrinsic`; the equivalence needed
  by this item is the current `CompletedPullback.towerComplete_iff_intrinsic`.
- `CompletedDirectImageLimits` supplies the normalized strict pullback comparison,
  actual tower pushforward/adjunction, `towerProjection`, its isomorphism and evaluation
  properties, `directImageRlimIso`, and `push_complete`. This is used unchanged.
- `CompletedPullbackReduction.completedPullback_reduction` and
  `FiniteReductionReconstructionCompleted.finiteReductionReconstructionCompleted`
  state the recorded mathematical dependency nodes in their existing representative
  presentations. Both are imported unchanged. The small canonical interfaces needed
  for sigma and rho in the present strict-tower presentation are constructed in the
  owning square module, under the explicit missing-helper authorization of §1.
  No second full definition of completion or replacement dependency theorem is supplied.
- `KoszulReconstruction.koszulReconstruction`, `PerfectProjectionFormula`, and
  `ProjectionFormulaBaseChangeNaturality.proEtaleProjectionFormulaMate` are read/imported for the source's reconstruction and canonical
  projection comparison. The published canonical projection arrows were also read via
  `scompile.py --source Sheaf.Paper.ProjectionFormulaArrows`; they specify the counit
  mate and finite-total inverse, not a bare existence isomorphism.

Mismatches and repairs:

The incoming packet contained 25 Lean modules and 27 node records from an older
coefficient interface. Several would overwrite newer landed dependencies and remove
APIs used elsewhere. I removed every replacement dependency/new-node file from the
final packet and reused the current published modules. The incoming packet and report
are archived under scratchpad and are not delivered. The final packet contains one
owning Lean module, its node record, and this report.

I replaced the obsolete ProjectionFormulaMap import by its current recorded module,
ProjectionFormulaBaseChangeNaturality. I changed the square from the removed `ConstantEtaleOriginWitness` to the published
`FiniteEtaleOriginWitness`, changed ideal-indexed strict tower uses to datum-indexed
uses, and supplied the canonical quotient completion/evaluation/rho and
completed-pullback comparisons as owning-node helpers. Sigma's postponed invertibility
is specialized to precisely Rf_*K as stated by this node. Chi and rho invertibility
remain the named theorems already required by the node. No dependency node, new node,
unit statement, natural-language item statement, or statement-dependency list changed.
The node's `lean.statement` is copied verbatim from the final signature, and all owning
helpers are listed in `lean.declarations`.

Edge cases — PASS. `n=0` encodes the first positive power, not I^0. The zero ideal
has constant quotient transitions; the top ideal permits zero quotient rings. Zero
complexes, empty schemes, identity squares, empty ideal-generating sequences and all
characteristics remain admitted. There are no divisions by generators and no chosen
nonzero object. The small pro-etale site's object/morphism sizes remain t+1/t, with
coefficient rings in t+1. The generic four-edge structure has independently bound v,w.
There is no extra universe equality. Ordinary pullback and its direct image may be
incomplete, exactly as the rho proof requires.

Independent H4 searches: `msearch.py NB def-weil-pbc-completed-reduction-square
leanfinder` with “Reducing derived adic completion after a direct image, canonical
finite quotient comparison square” returned ordinary adic-completion declarations;
Loogle `"DerivedCategory", "quotient"` returned localization declarations; Mathlib grep
`completed.*exchange|quotient.*completion|reduction.*square` returned ordinary algebra
or categorical results. Independent `rg` searches of Mathlib, WeilConjectures, and
shared lean/Sheaf for square/sigma/tau/chi and the new helper names found no existing
completed reduction square or duplicate helper. Existing general strict tower and
projection comparisons were opened and reused. No new mathematical notion was found
missing, so no new definition node is appropriate.

H5/H6/H8/H9 — PASS. Every definition has actual functor/map data. Each of the three
postponed theorems is a named isomorphism clause explicitly asserted by the owning node
(sigma, chi, rho), has its source/blueprint marker and a complete proof docstring.
There is no proof work, hidden data sorry, private/local duplicate, unnamed axiom or
unbound variable/universe. All declaration lines satisfy the 100-character convention.

Validation: `scompile.py NB def-weil-pbc-completed-reduction-square
lean/Sheaf/Paper/CompletedReductionSquare.lean` passed: the sandbox module and its
library-path module each compiled cleanly (3.5 s and 3.7 s). No warning was emitted.
The obsolete ProjectionFormulaMap import was diagnosed and replaced with the exact
current recorded ProjectionFormulaBaseChangeNaturality dependency before this clean run.
Delivery preflight follows through the prescribed deliver2.py wrapper.

`deliver2.py NB def-weil-pbc-completed-reduction-square --no-push` returned
`OK (dry run)` at e0f97b61b3: the final three-file packet compiles and passes
the current server preflight. No Lean or node change followed that validation;
this sentence records its result before the authorized final delivery.
