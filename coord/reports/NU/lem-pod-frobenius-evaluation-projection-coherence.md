## Worker report

The delivery states the evaluation, ordinary projection, open tensor/base-change square,
its coefficient images, the compactification projection, and refinement compatibility.
All theorem proofs are `by sorry`. The two local comparison records contain actual data
and representative normalizations, and no definition chooses from an existence theorem.
The TeX statement and proof are unchanged. The only extra statement dependency is the
already landed `def-pod-constructible-weil-model-squares`, for its `Models` abbreviation
and the two finite-type instances; no model square or separatedness condition is added.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors/`
`sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md`, especially the ordinary-adjunction,
evaluation and projection paragraph. The node's six proof steps are distributed among
the declaration docstrings. The module imports the recorded proof dependencies that have
Lean statements. The semilinear exchange-cube node has no recorded Lean statement; its
supplied Weil refinement comparisons are input in the final transport calculation, as
specified in the node, rather than a new construction in this delivery.

Hypothesis and clause correspondence:

* The finite field, its characteristic and algebraic closure are `D : FiniteFieldDatum`.
  Rational evaluation uses `C : D.CoefficientDatum`, hence its prime `C.l` and
  `C.different`; common evaluation writes `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p`
  explicitly. `E`, its field/algebra/finite-dimensional instances, and `Ω` with
  `[IsAlgClosure (Padic l) Ω]` are the two coefficient cases. The common-stage
  coefficient universe `v` is independent of the scheme universe `u`.
* `X : Models D` is every finite-type model, without a structural separatedness
  instance. `D.geometricFiber X.obj` is W and `D.geometricFrobenius X.obj` is g_W.
  `hP` fixes P to the actual `sfWeilFrobeniusPullback` or its common-stage version.
  The residue-prime inverse in the tensor and closed-structure expressions is exactly
  `sfWeilPrimeInvertible D ...`; it is not an extra invertibility hypothesis.
* `M N : IsoAlgebra P` supply the given invertible Weil structures. The definition of
  its morphisms is the stipulated commutative square. `IsoAlgebra.mapOfNatIso` and
  `mapOfNatIso₂` are the standard one-variable and tensor lifts. In the evaluation
  equations, `M.str.inv.op` is contravariant Hom transport and `N.str.hom` is covariant.
  `κ` precedes these maps and is componentwise normalized to
  `podRationalHomComparison` / `podCommonHomComparison`. `μ` is normalized to the
  corresponding canonical pullback tensor comparison.
* `h : constructibleRationalHomPairs ... (op M.carrier,N.carrier)` (respectively
  `commonStageHomPairs`) retains the exact allowed internal-Hom domain. `H`, `T` and
  `SC` are typed aliases, fixed by equality/heterogeneous equality to the published
  internal Hom, tensor, and partial closed structure. This avoids expensive repeated
  elaboration of the same derived categories. `hJ` expresses the published closure
  of that pair domain under the automorphism. It is supplied by the recorded
  `podRationalPairs_pullback` or `podCommonPairs_pullback`, not a smaller pair domain.
  The canonical signed braiding `β` changes the published Hom-first evaluation to
  `podArgumentFirstEvaluation`, so the conclusion is exactly the argument-first
  displayed equation, including `theta_M` and inverse Hom input. No perfectness or
  invariant-lattice assumption is introduced.
* The projection portion uses exactly the categorical supplied-domain interface of
  `def-exchange-projection`. Its categories X, B and Y are the stipulated closed full
  operation domains, and L/R (or jStar/J and P/R) their actual operation functors.
  Thus finite Tor, lattice presentations and witnessed-origin restrictions remain
  restrictions of these domains. This is not an assertion that higher-coefficient
  operations exist on an unrestricted ambient category. The geometric separated
  finite-type f is what supplies J, P and R through its compactification; no absolute
  separatedness or additional geometric existence claim enters this calculation.
* In `ordinary_projection`, `adj` is the ordinary adjunction; `_unit`, `_counit` fix
  the lifted adjunction's carrier maps to its actual unit and counit. `_mu` fixes the
  lifted tensor comparison. The conclusion gives a morphism of Weil pairs whose
  carrier is literally `adj.rightAdjointProjectionMap mu.hom`, namely the unit
  followed by R of tensor comparison then counit tensor identity. It does not ask
  for, or conclude, invertibility of this projection.
* `OpenSquare.open_square` uses the recorded `Input`, `SiteSquare`, `Operations`
  and normalized `Assertion` of `lem-sf-open-tensor-normalization`. These retain the
  actual open immersions, site square, coefficient map, derived pullbacks and open
  adjunctions. The parameter `Mode` includes ordinary coefficients and the vertical
  site of strict inverse systems with arbitrary coefficient transitions. In
  `OpenSquare.PullbackTensor`, `pure_unit` characterizes the ordinary comparison by
  insertion of one; `representative` fixes the derived comparison on flat K-flat
  pairs using the signed total map. These characterize the canonical maps, rather
  than accepting an arbitrary tensor isomorphism. `Transport` also retains the
  primed restriction comparison and characterizes `gammaPrime.inv` by the specified
  adjunction transpose. `transport_exists` states existence of these canonical
  comparison presentations. No data are chosen from it by a definition.
* The left route in `open_square` is pullback of gamma, then beta at the tensor
  object, then j'_! of the tensor pullback comparison and pullback compositor.
  The right route is ambient tensor pullback, beta tensor identity, then primed
  gamma. In particular `o.theta.inv.app N` inserts exactly
  Ls* j* N -> j'^* Lt* N. Endpoints are the node's two displayed derived objects.
  The theorem is already an equality of derived system morphisms, without finite
  evaluation detection. Its general site-square form includes the Frobenius square;
  semilinear relabelling changes the structure map, not the sites or these arrows.
* `realized_open_square` applies the actual
  `exchangeProjectionCoefficientRepresentative F s z` to both routes. This is the
  dependency's endpoint-conjugated image of a given component. Taking F to be the
  supplied integral realization gives its square; composing with localization gives
  the rational square; taking the common-field inclusion gives the common-stage
  square. The same equality holds for every common-stage representative and every
  endpoint comparison, so neither the identity stage nor a further field lift is
  discarded. The dependency's coefficient identity/tower comparisons identify the
  displayed images with the actual supplied maps. No faithfulness is assumed of F.
* `open_projection` uses the actual open gamma, fixed by `_normalization` to have
  inverse `jAdj.projectionMap ... mu.inv`. Its output Weil map has precisely gamma
  as carrier. Its unit/counit and tensor restrictions are precisely the hypotheses
  already assumed Weil in the node.
* In `compact_projection`, `gammaP` includes the open gamma evaluated at P N and the
  pullback compositor `phi : P ⋙ jStar ≅ F`; `_gammaP` states that formula component
  by component. `phiW` with `_phi` says that this given compositor is Weil. The
  conclusion's carrier is literally `compactificationProjectionFromData J F P R ...`,
  hence Rp_*(gamma) pi_p with the actual f-pullback target. Proper/open unit, counit
  and tensor lifts have explicit carrier normalizations, not arbitrary adjunctions.
* `refinement_compatibility` promotes the supplied underlying canonical rho identity
  to equality of Weil arrows. `refinement_transport` starts with only the specified
  second underlying projection and the canonical comparison identity; it concludes
  existence of its Weil lift and the equality. The first projection may come from a
  model compactification (Nagata and base change are imported proof dependencies),
  while the second can be an arbitrary geometric compactification. Only rho is
  inverted. The underlying identity is precisely the one supplied by
  `FixProjectionCompactification.comparison` / `higherLaw`, keeping its original
  finite-Tor and witnessed-origin domains. The canonical rho's being Weil is the
  supplied refinement-comparison input of this node.

Dependency declarations read and used:

* `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`;
  `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `geometricFrobenius`;
  `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`,
  `sfWeilFrobeniusPullback`, `sfCommonStageWeilFrobeniusPullback`,
  `sfWeilPrimeInvertible`, and their `IsoAlgebra` encoding.
* `Sheaf.Paper.DerivedPullbackTensorHom`: actual rational/common tensor, pullback,
  internal Hom and pair domains. `Sheaf.Paper.DerivedAutomorphismHomEvaluation`:
  `derivedAutomorphismHomEvaluation`, `PodPartialClosed`, `podPairPullback`,
  `podRationalClosed`, `podCommonClosed`, both canonical Hom comparisons and
  `podArgumentFirstEvaluation`.
* `Sheaf.Paper.DerivedPullbackTensorIso`: `derivedPullbackTensorIso`, both
  `canonical...PullbackTensor` comparisons and both signed braidings.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: `ExchangeProjectionStage`,
  `compactificationProjectionFromData`, `exchangeProjectionCoefficientRepresentative`.
  The ordinary projection map is the published `Adjunction.rightAdjointProjectionMap`.
* `Sheaf.SixFunctors.OpenTensorNormalization`: `openTensorNormalization` and the
  exported `OpenTensorNormalization.Input`, `SiteSquare`, `Operations`, `Assertion`,
  `Pullback`, `TensorModel`, `TensorComparison`, and representative maps.
* `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum` and its exact
  stage domains, read to check the supplied-domain typing; no private replacement.
* `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`.
  Proof imports: `IntegralSystemRealization.integralCompactificationSystemRealization`,
  `FixProjectionCompactification.comparison`, `AlgebraicGeometry.NagataCompactification`,
  and `AlgebraicGeometry.HasCompactification.of_isPullback`.
* Already landed `Sheaf.Paper.ConstructibleWeilModelSquares`: `Models`,
  `modelLocallyOfFiniteType`, `modelQuasiCompact`. The new dependency edge is only
  for these existing declarations, not the downstream constructible coherence theorem.

Edge cases checked: empty schemes and zero inputs are admitted; no nonemptiness
condition appears. Structural morphisms can be nonseparated. f is only relatively
separated finite type through its compactification data. Both the finite-field and
algebraically closed coefficient cases are present, with independent Ω universe.
The ordinary and strict-system modes admit identity squares, identity coefficient
maps, arbitrary semilinear transitions and further finite-field representatives.
No n=0 finite coefficient ring is introduced in the field evaluation statements.
The projection may fail to be invertible; the assertions remain statements about
its Weil equation. Hom pair and supplied operation domains are retained unchanged.

Searches before writing:

* `msearch.py ... leanfinder "Frobenius equivariance evaluation internal Hom open
  extension zero compact support projection formula"`: eight hits, chiefly
  `LightCondensed.ihomPoints`, `LightCondensed.ihom_map_val_app`, module tilde
  restriction and ordinary module restriction counits. None states this lemma.
* `msearch.py ... loogle "CategoryTheory.Adjunction.rightAdjointProjectionMap,
  CategoryTheory.Endofunctor.IsoAlgebra"`: no hits; the first name is a project
  declaration rather than a Mathlib declaration.
* `msearch.py ... grep "frobenius.*evaluation|evaluation.*frobenius|projectionFormula"
  CategoryTheory`: no Mathlib hits.
* `msearch.py ... leansearch "Frobenius equivariant evaluation internal Hom and open
  compactification projection square"`: eight hits including `exp.ev`, `ihom.ev`,
  `ihom.ev_naturality`, `expComparison_ev`, `frobeniusMorphism`, Day convolution
  evaluation and residue-field evaluation. These are different categorical or
  scheme evaluations and do not state this constructible Weil result.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for evaluation/Frobenius/projection
  names located the dependencies above. Searching the exact item id found only
  two downstream docstring references in `ConstructibleMateCoherence.lean`, not a
  declaration of this result. That downstream module is not imported.

Validation: `scompile.py NU lem-pod-frobenius-evaluation-projection-coherence` compiled
both the sandbox and library module names cleanly, with no errors or warnings.
Every variable/universe is bound explicitly (`autoImplicit` and `relaxedAutoImplicit`
are disabled). All postponed proofs have source and natural-language proof docstrings.
No statement correction, disputed statement, new independent node or dependency repair.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
