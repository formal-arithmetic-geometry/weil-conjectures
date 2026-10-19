## Worker report

Repair of the returned immutable head aa18072b2464. The saved packet was first inspected
and dry-run: commit 8d242db291 passed mechanical preflight and compilation, but self-reading
confirmed that the returned semantic defects were still present. This delivery changes the
Lean interface to repair them; it does not simply re-push that packet.

The item is stated by two declarations in `Sheaf.SixFunctors.ProperOpenProjectionMate`:
`AlgebraicGeometry.ProEtale.properOpenProjectionMate` for ordinary finite coefficients and
`WeilConjectures.IntegralSystemRealization.properOpenProjectionMateSystems` for strict
semilinear systems. The node's mathematical statement is unchanged.

Ordinary hypothesis and clause correspondence:

* `Λ : Type (u + 1)`, `CommRing Λ`, `Finite Λ` give any finite commutative ring, including
  the zero ring. `finiteRingIsNoetherian` supplies the derived flat-pullback instance from
  finiteness; it adds no ring hypothesis.
* `A B C D : Scheme.{u}`, arrows `k r p i`, `IsOpenImmersion k/i`, `QuasiCompact k/i`,
  `IsProper r/p`, and `h : k ≫ p = r ≫ i` are precisely the commutative proper/open
  square. There is no Cartesian-square hypothesis.
* `ProperOpenDerived` is an abbreviation for the ordinary unbounded derived category
  of `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u+1} Λ)`; `ProperOpenPull`,
  `ProperOpenPush`, `ProperOpenShriek`, `ProperOpenTensor` abbreviate the published
  operations, not replacement categories or tensors.
* `StrictTower.squareLift k r p i h` is the canonical map s into `pullback p i`;
  the recorded `squareLift_open` and `squareLift_closed` supply its clopenness.
  `properOpenClopenProjection` is the actual proper-adjunction unit followed by the
  upstream canonical `rightDerivedLowerStarIsoOfIsClosedRange`. Thus it is projection
  onto s(A), identity there and zero on the complementary open.
* `properOpenBeta` transports the existing ordinary open-base-change isomorphism through
  `leftDerivedUpperStarIsoMapDerivedCategory`. `properOpenAlpha` explicitly composes
  this beta, b_! of the clopen projection, the open-extension compositor for bs=k,
  and the pullback compositor for qs=r. Both compositors are normalized by the canonical
  pullback maps and their adjunctions. No alpha parameter or unnormalized map remains.
* `properOpenMate` is `mateEquiv` of this fixed alpha, using the published proper
  adjunctions. Its normalization is the same beta/projector/unit/counit word as
  `StrictTower.alpha/gamma`, on the ordinary site rather than strict constant towers.
* `properOpenProjection` is now an abbreviation of the existing
  `rightDerivedLowerStarProjectionMap` component. This is exactly the counit-defined
  map used by def-exchange-projection, not another local counit definition.
  `properOpenTensorIso` uses the inverse of the recorded open projection isomorphism,
  oriented from tensor after extension to extension after tensor.
* `M : ProperOpenDerived Λ A` and `N : ProperOpenDerived Λ D` are unrestricted
  unbounded objects. The displayed left side is delta_i, i_!(pi_r), canonical pullback
  transport, then gamma at the tensor object. The right side is gamma_M tensor identity,
  pi_p, then R_p(delta_k). `properOpenPullSquareIso` gives P_r P_i = P_k P_p; the same
  transport makes the two codomains agree. All factors are natural transformations,
  so the component identity is natural in both objects.

System hypothesis and clause correspondence:

* `F : FiniteFieldDatum`, prime `l` with `l ≠ F.p`, the finite extension `E` of
  `ℚ_[l]`, finite-type schemes over `Spec F.k` and their compatible scheme morphisms
  render the setting of lem-sf-integral-compactification-system-realization.
  The coefficient rings and adjacent quotient maps are those already fixed by that
  interface, with positive exponent n+1; they are not extra arbitrary coefficient maps.
* `o : Operations l E`, `z : Realizations l E F o` are the universal presentations of
  the actual simultaneous operations supplied by the recorded realization theorem.
  `Operations.push`, `Operations.shriek`, `pull`, and
  `(calculus l E X).systemClosed.tensor` are derived direct image, exact termwise open
  extension, exact system pullback, and the derived tensor over the ring system.
  Their existence is supplied upstream; this theorem is independent of presentation.
* `z.properOpen.gamma` is precisely the intrinsic Gamma_Q: `ProperOpenCoherence.adjunct`
  fixes its adjunct to inverse lambda, and `.canonical` compares it with the actual
  ringed-diagram clopen alpha's proper mate. Hence it is not a free alpha or gamma.
* The same square assumptions and arbitrary `M : System l E A`, `N : System l E D`
  give the before-evaluation identity. The left side uses
  `z.openComparisons.projection i`, the recorded `properProjection r`, transport by
  `z.compositors.square`, and Gamma. The right side uses system tensor of Gamma with
  identity, `properProjection p`, and pushforward of the open projection for k.
  This is equality in `System l E D` itself, with no evaluation or limit functor and
  no Good/normalized/constructibility/Tor condition on M or N.

The full eight-step proof is in the ordinary theorem docstring, including the beta/tensor
square, the (1,0) clopen calculation, both explicit adjunction transposes, arbitrary
unbounded input check, intrinsic Gamma identification, and before-evaluation system
argument. The system theorem also spells out each of these eight steps.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its two
  projections and canonical `pullback.lift`.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the supplied-domain projection
  construction; its first map is the published `Adjunction.rightAdjointProjectionMap`.
  The ordinary specialization is the upstream `ProEtale.rightDerivedLowerStarProjectionMap`.
* `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` and its public arrows module:
  `squareLift`, its clopen instances, `alpha`, `gamma`, `normalizedProperOpenCalculus`.
  The ordinary helper word follows these definitions using the ordinary operations.
* `Sheaf.SixFunctors.OpenTensorNormalization`:
  `SheafOfModules.openTensorNormalization`, ordinary beta, the published
  `derivedOpenImmersionLowerShriekProjectionIso` and tensor/pullback comparison.
* `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`: `Realizations`,
  `ProperOpenCoherence`, `properProjection`, and `integralCompactificationSystemRealization`;
  its public `IntegralSystemOperations` and `IntegralSystemCanonicalBridge` give the exact
  operations, compositors and open normalization used in the system equation.
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent`:
  `rightDerivedLowerStarIsoOfIsClosedRange`; the actual upstream comparison identifies
  clopen direct image with open extension.

Edge checks: identity square (s identity, beta and mate unit/counit normalization),
Cartesian square (clopen projector identity), non-Cartesian fold/refinement square
(the projector selects just the clopen section), empty open/empty scheme, zero complexes,
zero finite ring, and arbitrary unbounded inputs. In the system case no coefficient
transition is inverted and no faithfulness of derived evaluation is used. Site object
universe u+1 and morphism universe u remain distinct; coefficient modules use u+1.

Searches retained from the original packet and repeated in this repair:

* msearch leanfinder, "canonical proper open clopen projection mate tensor compatibility":
  8 general mate/monoidal hits, including frobeniusMorphism_mate; no normalized scheme identity.
* msearch loogle, "CategoryTheory.mateEquiv, CategoryTheory.Adjunction": 12 hits for the
  general mate calculus, not this projection identity.
* msearch grep, "proper.*open.*projection|clopen.*mate", Mathlib CategoryTheory: zero hits.
* rg in upstream WeilConjectures for the item ID: no result; rg for canonical clopen maps
  found the existing ClopenIdempotent comparison, which is reused. rg in shared lean/Sheaf
  found SystemClopenTensorCompatibility, a downstream system specialization citing this item,
  not an existing statement of the ordinary and intrinsic-system clauses together.

No STATEMENT-DISPUTED flag or source statement correction is needed.

## Dependency modules

`def-coef-semilinear-system-models`: compilation of the newly imported system realization
initially stopped in the published SemilinearSystemModels at lines 606, 619, 639 and 663,
with unsolved universe constraints `max (max c r) v = ?u + 1` when inferring projections
of the actual derived change-of-rings model. The same source was confirmed by
`scompile.py --source Sheaf.Paper.SemilinearSystemModels`. The dependency repair preserves
all definitions and statements and makes the ordinary scalar-extension projection's
universes explicit through `ScalarData.ordinary`, `.object_eq`, `.counit` and
`.computesOnKFlat`, and through the existing `.T` alias; the coefficient/site sizes and all
canonical scalar and representative normalizations remain unchanged. Profiling also found
expensive unfolding while generating auxiliary structure lemmas. The internalHom alias
keeps its exact body as a def, with local irreducibility only after its model definitions;
unused generated injectivity and size-specification lemmas for the three large structures
are disabled (a source search found no callers). All structure fields and mathematical
conditions remain intact. The repaired dependency compiled cleanly in the published module
position in 22.8 seconds, as well as in the sandbox position. The node is copied
with only its lean record changed, and is added as a landed statement dependency.

A separate ordinary-only compile probe found duplicate declarations when importing the
legacy ClopenIdempotent and LowerStarProjection modules alongside the current finite
coefficient operations. The current server sources were read with scompile.py --source,
and both imports were changed to their published FiniteCoefficient.Derived counterparts.
The probe is temporary and is not part of the delivery.

## Second reading by Q09

Self-reading required by the dispatcher (no other agents may be started). I reopened the
node statement, all eight proof steps, the current dependency signatures and the repaired
file. Returned H3(1) is addressed by deleting alpha from both the theorem and mate helper
and writing the actual canonical ordinary beta/projector composite. H3(2) is addressed by
the second declaration: its equation is in the whole unbounded system category and uses
z.properOpen.gamma, with the intrinsic open-adjunct normalization, before evaluation.
H8 is addressed by the complete eight-step docstring. Advisory H4 is addressed by replacing
the local counit definition with the existing published projection component. The remaining
ordinary hypotheses, directions and universes agree with the accepted parts of the returned
review. The semilinear dependency repair changes elaboration of a projection only.
