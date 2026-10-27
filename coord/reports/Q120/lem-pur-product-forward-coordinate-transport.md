## Worker report

The module `Sheaf.Paper.ForwardProductCoordinateTransport` states
`AlgebraicGeometry.ProEtale.finiteForward_coordinate_transport`. Its sole postponed
proof is this named theorem. The helper declarations contain actual canonical
constructions. There are no statement corrections or new independent notions.

The source is the opening choice-coherence and symmetry paragraphs of
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md`,
with the ten-step finite-level expansion in the assigned node. The source describes
the actual forward map as composition comparison, compact-support exchange and
projection transformations. This delivery asserts its expansion and transport,
without asserting its equality with an ordinary external-product map.

Hypothesis and clause correspondence:

- The fixed finite coefficient datum is `C : WeilConjectures.PurityFiniteSetting`;
  the coefficient ring is exactly `C.Coefficient`, the established universe lift
  of `O_E/(varpi_E^n)`, with `C.level_pos`. No different coefficient field or quotient
  is introduced.
- The separated finite-type schemes B, X, Z over k have their `Over`,
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` structure-morphism
  instances. The morphisms f and g have `IsOver`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` instances. The compactness and
  quasi-separatedness instances inside the assertion are constructed consequences
  of these hypotheses, for Nagata; they are not additional hypotheses.
- The sites are `Scheme.ProEt.topology`, and every category is the ordinary
  unbounded `DerivedCategory (Sheaf ... (ModuleCat ... C.Coefficient))`.
  `ProperOpenDerived`, `ProperOpenPull`, `ProperOpenPush`, `ProperOpenShriek`,
  `ProperOpenTensor` are existing abbreviations for these actual operations.
  The braiding is `finiteForwardTensorSymmetry`, obtained from the signed
  homotopy-complex braiding by derived tensor localization.
- M and N are `DerivedCategory.Plus` objects, and wM and wN are the recorded
  `Scheme.FixedEtaleOriginWitness` structures, retaining both the antecedents
  and their specified comparison isomorphisms. These witnesses are used in the
  normalized endpoint comparisons.
- The choices are arbitrary `cf : Compactification f`, `cg : Compactification g`.
  Their fields are j=cf.i, a=cf.g, k=cg.i, b=cg.g. `pullback f g` is P, with p and q
  the actual projections; `pullback cf.g cg.g` is C; `pullback cf.g g` is W.
  `cf.ofIsPullback (IsPullback.of_hasPullback f g)` is exactly (j_q,v).
  `ForwardProductCoordinates.middleOpen` is the unique i with its two specified
  projections. `middleSquare` supplies its Cartesian open square.
  `productChoice` has u=j_q followed by i and c=t followed by b; its factorization
  is computed from the projection identities. Thus h=q followed by g, equal to
  p followed by f by `pullback.condition`.
- H=j!M and J=k!N occur literally as `ProperOpenShriek` objects. L=RaH is the
  cf compact-support candidate, and L0=PbL is its `ProperOpenPull` along cg.g.
  K=j_q!PpM and KD=j_q!D occur literally in `compactificationOpenFactor` and `psi`.
  D is the existing `finiteProductExternal`, namely PpM tensor PqN.
  F=PrH, E=PiF, m=i!K, A0, beta, chi and s are auxiliary abbreviations in the
  natural-language setup; no conclusion of this node uses them. The displayed
  maps here expand B0 directly by the existing compactification exchange, rather
  than adding parameters for any of those canonical maps.
- `exchange` is B0, the component of the recorded finite compactification exchange,
  preceded only by the canonical PkPb=Pg comparison. It is not an arbitrary
  supplied arrow and has exactly the base-changed f compactification as target.
- `compactificationOpenFactor` specialized to the base-changed f choice is d: the normalized open tensor isomorphism at j_q, followed by
  j_q! of the canonical P_jq P_v=P_q comparison. `psi` is a helper on a displayed proper/open square; its canonical specialization
  in `route` is k! of (B0 tensor 1),
  then k! of pi_v, then k!Rv(d), then the existing normalized proper/open mate
  `properOpenMate` at KD. No exchange for q is inserted.
- `nu` is the specified two signed swaps around delta_k. `z` is the initial
  signed swap, the counit-defined pi_b, and Rb of the final signed swap.
  `route`, at this canonical specialization, is z followed by Rb(nu followed by psi), then the necessary open
  compositor i!j_q!=u!, then the inverse `finiteDirectImageComposition`.
  This is exactly kappa inverse Rb(Psi nu) z with Lean's left-to-right `≫`.
- The main assertion uses the existing six-factor `finiteProductChosenForward`
  as T, with the normalized `finiteProductComposition` alpha and the actual
  projection/exchange factors. `Expansion` equates this map with the canonical specialization of `route`.
  It uses `HEq` for this single equality: the two morphism types have definitionally
  identical endpoints, but are expressed through the compactification record on
  the left and through its explicit two factors on the right. Thus HEq is precisely
  equality of the specified maps; no endpoint isomorphism or arbitrary map is
  supplied as a hypothesis. This avoids repeatedly normalizing the same large
  derived-category type in the kernel.
  `ProjectionFactorization` explicitly equates PF_q with pi_v followed by Rv(d),
  and PF_g with
  pi_b followed by Rb of delta_k and its canonical pullback compositor.
  Its last equality expresses that the following signed swap gives nu, including
  the same canonical pullback compositor on both sides.
- The hypothesis d is `FiniteProductCompactificationDomain`: it requires all
  six tensor objects in this forward composite to be bounded below and of etale
  origin (both orders at the source, both orders at g's pullback, the exchanged
  tensor, and D). The second system is required to have the same domain by d'.
  No constructibility, finite Tor amplitude, invertibility of projection, or
  invertibility of exchange is assumed.
- `TransportEquation` says T1 followed by theta_h equals theta_f tensor theta_g
  followed by T2, with Lean's composition order. Every theta is the existing
  canonical `finiteForwardCompactificationComparison`, at the retained M,N,D
  witnesses. The endpoint compactifications ch,ch' are arbitrary as well as
  cf,cg,cf',cg'. The q compactifications remain exactly the respective base
  changes in each occurrence of `finiteProductChosenForward`. This same formula
  holds through further common refinements because these specified comparisons
  are the common-refinement-independent ones with the recorded cocycle; no
  arbitrary comparison or refinement is supplied as a hypothesis.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `PurityFiniteSetting.Coefficient` and its coefficient ring instance.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and its category;
  `Compactification`, `Compactification.ofIsPullback` give the actual choices.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded finite intrinsic operations;
  this statement uses their established ordinary fixed-scalar realization, as
  prescribed by this node, and imports the recorded dependency rather than
  defining an alternative tensor or pullback.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`; its middle fixed-scalar
  `ProEtale.openImmersionLowerShriek` is the ordinary extension used here.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`; its finite
  canonical operations are the existing `projectionMapOfCompactification` and
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap` used in the existing
  forward-map definitions, not the generic supplied higher-stage data.
- `Sheaf.SixFunctors.OpenTensorNormalization`: the unit-normalized open comparisons,
  including `SheafOfModules.OpenTensorNormalization.finiteGamma` and the canonical
  beta compatibility; `properOpenTensorIso` is its existing finite inverse
  projection realization.
- `Sheaf.SixFunctors.ProperOpenProjectionMate`:
  `AlgebraicGeometry.ProEtale.properOpenMate`, `properOpenProjection`,
  `properOpenTensorIso`, `properOpenShriekComp`, and the `ProperOpen*` abbreviations.
- `Sheaf.Paper.FiniteDirectImageComposition`:
  `AlgebraicGeometry.ProEtale.finiteDirectImageComposition`.
- `Sheaf.Paper.CompactificationCoherence`: `compactification_coherence`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `originComposition`, `originCompositionAmbient`.
- Reused existing helper declarations in `Sheaf.Paper.FiniteProductCompactification`:
  `finiteProductGeometry`, `finiteProductExternal`, `FiniteProductCompactificationDomain`,
  `finiteProductPullTriangleObj`, `finiteProductChosenForward`,
  `finiteProductComposition`. Its imported `FiniteForwardProductSymmetry` gives
  `finiteForwardTensorSymmetry`, `finiteForwardProjectionMap`, and
  `finiteForwardCompactificationComparison`.

The stronger theorem `finiteProduct_compactification` in that last module is NOT
used. Its helper definitions already express the forward map independently of
this theorem. There is a potential reverse proof import after this item lands:
the maintainer must omit the back proof import into `FiniteProductCompactification`
to avoid a module cycle, under stages/2-statements.md rule 7. There is no circular
use of its ordinary-product assertion in this statement or proof plan.

The stated proof dependencies that are already publicly available through these
modules are imported with the appropriate visibility; the existing
`Sheaf.Paper.PfRefinementCompatibility` is also imported for the proof. The proof-only product-exchange-coordinate node has no Lean attachment yet.
Unstated proof prerequisites need no new statement here because this work only
states the theorem; its docstring names all ten proof steps and every source node.

Edge cases checked before writing:

- Empty X or Z: the same products, open extensions, and canonical maps exist;
  no nonempty hypothesis or point choice occurs.
- Zero complexes and unbounded objects in the auxiliary maps: all helper
  composites are defined on the actual ambient unbounded categories; lower
  bounds and etale witnesses are restricted to the theorem's stated domain.
- Identity open and proper compactifications: no nontrivial-open or boundary
  hypothesis occurs; the existing unit-normalized comparisons apply.
- Refining only g, only f, or only h: all pairs of endpoint choices are quantified
  independently, and q is always the base change of the current f choice.
- Lowest allowed coefficient level n=1: it is covered by `C.level_pos`; there
  is no imposed divisibility, Kummer, constructibility or Tor hypothesis.
- Site universes: Scheme.{u}, site objects u+1 and arrows u, coefficients in
  Type (u+1), and ModuleCat.{u+1} are retained; no site-universe equality is added.

Searches for an existing exact statement:

- `msearch.py ... leanfinder` with "Expand forward compact support external product
  into proper projection maps and open extension factors; transport under
  normalized compactification comparisons": eight hits, all topological support
  or compactly supported function constructions (including
  `HasCompactSupport.extend_zero`); none states this sheaf-theoretic formula.
- `msearch.py ... loogle` with
  `projectionMapOfCompactification, rightDerivedLowerShriekOfCompactificationBaseChangeMap`:
  zero hits, the project identifier is unknown to the Mathlib search service.
- `msearch.py ... grep` with `compactification|lowerShriek|kunneth|projectionFormula`
  in CategoryTheory: zero hits.
- `rg` for the item id in `lean/WeilConjectures` and `lean/Sheaf`: no exact match.
  Broader `forwardProduct|ForwardProduct|forward.*[Cc]oordinate` searches found
  `FiniteForwardProductSymmetry` and `FiniteProductCompactification`; their
  helper maps are reused. Their main statements are respectively product
  symmetry and comparison with the ordinary product, not this coordinate
  expansion plus normalized choice transport, so neither is an existing match.
- The current server source of `Sheaf.Paper.FiniteProductCompactification` was
  read using `scompile.py --source` and agrees with the relevant local helpers.

No STATEMENT-DISPUTED finding or source correction is asserted.

Compilation diagnosis: module-mode import probes passed. The finalized helpers
use explicit generic parameter interfaces for open projection and the proper/open
composite, avoiding repeated concrete fibre-product reduction. A bounded diagnostic
compile at 5,000 heartbeats per declaration passes in approximately six seconds.
No diagnostic option or probe is included in the delivery module.

## Second reading by Q120

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
