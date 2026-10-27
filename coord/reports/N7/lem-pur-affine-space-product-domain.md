## Worker report

The module `Sheaf.Paper.AffineSpaceProductDomain` states
`WeilConjectures.AffineSpaceProduct.affine_space_product_domain`, with its sole
postponed proof `sorry`. The definition prerequisite `Sheaf.Paper.AffineSpaceProductConstructions`
constructs the concrete finite-coefficient relative maps, without assuming a six-functor datum, duality, or an exceptional
adjoint. All definitions have real data.

Clause-by-clause translation:

- The global finite field, distinct coefficient prime, finite extension and
  positive coefficient level are `P : PurityFiniteSetting.{u}`. `P.Coefficient`
  is precisely the standard size lift of `A_{E,n}`.
- A separated finite-type base is `B`, its structure morphism `b`, and the
  instances `IsSeparated b`, `LocallyOfFiniteType b`, `QuasiCompact b`.
- The separated finite-type map is `f : X ⟶ B` with the same three instances.
  Together with the base assumptions this also makes X a separated finite-type
  k-scheme; no independent stronger hypothesis on X is imposed.
- `M : D P X` and `_hM : ProEtale.DerivedCategory.constructibleFiniteTor ... X M`
  express exactly membership in the recorded finite-stage D^b_ctf. This is the
  native fixed-module version exported by def-weil-finite-tor-amplitude.
- The given isomorphism is `u : image P f M c 0 ≅ 𝟙_ (D P B)`.
  The monoidal unit is the coefficient sheaf in degree zero. Each compactification
  family `c` is universally quantified: this is a presentation choice for Rf!,
  not an additional admissibility hypothesis. Separated finite-type maps have
  compactifications; the node's independent geometric factors supply those for
  the successive products as well.
- The index `j : ℕ` represents m=j+1; thus precisely every m>=1 occurs, and
  `space f 0 = Over.mk f` and `external ... 0 = M`. `space` specializes the
  recorded `RelativeExternalPower.product` to a constant family. `first` and
  `last` specialize its actual pullback projections. `external` is the derived
  external tensor in its canonical successive regrouping; the recorded rho_j
  identifies this with the tensor over all coordinate pullbacks. No new notion
  of fibre product, pullback or derived tensor is introduced.
- `image ... j` is V_m, the concrete compactification compact support of this
  external tensor. The first conjunct gives M_m in D^b_ctf. The next two give
  V_m isomorphic to the coefficient unit and its Tor amplitude in [0,0].
- `∃ d : ∀ j, StageDomain ... j` asserts, rather than assumes, every domain
  needed for the inversions. Its `firstInput` is Lpi_X* M_m in D^b_ctf;
  `baseM` is M on X and `baseV` is V_m on B, both finite-Tor constructible.
  `projectionFirst` and `projectionLast` assert invertibility of exactly the
  concrete PF components with those coefficients, using the compactification
  of pi_Y induced by base change from c_m and c_1 respectively. `origin`
  supplies the already implied bounded-below etale-origin domain of the
  composition isomorphism, `quasiCompact` its geometric typing, and
  `exchangeIso` invertibility of the specified exchange factor.
- `step` is kappa_(m,1): composition inverse, inverse first PF, inverse exchange
  tensored with identity, tensor symmetry inside Rf!, inverse second PF, and
  symmetry on the base. `compositionInverse` includes the canonical comparisons
  between the specified compactifications and the published origin compositor,
  including pi_Y f=f_(m+1). `exchange` is the recorded supplied-domain proper
  mate followed by open-extension exchange, specialized by the geometric-factor
  module to the actual finite operations. The braidings are the published
  Koszul derived braiding, installed only inside the opaque `symmetry` construction body.
- `IsIso (step ...)` is the isomorphism assertion for every binary relative map.
  `tensorPower` fixes left association of (Rf! M) tensor m. `comparison` starts
  with identity and recurses by `step ≫ (comparison ⊗ₘ 𝟙 _)`, exactly kappa_m.
  Its `IsIso` conjunct and that of `comparison ≫ unitPower ... u j` give the
  two final displayed isomorphisms. `unitPower` tensors the supplied u in every
  factor and applies the canonical left unitor at each stage.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  its quotient `Ring`, standard lift `Coefficient` and their ring structures.
- `Sheaf.Paper.FiniteTorAmplitudeSites`:
  `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor` and
  `.torAmplitudeIn`, publicly exported from the recorded upstream TorAmplitude.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `.fst`, `.snd`, `.condition`, used also through the recorded external-power
  geometry. Scheme pullbacks provide their existence.
- `Sheaf.Paper.RelativeExternalPowerRegrouping`:
  `RelativeExternalPower.product`, `.fst`, `.snd`, `.regroup` and
  `.relative_external_power_regrouping`. Its canonical regrouping justifies
  the recursive external-tensor coordinates. Its theorem remains a proof dependency;
  its plain definitions are now definition-owned public re-exports.
- `Sheaf.Paper.RelativeProductGeometricFactors`:
  `RelativeProduct.D`, `.exchange`, `.relative_product_geometric_factors`,
  `.relative_product_composition_exchange`; the last two are proof inputs.
  The theorems remain proof dependencies only; the D/exchange definitions are
  now definition-owned public re-exports.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData`,
  specialized by `RelativeProduct.exchange`. The finite PF is
  `AlgebraicGeometry.ProEtale.projectionMapOfCompactification` from
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `ProEtale.originCompositionAmbient`, `originCompactSupport`, together with
  `ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso` from
  the upstream `CompactSupportCandidate` module; these construct compositionInverse.
- `Sheaf.Paper.RelativeKunneth`: `relativeKunnethIso`, `relativeKunnethMap`, and
  full `relativeKunneth` signatures/docstrings were read. They require an axiom
  package `SixFunctorDatum`; no such package is assumed here. Its construction's
  six prescribed factors are instantiated concretely by `step` instead.
- Proof-only imports `Sheaf.Paper.FiniteTorStability` (`finiteTor_stability`)
  and `Sheaf.Paper.SfProEtaleProjectionFormula`
  (`sf_proetale_projection_formula`) retain the recorded induction's proof plan.
  `RelativeKunneth` is likewise a proof-only import for the construction's shape.

Edge cases checked before and after drafting: m=1 is precisely j=0, its
comparison is identity and unit comparison is u. The next stage uses the two
correct projection coefficients M and V_1. There is no accidental m=0 or
nonempty-scheme restriction; an empty base or source is permitted, and u itself
controls whether a particular input can meet the hypothesis. For identity maps
and coefficient units the construction reduces to the unit comparisons. Level
n>=1 and ell distinct from the characteristic come from P; no ramification
index divisibility, smoothness, properness of f, or flatness hypothesis was added.
The small site and coefficient universes remain u+1 over Scheme.{u}.

Searches (2026-10-25; msearch records preserved in sandbox searches.jsonl):

- leanfinder, `iterated relative external tensor powers compact support direct
  image is coefficient unit finite Tor amplitude`: eight results concerning
  internally projective light condensed objects; none states this assertion.
- loogle, `CategoryTheory.MonoidalCategory, CategoryTheory.IsIso`: twelve
  generic tensor/whiskering inverse lemmas, including `tensor_isIso`; no
  geometric compact-support statement.
- leansearch, `finite Tor admissibility iterated relative compact support
  external tensor products unit`: eight tensor-product / complex-unit results,
  none with the required geometry or finite-Tor assertions.
- msearch grep, `kunneth|compactSupport.*(Tor|tensor)|etale.*trace`, restricted
  to Mathlib/AlgebraicGeometry: zero hits.
- rg in live lean/WeilConjectures for the item id: no match. Concept search
  for relative Kunneth found the existing projection operations and
  KunnethDefs, but no iterated domain theorem. rg in lean/Sheaf found
  RelativeExternalPowerRegrouping and RelativeProductGeometricFactors, both
  reused, and the axiom-package RelativeKunneth, whose map interface was read.
- Name check `AffineSpaceProduct|affine_space_product_domain` in lean/Sheaf,
  lean/WeilConjectures and dag/lean_names_upstream.json: no existing declaration.

No statement correction, dependency-interface repair, or STATEMENT-DISPUTED flag.
One definition ownership node is added in this returned-delivery repair, as detailed below.
The repair note is a resolved stage-1 re-split, preserved without changing its
accepted proof or statement. The newest blueprint ancestor and relative-product
proof were read; this derived helper retains the accepted node's finite-stage
induction, despite the ancestor's now shorter presentation of the composition law.

## Second reading by N7

Separate review pass by the assigned worker (no other agents were started, as
instructed). Re-read the node beside the file, matching each hypothesis and every
conclusion as listed above. In particular the Tor-domain proofs are conclusions,
not hypotheses; the inverse projection maps have second coefficients M and V_m;
the kappa recursion is in the source-to-target direction; arbitrary positive
numbers of factors and arbitrary compactification choices remain covered. The
recursive external tensor is a canonical regrouping of the already recorded
all-projection tensor, not an arbitrary replacement object. The canonical
origin compositor and exchange are used, not arbitrary isomorphisms. The first
compiler passes identified missing flat-pullback and braiding interfaces; added
the published flat ModuleCat import and explicit canonical braiding helper. The first complete composite timed out;
made its braiding helper irreducible to avoid repeatedly expanding its descent.
No mathematical hypothesis or conclusion changed during these repairs.

Validation: declaration checkpoints located the expensive elaboration in step.
The projection and exchange helpers now have explicit source and target types
and irreducible bodies. This preserves their exact published maps and avoids
unfolding large natural-transformation constructions at every composite factor.
All temporary diagnostic checks and the diagnostic heartbeat bound were removed.


## New nodes

`def-pur-relative-product-constructions` owns the concrete constructions in
`Sheaf.Paper.AffineSpaceProductConstructions`. All 17 specialized helpers, from
`space` through `unitPower`, are moved from the returned module without changing
their signatures or bodies. Their blueprint anchors now identify this definition
node. This also gives `StageDomain`, the six-factor `step`, and its recursive
comparison arrows explicit definition ownership. The node additionally records
nine unchanged public re-exports: `RelativeExternalPower.product/fst/snd`,
`RelativeProduct.D/exchange`, `ProEtale.projectionMapOfCompactification`, and
`ProEtale.originCompactSupport/originCompositionModel/originCompositionAmbient`.
The public imports supply those exact definitions; no duplicate product, exchange,
projection, or compositor is introduced. The module's implementation imports
contain the earlier theorem statements, but none is a statement prerequisite of
this new definition node. Its source is the latest blueprint relative Kunneth
proof, Steps 1--4, and the accepted product-domain induction. Its compositor is
the specified etale model transported along the canonical origin equivalence,
including all canonical compactification comparisons.

New-node searches on 2026-10-25: LeanSearch query `iterated scheme fibre products
projections compact support exchange and etale origin composition` returned eight
ordinary scheme pullback/flatness declarations, no combined construction.
LeanFinder query `canonical iterated relative fibre product compact support
exchange origin compositor` returned eight scheme pullback gluing declarations.
Mathlib grep `originCompositionAmbient|originCompactSupport|RelativeExternalPower|
projectionMapOfCompactification` returned zero hits. DAG and project rg located
the exact existing definitions, previously owned only by the theorem records.
The blueprint search `relative product` returned five general Kunneth nodes and
no definition of this package. Existing coefficient-first projection definition
nodes concern ordinary etale arrows and do not own the native pro-etale
`projectionMapOfCompactification`. Search records are retained in the new node.

## Returned delivery repair

The sole numbered defect, H2 at immutable head `c1d5d05d7214`, is repaired by
adding the definition node above, replacing the two added theorem stmt_deps
with it, and explicitly adding `def-pur-origin-compactification-comparison` to
the item's stmt_deps. That existing definition owns
`rightDerivedLowerShriekOfCompactificationEtaleOriginIso` used by
`compositionInverse`. The original proof_deps, item statement, theorem signature,
and all mathematical constructions are unchanged. The new ownership also
addresses the advisory about the native projection map lacking a definition
owner. The finite-Tor predicate bridges remain proof work; no proof or extra
hypothesis is introduced in this statement-stage repair.

Second reading of the repair by N7: compared each moved helper with the returned
file and checked that only its owning module and blueprint anchor changed.
The new node explicitly describes the general iterated fibre product with actual
projections, the fixed ModuleCat derived category, concrete proper/open exchange
and projection, the origin compact-support functor and canonical transported
compositor, and every specialized helper. The latter retain all stage domains
and precisely the accepted six factors. All statement dependency ids occur in
its TeX. The item no longer cites either geometric/regrouping theorem as a
statement dependency. As required by the dispatch, this review was performed by
the worker, without starting another agent.
