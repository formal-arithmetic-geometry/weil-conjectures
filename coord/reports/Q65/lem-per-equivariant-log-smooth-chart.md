## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantLogSmoothChart` states
`AlgebraicGeometry.LogSmoothPreparation.exists_equivariant_logSmooth_chart`.
Its only theorem proof is `sorry`. No data are chosen from a postponed existence
assertion. The conclusion is `Nonempty (Chart ...)`: the structure packages the
existential conclusion, including its canonical maps, rather than defining any
chart by an unconstrained choice.

I read ILO X Proposition 1.2 and its proof on printed pages 136--139. The item is
its first assertion and its final fs refinement; the representation assertion is
not part of this item. The statement of the node is unchanged. Its statement
dependencies gain the already landed group-action node and the node owning the
existing strictness interface. These are existing notions, not replacement definitions.

Hypotheses, in the order of the node:

- Locally Noetherian fs log schemes: `X B : FineSaturatedLogScheme.{u}`. This
  bundled type contains exactly the locally Noetherian and fs assumptions.
- The log morphism is `f : EtaleLogHom X B`; log smoothness is `hf : f.IsLogSmooth`.
- Finite group and actions by log automorphisms: `G : Type v`, `[Group G]`,
  `[Finite G]`, `aX : FSLogGroupAction G X`, `aB : FSLogGroupAction G B`.
  `hequivariant : aX.IsEquivariant aB f` includes equality of both log composites.
- The geometric point is `x : Spec (.of Ω) ⟶ X.scheme`, where `Ω : Type u`
  has the explicitly bound field and algebraically closed instances. Its base
  image is the actual composite `x ≫ f.base`, not another independently chosen point.
- Every group element fixes the geometric point: `hfixed`. This is equality of
  geometric-point morphisms and therefore includes the residue-field condition.
- The order is invertible near the image: `horder` says its image is a unit in
  the ordinary local ring at `(x ≫ f.base) default`. For a fixed integer this
  is equivalent to invertibility on an open neighbourhood, and it avoids
  imposing invertibility on all of the original base.
- Trivial characteristic actions: `hX` and `hB`, using `FixesCharacteristic`.
  This predicate compares the characteristic classes of germs on every pointed
  relative etale diagram of the *given* log automorphism. Those representatives
  compute its actual action on the geometric stalk; no separate trivial action
  is substituted. The geometric-point-fixing hypothesis makes this an endomap.
- Positive integer divisible by the exponent: `N`, `hN`, `hexponent`.
  Positivity is the usual convention for the N-th roots and for `1/N` in ILO.
  `hexponent` is the equivalent statement that every `g ^ N = 1`.
- Cyclotomic localization: `Λ`, `[CommRing Λ]`, the algebra over
  `CyclotomicRing N ℤ ℚ`, `S`, `[IsLocalization S Λ]`, and `hinvertN`.
  Localizing the cyclotomic integer ring at a multiplicative set containing N
  gives exactly a localization of Z[1/N,zeta_N].
- The chosen primitive root is `ζ : Λˣ`, with `hζ : IsPrimitiveRoot (ζ : Λ) N`.
  Thus the group called mu_N is the existing `Subgroup.zpowers ζ`.
- Definition over Λ is the ring map `cB : Λ →+* Γ(B.scheme, ⊤)`.
  The coefficient map on X is its composite with `f.base.appTop.hom`, so f
  is over Λ by construction. Trivial group action on coefficients is
  `hcoefficients`; equivariance makes the same true on X.
- Sharp fs base monoid and given chart: `Q`, `[CommMonoid Q]`, `hQ`, `hsharp`,
  `a`, `ha`. The chart is on the terminal etale object, as in the existing interface.
- Given character pairing: `χQ : G →* (GrothendieckGroup Q →* Subgroup.zpowers ζ)`.
  This curried bihomomorphism is exactly a homomorphism from Gab tensor Q^gp:
  each G-character has commutative codomain and factors uniquely through Gab;
  the tensor universal property identifies the two encodings.
- The prescribed equivariance equation of a is `heigen`.
  `globalLogAction` is precisely the terminal-test component of `aB.logMap g`.
  `UnitMultiple` multiplies by the log unit with structural image `cB (χQ g q)`;
  existence and uniqueness of that unit are the log unit axiom. No arbitrary
  scalar action or merely ring-valued equality replaces the log equation.

Conclusion clauses, using the fields of `Chart`:

- Equivariant pointed etale neighbourhood: `W`, `inclusion`, `etale`,
  `restriction`, `point`, `point_over`, `action`, `equivariant_inclusion`,
  `point_fixed`. Strictness of inclusion means W has the pulled-back log structure.
  `toBase` and `over` keep the actual composite with f, including its log map;
  `equivariant_base` records the induced base equivariance.
- The fs monoid P is `P`, `instP`, `fs`. Its units are torsion free by
  `units_torsionFree : IsMulTorsionFree Pˣ`; units need not be trivial.
- The homomorphism gamma and chart b are `gamma`, `b`, `isChart`.
  `compatible` is the equality `b.comp gamma = (globalLogPullback toBase).comp a`.
- The extending pairing is `character`; `extends_character` is its equality
  with χQ on the canonical images of Q. Since Q generates its group completion,
  this is equivalent to extension on all Q^gp. `eigenvectors` is exactly the
  asserted log-section eigenvector equation, using the coefficient pullback from B.
- Injectivity of gamma^gp: `injective`, for the existing Grothendieck-group lift.
  Finite torsion cokernel: `finite_torsion`, using the actual quotient by its range
  and `CommGroup.torsion`. Its order is invertible on the neighbourhood by
  `invertible_torsion`, tested in every local ring of W.
- The comparison target is `target`, `targetToBase`, `targetToMonoid`, `cartesian`.
  `cartesian` is an `IsPullback` over Spec Λ[Q]. Its base map is built directly
  using `ΓSpec.adjunction.homEquiv` and `MonoidAlgebra.liftNCRingHom`, with the
  coefficient map cB and the structural image of a. Its second map is
  `Spec.map (MonoidAlgebra.mapDomainRingHom Λ gamma)`. It is therefore the
  stated fibre product, up to its uniquely specified pullback isomorphism.
- Its log structure is fixed by `targetChart`, `target_isChart`,
  `target_monomials`, `target_compatible`. This is precisely the log structure
  of the pulled-back P-chart and the induced log morphism to B, not another
  unspecified log structure on the same scheme.
- The comparison itself is `comparison`, `comparison_over`, `comparison_chart`,
  `comparison_monomials`. The last equation makes its monoid-spectrum component
  the chart map of b with the pulled-back coefficients. Together with the first
  projection equation and `cartesian`, this uniquely determines the scheme map.
  Chart normalization determines the log map as well.
- Strictness is `strict : comparison.IsStrict`, and smoothness is
  `smooth : Smooth comparison.base`, using the recorded existing notions.
- Equivariance is `targetAction`, `equivariant`, `target_base_equivariant`,
  `monoidAction`, `target_monoid_equivariant`, `model_monomials`.
  The final formula specifies pullback of every coefficient monomial as
  z^p r -> z^p χP(g,p)r. Thus it fixes coefficients and is the prescribed
  character action. The cartesian projections then determine the target action;
  no arbitrary target action is accepted by the statement.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogStructure.IsChart`, `EtaleLogHom`,
  `EtaleLogHom.CompEq`, `EtalePrelogStructure.germ`, and the characteristic
  quotient `Associates` underlying `EtaleLogStructure.characteristic`.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `EtaleLogHom.IsLogSmooth`;
  the existing monoid-spectrum convention and chart compatibility are retained.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.FSLogGroupAction`: `FSLogGroupAction` and
  `FSLogGroupAction.IsEquivariant` (already landed `def-per-fs-log-group-action`).
- `Sheaf.AlgebraicGeometry.LogFanChartBlowup`: `EtaleLogHom.IsStrict`
  (`def-per-strict-log-morphism` owns the reused strictness definitions), defined by the canonical
  characteristic-stalk relation, not by an unrelated isomorphism.
- Mathlib's `Algebra.GrothendieckGroup`, `CommGroup.torsion`, `IsPullback`,
  `MonoidAlgebra`, `ΓSpec.adjunction.homEquiv`, `CyclotomicRing`, `IsLocalization`,
  `IsPrimitiveRoot` and `Subgroup.zpowers` provide the remaining canonical objects.

All already recorded proof-dependency modules are imported, including
`SharpConeLatticeIntersection`, `StrictLocalRootsOfUnity`,
`DivisibleUnitLatticeExtension`, Mathlib's `FreeModule.PID`,
`FineLogStalkChartSpreading`, `AssociatedLogUniversalStalks`, and the recorded
etale site/stalk modules through their existing imports. The three proof inputs
with no Lean record (cotangent characteristic quotient, equivariant sharp chart,
strict log Jacobian criterion) do not occur in the statement and are named in
its full ten-step proof docstring for subsequent stage 3.

The file uses the non-module syntax because its existing strictness dependency
`LogFanChartBlowup` is not a `module`. No dependency source is modified.

Edge cases checked:

- Trivial G and N=1: all characters are trivial; the conclusion is the usual
  compatible chart, allowing a smooth comparison of positive relative dimension.
- Nonabelian G: the curried characters automatically factor through Gab.
- Q={1} and trivial characteristic: unit directions in P remain allowed,
  and no positivity or nonemptiness of a rank is assumed.
- Noninjective Q -> the characteristic of X: no such injectivity is assumed;
  the conclusion concerns gamma into the enlarged chart P, as in ILO.
- Kummer chart: finite prime-to-residue-characteristic torsion is allowed; the
  conclusion does not incorrectly demand a torsion-free cokernel or etaleness.
- The target and the initial base need not be affine. Global-sections/spectrum
  adjunction gives their chart maps for arbitrary schemes.
- Empty X has no geometric-point input; no unintended nonemptiness condition is
  imposed on the schemes or on unrelated chart fibres. Group universe v is
  independent of scheme/monoid/field/coefficient universe u.

Searches for an existing assertion and interfaces:

- `msearch.py leanfinder`, query "fine saturated logarithmic equivariant smooth
  monoid chart": eight results about smooth manifold monoid structures; no match.
- `msearch.py leanfinder`, query "equivariant compatible chart of fine saturated
  log smooth morphism with torsion free units and smooth comparison": no matching
  logarithmic theorem in the returned search material.
- `msearch.py leansearch`, query "An equivariant logarithmically smooth morphism
  admits compatible monoid charts and a smooth strict comparison": eight results
  about manifold morphisms and WithZero.logEquiv; no match.
- `msearch.py loogle`, query "FSLogGroupAction, FSLogChart": zero results;
  FSLogGroupAction is not a Mathlib identifier, as expected for a side-library notion.
- `msearch.py grep`, regex "Equivariant.*Log|Log.*Equivariant|LogSmooth" in
  Mathlib/AlgebraicGeometry: zero results.
- `rg` of the slopmaster2 WeilConjectures tree for the node id and for logarithmic
  equivariant-chart/action names: no matching statement.
- `rg` of `lean/Sheaf/AlgebraicGeometry` found the existing group-action and
  strictness interfaces, which are reused. The existing Gabber fixed-locus module
  has a different, more specialized standard-coordinate chart with representation
  coordinates and fixed-locus blowups; it does not state this prescribed-base-chart
  assertion for arbitrary fs X and B. It is downstream, and is not imported.

No `STATEMENT-DISPUTED` finding, no statement correction, and no dependency replacement.
The now-landed definition node `def-per-strict-log-morphism` records the existing
strictness interface and is reused without edits. The five helper declarations in this module
are the explicit data/normalizations of this theorem's hypothesis and conclusion,
as authorized by the owning-node helper rule. They do not contain `sorry` data.


## Landed definition dependency

`def-per-strict-log-morphism` landed during this repair, with an `existing: true`
record on `Sheaf.AlgebraicGeometry.LogFanChartBlowup`. Its declaration list includes
`AlgebraicGeometry.EtaleLogHom.CharacteristicRelation`,
`AlgebraicGeometry.EtaleLogHom.IsStrict`, and `AlgebraicGeometry.EtaleLogHom.IsIdentity`.
I read the landed node and the first two definitions at lines 82 and 100. They give
exactly the required characteristic relation and strictness; the identity predicate
is not used by this item. The strictness signature in the record is verbatim.
The item now cites this definition node instead of the fan-chart theorem; its module
already imports `LogFanChartBlowup`, so the Lean file needs no change. No dependency
record is edited, and no new node or module is delivered.

The repair searches were `msearch.py leansearch` for a strict fs log morphism inducing
an isomorphism of geometric characteristic stalks (ordinary scheme stalk-map hits),
`msearch.py loogle '"IsStrict"'` (strict cuts and implicit binders), and Mathlib grep
for `CharacteristicRelation|EtaleLogHom.IsStrict|strict.*log.*morphism` (zero hits).
Grep in slopmaster2 found no corresponding declaration; grep in `lean/Sheaf` found
the two existing definitions in `LogFanChartBlowup`. Initial DAG and blueprint search
found no separate definition owner. The refreshed base now contains the definition
node landed by NG, which is reused in accordance with one definition per notion.

## Repair of returned delivery

The independent review of immutable head `afea8ee616ca` returned one H2 point:
`lem-trf-log-fan-chart-blowup` was cited solely for its plain strictness helper definitions.
Replaced that statement dependency by `def-per-strict-log-morphism`, whose landed
record owns both requested definitions. The theorem node's statement, proof, and proof
dependencies are unchanged. The reviewed Lean module is byte-identical to the saved
packet. Current-base comparison confirms that the item's only changed fields are
`lean` and the authorized added definition dependencies.
The initial saved-packet dry run passed at `ba5a876c8b`; it did not address definition
ownership, so the dependency replacement is a substantive repair. The next dry run
reported that my newly added strictness node had meanwhile landed on the base and
was therefore being treated as a dependency edit. I read the landed record, confirmed
it owns both definitions, and removed my redundant node copy from the packet.

## Second reading by Q65

Repair self-check: reopened the landed definition record, its source definitions,
and the theorem module. The characteristic relation is the existential pointed
relative etale diagram with its two characteristic germs and equality of pointed
lifts; strictness is the isomorphism whose graph is exactly that relation at every
geometric point. Neither definition uses the fan-chart theorem or `.choose`.
Empty sources make the stalk criterion vacuous as required; identity strictness uses
the identity characteristic map; trivial log structures have the one-element
characteristic monoid, with no additional hypotheses. The independent maintainer's
reading of `afea8ee616ca` already passed every theorem hypothesis/conclusion clause
and all edge cases; this repair changes none of them. The advisory about further
specifying `targetAction` on `targetChart` is recorded; the required ownership
correction explicitly permits leaving the Lean file byte-identical. No additional
agent was started, in accordance with the dispatcher brief.

The delivered theorem module compiled cleanly through `scompile.py`: sandbox 8.8 s,
library 8.7 s. The theorem's recorded signature and the unchanged mathematical fields
were checked directly against the module and refreshed base node.
