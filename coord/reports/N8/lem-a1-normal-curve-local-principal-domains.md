## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.NormalCurveLocalPrincipalDomains` states
`AlgebraicGeometry.IsIntegralCurve.stalk_local_principal_domains` with a single `sorry`.
No definitions or proofs are added. The node changes only in `lean`.

The hypothesis and clause correspondence is:

- The field k is `{k : Type u} [Field k]`.
- The curve Y over k is `{Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  [IsIntegralCurve f]`. The recorded curve class extends `IsVariety f`, which gives
  integrality, separatedness, local finite type and quasi-compactness (finite type),
  and its `topologicalKrullDim_eq_one` field gives dimension exactly one.
  Its topological dimension agrees with the supremum of stalk dimensions by
  `Scheme.dim_eq_topologicalKrullDim` in the recorded dimension module.
- Normality is `(hY : IsNormalScheme Y)`, the recorded definition combining
  integrality with `∀ y, IsDomain (Y.presheaf.stalk y) ∧
  IsIntegrallyClosed (Y.presheaf.stalk y)`.
- The arbitrary point is `(y : Y)`; its actual structure-sheaf local ring A is
  `Y.presheaf.stalk y` throughout. No substitute ring or arbitrary algebra structure is used.
- Noetherianity is `IsNoetherianRing (Y.presheaf.stalk y)`.
- Dimension at most one is `ringKrullDim (Y.presheaf.stalk y) ≤ 1`.
- The dimension-zero implication is
  `ringKrullDim (Y.presheaf.stalk y) = 0 → IsField (Y.presheaf.stalk y)`.
  `IsField` expresses the property of the existing ring structure, without choosing new data.
- The dimension-one implication is
  `ringKrullDim (Y.presheaf.stalk y) = 1 → IsDiscreteValuationRing (Y.presheaf.stalk y)`.
  The domain instance needed to type this is supplied by integrality of the curve.
- “These are the only cases” is the explicit disjunction of dimension zero and dimension one.
- The PID assertion is the conjunction `IsDomain (Y.presheaf.stalk y) ∧
  IsPrincipalIdealRing (Y.presheaf.stalk y)`: a domain with every ideal principal.

All six statement-dependency nodes and their recorded declarations/docstrings were read:

- `def-pc-curve`: `AlgebraicGeometry.IsVariety`, `AlgebraicGeometry.IsIntegralCurve`,
  module `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`.
- `def-sbc-normal-dominant-galois`: `AlgebraicGeometry.IsNormalScheme`, module
  `WeilConjectures.AlgebraicGeometry.NormalScheme`. Only its normal-scheme notion is needed.
- `def-weil-pbc-module-stalk`: `PresheafOfModules.moduleStalkFunctor` and `stalkObj`,
  module `WeilConjectures.Topology.PresheafModuleStalkFunctor`; its underlying ring stalk
  is Mathlib's `TopCat.Presheaf.stalk`, precisely the structure-ring stalk used here.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, module
  `Mathlib.RingTheory.Noetherian.Defs`; `isNoetherianRing_iff_ideal_fg` verifies the ideal formulation.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`, module
  `Mathlib.RingTheory.KrullDimension.Basic`, valued in `WithBot ℕ∞`.
- `def-sc-discrete-valuation-ring`: Mathlib match `IsDiscreteValuationRing`, module
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, a local PID domain with nonzero maximal ideal.

The stated proof dependencies are imported privately: locally Noetherian schemes and finite-type
permanence (`Mathlib.AlgebraicGeometry.Noetherian`); affine stalk localization
(`Mathlib.AlgebraicGeometry.AffineScheme`); Noetherian localization
(`Mathlib.RingTheory.Localization.Submodule`); `Scheme.dim`
(`WeilConjectures.AlgebraicGeometry.Dimension`); scheme residue fields
(`Mathlib.AlgebraicGeometry.ResidueField`); and the normal one-dimensional regularity criterion
(`WeilConjectures.AlgebraicGeometry.Regular`, with
`IsRegularLocalRing.of_isIntegrallyClosed` in
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`). The scheme and open-immersion proof modules are also imported explicitly. The regularity dependency record gives a criterion
rather than a literal DVR conclusion; the existing
`IsRegularLocalRing.isDiscreteValuationRing` supplies that last implication in stage 3.
No dependency record needs repair to state this item.

Sources read directly: `literature/stacks-project/curves.tex`, lemma-flat (0CCK), whose first
proof sentence includes both fields and DVRs; `varieties.tex`, lemma-regular-point-on-curve
(0B8Y), whose perfection condition concerns smoothness only; `algebra.tex`,
lemma-characterize-dvr (00PD), including its Noetherian normal local domain criterion.

Edge cases checked: the generic point has a field stalk and dimension zero, so is retained;
a nongeneric point of a normal integral curve has the dimension-one DVR case. The example
`k[t]` localized at a closed prime and the generic `k(t)` both fit. Imperfect fields and
inseparable closed-point residue fields are allowed: no smoothness, perfection, algebraic
closure, or separability hypothesis is introduced. The empty scheme is excluded by integrality
and dimension one; zero rings cannot be scheme local rings or domains. The `WithBot ℕ∞`
dimension disjunction explicitly excludes bottom and infinity. The field and scheme share
universe u as in the recorded curve class, with u explicitly declared and all variables bound.

Searches performed with the required `msearch.py N8 <item>` wrapper:

- LeanFinder: “Every local ring of a normal integral curve over a field is Noetherian of
  dimension at most one and is either a field or a discrete valuation ring, hence a principal
  ideal domain”. Eight hits, including `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`,
  `IsDiscreteValuationRing.TFAE`, and Dedekind-domain localization criteria. These are local
  algebra ingredients, not the complete geometric statement with all its conclusions.
- Loogle: `IsIntegrallyClosed, IsLocalRing, IsPrincipalIdealRing`. One hit:
  `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`; it assumes the local Noetherian
  domain and does not state the geometric Noetherianity, dimension bound, and dichotomy.
- Mathlib grep: `IsDiscreteValuationRing|IsPrincipalIdealRing|ringKrullDim_stalk` in
  `AlgebraicGeometry`. Nine hits, consisting of elliptic-curve assumptions and stalk dimension
  identities, with no exact match.
- LeanSearch: “Every local ring of a normal integral curve is a Noetherian principal ideal
  domain and is either a field or a discrete valuation ring”. Eight hits, again the DVR TFAE,
  local Dedekind/PID facts and DVR projections, not the complete statement.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf/AlgebraicGeometry`, and `lean/Sheaf/Paper`:
  stalk PID/DVR patterns. The PID assertion in `RelativeEffectiveCartier.lean:509` is an
  internal proof under regularity; the smooth-curve statements in `Curve/SerreDuality.lean`
  and `Sheaf/AlgebraicGeometry/SmoothConnectedCurveLocalRings.lean` impose smoothness or an
  algebraically closed base and treat closed points. Their signatures were opened and checked;
  none is this theorem for all points of an arbitrary normal integral curve.
- `rg` for the item id in `lean/WeilConjectures`: no hit. Searches for the new declaration name
  in Mathlib, project sources and `dag/lean_names_upstream.json`: no hit.

Validation: `scompile.py N8 lem-a1-normal-curve-local-principal-domains <module>` compiled both
its sandbox view and library-module view cleanly (7.9 s and 6.1 s); no errors or warnings.
The only postponed theorem is the named item itself, with all six natural-language proof
steps and their DAG dependencies in its docstring. No statement dispute or correction. The inherited sandbox draft was replaced by the final
module above; no obsolete module is delivered.

## Second reading by N8

Author self-check under the dispatched-worker protocol; independent review is the maintainer's.
Reopened the node and final module and checked the field binder, the full recorded integral-curve
class, the recorded normality predicate and the arbitrary point. Checked each of the seven
conjuncts against the node: Noetherianity, the upper dimension bound, the dimension-zero field
implication, the dimension-one DVR implication, the exhaustive dimension disjunction, the domain
property and the principal-ideal property. The field case is included rather than being
incorrectly called a DVR. No statement change, missing helper, new node, or dependency module
was needed. All proof dependencies with recorded modules are imported, and the six-step proof
is preserved in the theorem docstring. No mismatch was found.

## Searches refreshed in this delivery

The current `searches.jsonl` records the exact wrapper queries and responses.

- LeanFinder: “Local rings of a normal integral curve over a field are Noetherian of dimension
  at most one, fields or discrete valuation rings, hence principal ideal domains”: eight hits,
  including the local Noetherian-domain TFAE, DVR TFAE, and Dedekind criteria; no full match.
- Loogle: `IsDiscreteValuationRing, IsPrincipalIdealRing`: three hits, the DVR-to-PID
  projection, DVR constructor, and unique nonzero prime characterization; none includes
  the geometric hypotheses or the dimension and field assertions.
- Mathlib grep: `IsDiscreteValuationRing|IsPrincipalIdealRing|IsDedekindDomain` in
  `AlgebraicGeometry`: eight hits, elliptic-curve assumptions and order-of-vanishing material.
- LeanSearch: “Every local ring of a normal integral curve is Noetherian of dimension zero
  or one, a field or a discrete valuation ring, and a principal ideal domain”: eight hits,
  DVR TFAE, local Noetherian-domain TFAE, DVR projections, Dedekind/PID implications,
  and the local-ring field criterion. All are ingredients rather than the full theorem.
- `rg` in `lean/WeilConjectures`, Mathlib, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the final declaration: no collision. The required
  item-id grep in `lean/WeilConjectures` has no hit.
