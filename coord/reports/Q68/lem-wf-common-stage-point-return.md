## Worker report

The module `Sheaf.Paper.CommonStagePointReturn` states
`WeilConjectures.commonStagePointReturn`, with its sole proof `sorry`. Its seven
helpers are actual canonical composites or Prop-valued predicates. No theorem is
proved, no definition contains `sorry`, and no mathematical statement is changed.

Hypotheses and objects, in node order:

- `D : FiniteFieldDatum.{u}` supplies p prime, a positive, q=p^a, k₀ of cardinality
  q, and its fixed algebraic closure k, with its specified inclusion.
- `c : D.CoefficientDatum` supplies ℓ prime, ℓ≠p, and the chosen algebraic closure
  Ω of ℚ_[ℓ]. Finite coefficient fields are the recorded
  `Padic.FiniteCoefficientFields c.l c.Qbar`; raw rational stages use
  `sfRationalConstructibleCategory`.
- `Y₀ : Over (Spec (.of D.k₀))`, `[LocallyOfFiniteType Y₀.hom]`,
  `[QuasiCompact Y₀.hom]`, and `[IsSeparated Y₀.hom]` are respectively the
  k₀-scheme, finite-type and separated hypotheses. Y is
  `(D.geometricFiber Y₀).left`, and s is `Spec (.of D.k)`.
- The stipulated normalized comparison family is the datum
  `C : IntegralComparisonSystem c.l`, with `_hC` asserting
  `IntegralComparisonRealizationCoherence` for its coefficient inclusions.
  This is a parameterization of the source's specified simultaneous comparisons,
  exactly as in the recorded finite-coefficient comparison theorem, rather than
  a new geometric, lattice or Tor assumption. Here all fields are quantified
  because the conclusion concerns the entire common-stage category. The system
  includes the whole strict quotient-diagram normalization, equality-of-map
  transport, composition, units and towers.
- `r : ℕ` represents n=r+1, and
  `x : D.extensionPoints Y₀ (r+1) (Nat.succ_pos r)` is exactly the requested
  F_(q^n)-point. Every positive n is covered, including n=1 at r=0.
  `localExtensionPoint` is xbar. The return construction invokes the recorded
  `localExtensionPoint_return`, whose equation is semilinear.
- g_Y is `(D.geometricFrobenius Y₀).hom`; g_s is `(frobeniusPointIso D).hom`.
  `localPositivePower` represents positive powers. We use the direct pullback
  along g_Y^n, canonically identified with T_E^n by the stipulated compositors.
  This is the same presentation used by the recorded normalization and
  coefficient-extension modules, with d_n their specified power comparison.

Conclusion, clause by clause:

1. P_E is `LocalFrobeniusCoefficient.fibre`: rational pullback at xbar composed
   with `pointRationalFibre`. T_E^n in the compositor presentation is
   `LocalFrobeniusCoefficient.pullback ... r`. The map J_E,K is exactly
   `LocalFrobeniusCoefficient.returnTransport ... C r x K`; it expands to the
   successive rational point transports and the normalized semilinear return,
   with no Weil structure. `FiniteNaturality` states
   `P_E(v) ≫ J_E,L = J_E,K ≫ P_E(T_E^n(v))`. Lean uses left-to-right
   composition, so this is the node's first displayed naturality equation.
2. b_K is the isomorphism `LocalFrobeniusCoefficient.pointComparison`, namely
   inverse `pointRationalFibreScalarIso` followed by point fibre of
   `LocalFrobeniusTransport.rationalScalar`. d_n is
   `LocalFrobeniusCoefficient.comparison ... r`, the specified scalar comparison
   for the scheme power. `ScalarEquation` states precisely
   `R(J_E,K) ≫ b_(T^n K) ≫ P_M(d_n,K) = b_K ≫ J_M,S(K)`.
3. `ScalarCoherence` explicitly gives naturality of b for every rational
   underlying map, its identity-extension normalization using
   `sfRationalScalarUnit` and `DerivedCategory.fieldScalarUnit`, and its tower
   formula using `sfRationalScalarComp` and `pointFibreFdTensorTower`.
   All embeddings, including identities and repeated fields, are allowed.
   Applying `ScalarEquation` to each link and to the composite, with this tower
   law and `_hC`'s scalar-power tower law, expresses the stated compatibility
   of the transport equation with identity extensions and towers.
4. The common-stage P is the existing composite
   `commonStageDerivedPullback ... xbar ⋙ pointQbarFibre ...` from the literal
   pair category `generalAlgebraicallyClosedConstructibleCategory` to
   `DerivedCategory.PointFdQbar`. Both factors are already actual functors,
   with recorded normalized representative actions; the construction is reused
   directly rather than positing an arbitrary functor. `pointObjectIso` is the
   composite of their defining object identifications with the literal pair
   `(E, P_E K)`, including the existing Shrink-to-subfield coefficient transport.
   The existing map formulas give the node's conjugation by b on common-stage
   representatives, and therefore their independence and functor laws.
5. `component` constructs J_K by inserting `pointObjectIso` at the two
   boundaries of the recorded finite-stage `returnTransport`, mapped by the
   Shrink coefficient equivalence and `pointFdQbarStage`. Thus its finite
   representative is specified; no arbitrary map is chosen. The final boundary
   uses the defining `localQbarPullbackStageIso` for the actual common-stage
   pullback object.
6. `CommonNaturality` states the node's last equation for every morphism
   `v : K ⟶ L` in the actual common-stage quotient category. K and L are all
   bounded constructible complexes, with no Weil structure.
7. `RepresentativeCompatibility` explicitly specializes compatibility to the
   canonical `StageSystem.isoToStage A h` for every larger coefficient field M.
   It compares the constructed J_A and J at the literal scalar-extended pair,
   using P and T^n on their canonical boundary isomorphisms. Equal fields and
   arbitrary towers are included. Since the action is on actual quotient Hom
   classes, eventual equality of representatives gives identical arrows.
8. Neither statement nor construction assumes a Weil-stable lattice,
   finite-Tor reductions, or the false scheme equality g_Y^n xbar=xbar.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`,
  `geometricFiber`, `extensionPoints`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPositivePower`,
  `localExtensionPoint`, `localExtensionPoint_return`,
  `localQbarPullbackStageIso`; its local transport/return definitions fix
  the intended map recipe.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `stageSystem`,
  its recorded `StageSystem.PairCategory` and canonical `isoToStage`.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `IntegralComparisonSystem`, `IntegralComparisonRealizationCoherence`,
  `integralPullbackComparisonRealization` and its normalized comparison formulas.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`,
  `pointRationalFibreScalarIso`, `pointFibreFdTensorTower`, `pointQbarFibre`,
  `pointQbarFibre_existsUnique`, `pointStageFibre` and its representative action.
- `Sheaf.Paper.LocalFrobeniusCoefficientExtension`:
  `LocalFrobeniusCoefficient.fibre`, `pullback`, `scalar`, `comparison`,
  `pointComparison`, `returnTransport`. Its proof-only normalization hypothesis
  supplies the precedent for expressing the source's stipulated family by C.
- `Sheaf.Paper.LocalFrobeniusTransportNormalization`: `rationalTransport`,
  `rationalFibreScalar`, `rationalScalar` and
  `localFrobeniusTransportNormalization` (proof import). Its complete naturality
  and scalar clause was read, not just its declaration name.
- `Sheaf.Paper.PointSectionsScalarExtension`: `pointSectionsScalarExtension`
  and its rationalized naturality, identity and tower clauses (proof import).
- `Sheaf.Paper.PointFdQbarCategory`: `DerivedCategory.PointFdQbar`,
  `pointFdQbarStage`, `pointFdQbarStageComp`,
  `pointFdQbarCocone_isFilteredTwoColimit`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback`,
  `commonStagePullbackObject`, `commonStagePullbackComparison` and its
  `existsUnique` object/representative specification.
- Existing transitive scalar dependencies: `sfRationalScalarUnit`,
  `sfRationalScalarComp`, `DerivedCategory.fieldScalarUnit`, and the
  `Shrink.algEquiv` coefficient identification.

The repaired item adds only `def-fd-local-frobenius-coefficient-data` to its
original five statement dependencies. It no longer adds the theorem node
`lem-fd-local-frobenius-coefficient-extension`. The new definition record uses
`existing: true` and the same public module import for the actual data; no theorem
or `Properties` predicate supplies those definitions. The positive-power
`pullback` already has the landed owner `def-fd-specified-weil-iterate`, which the
new node cites. The point-category and derived-pullback definitions remain in
the original prerequisite closure (and are explicitly imported where used).
No existing dependency node is changed.

Edge cases checked before writing: n=1; nonminimal positive return periods;
E=M and E=M=N; arbitrary coefficient towers; zero complexes and zero morphisms;
noninvertible underlying morphisms; objects with no Weil structure or stable
integral lattice; and an empty scheme or empty rational-point set (there is then
no x to instantiate). The target remains the full bounded finite-dimensional
point-complex category, not H^0 or only the constructible heart. The scheme,
finite field and coefficient universe uses the published dependency size
conventions; every variable and universe is explicitly bound.

Searches, performed with the required `msearch.py Q68 <item>` wrapper:

- LeanFinder: "Point fibre and semilinear Frobenius return transport descend
  naturally to common-stage rational constructible complexes". Eight results,
  including `PerfectionMap.map`, Witt-vector Frobenius/isocrystal facts and
  perfect-closure maps; none is this statement.
- Loogle: `CategoryTheory.NatTrans, CategoryTheory.Functor`. Twelve generic
  natural-transformation results (`NatTrans`, `naturality`, `app`, etc.);
  no normalized adic point-return/common-stage descent statement.
- Mathlib grep: `commonStagePoint|semilinear.*return|rationalTransport`.
  Zero hits.
- LeanSearch: "The point fibre functor on constructible rational complexes has
  natural semilinear Frobenius return compatible with finite coefficient
  extension and common stage descent". Eight results: semilinear ring
  Frobenius, generic site fibres and Galois-category fibre functors;
  none gives this normalized derived transport.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `commonStagePointReturn`/`CommonStagePointReturn`: no existing declaration.
  Broader searches for point functors, return transports and scalar comparisons
  found the existing constructions listed above, which are reused. In
  particular the downstream `wfPointFunctor` is just the same composite and
  is not redefined or imported here, avoiding a proof-dependency cycle.
- The raw remote search results are retained in the sandbox's `searches.jsonl`.

Source check: the item's older source path
`sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md`
is no longer a separate file in `literature/blueprint/latest`. I read the current
trace-transport `_section.md` (local Frobenius is return around the orbit) and
current `sec-purity-real-sheaves/sk-lem-wrp-l2-growth/lem-wf-l2-upper.proof.md`
(opening punctual-Frobenius clause), together with the accepted node's five-step
agent-extracted argument and its exact recorded normalization dependencies.
This delivery preserves that accepted node statement and proof verbatim.

Validation of the returned head: the module compiled twice in the prescribed
private server modes (sandbox and actual library module name), with no errors or
unexpected warnings. The repair changes only a comment in the module, the item
prerequisite record, this report, and the new existing-definition node. Fresh
repair compilation and delivery-preflight results are recorded below. The file
uses `module`, public statement imports and plain proof imports, and sets
`autoImplicit false`. No `#check` probes remain. Its only postponed proof is
`WeilConjectures.commonStagePointReturn`, with the source and complete five-step
proof in its docstring.

No STATEMENT-DISPUTED flag or mathematical node correction is required.

## Second reading by Q68

Final self-audit against the open node and module: the finite equation has the
same orientation after reversing notation from function composition to `≫`;
b is the inverse-sections-then-pullback comparison, not its inverse; d has source
S(T^n K); and the common-stage component has the canonical object identifications
on both endpoints. The point is an extension-valued point, not an arbitrary
fixed scheme point. The exponent r+1 covers all positive n. ScalarCoherence
includes the completed source associator and ordinary point tensor associator,
and RepresentativeCompatibility includes equality of fields. No Weil-pair or
heart restriction appears. No mismatch was found in this self-audit; the
maintainer's independent review is separate, as the dispatcher brief specifies.

## New nodes

`def-fd-local-frobenius-coefficient-data` records the existing normalized rational
point-fibre, coefficient scalar extension, power scalar comparison, point scalar
comparison, and positive return transport. Its primary declaration is
`WeilConjectures.LocalFrobeniusCoefficient.returnTransport`; the record also lists
`fibre`, `scalar`, `comparison`, and `pointComparison`. The sixth reused coefficient
helper, `pullback`, has already landed under `def-fd-specified-weil-iterate`; this
new node cites that owner rather than duplicating it. The module is
`Sheaf.Paper.LocalFrobeniusCoefficientExtension`, with `existing: true` and no new
Lean file. Thus the item's existing public import now imports definition-node
data rather than using the coefficient-extension theorem as their owner.

The return advisory is repaired explicitly: the record also lists the publicly
re-exported `LocalFrobeniusTransport.rationalPointIterate`, `rationalReturn` and
`rationalTransport`. Its natural-language statement gives the recursive
successive point transport, then the inverse compositor, equality transport and
forward compositor around the semilinear square, followed by the extension-point
specialization. These are the actual composites in the existing source, not an
arbitrary return arrow or existence choice. The normalized compositor and scalar
comparison themselves are the previously owned notion of
`def-trf-realized-pullback-comparisons`; their localized integral component formulas
are spelled out and cited. No transport property theorem is used as an owner.

Source: the current blueprint local-Frobenius definition, its derived stalk and
positive iterate/return paragraphs; the new node is attached to the unchanged
`lem-wf-l2-upper` ancestor through this item and `lem-wf-rational-stalk-exact`.
The construction is the finite-stage data used in the item's accepted
five-step common-stage argument, before applying a Weil structure. Definitions
have no separatedness, Weil, lattice or Tor condition; the item's existing
separatedness hypothesis remains exactly as independently checked.

Searches for this definition node were made before adding it. `leansearch`
("Normalized rational point Frobenius return transport and coefficient scalar
comparison data") and `leanfinder` ("Rational constructible point fibre pullback
coefficient extension comparison and successive semilinear Frobenius return
construction") each returned eight Witt-vector, perfection or purely inseparable
Frobenius results. Mathlib grep for
`rationalTransport|pointComparison|LocalFrobeniusCoefficient` returned zero hits.
Direct project searches found the exact existing definitions reused here; DAG
and blueprint searches found theorem nodes and the recently landed
`def-fd-specified-weil-iterate`, but no owner for the other five coefficient
helpers and rational return recipe. The raw remote results are in
`searches.jsonl`; the new node records the queries and results. This is definition
ownership, not a duplicate implementation.

## Returned-delivery repair

H2 of the immutable head `d43bcd840b0b`: removed the added coefficient-extension
theorem prerequisite and replaced it with the new definition node above. Removed
the two other added existing-node prerequisites as direct item additions: they
were already in its original prerequisite closure. The item now changes only
`lean` and `stmt_deps`, and the sole added direct prerequisite is a new definition
node in this delivery. All mathematical statement/proof fields are unchanged.
The return-transport advisory is handled by the explicit existing-definition
bindings and full return recipe in the new node. The landed pullback owner is
cited rather than recreated. No imported source definition is copied or changed.

Repair self-audit: read the new definition statement against every bound existing
definition. The point comparison is inverse sections comparison followed by the
fibre of the pullback/scalar comparison. The positive recursion uses successive
one-step point transports, not a transport chosen for the composite power. The
return comparison has inverse first compositor and forward second compositor,
with equality transport in between. Generic `rationalTransport` takes arbitrary
`z,w`; `returnTransport` uses the canonical extension point and its semilinear
return. The record exports all these data through the same public import.

Repair compilation: `scompile.py Q68 lem-wf-common-stage-point-return` completed
with exit 0, no errors and no warnings, for both `Sheaf.Stage2.Sandbox0`
and `Sheaf.Paper.CommonStagePointReturn` (reported 20.8 s and 90.4 s wall times,
including server slot acquisition; the default per-file compiler limit was unchanged).

Repair dry run: `deliver2.py Q68 lem-wf-common-stage-point-return --no-push`
printed `OK (dry run)` at `a2e7899c0c8`: server preflight, the existing-definition
public-declaration probe and the delivered module compile all passed.
