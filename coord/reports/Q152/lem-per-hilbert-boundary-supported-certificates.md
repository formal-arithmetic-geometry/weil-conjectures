## Worker report

The item is stated in `Sheaf.RingTheory.HilbertBoundarySupportedCertificates`, namespace
`AlgebraicGeometry.HilbertCoefficient`. The main declaration is
`hilbert_boundary_supported_certificates`. Its two companion declarations state the
coefficient-field extension and conditional boundary Taylor-chart clauses. All three proofs
are `sorry`; their docstrings carry the owning node's proof, including the minimal failing
order, strict dimension drop, closed supported-sum argument, and saturation calculation.
No mathematical statement of the item was changed.

Hypothesis and clause reading, against the node:

- `L : Type u`, `[Field L]`, `[CharZero L]` render the characteristic-zero coefficient field.
  `m r s : ℕ` and the split variable set `Fin m ⊕ Fin r` render all finite coefficient,
  transverse and generator counts. `f` is the actual family of formal series; its ideal is
  always `Ideal.span (Set.range f)`, never an arbitrary ideal containing that family.
- `α`, `cert.positive`, and `cert.ordered` give positive vertex degrees and the ordered minimal
  orthant vertices. Their full vertices are the existing `fullVertex m (α i)`, with zero
  coefficient-variable components. Every quotient support is the recorded
  `MonomialDiagram.quotientSupport` of these full vertices. `generated` is the union of orthants.
- `A`, `cert.homogeneous`, and `cert.pureDivision` give the pure transverse homogeneous forms
  and unique division in every degree of every degree prefix. Prefix indices are the recorded
  `prefixVertices α q`, including all vertices of a common degree together. There is no first
  exponent hypothesis on the deformed `f`: it is precisely the order condition that may fail.
- `cert.transverseJet` equates the coefficients at `(0,γ)` through degree `d_i` to `A_i`.
  Thus it says `f_i(0,Z) = A_i` modulo degrees greater than `d_i`, including the required zero
  coefficients in smaller degrees.
- `cert.multiplication` quantifies over every `i` and every transverse exponent `γ`, producing
  a supported series quotient for every generator. The equation is between whole series.
  It is outside the order-condition implication, so these certificates are required even
  away from the equality locus.
- `cert.pick` and `cert.beta` choose derivatives only for `EssentialVariables α`.
  `pick_vertex` is `α_(i(j)) = β_j + e_j`; `pick_prefix` places the choice in the first block
  where the variable is essential. `block_membership` and `block_jacobian` express membership
  in the actual prefix transverse ideal and invertibility of its constant Jacobian determinant.
  The determinant includes exactly the accumulated essential variables in its row and column set.
- `cert.later_derivatives` requires the existing `iteratedPartial` of each later generator to
  lie in the existing `transverseIdeal` whenever `δ` is supported on prefix essential variables,
  belongs to its diagram (`inDiagram α q δ`), and has degree at most `Q`.
  `cert.bound` is `d_i - 1 ≤ Q` for every `i`, equivalent to the maximum bound and meaningful
  for the empty family. Only actual degree blocks require Jacobian and derivative certificates.
- `transverseCoefficient` is the actual coefficient series: its `μ` coefficient is the
  coefficient at `(μ,γ)` of `f_i`. `BoundaryOrderCondition α f` says exactly that this series
  belongs to `(W)^(d_i-|γ|)` for every low transverse degree. Thus zero coefficients have
  infinite order. This uses literal ideal-power containment, as the node explicitly requests,
  without turning a formal ring into a scheme stalk merely to use scheme ideal-order notation.
- `boundaryHilbert` is `Module.finrank L` of the actual quotient by `I ⊔ (W,Z)^(t+1)`.
  These quotients are finite dimensional (a quotient of the finite total-degree truncation).
  The complement count is the `Set.ncard` of the literal finite set of exponents outside the
  generated full diagram and of degree at most `t`. The existing `HilbertSamuel.le` and `.lt`
  give lexicographic comparison, with equality up to the first differing degree.
- The first two conjuncts of `SupportedBoundaryConclusions` give `H_K ≤lex H_D` and
  `(∀ t, H_K(t)=H_D(t)) ↔ S`. The implication from `S` supplies exact series orders,
  `HasUniqueDivision` for every prefix's degree-`d_i` initial polynomials, supported generation
  of the entire ideal, and saturation equality for every coefficient coordinate. The initial
  polynomial is `truncTotal (d_i+1) (homogeneousComponent d_i (f_i))`, not a truncation of
  the complete series that might retain lower terms in the failure case.
- `boundarySaturation` is the supremum of the increasing chain of coordinate-power colons,
  constructed using `Submodule.colon`. The next conjunct explicitly states its exact existential
  membership criterion, including exponent zero. The final conjunct gives pointwise decrease
  of `H_K` after saturation and persistence of any strict lexicographic drop from `H_D`.
- `hilbert_boundary_supported_certificates_map` quantifies over any field homomorphism
  `φ : L →+* E` in an independent coefficient universe. It asserts the same full conclusions
  for coefficientwise mapped series and equivalence of the old and new order tests.
  `[CharZero E]` is inherited automatically by every field extension of `L`, not a restriction
  on the extensions covered. No algebraic, finite, separable, or algebraically closed
  extension assumption is imposed.
- `boundaryChartVariables u v ξ` has exactly `W_u ↦ W_u=e`,
  `W_v ↦ W_u(ξ+W_v)`, the other `W` fixed and all `Z` fixed. Here the target `W_v` is the
  Taylor displacement `V`. `hilbert_boundary_supported_certificates_chart` uses Mathlib's
  actual `subst` after coefficient extension, and requires retained pure forms and
  whole-series certificates on those actual substituted series. It concludes the whole
  conclusion predicate for them, as requested conditionally by the node. Distinct `u,v`
  are the two distinct labelled boundary coordinates. Every image has zero constant
  coefficient, so this is an ordinary continuous formal substitution. There is no
  exceptional-power division. Every regular Taylor model mentioned by the node is covered
  by its residue field and resulting series; no additional geometric existence is asserted.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; characteristic zero is Mathlib `CharZero`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `coeff`, `monomial`, `X`, `map`.
- `Sheaf.RingTheory.SupportedHomogeneousDivision`: `MonomialDiagram.generated`,
  `IsOrderedVertexFamily`, `quotientSupport`, `prefixVertices`, `HasUniqueDivision`,
  `EssentialVariables`; their full definitions and indexed-division signatures were read.
- `Mathlib.RingTheory.MvPowerSeries.Derivative`: `MvPowerSeries.pderiv`, the actual derivation
  with coefficient at `d` equal to the coefficient at `d+e_j` times `d_j+1`.
- `Sheaf.AlgebraicGeometry.MarkedIdealOrder`: `HilbertSamuel.order` and `stalkIdeal` were read.
  The item instead expressly defines formal coefficient order by maximal-ideal-power
  containment; its module is imported as the recorded statement dependency.
- `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank`, whose cardinal rank conversion
  is the actual finite quotient dimension in this application.
- `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum`: `fullVertex`, `supported`,
  `essential`, `transverseIdeal`, `iteratedPartial`, `inDiagram`. These already define
  the needed constituent notions and are reused, with the landed owning node added to
  `stmt_deps`. Its geometric datum is not assumed.
- `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`: `HilbertSamuel.le`, `HilbertSamuel.lt`;
  the landed owning node is added to `stmt_deps`.
- `Sheaf.RingTheory.HomogeneousDivisionExtraVariables` is a plain proof import for the
  recorded `hasUniqueDivision_extraVariables_iff` and `_map` statements. The continuous
  formal division proof dependency has no recorded declaration locally, so no unrecorded
  proof module is imported. The main proof docstring names that DAG input for stage 3.
- Mathlib's `Submodule.colon`, `MvPowerSeries.homogeneousComponent`, `truncTotal` and `subst`
  supply all the remaining operations; no arbitrary canonical map or existence choice is used.

Edge cases checked before drafting and again on reading:

- `s=0`, including `r>0`: no artificial map `Fin r → Fin s` is required; the essential-variable
  type is empty. Pure division is the monomial basis, `K=0`, `D=∅`, `S` is vacuous, and
  coordinate saturation leaves zero because coordinate multiplication is injective.
- `m=0`: the coefficient order tests are order in the zero-variable ring, the saturation
  quantifiers are empty, and boundary charts need two coordinates and hence have no instance.
- `r=0`: positive degrees force the vertex family empty. Empty degree prefixes also have no
  determinant or later-derivative assumptions; the complement-monomial interpretation remains.
- `t=0`, degrees below a vertex, vanishing coefficients, `Q=0` with degree-one vertices,
  and the saturation exponent `v=0` are all retained by the formulas. A failed coefficient
  condition is allowed by the certificate data; no fixed order of `f_i` is a hypothesis.
- Field extensions may have independent universes or be the identity. In boundary charts
  `ξ=0` is allowed and the transverse variables are literally unchanged.
- The first degree-prefix variables are not required to exhaust all transverse coordinates.
  The later-derivative condition explicitly kills whole coefficient series in the complementary
  variables; replacing that membership by a condition on initial forms would lose the strict-drop
  argument and was avoided.

Searches for an existing statement or definition:

- `msearch.py leanfinder`: "Supported formal power series division Hilbert Samuel coefficient
  order equality and saturation by coefficient variables". Eight related univariate
  Weierstrass division hits; no supported block-certificate theorem.
- `msearch.py loogle`: "MvPowerSeries, Ideal". Twelve hits for substitution ideals, truncations,
  adic completion and mapped coefficient ideals; no requested comparison.
- `msearch.py leansearch`: "Formal power series Hilbert Samuel function coefficient ideal
  saturation". Eight results about univariate coefficient ideal products and Noetherianity;
  no certificate package.
- `msearch.py grep`: "hilbert.*[Ff]unction|supported.*division|saturation" restricted to
  `RingTheory/MvPowerSeries`, and "transverseCoefficient|boundarySaturation|
  SupportedBoundaryCertificates|boundaryHilbert" globally: no exact hits.
- `rg` in `lean/WeilConjectures` for the item id and supported/boundary Hilbert division:
  no declaration. `rg` in `lean/Sheaf` found and prompted reuse of the block derivative
  helpers in `RegularHilbertCoefficientDatum`, lex comparison in `HilbertSamuelInvariant`,
  and indexed polynomial division in `SupportedHomogeneousDivision`. `FormalInitialDiagram`
  has complement counts and truncations for `Fin d`; here the literal split-variable
  count and quotient are written without creating another initial-diagram definition.
- Searched `dag/nodes` for the certificate package, coefficient orders and saturation;
  the geometric coefficient datum and coefficient-order equality theorem differ from
  this off-locus whole-series hypothesis package. `tools/blueprint_refs.py search
  'supported boundary'` and `'boundary certificate'` both returned zero blueprint nodes.
- Read the current blueprint unit and affine-curve ancestor in `literature/blueprint/latest/`.
  Read BMT 6.1--6.6 at https://arxiv.org/html/0905.3580; specifically 6.5 gives the
  complement count, and 6.6 identifies BM (7.2) as the formal conditions. The detailed
  step-by-step algebra used here is the owning DAG node's explicitly written argument.

No statement correction or disputed mathematical assertion was needed. A compiler issue
in the definition of the finite essential-variable Jacobian was repaired by supplying
concrete finite enumerations; it does not change its determinant or its hypotheses.

## Repair of return 4f885346c5ec

The return names three duplicates: `boundaryChartVariables`, `boundaryHilbert`, and
`boundarySaturation`, attributed both to the helper module and the item module. I read
both delivered sources retained in the sandbox and the return in `coord/returns/Q152.md`.
The delivered helper module declared all three; the delivered theorem module imported it
and declared only the three theorem statements. Neither module exists in the current
local main source tree. The prescribed live server source lookup (`scompile.py --source`)
also reports "Module source unavailable" for both module names. Thus there is no live
source definition to import, and importing the reported item module from its own helper
would in any event create an import cycle.

The repair removes the split that triggered the source-index collision. There is now one
module, `Sheaf.RingTheory.HilbertBoundarySupportedCertificates`, containing all eight
concrete helper definitions/data specifications followed by the three consuming theorem
statements. The three named definitions retain their canonical names and exact bodies in
the module the return identifies as their existing location. The other helper declarations
also retain their names and bodies. No definition or theorem has been renamed or copied;
the separate `SupportedBoundaryCertificates.lean` source is removed from the delivery.
The redundant new definition node `def-per-supported-boundary-certificates` is also
removed, and the item no longer adds it to `stmt_deps`. All eleven declarations are
recorded in the item's `lean.declarations` and carry its source/blueprint docstrings.
This uses the explicit authorization for helper definitions belonging to the same notion
in the owning node's module (brief-stage2 section 1, Missing helpers). Its other two
landed definition dependencies remain recorded. The original mathematical statement,
theorem signatures, hypotheses, conclusions and definition bodies are unchanged.

## Second reading by Q152

This is the worker's second pass with the original item, the repaired item record and the
consolidated module open. No other agent was started, as required by the dispatcher;
the maintainer supplies the independent review. I checked each of the three returned
names: each now has exactly one source declaration, in the item module, and all its
consumers refer directly to that declaration. The module has no import of its former
helper or itself. All eleven declarations are listed in the one owning record.

I compared the consolidated definition bodies and theorem signatures against the retained
version described by the returned head: the change is solely placement, imports,
blueprint ownership and node metadata. The clause mapping above still applies literally:
whole-series multiplication is required away from S; pure-prefix division is a hypothesis
and full-prefix division a conclusion; the essential-variable derivative choices still
include empty families with transverse variables; and coefficient saturation retains the
existential power criterion and both Hilbert-decrease conclusions. Field extensions and
the conditional ordinary boundary chart application are unchanged. All definitions have
real data, and each of the three theorem proofs remains exactly `by sorry`.

Validation of the repair: `scompile.py Q152 lem-per-hilbert-boundary-supported-certificates`
compiled the consolidated file cleanly in sandbox and library module modes (10.0 and
7.8 seconds). `deliver2.py ... --no-push` then reported `OK (dry run)` for commit
`cdc36bd2e52`: preflight passed and the consolidated file compiled. The packet contains
only the item record, its single canonical module, and this report; no helper module or
new definition node remains. The added dependencies are exactly the two existing landed
definition nodes already justified above. The live-source lookups, failed because their
modules are absent, were read-only; all edits stayed in this sandbox.
