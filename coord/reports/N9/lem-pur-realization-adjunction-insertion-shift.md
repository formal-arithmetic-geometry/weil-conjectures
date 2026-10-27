## Worker report

The module Sheaf.SixFunctors.RealizationAdjunctionInsertionShift states
`WeilConjectures.IntegralSystemRealization.realizationAdjunctionInsertionShift` with
one `sorry`. Definitions contain real composites and predicates only. There are no
new nodes, dependency repairs, statement corrections, or disputed statements.

The proposition `RealizationAdjunctionInsertionShift` has six fields, for the inverse
unit, pullback, proper image, open extension, first tensor slot, and second tensor slot.
Its generic helper `InsertionShiftLaw` records coherence of the specified source/target
shift comparisons, invertibility of the actual insertion on the domain, the displayed
square for every integer, and naturality in all morphisms between admissible inputs.
These helpers belong to this node, rather than introducing independent constructions.

Hypotheses and clauses, read against the node:

- The global algebraic closure of a finite field, its characteristic p, and q are
  `D : FiniteFieldDatum.{u}`. The coefficient prime is `l : ℕ`, `[Fact l.Prime]`,
  with `_hl : l ≠ D.p`. The finite extension is `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. The valuation ring,
  uniformizer, and all positive quotient levels are those already used by calculus;
  level index n in the library means exponent n+1. No new coefficient ring is defined.
- Schemes are `Over (Spec (.of D.k))` with `LocallyOfFiniteType` and `QuasiCompact`
  on the structure map: exactly finite type over the fixed k. Arrows are over k.
  Pullback additionally requires `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`;
  proper image requires `IsProper`; open extension requires `IsOpenImmersion` and
  `QuasiCompact`. No separatedness assumption on the individual schemes is added.
- `System l E W` and `Integral l E W` are the published unbounded derived categories
  on the small pro-etale sites; `calculus.reduction`, `coefficientSequenceLimit`,
  and `calculus.adjunction` give the actual R, L, unit and counit.
- Each operation domain is `GeneratorReduction.SystemAdmissible` on both its input
  and output. Tensor requires it for M, N, and their tensor, all at exactly the same
  `lo hi torLo torHi`. This predicate expands to normalization, compatible
  `Origins`, constructibility at every positive level, common bounded cohomology,
  and common finite Tor amplitude. No arbitrary finite-level arrow lift is used.
  The integral variable domain explicitly requires `sfIntegralConstructible` and
  the same admissibility of its actual reduction. Integral inputs elsewhere are
  the actual L M, whose completeness/constructibility is the reconstruction-domain
  property used by the recorded recursion. They are not extra arbitrary inputs.
- The operations and their integral counterparts are exactly those of `o : Operations`
  and `c : Realizations l E D o`. `c` also supplies the fixed canonical realization
  family and proper/open realization model, needed by `Recursion.properA/openA`.
- The inverse unit is `GeneratorReduction.inverseOrZero (calculus.adjunction.unit.app K)`.
  The other maps are exactly `Recursion.pullA`, `properA`, `openA`, `tensorA`.
  Opening those definitions gives inverse L A(e), then d_A(L M), and inverse
  L(e_M tensor e_N), then d_tensor(L M,L N), in Lean's diagrammatic order.
  `InsertionShiftLaw` asserts `IsIso` on the stated domains, so inverseOrZero is
  there the genuine inverse. Its arbitrary ambient zero branch changes no asserted map.
- Source comparisons are `insertionSourceShift`: map the operation's fixed shift
  under L, then the fixed L shift. Targets are `insertionTargetShift`: map the L
  shift under the integral operation, then its fixed shift. At a variable the source
  is reduction shift mapped under L, then L shift, and the target is identity.
  `insertionCompositeShift` constructs precisely these composites.
- The tensor fields use the curry and flipped curry of the actual bifunctors, so
  the unshifted operand is held fixed in each designated slot. Both system and
  integral shifts come directly from `tensorShifts.systemLeft/systemRight` and
  `integralLeft/integralRight`. The right properties are pinned to (-1)^(r i);
  the left properties are unsigned. The integral shifts and `limitShift` retain
  their existing product and cone normalization, with diagonal (1,(-1)^r).
- The exact equation is `a (M⟦r⟧) ≫ (τ r M).hom =
  (σ r M).hom ≫ (a M)⟦r⟧'`: this is χ_target a(M[r]) = a(M)[r] χ_source
  in the node's functional order. Naturality is `F.map f ≫ a N = a M ≫ G.map f`.
  Tensor naturality in each operand implies joint naturality by bifunctoriality.
- The two explicit existential clauses in `InsertionShiftLaw` say an actual Mathlib
  `CommShift ℤ` has exactly these fixed
  components, thereby asserting naturality, zero normalization and addition coherence
  for these comparisons, not for replacement choices. All `r : ℤ` are included.
  `limitShift` is specifically the shift with the representative characterization
  `limitShift_roos`; no finite-level equality detection or endpoint choice is added.

Dependency declarations read and used:

- Sheaf.Paper.CoefDerivedSystemEvaluationCalculus:
  `CoefficientDerivedSystemCalculus` (actual adjunction, reduction, system tensor),
  `coefficientDerivedSystemEvaluationCalculus` and its full proof docstring.
- Sheaf.SixFunctors.IntegralCompactificationSystemRealization:
  `Realizations`, its comparison and realizationModel fields, and
  `integralCompactificationSystemRealization`.
- Sheaf.SixFunctors.IntegralOperationShiftData:
  `TensorShifts`, `tensorShifts`, `limitShift`, `reductionShift`, `systemPullShift`,
  `systemPushShift`, `systemOpenShift`, `integralShifts`, and `limitShift_roos`;
  all four tensor normalization predicates were read.
- Sheaf.Paper.SfIntegralConstructible: `sfIntegralConstructible`.
- Sheaf.Paper.FiniteTorAmplitudeSites: `finiteTorConstructibleEtale`; its imported
  Sheaf.Paper.FiniteTorAmplitude supplies the same pro-etale/integral amplitude notions
  used by the system domains. These notions are not redefined here.
- Sheaf.SixFunctors.IntegralRealizationRecursion:
  `Recursion.pullA`, `properA`, `openA`, `tensorA`, `OperationLaws`, and
  `integralRealizationRecursion`, including its seven-step proof docstring.
- Sheaf.SixFunctors.GeneratorReductionStatement:
  `inverseOrZero`, `pullD`, `tensorD`, `openD`, `SystemAdmissible`, and
  `generatorReductionCoherence`, including its actual-map normalization.
- Sheaf.SixFunctors.IntegralBasicOperationShift: `integralBasicOperationShift`,
  retained only as a proof dependency and plain import. The statement directly
  expresses its two Mathlib CommShift component characterizations.
- Proof imports also include Sheaf.Paper.PurReductionLimitShiftAdjunction
  (`purReductionLimitShiftAdjunction`) and Mathlib.CategoryTheory.Shift.CommShift /
  Adjunction. Read `NatTrans.CommShift.comp/whiskerRight/whiskerLeft/associator` and
  `Adjunction.CommShift.compatibilityCounit_of_compatibilityUnit`,
  `compatibilityUnit_right`, `compatibilityUnit_unique_right`,
  `rightAdjointCommShift`, `commShift_of_leftAdjoint` at their recorded source places.

Edge cases checked: r=0 is covered by coherence and yields identity comparisons;
r=-1 and arbitrary negative r retain integer signs. Repeated shifts use the additive
CommShift laws, and shifting moves cohomological and Tor intervals by -r; no demand
that the shifted object retain its original interval is imposed. Empty schemes,
empty opens, and zero inputs are allowed; the canonical maps are their unique zero
maps. There is no nonzero-object assumption. Singleton intervals and degree-zero
objects are allowed. No undefined coefficient level zero is used. Tensor operands
are arbitrary normalized systems in the domain, not just chosen reductions, so
identity and arbitrary fixed-operand cases are retained. All variables and universe
parameters are explicitly bound (`autoImplicit false`).

Searches made (raw service results are also in searches.jsonl):

- msearch.py leanfinder, "Inverse reconstruction unit and actual counit insertion
  comparison commute with integer shifts for normalized coefficient systems": eight
  generic shift/commutator hits, including CommShift₂Setup.int_ε/hε and
  shiftEquiv'_counitIso; none states these insertion squares.
- msearch.py loogle, "CategoryTheory.NatTrans.CommShift": twelve generic hits,
  including comp, id, of_iso_inv, and of_isIso; reused the framework, not an existing
  statement of the specified normalized maps.
- msearch.py grep, "CommShift|commShift", CategoryTheory/Shift: 25 hits in
  Induced, Localization, Opposite, InducedShiftSequence, Twist, Adjunction; no
  specialized insertion result.
- rg in lean/WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  `insertion.*[Ss]hift|[Ss]hift.*[Ii]nsertion|realizationAdjunctionInsertionShift`:
  only three unrelated comments about insertions in ambient/Roos/clopen modules.
  rg for the exact node id in lean/WeilConjectures returned no match.
- Read the current blueprint at literature/blueprint/latest/blueprint/sec-six-functors/
  sk-thm-sf-compatibility/fix-prop-coherence.proof.md (the old source path's unit
  directory has moved). It attributes coherence to actual evaluation and adjunction
  maps. The node explicitly labels the additional shift calculation as agent-written;
  no independent shift assertion is attributed to that blueprint paragraph.

Validation of the repair: scompile.py compiled both sandbox and library forms
cleanly, in 11.9 s and 29.3 s respectively. The delivery dry run and actual delivery
also perform the required server checks.

## Second reading by N9

Author's second pass, not an independent reviewer claim; the maintainer performs
independent review of this direct worker delivery. Reopened the node, recursion
formulas, shift-data representative predicates, and delivered Lean. Checked all six
fields against their specified operations, direction of the composite, correct input
site for each L, and the fixed right tensor signs. The proper target is the recorded
integral proper direct image, rather than its defining strict tower; its map is exactly
Recursion.properA with the realization model's canonical conjugate. The open target
is ringedOpen and map is exactly Recursion.openA. No normalization was replaced.
Both tensor slots use arbitrary good system operands, with both counits in tensorA;
they are not restricted to reductions of arbitrarily supplied integral objects.
The `unit` domain explicitly includes completeness and constructibility and reduction
bounds. The per-input and intermediate bounds use the same four integers. The
coherence conditions are now written directly as existential CommShift structures
with fixed components; no theorem node was added to stmt_deps. No correction to the node's
mathematical statement was needed. The only postponed theorem is the item itself.

## Repair of returned delivery 5c1a6366d3b6

H2 / theorem-statement dependency: removed lem-pur-integral-basic-operation-shift
from stmt_deps, restoring the current base's seven entries verbatim. It remains
in proof_deps, unchanged. Replaced the public import with a plain proof import.
In InsertionShiftLaw, expanded each use of BasicShiftCoherent into exactly its
body: an existential F.CommShift ℤ (respectively G.CommShift ℤ), whose component
at every integer and input equals the fixed σ (respectively τ). No separate copy
of BasicShiftCoherent is declared. This is the reviewer's requested inlining and
is definitionally the same proposition. No .choose or theorem is needed to state it.

Compared the retained sandbox node with the current read-only main node: all
non-lean fields now agree, including stmt_deps and proof_deps. Delivery wrappers
rebase the resulting three-file delivery onto current main without direct git
mutations in the shared repository. Rechecked all six statement fields: no
insertion map, domain, shift comparison, square or naturality clause changed.
Compilation and the prescribed dry run are rerun for this repaired source.
