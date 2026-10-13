## What changed

Replaced the main theorem's hole by an assembly of the existing
`AlgebraicGeometry.internalHom_overEquiv` and two new intermediate statements:
`OrdinaryEvaluationTensorSummands` constructs the unit-normalized symmetric
monoidal comparison and fixes its action on total summand inclusions;
`OrdinaryEvaluationComponentOverTransport` computes the transported evaluation
components for an already fixed normalized tensor comparison. The main module
chooses the comparisons and applies the fixed-comparison component calculation.
Its statement and all existing definitions remain unchanged.

## Proved and sorry left

Closed `AlgebraicGeometry.exists_ordinaryEvaluation_over_tensor_formula`
(node `lem-pc-ordinary-evaluation-over-tensor-formula`) by decomposition.

Two holes are added, each the entire proof of a public named theorem:

- `AlgebraicGeometry.exists_ordinaryEvaluation_tensor_summands`
  (`lem-pc-ordinary-evaluation-tensor-summands`). This contains no Hom comparison,
  evaluation map, or evaluation predicate: it is the normalized tensor construction.
- `AlgebraicGeometry.ordinaryEvaluation_component_over_transport`
  (`lem-pc-ordinary-evaluation-component-over-transport`). This assumes an already
  fixed tensor comparison with its precise summand equations and proves its
  evaluation compatibility. It constructs neither c, the monoidal structure,
  nor the Hom comparison. Thus its hypotheses are supplied by the independent
  tensor construction, rather than a repackaging of the original existential goal.

This is a decomposition of one upper hole into two strictly smaller obligations,
not an axiom-free proof of the entire mathematical result. No hole is left inside
any definition or inside the main proof.

## No longer needed

No existing library imports or planned dependency modules are pruned. The two
original public imports remain required by the statement. InternalHomOverEquiv
and the two new modules are imported only for the proof.

The earlier sandbox's `OrdinaryEvaluationTensorCompatibility` module and its
unlanded node are removed. Their broad compatibility statement is replaced by
normalized tensor summands and fixed-comparison component calculations, combined
directly in the main module. They were never library modules, so their removal is not
counted as pruning the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left both the main hole and its new compatibility hole open,
and its new node lacked the required searches and a verbatim Lean statement.
The main wrapper itself can compile: keeping existential witnesses as local terms
avoids the expensive dependent motive produced by `obtain`. Local irreducibility
of `homComplexFunctor` and `IsSchemeOrdinaryEvaluation` keeps the assembly from
unfolding their large constructions; these attributes do not change any interface.
The complete main proof compiled in 38.1 seconds under the unchanged 60-second
limit. The delivery supplies the naturality witness using the library's existing
proved theorem.

Naturality alone does not normalize a tensor comparison. The new tensor statement
therefore specifies a core monoidal structure with the canonical unit and
symmetry law, as well as the exact summand equation required by the calculation.
The original node's three steps are retained: internal Hom, tensor construction,
and component calculation. The unit's realized statement and steps are unchanged.

Edge checks: the empty open and zero coefficient ring have the same unique zero
component maps; zero P or F makes the relevant evaluation components zero.
For r+q unequal to zero the component vanishes, while r+q=0 uses the prescribed
unit coefficient action. No truncation of the coproduct is assumed. On a one-point
ringed site in characteristic different from two, changing the tensorator's sign
requires changing its unit to retain the monoidal unit laws; the fixed unit thus
excludes that spurious normalization. A simultaneous sign change in the natural
Hom comparison changes both the dual and output comparisons and cancels in the
transported evaluation. These checks do not require an open to be nonempty.

The source tags were read online. Tag 0A8X supplies ordinary Hom complexes and
canonical tensor-Hom maps; 08DL is derived internal-Hom restriction, and 08DQ's
proof supplies the ordinary representative evaluation calculation. Neither
01CD (finite type modules) nor 06YN (definition of K-flatness) is an exact source
for normalized tensor transport; the new nodes instead describe the explicit
open-site construction, marked as an agent-written elaboration of the parent plan.

## New nodes

`lem-pc-ordinary-evaluation-tensor-summands`: normalized symmetric monoidal open-site
tensor comparison, with the total summand equation and canonical unit.

`lem-pc-ordinary-evaluation-component-over-transport`: transported ordinary
evaluation components for a fixed normalized comparison, with their zero and
degree-cancelling cases.

Both inherit the parent's chapter, unit, and blueprint ancestor and have complete
proof descriptions and recorded searches. The preflight conservatively requires
a record for the local reducibility command:
`coord/changes/ordinary-evaluation-over-local-reducibility.md`.
It changes no consuming module's interface or target meaning. No forced adaptation
is needed.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered main module with the repository version: the target
statement and all existing declaration signatures are unchanged; only imports,
local attributes, and proofs were added.
2. Compiled all three delivered modules with `lcompile.py`; there are no errors,
forbidden declarations, or sorries in definitions. The two remaining sorries are
the named split theorems listed above.
3. Checked both split statements and their DAG nodes. Each has a source,
natural-language proof, recorded searches, and a verbatim Lean statement; each is
strictly smaller than the parent target and supplies only the needed hypotheses.
4. Checked the proof route and imports. The main proof uses the existing
`internalHom_overEquiv` theorem and both new split declarations; no unused planned
dependency was removed, and the unit's internal-Hom, tensor, and component route is
retained.
5. Checked edge cases in the report (zero complexes, empty opens, zero ring, and
degree cancellation); the normalized unit and symmetry hypotheses preserve the
intended evaluation formula. Verdict: the delivered proof and decomposition agree
with the target and DAG.

6. Repaired reviewer point E5 in `OrdinaryEvaluationComponentOverTransport`: the
component proof description now derives the dual/output cancellation on arbitrary
local tensor generators, uses the unit and symmetry equations for the arbitrary
normalized `m`, and applies `he` only through its naturality squares. It explicitly
avoids identifying `e` with canonical reindexing. The corresponding DAG step 2 was
updated verbatim; the main theorem statement is unchanged.

Changed only the proof assembly, added the two explicitly documented split modules
and nodes, and recorded the local reducibility attribute change. No forced
adaptation or target-interface change was needed.

## Second reading by A4

1. Compared the delivered main module with the repository version. The target
statement and every existing declaration signature are unchanged byte-for-byte;
the differences are proof imports, local attributes, and the proof body.

2. Compiled all three delivered modules with `lcompile.py`. They compile without
errors. The only `sorry`s are the two named split theorems listed above; no
definition contains `sorry`, and no forbidden declaration occurs.

3. Read both split statements and their DAG nodes. Each statement is strictly
smaller than the parent obligation, has a natural-language proof, source, searches,
and a verbatim Lean signature. The tensor statement supplies only normalized
monoidal summands; the transport statement assumes those data and proves the
component implication.

4. Traced the proof and imports. The main proof uses the existing internal-Hom
comparison and both split declarations exactly as recorded in its DAG proof and
dependencies. No planned dependency is unused or removed, and the local
irreducibility change is recorded in its change file.

5. Checked the unit route and edge cases. The internal-Hom, normalized tensor,
and component-calculation steps are retained; zero complexes, empty opens, and
degree-cancelling components are covered by the split statements. Verdict: the
proof establishes the unchanged target statement, with the documented
decomposition remaining open only at the two named nodes.

Changed only proof assembly and the documented split modules/nodes; no forced
adaptation or target-interface change was needed.
