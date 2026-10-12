## What changed

Proved `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_retraction`
from a coefficient-linear trace degree identity and an explicit inverse-scalar calculation.
The signature and existing docstring are unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.FiniteEtaleModuleTraceDegree` and `Mathlib.Algebra.Field.ZMod`.
The latter supplies the prime-modulus field instance; `Defs` alone does not supply it.

The new module states trace existence with prescribed degree for any commutative coefficient
ring and any sheaf of modules. It assumes neither prime-to-degree invertibility nor local
constancy. This is the trace part of the argument, not the retraction statement renamed:
in characteristic dividing d its identity still holds but cannot yield the desired splitting.
The original module proves the normalization using nondivisibility, field inversion,
`ULift.ext`, `Linear.comp_smul`, and `smul_smul`.

Read the Stacks source Section 03SH, Definition 03SE and the following characterization and
restriction/trace formula. The new statement follows its local sum construction; sums and
restrictions are coefficient-linear, and the same descent works with module coefficients.
Edge cases checked: d = 0 gives the zero trace and zero composite; d = 1 gives the identity;
the zero sheaf and the zero coefficient ring cause no exception. No connectedness or
nonemptiness is needed for the helper. In the original statement d = 0 is excluded by hd.
Both delivery modules compile locally, including the scalar normalization.

## Proved and sorry left

Proved (reduced to the new trace step):
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_retraction`
(blueprint: split-locally-constant-retraction). No sorry remains in the item module.

One new sorry remains:
`AlgebraicGeometry.Etale.exists_finiteEtaleModuleTrace_degree`
(blueprint: lem-weil-pbc-finite-etale-module-trace-degree), in
`lean/Sheaf/AlgebraicGeometry/FiniteEtaleModuleTraceDegree.lean`.
Its docstring and node give the full local-sum, descent and degree calculation.
The result is a reduction, not a claim of closure under the three allowed axioms alone.

## No longer needed

No original imports were removed: both public imports supply the unchanged statement.
Removed a redundant proof-only `Mathlib.CategoryTheory.Linear.FunctorCategory` import during
validation; the new helper supplies the linear-category instances its statement uses.
The helper uses the narrower public import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, not ConstructibleSheaf.Defs.

The item's proof does not need `def-weil-pbc-finite-etale-trace`
(`Sheaf.AlgebraicGeometry.FiniteEtaleTrace`) or
`lem-weil-pbc-finite-etale-trace-degree`
(`Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree`). Neither is imported.
Their abelian trace definition and the bundled existence of an unspecified degree are
unnecessary here: the supplied hdeg already prescribes d, and the new theorem provides a
module-valued trace directly. The inverse-image node remains needed for the statement;
its proof edge is replaced by the helper edge. The helper's plan still uses the existing
abelian trace existence characterization, local splitting, and restriction/product nodes;
those are not claimed pruned. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old proof dependencies provide a trace only for AddCommGrpCat-valued sheaves.
Their signatures cannot be directly applied to ModuleCat-valued sheaves. The coefficient
extension is described informally in the trace definition's node, but has no Lean theorem.
Also the old degree theorem counts underlying points of a pullback over algebraically
closed fields, whereas hdeg counts geometric lifts over separably closed fields.
The new helper uses the precise hdeg already supplied, avoiding an unnecessary comparison
with the old degree theorem. Neither existing statement is changed or disputed.

## New nodes

`lem-weil-pbc-finite-etale-module-trace-degree`: coefficient-linear trace with prescribed
geometric degree, before division by that degree. One new module, one named public theorem
with a whole-proof sorry. Sources: Stacks 03SH/03SE and local splitting 04HN.
Searches: LeanFinder found pullback/pushforward API only; Loogle found no trace/sheaf match;
Mathlib Sites grep found no trace; LeanSearch was unavailable (HTTP internal server error).
The original node's proof and proof_deps now follow the actual reduction and scalar proof.
No change records are needed: existing statements, definitions and public imports are unchanged.

## Second reading by B2

1. Compared every delivered module with the repository. The existing theorem signature,
   docstring, definitions, and public imports are byte-for-byte unchanged. Only its proof
   and two proof-only imports changed. The second module is new; no change record is needed.
2. Compiled both modules in dependency order with lcompile.py: no errors or warnings.
   Scratch-copy `#print axioms` checks for both declarations show exactly propext,
   Classical.choice, Quot.sound, and sorryAx. The only direct sorry is the named public
   trace-degree theorem listed above. No forbidden declarations or hollow definitions occur.
   The inverse-scalar argument is a genuine calculation from the trace-degree identity;
   the delivery remains conditional on the trace theorem and existing open infrastructure.
3. Read the new theorem, its node, and the Stacks source text at Section 03SH/Definition 03SE.
   Its local sum construction works for arbitrary module sheaves and commutative rings.
   Checked degree zero, degree one, the zero coefficient ring, the zero sheaf, empty base,
   and characteristic dividing the degree. The latter case shows why this is only the trace
   step, not the retraction under another name. Nondivisibility excludes degree zero in the
   original theorem. Repeated searches using transfer, counit, sheets, normMap, sums and
   diagonal, via LeanFinder, Loogle, Mathlib grep, and rg on both library roots. No existing
   degree identity for module-valued sheaves was found. The upstream finite-etale retraction
   is on the source site and splits a different unit, so cannot replace this argument.
   Closing the trace theorem requires substantial local-splitting/descent infrastructure,
   not a short omitted tactic proof. Its source and complete natural-language proof are present.
4. Reviewed the proof from the original target downward. The scalar normalization is short
   and direct. Both old public imports supply the unchanged signature; the new helper's
   linear-category import supplies the scalar action in its statement. The new imports in
   the item are proof-only. Every old proof edge removed is accounted for above: the trace
   definition and old trace-degree theorem are unnecessary; inverse image is retained as a
   statement dependency, rather than an independent proof edge. Checked sk-thm-p1.realized
   and searched all unit records: neither removed trace node is a realized unit step.
   The chapter's locally constant reduction and trace splitting route is preserved.
5. Compared the node records with the Lean. The original node's two proof steps match the
   trace invocation and inverse-scalar calculation; proof_deps and proof_origin agree.
   The new node states the helper's exact hypotheses and identity, records its source,
   descent plan, searches, creation metadata, and Lean signature. Found stale blueprint
   metadata in the sandbox's existing node relative to the repository and restored it.
   Adjusted the new node's provenance to that now-explicit nearest blueprint ancestor.

Second reading changed only DAG provenance and this report: restored the existing node's
blueprint fields, corrected the new helper's blueprint ancestor/place, and recorded the
independent searches. No Lean proof or signature repair was necessary.
