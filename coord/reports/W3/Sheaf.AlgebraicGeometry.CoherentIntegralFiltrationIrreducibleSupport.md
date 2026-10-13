## What changed

Retry after the previous tool failure: `deliver3.py --no-push` now prints OK.
The earlier working-tree blocker did not recur. All three modules compile and
preflight accepts this as a CODEX decomposition; nothing was pushed. Added the
required copyright headers and module docstrings to both new modules. The prior
second-reading section below is retained as historical evidence; its final failure
status is superseded by this retry.

Kept the existing signature of
`AlgebraicGeometry.Scheme.Modules.coherentIntegralFiltration_of_irreducible_support`
byte for byte. Its proof now obtains a finite coherent adic chain, splits each graded
support into full or proper support, filters the full-support case using a generic
short exact sequence and the supplied smaller-support hypothesis, and descends through
the chain using `coherentIntegralFiltration_of_shortExact`. The terminal zero module has
an explicit length-zero filtration.

The first worker's `coherentIntegralFiltration_generic_reduction` and
`coherentIntegralFiltration_generic_case` were exact duplicates of existing declarations.
The second reading removed both new modules and their new nodes. They are replaced by
construction subproblems in `Sheaf.AlgebraicGeometry.CoherentSupportAdicChain` and
`Sheaf.AlgebraicGeometry.CoherentGenericFilteredExtension`. The first constructs a chain
and asserts no integral filtration. The second constructs a filtered submodule and a
smaller-support quotient, assumes no support induction and asserts no filtration of the
middle module. Neither is a renamed existing filtration theorem.

Added proof-only imports of these two modules, `CoherentIntegralFiltrationExtension`
and `CoherentKernelCokernelSum`. Every public import is needed by a statement; no existing
public import, declaration visibility, definition or statement changes.

## Proved and sorry left

Closed the local hole in
`AlgebraicGeometry.Scheme.Modules.coherentIntegralFiltration_of_irreducible_support`.
Added exactly two named theorem holes:

- `AlgebraicGeometry.Scheme.Modules.coherent_support_adic_chain`, node
  `lem-pc-s3-coherent-support-adic-chain`;
- `AlgebraicGeometry.Scheme.Modules.coherent_generic_filtered_extension`, node
  `lem-pc-s3-coherent-generic-filtered-extension`.

This is a decomposition, not a completed axiom-free proof: one old hole closed, two new
holes added, a local net of minus one. All three checked declarations depend only on
`propext`, `Classical.choice`, `Quot.sound` and `sorryAx`. The item itself has no `sorry`;
each new module has only its named theorem's `sorry`. No data definition was introduced,
and no data is defined by choosing a witness of an unproved existence theorem. The
existential witnesses are eliminated only locally in the target's proposition proof.

## No longer needed

The old direct proof dependencies
`lem-weil-pbc-coherent-integral-filtration-adic-reduction` and
`lem-weil-pbc-coherent-integral-filtration-generic-step` are replaced at this item by the
construction nodes and the actual extension and zero-coherence dependencies. Their
modules are `Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationAdicReduction` and
`Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationGenericStep`.
Neither module was imported in the repository baseline, so no repository import is
actually removed and no module is claimed globally pruned. Their existing declarations
remain available for other callers. The rejected duplicate intermediate modules and
nodes were removed from the sandbox, not pruned from the library.

## Where the brief, the DAG or earlier work was wrong

The two original proposed intermediates literally restated the existing adic-reduction
and generic-step declarations, so leaving them with `sorry` was impermissible duplication.
The reported import cycles were confirmed from the source graph: AdicReduction reaches
this item through HilbertPolynomial, Serre and DirectImage.FiniteFreeComplex; GenericStep
reaches it through CoherentGenericPointIdealInclusion, FinitePushforwardCoherent and
DirectImage.AffineMorphism. Both routes then pass through
FinitePresentationIntegralFiltration and FinitePresentationSupportReductionFiltration.
Thus importing those existing theorems directly is not a valid repair. Their underlying
construction lemmas are recorded as plans for the two new holes; future workers must
resolve their cyclic import paths before using them in a proof. The present delivered
source imports are acyclic and are checked by deliver3.py.

The unit `dag/units/sk-thm-picard-coherence.json` already has empty `realized.statement`
and an empty step realization. This delivery is below the unit level, preserves its
coherence/devissage route and makes no claim to repair those pre-existing unit records.

## New nodes

`lem-pc-s3-coherent-support-adic-chain`:
`lean/Sheaf/AlgebraicGeometry/CoherentSupportAdicChain.lean` constructs the coherent
ideal-power chain, zero endpoint and generic-annihilated short exact graded sequences.
Its docstring includes the literal P(0)=F endpoint, stalk argument and n=0 case.

`lem-pc-s3-coherent-generic-filtered-extension`:
`lean/Sheaf/AlgebraicGeometry/CoherentGenericFilteredExtension.lean` constructs a generic
ideal-sum inclusion with filtered coherent source and strictly smaller coherent cokernel.
Its docstring explains reduced integral support, nonzero ideal, partial sums, coherence
and strictness. No change record is needed: no existing interface or definition changes.

## Earlier second reading (a previous round; superseded)

1. Compared the item with the repository by diff and declaration-table comparison:
   existing signature changes are empty. The existing theorem's signature and docstring
   are byte for byte unchanged. Only its proof and proof-only imports change; all other
   delivered Lean declarations are new construction statements.
2. All three modules compile in import order through lcompile.py with no errors or
   warnings. Scratch copies with #print axioms show only the three standard axioms and
   sorryAx for each declaration. Inspected every delivered file: exactly the two named
   theorem holes listed above; no sorry in data, axiom, unsafe, opaque, extern,
   implemented_by or kernel-check bypass.
3. Checked both construction statements against Stacks Tags 01YF and 01YE online.
   Tested the n=0 endpoint and zero quotient cases for the chain. Empty T and zero F
   cannot satisfy the full-support generic-point hypotheses; in the generic case the
   nonzero generic stalk excludes rank zero or a zero ideal. The hypotheses give
   exactly the coherence, support and annihilation facts consumed by the proof.
   Independent leanfinder, loogle and Mathlib grep searches, plus attempted LeanSearch
   calls (service unavailable), are recorded in searches.jsonl
   and in each new node. Repository and upstream rg searches found the exact duplicates
   that were removed, but no theorem asserting either new construction package.
   These two holes need substantial sheaf constructions and cannot be closed in a few
   minutes using the current acyclic imports.
4. Read the proof from the item downward. It follows the existing adic/generic-point
   route with genuine support splitting, a zero filtration, decreasing induction and
   extension concatenation. Imports support only signatures or explicitly used proof
   declarations; proof-only imports are plain import. No longer needed lists both old
   direct proof dependencies and explicitly distinguishes these from globally pruned
   modules. The unit route is preserved; its already-empty realized fields are reported.
5. Read every delivered node alongside the corresponding Lean. New lean.statement
   fields are extracted verbatim from the final statements. Each new node has its source,
   complete proof plan, dependency union, search records, ownership, blueprint origin,
   chapter and unit. The existing node now records the support split, zero base case,
   finite induction and the actual extension/coherence dependencies of the item.

Changed the second reading's duplicated intermediate statements into construction
subproblems, expanded both natural-language proofs and DAG plans, wrote the actual
finite-chain reduction, and corrected the report's pruning and progress claims.

Delivery status: local compile, axiom probes, source-cycle checks and stage-3 structural
checks passed. After recording the required attempted LeanSearch calls, repeated
`deliver3.py --no-push` runs failed solely with `(a) uncommitted changes in the working
tree`. The read-only clone has a root-level report.md outside the delivery's allowed
paths; this worker did not create or alter it. The dispatcher forbids editing the clone
or running git there, so the worker cannot clean that foreign file. Nothing was pushed.

## Second reading by W3

1. I compared the delivered item against the repository version. The existing theorem
   signature is byte for byte unchanged; only its proof and proof-only imports changed.
   The two added modules have new declarations and do not alter existing interfaces.
   Verdict: pass.
2. I compiled all three modules with `lcompile.py --all`. The item has no `sorry`; the
   only remaining holes are the two named construction theorems listed above. No
   definitions contain `sorry`, and no forbidden commands or axioms occur. Verdict:
   pass, with the documented decomposition and `sorryAx` only for those two open nodes.
3. I checked the construction statements against Stacks Tags 01YF and 01YE, including
   the zero-power chain endpoint, generic annihilation, and strict smaller support of
   the cokernel. Searches of the repository and Mathlib found no duplicate declarations.
   Verdict: both statements are true construction subproblems and are strictly simpler
   than the item; no statement is disputed.
4. I read the proof downward from the target. It uses the finite chain, splits proper
   and full support, applies the generic extension, gives zero a length-zero
   filtration, and concatenates short exact filtrations. Proof-only imports are plain
   imports. The unit's coherence/devissage route is preserved. Verdict: pass.
5. I checked the two new DAG nodes and the updated item node against the Lean
   declarations. Their statements, proof dependencies, sources, search records,
   ownership, and split status agree with the delivered code. Verdict: pass.

This reading preserves the first worker's Lean code and nodes. I added the required
current second-reading section (the historical section has a different heading) and
independently repeated compilation, axiom probes, source checks and duplicate searches.
