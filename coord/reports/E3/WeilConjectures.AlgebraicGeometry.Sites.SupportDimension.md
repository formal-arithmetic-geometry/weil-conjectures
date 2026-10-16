## What changed

Proved `AlgebraicGeometry.Etale.exists_covering_supportedIn` in the assigned module.
Every existing public declaration, definition, target statement, and public import is unchanged.
The proof bounds the image of each affine chart's nonzero section locus by finitely many
closures of generic points, restricts to the complement, and lifts the section through the
support kernel. The unit record `sk-prop-sf-cbc` has no realized steps to bypass.

Repaired the returned duplicate: removed the private binary-union theorem
`AlgebraicGeometry.Etale.dim_union_le`. Generalized `dim_finite_union_le` from finite unions
of point closures on a scheme to arbitrary finite families of closed subsets of a sober T0
space, with a common bound in `WithBot ℕ∞`. Its direct proof embeds each point closure into
a family member and takes the supremum of point-closure dimensions. It does not reprove
or apply the duplicate binary statement. The only use is specialized to point closures.

Retained three proof-only imports: `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing`,
`WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus`, and
`Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`. Only the assigned Lean module
and the proof-route node record changed in this repair. No other Lean module is adapted.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.Etale.exists_covering_supportedIn`
(node `new-lem-sc-support-dimension-local-sections`). No holes are added or left in the
assigned module, and no theorem is split off.

All six private helpers are proved: `residueFieldHomOfOver_eq`, `dim_finite_union_le`,
`exists_closed_image_bound`, `trdeg_le_of_not_vanishing`, `unit_section_eq_zero_of_range`,
and `exists_covering_section_zero_off_closed`. Existing external statements are used
with their original signatures; their dependencies' existing holes are not claimed closed.

## No longer needed

Removed the duplicate private theorem `AlgebraicGeometry.Etale.dim_union_le` and its
binary-union induction. The generalized finite-family proof handles the empty union by
an empty supremum, so the earlier discrete-space base-case argument is also unnecessary.

No original public import was removed. The proposed `Mathlib.AlgebraicGeometry.Noetherian`
import remains omitted because the retained imports provide the needed API.

The planned node `lem-sc-etale-section-zero-open` and its module
`Sheaf.EtaleCohomology.EtaleSectionZeroOpen` are unused: the existing source vanishing-locus
API gives the needed local-zero implication, openness, and restriction formulas.
The separate colimit formulation's geometric-stalk comparison, cofinality, exactness,
and colimit steps are not used in this local-section theorem. The dimension,
finite-components, and sobriety inputs are retained. The separate node `lem-kun-etale-lfp`
and module `Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType` are also unused: Mathlib supplies
the local-finite-type instance for the chart directly; no global finite-type assertion
about the chart is needed. The second reading removed this dependency from the node.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the statement of private
`AlgebraicGeometry.Scheme.dim_union_le` in
`WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension`.
That module already reaches `SupportDimension`, as confirmed by `import_direction.py may`,
so importing it here would create a cycle; its lemma is also private. The repair uses the
requested generalization option: remove the binary helper and prove the strictly more
general finite-family statement directly, within the assigned module. No downstream
module or existing declaration visibility changes.

The original node `lem-sc-support-dimension-union` describes the separate colimit theorem
`AlgebraicGeometry.support_dimension_union` in `Sheaf.AlgebraicGeometry.SupportDimensionUnion`.
The retained local-section node records the theorem actually proved here. Its dimension
proof step now describes the finite-family generalization rather than the removed binary
lemma. The pullback-zero node attaches an existing proved source declaration.

The torsion hypothesis is retained although the proof does not need it. Empty supports,
empty charts, zero sections, repeated image generic points, and `a = 0` are handled;
no separatedness assumption is added. The generalized helper also handles arbitrary
bounds, including bottom and infinity, and arbitrary empty finite families.

Repair searches through Lean Finder, Loogle, and Mathlib grep found no applicable
finite-closed-union dimension theorem. The existing source binary lemma was identified
and its private visibility and cyclic import obstruction checked directly.

## New nodes

The prior delivery's `new-lem-sc-support-dimension-local-sections` records the actual
local-section theorem and its proof route; this repair updates its dimension step.
It adds no Lean statement or hole.

The prior delivery's `new-lem-sc-pullback-zero-vanishing-locus` records the already proved
`AlgebraicGeometry.Etale.range_subset_vanishingLocus_of_pullSection_eq_zero` in
`WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus`. It adds no Lean statement
or hole. This repair adds no nodes or change records: no existing public interface changes.

## Second reading by E3

1. Compared the complete delivered module with the shared repository using `diff -u`
   and the declaration parser. All five existing signatures, visibility, docstrings,
   four definition bodies, and public imports are unchanged. The only Lean additions
   are three proof-only imports, six proved private helpers, and the theorem proof.
   No change record or forced adaptation is needed. Verdict: pass.
2. Compiled the delivered file with `lcompile.py` without errors or warnings. Compiled
   a scratch copy with `#print axioms` for all eleven declarations, including the six
   private helpers: every result lists only `propext`, `Classical.choice`, `Quot.sound`.
   No `sorry`, forbidden declaration, hollow definition, or unproved witness occurs.
   The chosen component generic points are determined uniquely by sobriety and T0;
   algebraic closures and the closed support union are real constructions. Verdict: pass.
3. There are no split-off statements or added holes. Read both new node records and
   the existing vanishing-locus theorem they attach. Checked empty schemes, empty
   component families, zero sections, repeated image points, and `a = 0`; the finite
   family helper also permits bottom and infinite bounds. Checked Stacks 04FR and
   0B1C online. Fresh Loogle search `topologicalKrullDim, Set.iUnion` found no hit;
   Lean Finder search for dimension under a finite closed cover returned dimension
   and embedding lemmas, but no union theorem. Searched Mathlib and both library
   roots for union dimensions, support bounds, and kernel section lifts. Reused the
   existing kernel lift and vanishing-locus API; the returned private binary-union
   duplicate is absent. Verdict: pass.
4. Read the proof from its final kernel lift through unit vanishing, affine refinement,
   and the generic-point dimension bound. Each added import supplies a used theorem:
   HighDegreeVanishing supplies the kernel lift, EtaleVanishingLocus supplies the zero
   locus API, ClosedIrreducibleDimensionTrdeg supplies the dimension equality. Existing
   public imports support the unchanged interface. The unit sk-prop-sf-cbc has empty
   realized statement/step arrays, and this proof preserves the section-support route.
   No shorter applicable result was found. No longer needed now explicitly names
   the unused etale finite-type node/module. Verdict: pass after bookkeeping repair.
5. Matched the local-section node's six steps to the Lean proof and its attached
   signature, and checked the pullback-zero node against the existing proved source
   declaration. The finite-family dimension argument, ground-field map comparison,
   sieve naturality, covering criterion, and kernel lift are recorded accurately.
   Removed `lem-kun-etale-lfp` from the local-section node's step and proof_deps:
   its Sheaf declaration is never used; Mathlib instances provide the needed local
   finite type. Updated proof_origin to record this correction. Verdict: pass.

Second reading changed only the proof-route metadata and this report. The Lean proof
is retained unchanged. Closed holes: `AlgebraicGeometry.Etale.exists_covering_supportedIn`
(one of one); added holes: none; split off: none. No actual original import is pruned.
