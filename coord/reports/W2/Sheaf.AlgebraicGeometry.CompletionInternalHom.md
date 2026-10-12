## What changed

Replaced the entire proof hole of
`AlgebraicGeometry.completion_internal_hom_bijective` without changing its signature,
visibility, public imports, definitions, or existing docstring. This is a decomposition:
the parent now has a complete Lean proof from two strictly smaller intermediate statements.

The proof constructs the maps `e` by the cokernel universal property followed by the inverse
of precomposition with the quotient projection. It proves their factorization equations
and compatibility with every transition, using epimorphism cancellation for the cokernel
projection and isomorphism cancellation for precomposition. It constructs `Φ` as an actual
natural transformation with the required components, proves naturality using a proved
private helper `homObjSectionsEquiv_map`, and proves injectivity and surjectivity from the
existence and uniqueness of compatible section lifts. No object is selected from arbitrary
unproved existence: the only inverse used is that of an isomorphism, hence unique.

Added `Sheaf.AlgebraicGeometry.CompletionInternalHomQuotient`, which states the finite-level
annihilation and quotient-factorization argument for arbitrary modules, including unequal
powers `n ≤ m`. Added `Sheaf.AlgebraicGeometry.CompletionInternalHomSectionsLift`, which
states the remaining affine comparison and sheaf gluing as unique compatible section
lifting for prescribed component maps. These are two parts of the original proof, not
renamings of the original conjunction/existential statement. Each has one public theorem
with proof exactly `by sorry`, its source, detailed proof in words, and its own DAG node.

Updated the parent node's proof, proof dependencies, and proof origin to the actual Lean
argument. The unit `sk-thm-p1` and all of its realized statements and steps are untouched.
All three modules compile together using `lcompile.py --all`, with no warnings. The parent
single-file compile remains below the 60-second limit.

## Proved and sorry left

Hole closed in the original module:
`AlgebraicGeometry.completion_internal_hom_bijective`
(node `lem-weil-pbc-completion-internal-hom`). Its proof contains no `sorry`.

Holes added, both deliberately left for the next workers:

- `AlgebraicGeometry.completion_internal_hom_quotient`
  (node `lem-weil-pbc-completion-internal-hom-quotient`): finite-level annihilation and
  internal-Hom isomorphism for `n ≤ m`. It does not mention completion systems, coherent
  modules, global compatible families, or a Noetherian hypothesis.
- `AlgebraicGeometry.completion_internal_hom_sections_lift`
  (node `lem-weil-pbc-completion-internal-hom-sections-lift`): affine module comparison and
  gluing, giving a unique section family for an already prescribed compatible morphism
  family and prescribed quotient factorizations. It does not construct the quotient
  factorizations, prove their compatibility, or construct the canonical map `Φ`.

Counts: one original hole closed, two new holes added. This is a decomposition, not a
sorry-free mathematical proof or positive net hole reduction. No other `sorry` remains
in the delivered files. The private helper is fully proved.

Edge cases checked mathematically before stating the new results: `I = 0` gives the
identity quotient comparison; `I = O_X` gives zero quotients, singleton compatible section
and morphism families; zero `F` or `G` likewise causes no exception; the empty scheme has
singleton sections and morphisms; `n = 0` in the finite-level lemma gives `I^0 = O_X` and
a zero target quotient, and `m = n` is the exact case used in the original statement.
The inequality direction is essential: for a transition `a → b` in the opposite natural
numbers, `b.unop + 1 ≤ a.unop + 1`.

## No longer needed

Removed these direct proof imports from the parent module:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`
- `Sheaf.AlgebraicGeometry.CoherentSheafHom`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`

The affine-theory imports are now proof dependencies of the unique-lift module, where that
argument remains to be proved. Tensor products remain needed for finite-level factorization
and are available through the existing formal-module dependencies. Thus these are direct
parent-import removals and dependency relocation; no existing mathematical node or module
is claimed pruned from the targets' transitive closure. Every original parent dependency
remains used by one of the two intermediate arguments. No blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original planned dependencies provide the affine equivalence
and completion/base-change ingredients, but they do not directly supply the finite-level
internal-Hom factorization or the compatibility of the canonical evaluation map with that
affine equivalence. The two new statements make these remaining arguments explicit.
The finite-level isomorphism must be available for unequal powers as well as equal powers
to cancel precomposition in the transition-compatibility proof.

The local clone does not contain `literature/stacks-project/coherent.tex`. The published
Stacks Tag 0882 was read at https://stacks.math.columbia.edu/tag/0882; it confirms the
Noetherian affine completion-tensor and flat Hom base-change argument. The detailed
factorization and gluing proofs follow the existing parent node; new proof origins are
marked agent-written rather than claiming the missing local source was read.

LeanSearch returned HTTP 500 for both intermediate queries; this is recorded as unavailable,
not evidence of absence. LeanFinder, Loogle, and Mathlib/source searches ran; they found
completion and cokernel ingredients but no direct statement closing this module.
Whole-blueprint searches for `0882`, `internal hom`, and completion/Hom found no duplicate
of either new intermediate statement. Existing source APIs are used for all definitions.

## New nodes

`lem-weil-pbc-completion-internal-hom-quotient` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-completion-internal-hom-quotient.json`
realizes the finite-level part of parent step 1. Its module is
`Sheaf.AlgebraicGeometry.CompletionInternalHomQuotient`. Its statement is valid for arbitrary
scheme modules and unequal powers `n ≤ m`, and its three proof steps explain annihilation,
local quotient factorization, and annihilation of postcomposition.

`lem-weil-pbc-completion-internal-hom-sections-lift` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-completion-internal-hom-sections-lift.json`
realizes parent steps 2–5. Its module is
`Sheaf.AlgebraicGeometry.CompletionInternalHomSectionsLift`. It retains the affine finite
module, formal-module equivalence, completion-tensor, flat base change, and gluing route.
Both new nodes cite the same nearest blueprint ancestor as the parent, have complete
Lean records, and record the searches actually run. No interface change or change record
is needed.

## Second reading by W2

1. Compared the delivered parent module with the repository version; the existing declaration signature, visibility, docstring, and definitions are unchanged. Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds with no warnings, and the parent proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Verdict: pass.

3. Read both split-off statements and their docstrings. The quotient theorem is a strictly smaller finite-level factorization result; the sections-lift theorem isolates affine comparison and gluing for prescribed data. Both are stated with the required hypotheses and are not duplicates of the parent declaration. Verdict: pass.

4. Checked the parent proof route and imports. It uses the two split-off results, preserves the unit route, and removes only proof-only imports from the parent. Verdict: pass.

5. Checked the updated DAG node proof, proof dependencies, proof origin, and the two new node records against the Lean declarations. Verdict: pass.

Changes made: added this second-reading section only; no Lean statements, definitions, or proofs were altered during review.
