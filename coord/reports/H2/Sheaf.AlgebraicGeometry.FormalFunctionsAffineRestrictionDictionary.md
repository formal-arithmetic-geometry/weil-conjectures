## What changed

Proved `AlgebraicGeometry.formalFunctions_affine_restriction_dictionary` with its
signature unchanged. Added two fully proved private helpers:
`AlgebraicGeometry.affine_restriction_appTop` computes the scalar map, and
`AlgebraicGeometry.affineRestrictionSectionsIso` explicitly constructs a natural
section comparison for arbitrary modules. Properness follows from Mathlib;
coherence follows from the existing coherence criterion and restriction lemmas.
The affine ideal equality is proved directly using Mathlib ideal and chart formulas.
The quotient-system comparison is assembled from the already proved private
restriction helpers in `TorsionControlledFormalRestriction`, with its projection
identity proved using functoriality and naturality.

Added proof-only imports of `TorsionControlledFormalRestriction` and
`QuasicoherentFiniteTypeAffine` using `import all`, and of
`CoherentFiniteTypeLocallyNoetherian`. Updated the node's proof steps and dependency
list to describe this route. No existing signatures, definitions, visibility, or
public imports changed. No data are selected from unproved existence statements.
Local compilation passes without warnings; every line is at most 100 characters.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.formalFunctions_affine_restriction_dictionary`
(node `lem-weil-pbc-formal-functions-affine-restriction-dictionary`).
Both private helpers are proved. No holes remain in the item's module; no new holes
or modules are added. This closes 1 hole and adds 0, using existing library results.
It does not assert that every transitive dependency is free of `sorry`.

## No longer needed

No imports, node dependencies, or modules are pruned. All existing public imports
are retained; each added proof import supplies a declaration the proof uses.
The full torsion-controlled theorem and its annihilation-bound argument are not
used: only its proved finite-level quotient and completion restriction helpers
are used. No completion-limit isomorphism or theorem on formal functions is used.
These omissions do not remove their modules, since the helpers share that module.
The unit route in `sk-thm-p1` is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned coherence step also needs finite-type preservation under restriction;
the proved `finiteType_restrict` helper in `QuasicoherentFiniteTypeAffine` supplies
it, and its node is now an explicit proof dependency. The module did not initially
import the quotient helpers named by its DAG; the required proof-only imports are
now present. No mathematical statement was changed or disputed.

The cited Stacks TeX and blueprint section files are absent in this local clone.
The unit record and the module/node proof were available and read; the cited
[Stacks Lemma 088B](https://stacks.math.columbia.edu/tag/088B) and its cited affine
background were checked online. Empty affine opens, zero modules, and zero or
unit ideals require no additional hypotheses: the proof uses isomorphisms and
quotient universal properties uniformly.

## Second reading by H2

1. **Interface preservation — PASS.** Compared the only delivered Lean module
   with the repository using `diff -u` and a byte comparison of the existing
   theorem signature up to `:= by`. Its signature is identical; no existing
   definition, visibility, or public import changed. There are no change records
   or adapted modules. The two added helpers are private.
2. **Proof and axioms — PASS.** Independently compiled the module with
   `lcompile.py --all`; it passed without warnings in 17.5 seconds. Compiled a
   scratch copy printing axioms for `affine_restriction_appTop`,
   `affineRestrictionSectionsIso`, and
   `formalFunctions_affine_restriction_dictionary`. Each uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Scanned the source:
   no `sorry`, forbidden declarations, external implementations, or kernel-check
   bypasses. The section isomorphism is constructed from presheaf restriction
   maps; the quotient comparisons are constructed by cokernel universal
   properties, with no arbitrary witness chosen from an unproved theorem.
3. **Split statements and small cases — PASS.** No statements were split off,
   and no new holes or modules were added. Read both private helpers and the
   imported quotient-comparison constructions. Empty opens, zero modules, zero
   and unit ideals use the same top-open equalities and cokernel comparisons;
   neither a nonempty open nor a positive-rank hypothesis enters the proof.
4. **Route and pruning — PASS.** Repeated searches with Lean Finder for
   direct-image evaluation versus inverse-image global sections, Loogle for
   `Scheme.Modules.restrictAppIso`, and `rg` in both library roots. The hits give
   the underlying restriction and pushforward formulas already used, not the
   scalar-compatible natural comparison or this theorem. Inspected the coherent
   kernel restriction and finite-type restriction alternatives; replacing the
   present criterion would add machinery without shortening the argument. The
   three added imports are proof-only and each supplies a used declaration.
   Existing imports provide notions in the theorem signature. Every old
   `proof_deps` entry remains used, so `No longer needed` correctly reports no
   pruning. Read `dag/units/sk-thm-p1.json`: the realized unit statement and steps
   are unchanged and this local dictionary bypasses none of them.
5. **DAG agreement — PASS.** Compared the node JSON with the repository: only
   `proof` and `proof_deps` differ. The dependency list is exactly the union of
   step `uses`, and its added finite-type dependency matches the Lean helper.
   Read the imported modules and checked the scalar, ideal, quotient, and
   naturality steps against the actual proof. The original source-based
   `proof_origin`, statement, Lean record, chapter, and unit remain unchanged.

Second-reading changes: appended this review only; no Lean or node repair was
needed. The axiom check also establishes that the delivered theorem itself has
no transitive `sorry` dependency. Closed 1 original hole, added 0; pruned none.
