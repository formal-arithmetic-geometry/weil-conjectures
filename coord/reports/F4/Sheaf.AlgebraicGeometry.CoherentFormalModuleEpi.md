## What changed

Proved `AlgebraicGeometry.coherentFormalModule_epi_iff_first_component` with its
signature and public imports unchanged. Two proved private helpers show that a
power-annihilated sheaf with a zero quotient is zero, and then inductively show
that a coherent formal module with zero first component is zero. The supplied
termwise cokernel cofork and Mathlib's preadditive epi/cokernel criterion combine
these facts into both directions of the equivalence.

The finite-level proof replaces completion and affine localization by stalks.
For a stalk module M and ideal J, J^(n+1)M=M and J^(n+2)M=0 imply JM=M;
induction gives J^kM=M for every k, hence M=0. This is the power-annihilated
argument of Stacks 00DV (9). Mathlib's `TopCat.Presheaf.section_ext` makes every section zero from its
zero germs; extensionality then makes the identity of the module sheaf zero.
Sources checked online: https://stacks.math.columbia.edu/tag/087Y and
https://stacks.math.columbia.edu/tag/00DV. The local literature checkout has no
coherent.tex or algebra.tex. No new statement or definition is introduced.

The existing node `lem-weil-pbc-formal-systems-surjective` has its proof,
proof_deps and proof_origin updated to this route. No unit statement or realized
unit step is bypassed: this auxiliary node is not itself in the unit's realized
statement or steps. No interface changes or forced adaptations.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.coherentFormalModule_epi_iff_first_component`
(node `lem-weil-pbc-formal-systems-surjective`).

Added 0 holes; split off 0 holes. No sorry remains in the delivered module.
The existing proof dependency `AlgebraicGeometry.Scheme.ideal_module_product_stalk`
(node `lem-weil-pbc-ideal-module-product-stalk`) still contains sorry in the
library; it is used as intended for stage 3 and is not modified here.
The abelian theorem's existing downstream holes likewise remain outside this delivery.
All private helpers are proved. No data is chosen from a new unproved existence
statement; the cokernel cofork is used only in a proof of a proposition.

Validation: the final module compiles through lcompile.py. The proof covers
n=0, the zero and unit ideal, zero modules and the empty scheme; no proper-ideal,
nonempty-space or nonzero-module hypothesis is used. At the unit ideal,
annihilation already forces every component to vanish. At the zero ideal,
the quotient-isomorphism condition propagates vanishing immediately.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.CoherentFormalModule` (available through the unchanged
  public abelian-module import; its definitions remain used).
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness`.
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`.

The item's proof no longer uses these original planned dependencies:
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`
  (`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`).
- `lem-weil-pbc-coherent-formal-modules-local-exactness`
  (`Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness`).
- `lem-weil-pbc-coherent-formal-modules-affine`
  (`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`).
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
  (`Mathlib.AlgebraicGeometry.Modules.Tilde`).
- `def-weil-pbc-noetherian-ring` (`Mathlib.RingTheory.Noetherian.Defs`).
- `def-weil-pbc-adic-completion` (`Mathlib.RingTheory.AdicCompletion.Basic`).
- `lem-weil-pbc-adic-completion-mod-ideal`.
- `lem-weil-pbc-adic-complete-jacobson-radical`.
- `lem-weil-pbc-nakayama-jacobson`.
- `pqf-def-locnoeth` as a proof step (the original Noetherian hypothesis remains).

These are deletions from this node's proof route, not a claim that the modules
are globally unreachable: several remain needed by the abelian theorem and
other parts of the library. `SheafZeroStalks` was considered but not retained;
Mathlib `TopCat.Presheaf.section_ext` supplies that step.
The retained proof route uses the formal-module definitions, abelianness with
termwise cokernels, preadditive epi/cokernel criterion, module-sheaf category,
and ideal-product stalk formulas.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original DAG's completion/Nakayama route is
unnecessarily long for zero detection of the termwise cokernel: its defining
quotient condition and annihilation at each next level already suffice.
The shorter route uses the nilpotent-action form of Nakayama directly on stalks,
without asserting the ideal is nilpotent in the ambient stalk ring.

The first dry run rejected new direct Mathlib imports as missing source modules,
even though those files are readable in the installed package. The unused imports
were removed, and the zero-sheaf step was rewritten using the available section
extensionality theorem; no tool was changed and no source check was bypassed.

## Second reading by F4

1. Compared the delivered module with the repository version. The target theorem
   signature and all existing declaration signatures are unchanged; only the proof,
   proof-only imports, and the documented DAG proof route changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it has no errors, no `sorry`, and no
   forbidden declarations. The target's remaining `sorryAx` dependencies are the
   pre-existing abelian and stalk lemmas. A scratch `#print axioms` reports only the
   permitted axioms plus those pre-existing `sorryAx`s. Verdict: pass.
3. No theorem was split off and no new statement or definition was added. The
   existing target statement is unchanged and the stalk argument handles the edge
   cases described above. Verdict: pass.
4. Checked the proof from the target downward. It uses the existing abelian cokernel,
   epi/cokernel criterion, formal-module definitions, and ideal-product stalk lemma;
   the affine/completion imports and nodes are genuinely unused and are documented
   above. Verdict: pass.
5. Compared the node's `proof`, `proof_deps`, and `proof_origin` with the Lean proof;
   they agree, and no realized unit statement or step is bypassed. Verdict: pass.

Changed only the target proof, its proof-only imports, the existing node's proof
metadata, and this report. The delivery dry run is ready to pass once this section
is present.
