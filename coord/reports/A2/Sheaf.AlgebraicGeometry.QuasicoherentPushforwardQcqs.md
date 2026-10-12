## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated`
with its existing signature unchanged. The proof applies the already proved source-library criterion
`isQuasicoherent_of_forall_isAffineOpen` to the two elementwise localization conditions on inverse
images of affine opens. Naturality of the structure-sheaf map and restriction of scalars identify the
resulting scalar powers with the scalar action on the pushforward.

Added two general, fully proved modules:
`Sheaf.AlgebraicGeometry.QuasicoherentSectionPowerTorsion` and
`Sheaf.AlgebraicGeometry.QuasicoherentSectionPowerExtension`. The first proves power torsion on a
quasi-compact open by finite affine covering and sheaf uniqueness. The second extends sections
from a principal open of a qcqs open: extend on finitely many affine members, make exponents
uniform, kill the differences on the compact overlaps, and glue. Both reuse the proved affine
module localization lemmas in `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.
Two private helpers in the original module transport these results along equality of principal opens.

Updated the original DAG node's proof, proof dependencies, and proof origin to match the Lean.
Added two nodes for the proved section lemmas and a node recording the already proved source
criterion, without restating that criterion in Lean. The unit's `realized` fields are empty, so no
required unit statement or proof step is bypassed. The argument retains the original finite-affine
cover and principal-localization route, expressed elementwise.

## Proved and sorry left

Original module: proved 1 of 1 sorries:
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated`
(node `pqf-lem-pushforward-qcoh`). No sorry remains in the original module.

Also proved:
- `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isCompact`
  (node `pqf-lem-qcoh-compact-section-power-torsion`).
- `AlgebraicGeometry.Scheme.Modules.exists_map_eq_pow_smul_of_isCompact_of_isQuasiSeparated`
  (node `pqf-lem-qcoh-qcqs-section-power-extension`).

No new sorry, definition, or axiom is introduced. The source criterion is reused unchanged.
The general proofs handle empty opens and empty finite covers (the finite maxima are zero),
zero sections and zero modules, a unit scalar, and a zero or nilpotent scalar. They impose no
finite-generation hypothesis. Quasi-separatedness is needed only to make overlaps compact,
and is assumed for the open itself rather than the whole ambient scheme.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.AssociatedSectionsLocalize`
  (node `pqf-lem-associated-sections-localize`). Its base-change/tensor formulation is unnecessary;
  the proof uses the already proved affine principal-open section localization lemmas directly.
- `Sheaf.AlgebraicGeometry.Coherent` (node `pqf-def-coherent`). The quasi-coherent predicate used
  in the signature is already Mathlib's predicate. The source-library principal-open criterion
  supplies the affine-local characterization, so the module defining coherent modules is unnecessary.

These two modules are no longer proof dependencies of this item; other users may still need them.
The notion `pqf-def-coherent` remains a statement dependency of the new nodes, as appropriate.
No separate equalizer module, tensor base-change lemma, finite-product localization theorem, or
principal-open naturality lemma is needed: finite exponent bounds, restriction functoriality,
and sheaf gluing are proved directly. The existing affine tilde/global-sections and tilde-section
nodes are retained below the new lemmas.

## Where the brief, the DAG or earlier work was wrong

The original dependency modules do not by their statements supply the finite affine cover,
section equalizer, or localization/gluing steps needed for the theorem. In particular,
`AssociatedSectionsLocalize` only treats an associated sheaf on an affine spectrum, while
`Coherent` defines a predicate; neither is a general qcqs section theorem. The original plan
marked the global equalizer/localization steps elementary, but their Lean realization requires
substantial finite-cover work. That work is now proved in the two new modules.

No mathematical statement was changed or disputed. The principal-open criterion already exists
and is proved in `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`, so no duplicate
Lean statement was needed. LeanSearch returned Internal Server Error; this is recorded as
unavailable, not as absence. LeanFinder, Loogle, Mathlib grep, source-library rg, and blueprint
searches were also run. Mathlib has structure-sheaf versions of the two general power lemmas,
and the source library has affine module versions, but neither has the module results on general
qcqs opens. The source clearing-denominators theorem requires separatedness and does not apply
under the hypotheses here.

## New nodes

`pqf-lem-qcoh-compact-section-power-torsion`: compact-open power torsion, in the fully proved
new module `Sheaf.AlgebraicGeometry.QuasicoherentSectionPowerTorsion`. It is the injectivity half
of localization and needs no quasi-separatedness.

`pqf-lem-qcoh-qcqs-section-power-extension`: power extension from a principal open of a qcqs
open, in the fully proved new module `Sheaf.AlgebraicGeometry.QuasicoherentSectionPowerExtension`.
It uses affine lifting, the previous torsion theorem on overlaps, and finite sheaf gluing.

`pqf-lem-qcoh-principal-open-criterion`: records the already proved
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_forall_isAffineOpen` in
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`. It is reused as-is; no Lean file
or new proof obligation is added for it. The source declaration gives precisely the two
conditions combined by the original theorem's proof.

No change record is required: all existing public signatures and public imports are unchanged.

## Second reading by A2

1. **Existing declarations unchanged.** I compared the delivered pushforward module with the repository version. The public theorem signature is byte-for-byte unchanged; only its proof and proof-only imports changed. No target statement or definition was altered. Verdict: pass.

2. **Proof and axioms.** All three delivered modules compile with `lcompile.py --all`; the original module has no `sorry`, and the two added theorems are fully proved. No axiom, unsafe, opaque, extern, or hollow definition was introduced. The proofs use the finite affine cover, affine localization, compact-overlap torsion, and sheaf gluing argument described in their docstrings. Verdict: pass.

3. **New statements.** The two new section lemmas are general module statements, distinct from Mathlib's structure-sheaf results and the existing affine module lemmas. Their hypotheses and conclusions match the localization steps needed by the pushforward proof, including the separate compact and quasi-separated hypotheses. Verdict: pass.

4. **Pruning and imports.** The proof uses the existing principal-open criterion and the two new section lemmas. The former associated-sections-localization and coherent-definition imports are no longer needed and are removed; this is recorded above. The unit route remains finite affine localization followed by gluing and principal-open criteria. Verdict: pass.

5. **DAG agreement.** The original node proof, dependencies, and origin match the Lean proof. The two new theorem nodes contain their statements, sources, proof steps, Lean declarations, and creation metadata; the criterion node records the reused source declaration. Verdict: pass.

I changed only this report section after the initial delivery review; no Lean source or DAG content was changed.
