## What changed

Replaced the sole sorry in
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`,
`AlgebraicGeometry.Scheme.Modules.higherDirectImage_isQuasicoherent_on_affines`,
by a complete proof using the existing
`isQuasicoherent_of_forall_isAffineOpen` criterion and
`SheafOfModules.isQuasicoherent_over`. The proof supplies the criterion's two
independent hypotheses from new proof-only imports:
`Sheaf.AlgebraicGeometry.HigherDirectImageSectionDenominators` and
`Sheaf.AlgebraicGeometry.HigherDirectImageSectionTorsion`.
Updated the affine-local and global quasi-coherence nodes' proof routes.
No existing signature, universe, definition, visibility, or public import changed.

The remaining mathematics is explicitly reduced to two localization assertions,
each in its own module. Their proofs in words use Stacks 09MR (with the tensor
unit), the higher-image cohomology-presheaf description 01E4, associated modules
01HV, and extension from a principal-open basis. The argument does not use the
Leray affine-section comparison, which would be circular here. The unit
`sk-thm-picard-coherence` has empty realized bindings; its coherence, perfectness,
and vanishing route is unchanged.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.Scheme.Modules.higherDirectImage_isQuasicoherent_on_affines`
(node `new-higher-direct-image-affine-local-qcoherent`).
There are no sorries left in the assigned module.

Added holes, each a strictly separate part of the localization criterion:

- `AlgebraicGeometry.Scheme.Modules.higherDirectImage_section_clearDenominators`
  (node `lem-pc-higher-direct-image-section-denominators`): lift a section on
  D(a) after multiplication by a power of a.
- `AlgebraicGeometry.Scheme.Modules.higherDirectImage_section_pow_annihilates`
  (node `lem-pc-higher-direct-image-section-torsion`): kill a section on W whose
  restriction to D(a) is zero by a power of a.

This is a decomposition: one upper hole closed and two lower holes added,
net minus one hole locally. Neither new assertion supplies the other hypothesis
of the criterion or states quasi-coherence. No claim of a sorry-free proof of
quasi-coherence is made. Both statements were checked on degree zero, empty
opens, zero modules, zero a, and units a. At a=0 use exponent 1 for the torsion
assertion and the zero section for lifting; at a a unit the restriction is an
isomorphism. All three delivered modules compile through lcompile.py; the
assigned module compiles in about 17 seconds.

## No longer needed

No original imports were removed: they remain used by the other proofs or the
new localization criterion. The ordinary higher-image dependency
`lem-pc-ordinary-higher-image-quasi-coherent` and its module
`Sheaf.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent` are no longer needed
by either quasi-coherence node in this assigned module. It was not imported
in the baseline and was not added. Its own dependencies (derived restriction,
qcqs-open induction, relative Mayer--Vietoris, and extensions) are not needed
by this reduction; they may remain necessary elsewhere. The two new statements
still use the existing localization theorem and cohomology-presheaf theorem
in their planned proofs, so those nodes are retained.

## Where the brief, the DAG or earlier work was wrong

The documented ordinary higher-image interface is not acyclic:
`tools/import_direction.py may` refuses its import because it already reaches
`DirectImage.Sections` (in particular, its AffineMorphism proof import reaches
FiniteFreeComplex, which imports Sections). An unchanged-signature adaptation
of that other module is not forced by any interface change here and was not
attempted. The new modules import only DirectImage.Basic and avoid this cycle.

The old affine-local node's prose says "separated", while the unchanged Lean
signature assumes only quasi-separated. The new nodes and proofs use the
actual qcqs hypotheses, as Stacks 01XJ does. No statement was weakened.

Search: LeanFinder returned generic quasicoherence definitions/presentations,
Loogle found `SheafOfModules.isQuasicoherent_over`, and source search found the
existing localization criterion and the two underlying ordinary section
lemmas. Those ordinary section lemmas assume quasi-coherence already and
cannot establish it for the higher image. LeanSearch was unavailable (HTTP
500); no absence conclusion is based on that failure. DAG and blueprint
search found no duplicate higher-image denominator or kernel statements.

The new nodes use `lem-sc-invert-s-cohomology` (Tag 09MR) as a generic tool from
another unit; it provides localization, not a replacement for any coherence
unit statement or step. The maintainer can record this tool use during review.

## New nodes

`lem-pc-higher-direct-image-section-denominators`, module
`Sheaf.AlgebraicGeometry.HigherDirectImageSectionDenominators`, states only the
surjectivity-after-clearing-denominators assertion. Its proof identifies the
higher-image cohomology presheaf with the associated-module sections on the
principal-open basis, then represents a section as m/a^n.

`lem-pc-higher-direct-image-section-torsion`, module
`Sheaf.AlgebraicGeometry.HigherDirectImageSectionTorsion`, states only the
power-torsion kernel assertion. The same canonical comparison identifies a
vanishing restriction with t/1=0, and the module-localization zero criterion
gives the annihilating power. Each node has its source, proof, edge cases,
searches, exact Lean signature, and chapter/unit. No change records are needed.

## Second reading by Q4

1. Compared every delivered module against the repository. The two Sheaf modules
   are new. In Sections, the diff consists only of two plain proof imports,
   the affine-local theorem's docstring, and its proof. Every existing declaration
   signature, universe, section hypothesis, definition body, visibility and public
   import is unchanged. No change record or forced adaptation is required. Pass.
2. Compiled all three modules in import order with lcompile.py: clean compilation
   (approximately 3, 3 and 18 seconds). The sole remaining holes are the two named
   public localization theorems reported above, each exactly `:= by sorry`.
   Scanned all delivered Lean for forbidden declarations and kernel bypasses;
   none occur, and no definition has acquired a hole or arbitrary chosen data.
   A scratch copy with #print axioms for both quasi-coherence theorems and both
   new lemmas reports only propext, Classical.choice, Quot.sound and sorryAx.
   The scratch copy was removed. This certifies a decomposition, not a closed
   target or a sorry-free proof. Pass with the explicitly reported holes.
3. Read both new statements and their complete docstring arguments, the existing
   localization criterion, invertS_cohomology, the fraction presentation, the
   higherDirectImagePresheaf theorem, and the associated-module and basis-extension
   interfaces. Independently checked Stacks 09MR, 01E4 and 01XJ. The inverse image
   of an affine is qcqs under the actual hypotheses. Localization on the principal
   basis and exact sheafification give actual section comparisons without using
   the circular Leray affine-section result. Surjectivity after clearing powers
   and the power-torsion kernel criterion are separate, strictly partial assertions;
   neither restates quasi-coherence or implies the other. At a=0 the open is empty;
   choose zero for the lifted section and exponent 1 for torsion. At a unit,
   restriction is invertible and a vanishing section is zero. Degree zero, zero
   coefficients and empty opens obey the same fraction formulas. Repeated search
   with the different queries `IsLocalizedModule` (Loogle), localization of higher
   direct image sections to principal opens (LeanFinder), and higher-image
   localization/power-section names (msearch grep and rg on Lean/Mathlib).
   Found generic module localization APIs and ordinary quasi-coherent section
   results, but no acyclic theorem closing either new higher-image assertion.
   The ordinary quasi-coherence theorem imports AffineMorphism, then
   FiniteFreeComplex, then Sections; confirmed the cycle from source imports.
   No small existing result closes either new hole in a few minutes. Pass.
4. The affine-local proof directly supplies the two hypotheses of the already
   proved localization criterion, then uses isQuasicoherent_over. The global
   theorem remains the original affine-cover argument. Retained imports support
   the other section, restriction, projection-formula and vanishing proofs, plus
   the criterion; both added imports are plain proof imports. The new modules
   expose only DirectImage.Basic, which their signatures need. The old proof_deps
   of both changed nodes contained only the ordinary higher-image node; it and
   its unused module are explicitly named under No longer needed. No actual
   baseline import is removed and no globally unreachable module is claimed.
   Read sk-thm-picard-coherence's statement, proof and realized fields (empty
   statement binding and one empty step binding). Its coherence, perfectness and
   vanishing route is preserved; localization is a generic tool below that route.
   Pass.
5. Compared both existing node diffs: only proof, proof_deps and proof_origin
   changed. Their routes now match the actual Lean reduction and affine-cover
   proof. The new nodes have matching Lean statements, complete proof plans,
   exact unions of step dependencies, sources, search records, creation records,
   blueprint provenance, chapter and unit. The old node's separated-versus-
   quasi-separated prose discrepancy is recorded in the report; its existing
   statement and the stronger unchanged Lean theorem were not altered. Pass.

Changes by the second reader: clarified both new theorem docstrings and their
node proof plans to use right-derived module-section cohomology throughout, and
spelled out why the canonical fraction formula is A-linear and commutes with
further principal restrictions. No Lean statement, proof body, import, definition
or hole count changed. One original hole is closed, two lower holes remain added:
this remains a decomposition with local net minus one, not a proof-progress claim.
