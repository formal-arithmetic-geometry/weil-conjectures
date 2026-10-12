## What changed

The statement and visibility of `AlgebraicGeometry.exists_affine_quotient_sheafified_resolution`
are unchanged. Its proof maps the augmentation through tilde and the affine-chart restriction,
then composes with the single-complex comparison and the quotient-sheaf isomorphism.
The kernel-preservation argument is now a local proof term inside the target theorem, avoiding
a duplicate top-level declaration. It uses the existing, proved
`Scheme.Modules.isQuasicoherent_kernel`: the kernel lies in the essential image of tilde,
and full faithfulness transports and reflects its universal property. Thus tilde preserves
finite limits, while its left adjoint structure preserves finite colimits. Mathlib then
preserves the augmentation's quasi-isomorphism through this exact additive functor.

Added the proof-only import `Sheaf.AlgebraicGeometry.AffineQuotientRestrictedIso`, with
one module-sheaf comparison theorem. The unused exactness theorem from the earlier attempt
has been removed. All existing public imports remain. Both delivered modules compile without
warnings through lcompile.py. No existing statement, definition, or visibility was changed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exists_affine_quotient_sheafified_resolution`
(node `lem-sc-affine-quotient-resolution-sheafification`). Its chain-map construction,
kernel preservation, and quasi-isomorphism composition are complete Lean proofs.

Added one lower hole: `AlgebraicGeometry.affine_quotient_restricted_iso`
(node `lem-sc-affine-quotient-restricted-iso`, module
`Sheaf.AlgebraicGeometry.AffineQuotientRestrictedIso`). Its whole proof is `:= by sorry`;
its docstring and node give the basic-open localization argument and source. It has no
complex, augmentation, homology, or quasi-isomorphism hypothesis or conclusion, so it is
strictly the geometric identification step of the original argument. Edge cases I = top,
I = bottom, and the empty chart cause no exception to the localization calculation.

This is a decomposition: one upper hole closed and one strictly lower hole added, net zero
holes before accounting for pruned imports. It is not an axiom-free proof of the original
statement yet. There are no other sorries in the delivery.

## No longer needed

Removed the redundant proof import `Mathlib.CategoryTheory.Preadditive.LeftExact`: its
finite-limit theorem is already available through the other imports.

Removed the proof import `Sheaf.Algebra.Homology.ModuleStalkExact`
(node `lem-weil-pbc-module-stalk-exact`). The proof no longer needs that node, nor
`lem-weil-pbc-spec-tilde-stalk-localization` (Mathlib leaf in
`Mathlib.AlgebraicGeometry.Modules.Tilde`) or
`lem-weil-pbc-localization-module-exact` (Mathlib leaf in
`Mathlib.Algebra.Module.LocalizedModule.Exact`) from the original stalkwise route.
The categorical kernel argument uses the already proved quasi-coherent kernel result.
`def-weil-closed-immersion` is also no longer a proof dependency of the parent node:
the geometric identification now belongs to the new comparison node. It remains a
statement dependency, and its public import remains required by the unchanged signature.
These nodes may remain needed by other targets; no claim is made about their global reach.

Removed the earlier attempt's unused declaration `affine_quotient_termwise_quasiIso`,
its proposed node `lem-sc-affine-quotient-termwise-quasiiso`, and its unsubmitted module
`Sheaf.AlgebraicGeometry.AffineQuotientResolutionCore`. Only the quotient comparison is
split off. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox added an exactness sorry which its main proof never used, put two
statements in one new module, used the parent blueprint id in their docstrings, omitted
statement dependencies, and recorded English prose instead of Lean signatures. These
have been corrected. The returned delivery also exposed a duplicate private helper theorem;
this repair keeps its proof as a local term in the target theorem, since the existing
module theorem is private and cannot be imported by name. The parent node now follows the actual categorical proof and cites
the new module-sheaf comparison. New-node searches were rerun and recorded in searches.jsonl.

Tag 068C gives the perfectness argument via an algebraic Koszul resolution; the precise
source for the quotient pushforward comparison is Stacks Lemma 26.7.3(2), Tag 01I9
(https://stacks.math.columbia.edu/tag/01I9). The corresponding existing Mathlib leaf is
`lem-weil-pbc-pushforward-tilde-spec`; the remaining chart and restriction comparison
is written out in the new theorem's docstring. The source schemes.tex was read in the
available literature mirror. LeanSearch returned Internal Server Error; LeanFinder and
source grep ran successfully.

The previous delivery-tool failure concerned a missing unrelated FreeCechChainCochains
module. The fresh dry run passed: the old failure no longer blocks validation. No tool or
repository file was manually changed to evade validation. The only pending preflight section
is the independent second reading, which the second reader writes before delivery.

## New nodes

`lem-sc-affine-quotient-restricted-iso`, in
`dag/nodes/sec-picard-framework/lem-sc-affine-quotient-restricted-iso.json`, records
`AlgebraicGeometry.affine_quotient_restricted_iso` in the new module
`Sheaf.AlgebraicGeometry.AffineQuotientRestrictedIso`. It isolates the module-sheaf
identification and carries its complete localization-and-gluing proof in words.
No change record is necessary: existing interfaces are unchanged, and every added
import in the existing module is proof-only.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository. The quotient comparison module
   is new. The existing theorem signature is byte-for-byte unchanged (checked by extracting
   the text before `:= by`); all existing visibility and public imports are unchanged.
   No definition, target statement, or unrelated module was changed. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; both compiled without errors or
   warnings other than the declared theorem's sorry warning. A scratch copy printed axioms
   of the private kernel helper, the upstream quasi-coherent kernel theorem, the main
   theorem and the comparison theorem. The first two use only `propext`, `Classical.choice`
   and `Quot.sound`; the latter two also use `sorryAx`, as expected from the comparison.
   The only delivered sorry is the whole proof of `affine_quotient_restricted_iso`.
   There are no prohibited declarations or data definitions. The isomorphism witness is
   eliminated inside a proof of an existential proposition; no object definition is built
   from an arbitrary unproved existence claim. Verdict: pass as a decomposition.
3. Read the quotient comparison's signature, docstring and node against the local Stacks
   schemes.tex, lemma-widetilde-pullback, part (2). The basic-open calculation includes
   the module action and restriction compatibility; transporting the quotient presentation
   and restricting pushforward gives the stated objects. For I = top both sides are zero;
   for I = bottom this is the affine structure sheaf comparison; empty U also gives zero.
   The lemma has no resolution or quasi-isomorphism data and is strictly a part of the
   original proof. Independent Loogle search for pushforward with restrictFunctor found
   the open-immersion adjunction and its counit, not this comparison. Source searches in
   Mathlib and both library roots found the spectrum pushforward components, but no exact
   existing theorem for the chart comparison. Closing it requires further transport and
   restriction construction, not a direct application of a found theorem. Verdict: pass.
4. Read the proof from its conclusion back through the single-complex isomorphisms,
   exact functor and transported kernel fork. Full faithfulness reflects the kernel's
   universal property, so the exactness argument is valid. The similar helper in
   AffineDerivedTildeHomologyComparison is private and cannot be reused by an import.
   All remaining imports support signatures or the proof. The report now names every
   removed old proof dependency, distinguishing the retained closed-immersion signature
   dependency. The unit sk-thm-picard-duality has empty realized statement and step lists;
   those records were not changed and no recorded unit step was bypassed. Verdict: pass.
5. Checked the parent proof steps, their dependency union and origin against the proof;
   checked the new node's statement, dependencies, source, searches, creation, blueprint,
   chapter, unit and Lean record. The new lemma has its own module and blueprint id.
   Its Lean signature was recorded on one compressed line rather than verbatim; corrected
   it to the exact multiline declaration text. Verdict: pass after that repair.

Changes by this reader: removed the redundant proof import
`Mathlib.CategoryTheory.Preadditive.LeftExact` after a successful compile without it;
made the new node's Lean signature verbatim; completed the pruning report. No proof
argument or existing statement was rewritten. One original hole closed, one lower hole
added: decomposition, net zero before closure pruning. No additional hole was closed.

## Second reading by D3

1. Compared the delivered parent module with the repository version. The existing theorem
signature is unchanged byte for byte; the added comparison module is new, and no existing
definition or target statement was altered. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. They compile successfully. The
only delivered `sorry` is the named proof of `affine_quotient_restricted_iso`; no forbidden
declarations or hollow definitions occur. Verdict: pass as a documented decomposition.
3. Checked the new comparison statement against its docstring and node. It is the strictly
smaller module-sheaf identification needed by the parent and has no resolution hypotheses.
Its localization edge cases are covered in the proof plan and no duplicate library theorem
was found. Verdict: pass.
4. Read the parent proof from its conclusion downward. The kernel-preservation argument uses
the existing quasi-coherent-kernel theorem, the comparison isomorphism, and exact-functor
quasi-isomorphism transport; removed imports and dependencies are no longer used. Verdict:
pass, with the blueprint unit route retained.
5. Checked both DAG nodes against the Lean declarations, including `proof`, `proof_deps`,
`proof_origin`, source, searches, and Lean records. The parent hole is closed and the new
lower hole is represented by its own node. Verdict: pass.

Changes by this second reader: added this required review record only; no proof or interface
changes were needed after compilation and static inspection.
