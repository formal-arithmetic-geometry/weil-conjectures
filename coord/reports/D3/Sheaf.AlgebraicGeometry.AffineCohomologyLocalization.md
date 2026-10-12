## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.Modules.affine_cohomology_localization`
with a reduction separating degree zero from positive degrees. The nonvanishing open
comes from `affine_cap_section_open`. Positive numerator twists are quasi-coherent by
`isQuasicoherent_tensorObj` and the tensor-power invertibility instance. Affine-open
cohomology vanishing, direct-sum extensionality, and quotient induction prove the
positive-degree fraction group and target groups subsingleton; their unique additive
equivalence satisfies the required formula. The existing statement and visibility are
byte-for-byte unchanged. No definition was changed or introduced.

The proof-only import `Sheaf.AlgebraicGeometry.AffineCohomologyLocalizationZero`
is new. Its theorem isolates the degree-zero transport of section localization through
the canonical zeroth-derived isomorphism and the two fraction quotient presentations.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.affine_cohomology_localization`
(node `lem-sc-invert-s-cohomology-affine-case`), the only original hole in the item.

Hole added and left: `AlgebraicGeometry.Scheme.Modules.affine_cohomology_localization_zero`
(node `new-affine-cohomology-localization-zero`). This is a public named theorem in its
own new module, with a full natural-language proof in its declaration docstring.
It asserts only the degree-zero comparison on a specified nonvanishing open; it asserts
neither existence/affineness of that open nor any positive-degree comparison/vanishing.

Counts: one of one original theorem bodies closed, one smaller theorem split off.
This is a decomposition, not a complete proof or a net hole reduction: closed 1, added 1,
net 0. The item contains no remaining direct sorry. Existing dependencies with open
proofs remain open; no claim that the target is axiom-free is made.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.AffineSectionLocalization`
and `Sheaf.AlgebraicGeometry.InvertibleTensorQcoherent` from the item. The new zero
module still imports AffineSectionLocalization for its planned proof; that dependency
is moved, not removed from the import closure. InvertibleTensorQcoherent is unnecessary
in both delivered modules; the existing source theorem handles precisely the
nonnegative tensor powers present in the fraction presentation.

Of the old item proof_deps:
- `lem-sc-invertible-tensor-qcoherent` is not used: the source theorem
  `isQuasicoherent_tensorObj` handles the needed nonnegative powers.
- `lem-weil-pbc-module-restriction-open-immersion-colimits` is not directly used:
  restriction quasi-coherence is internal to the affine-vanishing declaration.
- `lem-sc-affine-section-localization` is not directly used by the item, but remains
  the proof dependency of `new-affine-cohomology-localization-zero`.

The two remaining old dependencies, `lem-sc-affine-cap-section-open` and
`pqf-lem-affine-vanishing`, are used directly. No assertion of whole-library pruning is
made; other target branches may still reach these modules. No unit realization is
removed or changed.

## Where the brief, the DAG or earlier work was wrong

The original mathematical route is sound. Its degree-zero step leaves Lean transport
work: cohomology fractions use an additive-subgroup closure while section fractions
use a module span. Scalar stability of the generators identifies these relation groups;
naturality of the zeroth-derived isomorphism then transports the comparison formula.
The original route did not make this transport explicit.

The first sandbox proof compiled with style warnings and changed signature indentation.
Its new theorem had only a module comment instead of the required declaration docstring;
its node lacked stmt_deps, had a placeholder Lean signature and searches unsupported by
recorded executions. The existing node retained unused dependencies and did not update
its proof steps; several strings were accidentally double escaped. These are repaired.

## New nodes

`new-affine-cohomology-localization-zero` is the strictly smaller degree-zero transport
in `lean/Sheaf/AlgebraicGeometry/AffineCohomologyLocalizationZero.lean`. Its node includes
a self-contained statement, statement dependencies, four proof steps, the section
localization proof dependency, its exact Lean signature, and real searches. Lean Finder
and Loogle locate `Functor.rightDerivedZeroIsoSelf`; this is one tool for the argument,
not an existing proof of the quotient comparison. LeanSearch returned Internal Server
Error, recorded as unavailable rather than a no-match result. No change record is
needed: no existing public signature, public import, definition or instance was changed.

## Second reading by D3

1. Compared both delivered modules with the repository. Only one module already
   existed. Its existing theorem signature is byte-for-byte identical after restoring
   indentation, with identical visibility and public imports. The new module declares
   only the reported intermediate theorem; no undeclared interface change or definition.
   Verdict: pass.
2. Compiled both modules locally through lcompile.py in import order, without errors or
   style warnings after repairs. The only direct sorry is the listed new public theorem;
   no axiom, unsafe, opaque, implemented_by, extern, or data definition is introduced.
   Scratch-copy #print axioms checks on both declarations show only the three permitted
   axioms and sorryAx from open dependencies. Verdict: valid reduction, still conditional
   on the identified open statements.
3. Read the new theorem, its node, both fraction definitions, and the existing section
   localization theorem. The additive closure/module span issue is resolved in its
   natural-language proof by scalar stability of relation generators. Checked empty Y,
   F=0, s=0 (U empty and all fractions killed), nowhere-vanishing s (U=Y), and n=0.
   These agree with the statement; no extra affineness assumption on U is needed in
   degree zero. It is strictly smaller than the parent. Repeated leanfinder, loogle,
   leansearch and grep searches with different queries and searched local Sheaf/upstream
   declarations: no existing full comparison. The quotient and naturality transport
   requires more than a few-minute lemma application and remains the single named hole.
   Verdict: true, needed decomposition.
4. Checked the top-down route: affine-open construction, positive vanishing, then
   section localization in degree zero. The nonnegative source tensor theorem avoids
   the integer-power lemma. All removed direct imports and old proof_deps are listed
   above; section localization remains reachable through the zero theorem. Read
   dag/units/sk-thm-curveestimate.json: realized.statement is thm-sc-proper-cohomology
   and realized.steps is empty; neither delivered node replaces a realized unit step.
   The Stacks 09MR affine paragraph and its 01PW zero step are retained. Verdict: pass.
5. Rebuilt the existing node from the repository, changing only proof, proof_deps and
   proof_origin; preserved its statement, lean signature and all other fields. Its
   steps now name exactly the direct node dependencies of the Lean reduction. The new
   node has the required fields, matching declaration, full signature, source, searches,
   and proof_deps equal to the union of its step uses. Verdict: pass.

Second reading changes: restored signature whitespace and the original global open
commands (spelled out DirectSum types to avoid a visibility change); replaced letI by let and
unnecessary simpa by simp; removed unused proof imports; documented the zero theorem's
full quotient/naturality argument under its own blueprint tag; corrected node records,
actual searches, double escapes and decomposition accounting. Proofs that were already
right were retained.

Sources checked: [Stacks 09MR](https://stacks.math.columbia.edu/tag/09MR),
[Stacks 01PW](https://stacks.math.columbia.edu/tag/01PW), and the pinned Mathlib
CategoryTheory/Abelian/RightDerived.lean (rightDerivedZeroIsoSelf).
