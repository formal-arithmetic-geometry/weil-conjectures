## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassRep`
with a complete Lean reduction to the geometric/derived comparison construction
and the existing `exists_etale_complex_class_rep`. The original theorem's
signature and public imports are unchanged. Its proof transports a representative
through additive stage/limit isomorphisms and cancels the injective limit
isomorphism. The full continuity theorem's injectivity half is unnecessary.

Added `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineComplexPresentation`.
Its inductive proposition explicitly quantifies the complex system, its coefficient
colimit, the canonical derived pullback equations, its cohomology cocone and the
raw/cohomology isomorphisms. It does not assert that the cohomology cocone is a
colimit or that its legs represent every class. The construction theorem is the
remaining hole. Witnesses are eliminated only inside a proof of a proposition;
no definition chooses data from the unproved existence assertion.

Updated the original node's proof, proof dependencies and origin to match the
shorter Lean route. Added the presentation node with its source, complete proof
in words, three kinds of searches and exact Lean signature.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.exists_higherDirectImage_raw_affine_class_rep`
(node `lem-sbc-higher-direct-image-raw-affine-class-rep`). Its body has no sorry.

Added one hole:
`AlgebraicGeometry.Etale.exists_raw_affine_complex_presentation`
(node `lem-sbc-higher-direct-image-raw-affine-complex-presentation`).
This isolates steps 1 and 3 of the original plan: geometric base change,
coefficient/single-complex transport and natural derived-Hom comparison.
Step 2 is supplied by the existing complex class-descent theorem.
This is a decomposition, not a net hole reduction: one closed and one added.
No other sorry remains in the delivered modules.

Both modules compiled together using lcompile.py, with no compiler warnings.
The delivery dry run passed compilation, the axiom probe and preflight, except
for the second reading which belongs to the next worker; nothing was pushed.
The statement was checked mathematically on a one-stage identity diagram,
zero coefficients, the empty etale object, and p=0: it constructs the usual
restricted-cohomology comparison in each case, and requires no torsion or
constructibility hypothesis. Nonempty directedness is retained. Lower bound
zero is available from the single complexes. These are mathematical edge-case
checks, not additional formal theorems.

## No longer needed

Removed the direct imports of
`Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`,
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
The latter two remain available transitively for the statement/construction;
no claim is made that they disappear from the whole targets' import closure.

This item's argument no longer needs
`lem-weil-pbc-etale-cohomology-limit-complex-systems`
(`Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`) or its injectivity branch
`lem-weil-pbc-etale-complex-class-vanishing`
(`Sheaf.AlgebraicGeometry.EtaleComplexClassVanishing`), nor its filtration-deepening
module `Sheaf.AlgebraicGeometry.EtaleComplexFiltrationDeepening`.
An independent comparison against the current repository finds these three
Sheaf modules are the complete set removed from this item's import closure.
The two Mathlib modules reported by the first reader remain transitively imported
in the current library and are not counted as pruned.
These nodes may still be used by other targets or modules. We import only
`Sheaf.AlgebraicGeometry.EtaleComplexClassDescent` for the continuity step.

The original direct proof dependencies on inverse-image definitions,
higher-direct-image sheafification and its natural comparison are replaced by
the new presentation node. The inverse-image and restricted-cohomology theory
is still needed within that construction; the natural sheafification comparison
is not invoked as a theorem by this raw-class argument. Its module stays public
because it defines the raw presheaf and pullback used by the unchanged signature.
No unit statement or realized step was bypassed (`realized` is empty for this unit).

## Where the brief, the DAG or earlier work was wrong

The original plan invokes full cohomology continuity and then forgets to types
only to extract a representative. The already available class-descent half is
sufficient, so the vanishing half can be pruned from this argument.

The existing abelian higher-image presheaf and natural-comparison theorems
concern sheafification, and do not provide the raw restricted-cohomology
presentation and its varying-site naturality needed here. That missing glue is
now a separate, explicitly typed construction item rather than an anonymous
hole in the target proof.

A large dependent structure for the presentation exceeded the per-file compile
limit. Representing the same existence assertion as an inductive proposition
avoids dependent projection generation and compiles within the limit; no existing
definition was changed, and no file was split to evade the limit.

LeanSearch returned Internal Server Error. LeanFinder, Loogle, local source
searches, DAG and blueprint searches were available. The cited Stacks tags
03Q8, 09Z1 and 0EZM were read online because the local Stacks source is absent.
The blueprint ancestor script returns None for this module-created item; the
new node inherits the original node's explicit blueprint ancestor instead.

## New nodes

`lem-sbc-higher-direct-image-raw-affine-complex-presentation`:
the geometric/derived-Hom presentation needed before applying complex continuity.
It introduces no representative assertion and no cohomology colimit assertion.
Its coefficient-complex cocone is colimiting by inverse image preserving colimits
and the degree-zero single-complex construction; cohomology continuity is left
to the existing class-descent theorem. Source: Stacks 09Z1/03Q8, with canonical
complex maps as in 0EZM. The new module is
`lean/Sheaf/AlgebraicGeometry/HigherDirectImageRawAffineComplexPresentation.lean`.
There are no interface changes, forced adaptations or change records.


## Second reading by N2

1. Compared both delivered sources and the existing node with the repository.
   The existing theorem signature is byte for byte unchanged; there are no
   modified definitions or statement changes and no change records are needed.
   Its two existing public imports remain unchanged. Restored its original
   docstring; the actual shorter route is recorded in the report and DAG.
2. Compiled both modules together using lcompile.py: no errors or warnings.
   Scanned both sources: the sole sorry is the named new construction theorem;
   no forbidden declarations or hollow definitions occur. A scratch-copy
   `#print axioms` check shows propext, Classical.choice, Quot.sound, and sorryAx
   for both the original theorem and the open construction theorem; the
   presentation proposition itself uses only the three permitted axioms.
   Witnesses of the presentation are eliminated into the original proposition,
   never used to define an arbitrarily chosen object.
3. Read the complete presentation constructor and the new theorem against
   Stacks 03Q8, 09Z1 and 0EZM. The canonical hP equation prevents an arbitrary
   choice of cohomology pullback. The new conclusion supplies geometric and
   derived-Hom comparison data, but supplies neither IsColimit B nor stage
   representatives. It is a strictly separate part of the argument: the
   continuity/class-descent theorem is still needed. Checked the construction
   on a singleton identity system (ordinary restricted cohomology), zero
   coefficients and empty U (zero groups), and p=0 (sections and their canonical
   pullback). No additional torsion hypothesis is required. Independent
   LeanFinder search for Ext on the etale slice found only generic Ext and
   sheaf-cohomology definitions; Loogle search for Ext and Sheaf returned
   generic presheaf results. Local searches and reading the upstream
   CohomologyPresheaf and HigherDirectImageAffineClassDescent modules show
   module coefficients, or fixed pulled-back coefficients, rather than the
   needed varying abelian-coefficient natural comparison. No duplicate found.
   Closing this construction requires substantial geometric and derived
   comparison formalization; it is not a hole closable in a few minutes.
4. Checked the isomorphism transport from the top downward: stageIso.inv gives
   t, its inverse identity gives stageIso.hom t = y, compatibility gives equal
   limit images, and injectivity of limitIso gives exactly the original raw
   pullback equality. Only class descent is invoked. Both proof imports are
   plain imports; the public imports of the new module provide names in its
   signatures. The old proof_deps removed are, explicitly,
   `def-weil-pbc-inverse-image`,
   `lem-weil-pbc-etale-cohomology-limit-complex-systems`,
   `sbc-lem-higher-direct-image-presheaf`, and
   `lem-sbc-abelian-higher-direct-image-natural-comparison`.
   Inverse-image theory remains needed within the construction. Independently
   recomputed the import closures and corrected the pruning count from five
   to three: the claimed Mathlib removals do not hold against the current
   repository. Read dag/units/sk-lem-failure-field.json: its realized statement
   and step lists are empty; no unit statement or route is changed or bypassed.
5. Checked that the original node changes only proof, proof_deps and
   proof_origin, and its steps match the actual Lean proof. The new node has
   the required source, natural-language proof steps and their dependency
   union, searches, creation data, inherited blueprint ancestry, chapter/unit,
   and exact Lean theorem signature. The quantified coherence, lower bound,
   coefficient colimit, and isomorphism equations agree with its Lean.

Second-reading changes: restored the existing theorem docstring, corrected the
import-closure pruning claim, and explicitly listed every replaced old proof
dependency. No mathematical proof, definition, or statement was changed.
The delivery remains a decomposition: one original hole closed, one new hole
added, and no claimed net hole reduction.
