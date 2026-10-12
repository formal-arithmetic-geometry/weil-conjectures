## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.exists_perfectComplex_representatives`
with a complete Lean combination of affine smallness, two-open gluing, the existing
`AlgebraicGeometry.quasiCompactOpen_induction`, and Mathlib's skeleton/shrink construction.
The original declaration signature, universe parameters and public imports are unchanged.

Added three modules, each with its own DAG node:
`PerfectComplexClassesSmallOnOpen` defines the actual induction predicate;
`PerfectAffineClassesSmall` states affine smallness;
`PerfectComplexClassesSmallGluing` states the two-open gluing implication.
The predicate quantifies over open immersions with specified image and derived-category
structures. This avoids assuming that `X` is definitionally its top open subscheme, or
assuming a global family of derived-category structures on every open subscheme.
The affine hypothesis is proved using the equal-range open-immersion isomorphism and
Mathlib `IsAffine.of_isIso`. The main proof applies induction at the top and evaluates
the predicate on the identity immersion of `X`.

The representative index is `Shrink (Skeleton Q.FullSubcategory) : Type u`, for the
property Q of perfect objects in D_QCoh. Its representatives come from Mathlib's
`fromSkeleton`; their perfectness is the stored full-subcategory property. The proof
constructs the index of any given perfect object and maps the skeleton isomorphism
through the fully faithful inclusion, giving the requested isomorphism in D_QCoh.
There is no new global choice construction from an unproved existence theorem.

All four modules compile together via the authorized local compiler. The two new
statement modules have exactly `:= by sorry`; there are no holes in definitions or
in the combining proof. This is a decomposition, not an axiom-free proof of smallness.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_perfectComplex_representatives`
(node `lem-pc-perfect-complexes-compact-set`). Its proof contains no sorry.

Added exactly two holes:

- `AlgebraicGeometry.Scheme.small_perfectComplex_classes_of_isAffine`
  (node `lem-pc-perfect-affine-classes-small`, module
  `Sheaf.AlgebraicGeometry.PerfectAffineClassesSmall`). This is only the affine
  base case and is strictly smaller than the qcqs conclusion.
- `AlgebraicGeometry.Scheme.perfectComplex_classesSmallOnOpen_union`
  (node `lem-pc-perfect-classes-small-gluing`, module
  `Sheaf.AlgebraicGeometry.PerfectComplexClassesSmallGluing`). This is only the
  gluing implication, with smallness hypotheses on U, V and U intersect V;
  it does not assert smallness without those hypotheses.

No sorry remains in the item's module. The delivery is a one-hole-to-two-hole
decomposition (closed 1, added 2), not positive net sorry progress. It still uses the
existing holed induction theorem. The affine criterion and Mayer-Vietoris triangle
remain inputs of the respective remaining tasks, as intended in stage 3.

Edge cases checked mathematically: the empty scheme/open has a singleton skeleton
(the zero object); zero modules and the zero ring occur among affine models; U or V
can be empty; nonseparated X is allowed because only quasi-separatedness and
quasi-compactness of the relevant opens are used. Neither helper assumes w = u:
the gluing proof explicitly accounts for the u-smallness of derived Hom types using
K-injective computation and localization comparison.

## No longer needed

Removed direct proof imports from the item's module:
`Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective` and
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle`.
They have moved to the affine and gluing helper modules, respectively, and remain
needed transitively. Their nodes `lem-pc-perfect-affine-bounded-projective` and
`lem-pc-derived-mayer-vietoris-triangle` are therefore NOT pruned.

No module or node of the original mathematical route is globally pruned.
The existing induction module remains directly imported, and the unchanged perfect
and derived-category definitions remain necessary. The unit record
`dag/units/sk-thm-picard-duality.json` has empty realized statement/step lists;
no realized unit declaration or unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG route is mathematically useful, but its step descriptions do not
provide Lean declarations for affine encoding or for the gluing smallness implication.
Those are the two explicit remaining tasks in this delivery. The affine criterion
alone does not prove its bounded-projective models have small isomorphism classes;
the Mayer-Vietoris triangle alone does not encode the possible cocones by a small type.

The DAG refers to Hom-sets simply as sets. The signature requests an index in Type u
and permits arbitrary w, so the gluing argument needs u-small Hom types, not merely
morphism types in Type w. Its new docstring spells out the missing universe argument.
The original node/docstring source file `derived-categories-of-schemes.tex` was not
present locally; the Stacks source chapter is `perfect.tex`. Read the affine criterion
(Tag 08EB), the actual Bondal-van-den-Bergh proof in
`/home/ubuntu/c1-stacks-review/perfect.tex` (lines 3893 onward), and Stacks Tags 08BV
and 08DR via the official site. The Bondal-van-den-Bergh theorem proves a single
perfect generator; the set-of-representatives route is the imported node's elaboration
of its input, not a verbatim claim in that proof. Existing source/statement metadata
was not silently changed.

Mathlib searches were run and logged in `searches.jsonl`: LeanFinder returned generic
scheme, Ext, and Mayer-Vietoris/sheaf results, with no matching affine/gluing smallness
result; Loogle found the generic EssentiallySmall machinery; grep found skeleton and
small_of_surjective infrastructure, but no scheme-perfect smallness theorem.
LeanSearch returned Internal Server Error and is recorded as unavailable, not as a
negative search. Blueprint searches for perfect/set/small found no duplicate of these
scheme-perfect smallness inputs. No definition or existing theorem statement changed.

## New nodes

`def-pc-perfect-classes-small-on-open` records the real induction predicate
`AlgebraicGeometry.Scheme.PerfectComplexClassesSmallOnOpen`, defined without holes
in its own module. The original target definitions are unchanged.

`lem-pc-perfect-affine-classes-small` records the affine smallness task, with its
Tag 08EB source and a detailed encoding proof. Its proof dependency on the existing
affine bounded-projective criterion is preserved.

`lem-pc-perfect-classes-small-gluing` records the gluing task, sourced to the original
node's Step 2 and Stacks 08BV/08DR. Its proof uses the existing Mayer-Vietoris triangle
and K-injective resolutions, transporting restrictions to skeleton representatives
and encoding cocones of fixed maps. Each theorem's docstring supplies the complete
natural-language argument for its next worker. No change record is needed: all
existing signatures, definitions and public imports remain unchanged.

## Second reading by X2

1. **Visible contract: PASS.** Read the full diff against the repository module.
   The existing theorem signature is byte-for-byte identical, including its universes
   and both derived-category hypotheses. Its docstring and public imports are unchanged.
   No existing definition changes. The existing node changes only proof, proof_deps,
   and proof_origin; the three other nodes are new.
2. **Proof and axioms: PASS as a decomposition.** Compiled all four modules in import
   order through lcompile.py. The original theorem has no sorry; precisely the two
   reported new public theorems have `:= by sorry`. No hollow definition or prohibited
   declaration occurs. A scratch copy with explicit #print axioms for all four
   declarations shows only propext, Classical.choice, Quot.sound and, for the three
   theorems, sorryAx. The induction predicate itself has no sorryAx. The remaining
   induction theorem is an existing open dependency, not a newly closed hole.
3. **Split statements: PASS.** Affine smallness is the base case; the union theorem
   assumes smallness on three strictly smaller regions and supplies one gluing step.
   Neither restates the qcqs conclusion. Tested the empty scheme, zero ring, empty
   opens and overlapping/repeated opens: the zero object gives the sole empty-scheme
   class, and the gluing map/cocone argument needs no nonempty cover members. Arbitrary
   morphism universe w is handled by K-injective computation of u-small Homs and
   transport of localized-site structures, not by assuming w equals u. Each remaining
   theorem has a source, detailed proof docstring and matching node. Independent
   searches used LeanFinder for bounded finite-projective complexes, Loogle for
   Skeleton/Small, grep for K-injective localization comparisons, and rg over Sheaf
   and the upstream AlgebraicGeometry sources. Mathlib's FGModuleCat small model
   shortens the affine encoding component, but does not supply the affine derived
   comparison or a whole helper theorem. Qh_map_bijective supplies the Hom comparison;
   no existing result closes either helper in a few minutes.
4. **Route and pruning: PASS.** Read the affine criterion, Mayer--Vietoris triangle,
   induction statement, perfectness definitions and the unit's realized record.
   The main proof really combines base, gluing and induction, then constructs
   representatives through skeleton/shrink and maps their isomorphisms through the
   full-subcategory inclusion. The original affine and Mayer--Vietoris nodes remain
   transitively needed, the induction and perfectness remain directly needed; every
   old proof dependency is accounted for. No globally pruned node or module. The
   unit has no realized statement/step entries that could be bypassed. Removed the
   affine helper's unused dependency on the induction-predicate module, replacing it
   with the exact public definition/infrastructure imports its statement needs.
5. **DAG agreement: PASS.** Checked the main node's steps against the Lean proof,
   proof_deps against their uses, and the three new nodes' signatures, source,
   searches, origin, chapter, unit, blueprint provenance and creation metadata.
   The helper nodes retain their intended original affine/Mayer--Vietoris inputs.

Second-reading changes: removed the affine helper's unnecessary public import of
PerfectComplexClassesSmallOnOpen; recorded the existing FGModuleCat small-model
shortcut; clarified transport of derived-category structures to open subschemes and
iterated open sites in the same universe w; named Mathlib's K-injective Hom comparison;
and clarified that an admissible map determines its cocone skeleton class uniquely.
Updated the two helper proof plans accordingly. No Lean proof body, existing signature,
or definition was changed. Closed 1 original hole, added 2 strictly smaller holes:
net -1, a decomposition rather than positive net proof progress.
