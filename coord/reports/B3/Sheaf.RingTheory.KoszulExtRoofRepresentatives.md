## What changed

The statement and visibility of
`ExteriorAlgebra.exists_koszul_ext_roof_representatives` are unchanged. Its complete
proof constructs the normalized augmentation explicitly, proves it quasi-isomorphic
and unique among normalized augmentations, lifts derived morphisms using
K-projectivity, constructs top cycles using the empty exterior basis in degree r+1,
and establishes the exact roof equation by linear-equivalence cancellation.

The new, completely proved module `Sheaf.RingTheory.KoszulDerivedDualEvaluation`
provides the augmentation-free signed-dual comparison and its evaluation formula.
It constructs an A-linear map from the concrete kernel to derived morphisms, proves
surjectivity by K-projectivity, identifies its kernel with incoming boundaries by
single-target cocycle formulas, and passes to the quotient. Its projection equation
proves the exact component-evaluation formula, with no discretionary sign.
The item's import of this module is proof-only. The retained added Mathlib imports support
these proofs. No existing public imports, signatures or definitions changed.
No other module is adapted. The writer repair adds no imports: the two
inaccessible private special cases are replaced by proved generalizations.
The current second reader removed four redundant proof-only imports.
The roof DAG proof records both generalizations. Compiled both delivered modules
in import order and checked the public theorems' axioms after the repair.

Repair of the landing return: removed both duplicate private declarations from
`KoszulDerivedDualEvaluation`. The lifting helper is now
`kprojective_Q_map_surjective`, with an arbitrary K-projective source E and arbitrary
complex T; it proves a strictly more general statement. Importing the roof module
would form a cycle, and its old lifting helper is private. The duplicate
`koszul_dual_top_differential_zero` was removed without replacement: the cycle
condition in the surjectivity proof now follows directly from the chain-map equation
returned by `Cocycle.toSingleMk_surjective`, transported with `extend_d_eq` and
isomorphism cancellation. The comparison no longer requires top-degree vanishing.
The item's two duplicate helpers are now generalized as described below. The augmentation helper
was adapted from `exists_koszul_quotient_augmentation`; its source module would
create a cycle. The Stacks source read was Tag 0BQZ, lemma-regular-immersion-ext,
especially its finite free Hom-complex computation. Mathlib KProjective,
HomComplexSingle, HomComplexCohomology, HomComplex, ShortComplex.ModuleCat,
ExteriorPower.Basis and Ext.Linear were read directly.

## Proved and sorry left

Closed: `ExteriorAlgebra.exists_koszul_ext_roof_representatives`
(node `lem-sc-koszul-ext-roof-representatives`), the sole original sorry.

Also proved in the new module:
`ExteriorAlgebra.exists_koszul_derived_dual_evaluation`
(node `lem-sc-koszul-derived-dual-evaluation`). Every private helper is proved.
No sorry remains anywhere in the delivery. No holes were added. The net is one
original hole closed, not a decomposition into remaining holes.

The proof checks r=0 separately in the kernel/image identity: E^1=0 and the incoming
natural-number differential is zero. The augmentation construction includes A/I=0
and requires no properness of I. The exterior-basis argument includes the zero ring
and requires no Nontrivial instance. The new comparison does not assume regularity:
any finite free Koszul complex is K-projective even if it does not resolve its
zeroth homology. No object is chosen from an unproved existence theorem.

## No longer needed

No original imports were removed; they support the original public statement.
All retained added imports are used; the second reader removed the four
redundant imports listed below. The repaired comparison removes its duplicate
Koszul-specific lifting and top-vanishing helpers. It needs neither the roof
module's private lifting theorem nor the private `koszulDual_outgoing_zero` in
`Sheaf.RingTheory.KoszulConormalTopHomologyPos`: lifting uses the generic
K-projective argument and cycles use the chain-map equation in the comparison.
The roof module now uses the genuinely general arbitrary-module contraction
formula and all-above-rank differential-vanishing formula; it does not duplicate
the two private special-case statements cited in the current return.

The original planned route no longer needs
`new-j3-koszul-projective-resolution`
(`Sheaf.RingTheory.KoszulProjectiveResolution`) or
`lem-sc-projective-ext-cocycle-roof-formulas`
(`Mathlib.CategoryTheory.Abelian.Projective.Ext`). They were not imported.
The proof uses an explicit quotient augmentation and direct K-projective morphism
lifting instead of packaging a ProjectiveResolution and using extMk roof formulas.
These nodes are absent from both delivered proof dependency lists. Other target
branches may still need them.

`lem-sc-hom-single-cocycle-component-formulas` and
`lem-sc-hom-cocycle-homotopy-quotient-formulas` remain needed by the fully proved
comparison. `lem-sc-module-homology-quotient-formulas` remains needed by both modules.
The added Mathlib leaf `lem-pc-ring-derived-map-representative` is used through its
existing Qh_map_bijective match. No unit-level statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current landing return identified two duplicate private helpers in the roof
module. Both cited existing theorems are private, so they cannot be imported and
used by name. The permitted generalization repair is implemented in place:
`contractLeft_exterior_one_formula` computes contraction of degree-one exterior
powers for any A-module M and any linear functional phi, without a finite basis;
`koszul_dual_differential_above_rank_zero` kills the differential from any degree i
into every n>r, rather than only r to r+1. Their finite-free and top-degree
specializations supply the augmentation and cycle proofs. The old duplicate
helpers are removed. The public theorem signature and visibility are unchanged.
The earlier second readings are superseded; this repair needs a fresh reader.

There is no disputed statement. The existing
`exists_koszul_ext_dual_homology_equiv` and the proved generic
`exists_ext_signed_dual_homology_equiv` assert only Nonempty of an equivalence;
they do not determine its evaluation on roofs. The new proof constructs its own
quotient equivalence and proves its projection formula explicitly.

The original module did not import its planned proof-dependency modules, despite
the standing brief saying these imports were already present. Proof imports were
added explicitly. The unit sk-thm-picard-duality was read; its realized arrays are
empty. The blueprint ancestor helper returns None because this item's created.item
is a module name; the original node's explicit nearest ancestor,
lem-sc-finite-duality, was used for the new node.

## New nodes

`lem-sc-koszul-derived-dual-evaluation`, in
`dag/nodes/sec-picard-framework/lem-sc-koszul-derived-dual-evaluation.json`, is
stated and fully proved in `lean/Sheaf/RingTheory/KoszulDerivedDualEvaluation.lean`.
Its statement concerns derived maps from the unaugmented Koszul complex, not Ext,
an ideal, regularity, or roof representatives. Its recorded proof follows the
actual linear map, kernel/image calculation and quotient projection equation.
LeanSearch was unavailable (HTTP 500); LeanFinder returned projective-resolution
Ext comparisons, and grep found K-projective comparisons but no Koszul evaluation
theorem. Blueprint searches for Koszul and dual found no duplicate. No change
record is needed because no existing interface changed.

## Second reading by B3

1. **Interfaces: pass.** Diffed the complete item against the repository module.
   The sole original declaration's signature is byte for byte unchanged; the
   changes are its proof, proof documentation, private proved helpers, and plain
   proof imports. No existing definition, public import, visibility, hypothesis,
   or conclusion changed. The comparison is a new module, not an adaptation of
   another group's module. Both node Lean signatures match their modules verbatim.
   No change record is required.
2. **Proof and axioms: pass.** Read both modules completely, including the quotient
   augmentation, localization lifting, signed incoming-boundary identity, quotient
   projection, augmentation uniqueness, and exact shift cancellation. Both compile
   in import order without warnings. The delivery contains no sorry, axiom, unsafe,
   opaque, implemented_by, extern, or kernel-check bypass. Fresh scratch copies
   print the axioms of every theorem, including all eight private helpers: only
   propext, Classical.choice and Quot.sound occur. Every construction is explicit
   or uses proved statements; no arbitrary data comes from an unproved existence.
3. **New statements and searches: pass.** There is one new fully proved comparison
   and no split-off hole. It concerns the unaugmented complex, with actual
   component evaluation, so it does not restate the Ext roof theorem. Checked r=0:
   E^1=0 and the incoming natural-number differential is zero. Checked r=1 and
   f=0: the incoming image is zero, and evaluation has no extra sign. For a unit
   generator the quotient and dual homology vanish; the zero ring also gives zero
   modules, and the exterior-basis argument needs no Nontrivial instance. The
   incoming sign is absorbed by its own inverse (-1)^r in both directions.
   Independently searched LeanFinder for K-projective maps to a single object
   represented by component evaluation modulo the incoming differential; it gave
   projective-resolution Ext formulas, not this evaluated comparison. Loogle gave
   IsKProjective.Qh_map_bijective. Launcher grep found the single-cocycle boundary
   formula. Further rg searches of both library roots found the existence-only
   KoszulExtDualHomology / ExtSignedDualHomology comparisons and inaccessible
   private lifting helpers; none supplies the new public evaluation conclusion.
   The existing private degree-one and top-vanishing special cases are not copied:
   the retained helpers prove the reported strictly more general formulas. Read
   Stacks Tag 0BQZ's finite free Hom-complex calculation and the relevant Mathlib
   sources; the additional component/quotient details are the recorded agent proof.
4. **Route and pruning: pass after import repair.** The proof takes the direct
   K-projective localization route and proves the component quotient calculation;
   it uses no remaining Sheaf hole. Existing Nonempty equivalences cannot supply
   the required normalization, and importing the existing augmentation module
   would create a cycle through this item. The unit sk-thm-picard-duality has empty
   realized arrays; no realized statement or step is bypassed. Compared all old
   proof_deps: new-j3-koszul-projective-resolution and
   lem-sc-projective-ext-cocycle-roof-formulas are unused; the old
   lem-sc-hom-single-cocycle-component-formulas and
   lem-sc-hom-cocycle-homotopy-quotient-formulas are still used transitively in the
   comparison node. All other old dependencies remain used directly. Removed
   Mathlib.Algebra.Category.ModuleCat.Projective from the roof module (supplied
   by its public Ext.HasExt import), HomComplexCohomology from the comparison
   (supplied by HomComplexSingle and KProjective), and ShortComplex.ModuleCat
   from both (supplied publicly by KoszulDualComplex). Public imports were retained
   because they form the unchanged statement interface. Recompiled the repaired set.
5. **DAG: pass.** The existing node changes only proof, proof_deps, proof_origin.
   The new node has its source, self-contained statement and statement dependencies,
   complete proof steps, union proof_deps, actual search records, status split,
   created.item/group/date, blueprint ancestor, chapter/unit, and verbatim Lean
   record. Both proof plans agree with the actual augmentation, localization,
   kernel/image, and projection arguments. The removed redundant imports do not
   remove any mathematical dependency: their declarations remain available through
   the retained imports. No node or route changes were needed in this reading.

**Second-reader changes:** removed the four redundant plain imports above and
corrected this report's import claims. No theorem proof or signature needed repair.
Closed one original hole; added zero holes; this is a proof, not a decomposition.
