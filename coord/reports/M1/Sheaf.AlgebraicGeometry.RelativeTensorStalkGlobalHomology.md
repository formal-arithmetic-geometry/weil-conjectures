## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.relativeTensor_stalk_global_homology_iso`
with a compiling proof from two strictly smaller comparisons. The actual module M is the stalk
of F on the inverse-image ringed space, restricted along the canonical ring stalk isomorphism.
The proof constructs that ringed space and isomorphism, proves exactness of the module stalk
functor through the faithful forgetful functor, maps the prescribed quasi-isomorphism q through
this exact functor and Q, and composes tensor, homology and abelian-group isomorphisms.
It uses one constructed M in every degree. All three delivery modules compile without warnings through lcompile.py --all.
The existing public signature and docstring are unchanged. No definition or existing statement changed.

Added `Sheaf.Algebra.Homology.StalkKFlatTensorHomology`, with an arbitrary ringed space,
a ring isomorphism and a K-flat sheaf complex. This comparison has no scheme morphism,
relative model K, q or existential module choice. Added
`Sheaf.AlgebraicGeometry.RelativeInverseImageStalkRestriction`, comparing two actual module
stalk complexes after scalar restriction. This comparison has no tensor factor F, no K-flatness,
no quasi-isomorphism q and no homology or derived category. Both are strict parts of the
argument, not renamed versions of the item. Updated the item's proof route in its node.

New proof imports in the item: the two comparisons,
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`,
`Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`Mathlib.Algebra.Category.Grp.Colimits`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
The last imports support the local exactness proof and the quasi-isomorphism mapping step.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.Scheme.relativeTensor_stalk_global_homology_iso`
(node `lem-pc-relative-tensor-stalk-global-homology`). Its proof compiles without a sorry.

Added one hole: `stalk_kFlat_tensor_homology_iso`
(node `lem-pc-stalk-kflat-tensor-homology`).

Fully proved the new theorem
`AlgebraicGeometry.Scheme.relative_inverseImage_stalk_restriction_iso`
(node `lem-pc-relative-inverse-image-stalk-restriction`). Its private ring stalk map and scalar
compatibility helpers are also proved. The ring comparison follows the sheaf adjunction unit;
the scalar compatibility is checked on germs on a common neighborhood. ModuleCat.isoMk uses
the identity abelian-group isomorphism, and naturality makes the complex comparison.

This is a decomposition: one upper hole closed, one strictly smaller hole added.
There is no sorry in the item's module or in any definition or private helper.
The remaining theorem has a source reference, a full proof sketch, and a matching DAG node.

The new statements were checked against zero modules, zero rings, an empty space (where no
point can be supplied), and arbitrary unbounded complexes. Neither requires flatness of F.
The scalar-restriction theorem is degreewise and does not assert that f.stalkMap is invertible;
only the inverse-image ring stalk comparison is invertible.

## No longer needed

No existing Lean import was removed: the item originally had no imports of the six planned
proof dependencies. Its public imports supply the unchanged statement and its instances.

The revised route does not need `lem-pc-kflat-resolution`
(`Sheaf.Algebra.Homology.KFlatResolution`) or `lem-pc-kflat-tensor-quasi-iso`
(`Sheaf.Algebra.Homology.KFlatTensorQuasiIso`). The prescribed P already exists, and the
proved source declaration `DerivedCategory.QObjTensorQObjIsoOfKFlatLeft` gives the K-flat
derived tensor computation directly; a second K-flat replacement and one-point-site comparison
are unnecessary. It also does not need `lem-pc-ringed-inverse-image-stalk-scalar-transport`
(`Sheaf.Algebra.Homology.InverseImageStalkScalarTransport`), which compares inverse-image
modules and extensions of scalars, rather than stalks of an arbitrary relatively restricted
module sheaf. The new restriction comparison states the required operation directly.

The stalk criterion, stalk tensor complex comparison and module stalk exactness remain needed
in the new K-flat comparison's proof plan; they are not claimed as pruned. No node realizing
this unit's own statement or steps was bypassed (`realized` is empty for this unit).

Second reading removed the redundant imports `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
and `Mathlib.Topology.Sheaves.Sheafify` from the new restriction module, and
`Mathlib.Topology.Sheaves.Abelian` from the new K-flat module. In both new modules, the broad
`Sheaf.AlgebraicGeometry.DerivedCategory` import was replaced with
`Sheaf.Paper.DerivedHomMayerVietoris`, which supplies the signature notation `moduleRings`.
These are import cleanups, not claims that existing modules left the targets import closure.

## Where the brief, the DAG or earlier work was wrong

The existing inverse-image scalar transport dependency supplies inverse-image module stalks
and extension of scalars; its public statement does not supply the restriction-of-scalars
comparison for res(K) used in this item. Likewise the planned K-flat tensor quasi-isomorphism
lemma is on a one-point sheaf category, while this item needs the source library's actual
ModuleCat derived tensor. These are interface gaps in the plan, not false mathematics.

No disputed statement, target signature change, hollow definition or forced adaptation.
The main proof's exactness lemmas use the actual categorical stalk functor and faithful module
forgetful functor, not an assumed unproved stalk representative. Compilation is exclusively
through lcompile.py. The first dry run requested a change record for file-level elaboration options; those options
were removed from the item, and its exactness helpers are private theorems rather than global
instances. The unchanged signature still compiles. The second-reading section is left for the
independent reader, as required by the brief. The tool uses a shared compiler queue; elapsed command time can include
waiting for a compiler slot.

## New nodes

`lem-pc-stalk-kflat-tensor-homology`: a source-backed generic K-flat computation at one stalk,
with scalar transport along an arbitrary ring isomorphism. The planned source module
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` provides the K-flat tensor model
comparison, so the next worker need only combine it with stalk and scalar-transport interfaces.

`lem-pc-relative-inverse-image-stalk-restriction`: a proved, source-backed complex comparison for the
canonical ring map of a scheme morphism. Its proof is the identity on underlying additive
stalks, linear by the germ action formula and the adjunction equality for the ring map.

Both nodes are below the same existing unit and nearest blueprint ancestor as the item.
Searches used LeanFinder, Loogle, grep and LeanSearch; LeanSearch returned an Internal Server
Error, recorded as unavailable. No change record is needed because existing interfaces stay
identical.

## Second reading by M1

1. **Existing interface — pass.** Compared the delivered main module with the repository
   version by diff and compared the declaration text programmatically. The entire signature
   of `relativeTensor_stalk_global_homology_iso` is byte-for-byte identical after restoring
   one extra space before `:=`; its docstring and public imports are unchanged. The other
   two modules are new, and all three node `lean.statement` records occur verbatim in Lean.
   No existing definition or statement changes, and no change record is necessary.
2. **Proof and construction — pass.** Read all three files, including the private helpers.
   The main proof constructs Z, k and S and takes the single module `S.obj F`; it does not
   choose arbitrary data from an unproved existence theorem. Exactness is reflected through
   the module forgetful functor, q is mapped by an exact S, and its derived isomorphism is
   tensored with the identity before applying homology. The scalar comparison proves
   `k ≫ psi = f.stalkMap y` by the
   adjunction unit, checks scalar actions on germs over `U ⊓ V`, and applies its natural
   identity isomorphism degreewise. Initial `lcompile.py --all` passed for all three modules,
   without warnings. There is exactly one delivered `sorry`, the public named theorem
   `stalk_kFlat_tensor_homology_iso`; no forbidden declaration or hollow definition occurs.
3. **New comparisons — pass.** Read Stacks [06YB](https://stacks.math.columbia.edu/tag/06YB),
   [09U9](https://stacks.math.columbia.edu/tag/09U9),
   [01AG](https://stacks.math.columbia.edu/tag/01AG),
   [008H](https://stacks.math.columbia.edu/tag/008H), and
   [0098](https://stacks.math.columbia.edu/tag/0098), as well as the upstream
   `DerivedCategory.QObjTensorQObjIsoOfKFlatLeft` and the existing stalk criterion,
   stalk tensor complex comparison, and inverse-image scalar transport interfaces.
   The remaining hole is a generic K-flat computation with an explicit stalk module,
   without f, K, q or the existential choice. The relative restriction comparison is
   a separately proved part of the main argument without tensor or derived homology.
   Neither is a renamed main conclusion. Their full docstring arguments and matching
   nodes are present. In the zero-ring case every module is zero; zero complexes give
   zero homology; an empty space supplies no x; unbounded complexes use sums in the
   total tensor. Restriction is only along a ring isomorphism in the K-flat lemma;
   the other lemma does not assume `f.stalkMap y` invertible. Independent LeanFinder
   query `exact monoidal stalk functor derived tensor cohomology K flat`, Loogle query
   `TopCat.Presheaf.stalkFunctor`, and grep query
   `restrictScalars.*(tensor|equivalence)|homologyIso` found components, not the comparison.
   Additional rg searches in lean/Sheaf and the upstream algebra modules found no duplicate.
   Closing the remaining scalar-transport/tensor/homology glue is not a few-minute proof.
4. **Route and pruning — pass after import cleanup.** The exactness and representative
   comparison are actually discharged above the remaining K-flat computation. The original
   six planned proof dependencies are accounted for under `## No longer needed`: resolution,
   tensor quasi-isomorphism, and inverse-image extension-of-scalars transport are bypassed;
   stalk criterion, stalk tensor complex and module stalk exactness remain in the new hole's
   plan. No existing imported module is claimed pruned. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement is empty and its single
   realized step list is empty, so this reduction bypasses no fixed realized unit step.
   All added imports of the main proof are plain imports. In the new modules I replaced
   the unnecessarily broad DerivedCategory import with the module that defines moduleRings,
   `Sheaf.Paper.DerivedHomMayerVietoris`. I also removed redundant ModuleCat.ChangeOfRings
   and Topology.Sheaves.Sheafify imports from the restriction module and the redundant
   Topology.Sheaves.Abelian import from the K-flat module. Remaining public imports support
   the signatures and their required instances.
5. **DAG — pass.** The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   Its three steps match the construction of S, mapping q plus the restriction comparison,
   and composition with the K-flat homology comparison. Its dependencies are exactly the
   two new comparisons and the module-sheaf colimit forgetful theorem used for exactness.
   The new restriction node records the adjunction/germ/naturality argument that is proved.
   The new K-flat node records the remaining stalk criterion, tensor, exactness and source
   derived tensor components; their statements supply the facts its plan invokes. Both
   nodes have source, searches, creation, blueprint, chapter, unit and verbatim Lean records.

Removing the new restriction module’s public Sheafify import exposed a proof-only dependency
of the main module: its use of `stalkFunctor_map_unit_toSheafify_isIso`. I added
`import Mathlib.Topology.Sheaves.Sheafify` directly to the main module, with plain visibility.

Second-reading changes are import minimization in the two new modules, the direct plain
Sheafify proof import in the main module, restoration of the
main signature's whitespace, removal of one blank line, and this review. The mathematical
proofs and the named remaining hole were retained. This remains a decomposition: one old
hole closed and one new hole added, with no claimed positive net hole reduction.

Final axiom check: a scratch copy of the main module with explicit `#print axioms` for all
three public theorems compiled with exit code 0. The restriction comparison uses exactly
`propext`, `Classical.choice`, and `Quot.sound`; the main theorem and the remaining K-flat
comparison additionally use `sorryAx`, as expected from the named remaining hole. No other
axiom occurs. Both new modules compiled after import cleanup, and the main module compiled
with its direct plain Sheafify import; all were warning-free.
