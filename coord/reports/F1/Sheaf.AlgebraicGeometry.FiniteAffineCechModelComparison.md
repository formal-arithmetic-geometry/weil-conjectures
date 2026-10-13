## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.FiniteAffineCechModelComparison`
with a complete Lean reduction. The original theorem signature and public imports are unchanged.
Added proof-only imports of `FiniteAffineCechIntersectionBaseChange`,
`FiniteAffineCechSectionBaseChange`, `LinearCechSheafResolution`,
`OpenPushforwardDerivedComparison`, and the source `Cohomology.Exact`,
`Affine.CechAcyclic`, `InjectiveFlasque`, `Topology.Sheaves.CechFlasque`, and
`Modules.QuasicoherentKernel` modules. The source `DirectImage.AffineMorphism` import
from the earlier attempt was removed because it creates an import cycle through
`DirectImage.FiniteFreeComplex` and the proper-flat model back to this module.
Its proved affine acyclicity argument is reproduced in four private proved helpers.
The two transparency settings are scoped to the assigned theorem; no heartbeat increase remains.

The proof constructs the inverse-image cover, proves that it covers using the supplied square,
and consumes a Čech resolution witness inside the proof. It proves all terms acyclic by affine
higher-image vanishing, open pushforward composition and finite products. It then composes the
section-complex comparison with the existing proved `rightDerivedObjIsoOfResolution`.
No data definition chooses a witness from an unproved existence statement.

The affine intersection lemma is proved entirely from Mathlib: cancellation and pasting of
cartesian restriction squares, affine base change, and `IsAffineHom.of_comp`.
The new resolution statement adds explicit local scalar compatibility to the existing Čech
interface. The section-complex comparison is independent of covering, augmentation, acyclicity
and injective resolutions; it does not mention higher direct images.

All four delivered modules compile in dependency order with no warnings.
The new-node Lean statement records now reproduce the exact multiline theorem signatures. The original theorem's
signature is preserved. The unit is `sk-thm-picard-coherence`, whose realized fields are empty;
the proof retains its affine Čech and acyclic-resolution route, below the unit level.

## Proved and sorry left

Closed one original hole, by decomposition:
`AlgebraicGeometry.Scheme.Modules.finiteAffineCechModel_comparison`
(node `lem-pc-finite-affine-cech-model-comparison`). No sorry remains in the assigned module.

Also proved, with no sorry:
`AlgebraicGeometry.finiteAffineCech_intersection_baseChange`
(node `lem-pc-finite-affine-cech-intersection-base-change`).

Added exactly two public named theorem holes, each with its full proof in words:

- `AlgebraicGeometry.exists_linear_cech_sheaf_resolution`
  (`lem-pc-linear-cech-sheaf-resolution`, module `Sheaf.AlgebraicGeometry.LinearCechSheafResolution`).
- `AlgebraicGeometry.Scheme.Modules.finiteAffineCech_section_baseChange`
  (`lem-pc-finite-affine-cech-section-base-change`, module
  `Sheaf.AlgebraicGeometry.FiniteAffineCechSectionBaseChange`).

This is a decomposition, not a sorry-free proof of the comparison: one upper hole closed and
two lower holes added. Existing dependency holes are not claimed as proved. There are no other
sorries in the delivered files, no new axioms and no definitions with missing data.

## No longer needed

Removed the earlier attempt's proof-only import of
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`. Its proper
finiteness declarations are not needed; the actual affine acyclicity proof uses only
the lower Čech and dimension-shifting modules listed above.
No original import was removed. In particular the original public `DirectImage.Sections` import
is retained, preserving the public environment through which the theorem's higherDirectImage
signature was supplied. No claim that a module leaves the targets' import closure is made.

The assigned node no longer directly uses `lem-pc-affine-vanishing`, `lem-pc-cech-computes`,
`lem-pc-cohomology-sections-affine-base`, `lem-pc-alternating-cech-computes`,
`def-pc-affine-alternating-cech-model`, or `def-pc-finite-affine-cech-model` as proof dependencies.
The model definition remains a statement dependency. Alternating comparison remains needed
below the new section-complex lemma, and affine vanishing/cohomology comparisons can remain
reachable through existing public imports. These are removals from the direct proof plan, not
claims of global module pruning. The proof-dependency imports of the two open lemmas are retained as their future proof plan.
Second reading removed the new resolution module's unnecessary public import of
`Sheaf.AlgebraicGeometry.CechSheafResolution`; it now directly exposes only the types used
in its statement and privately imports `CechSheafConstruction` and `CechSheafLocalQuasiIso`.
The section-base-change module privately imports its intersection, affine-section and
ordered-comparison proof dependencies. This is import cleanup, not a claim of global pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt compiled against cached modules but failed the dry-run
source import-cycle check. The cycle was
`FiniteAffineCechModelComparison → DirectImage.AffineMorphism →
DirectImage.FiniteFreeComplex → ProperFlatCechModel → ProperFlatCohomologyModel →
ProperFlatCohomologyData → FiniteAffineCechModelComparison`. The private acyclicity
helpers remove this cycle without changing any other module or public signature.

The old node's two proof steps describe the mathematics but their listed declarations do not
supply the required termwise base-change and sheaf-linear compatibility interfaces. Merely
applying affine cohomology comparison statements cannot produce the specified model comparison.
The reduction uses the ordinary acyclic-resolution criterion already proved in the source.

`exists_cech_sheaf_resolution` identifies terms as presheaves of modules over the global ring.
Its stated e and hd alone do not assert compatibility with scalars over arbitrary opens.
That is sufficient for its abelian-sheaf exactness argument, but is not a sufficient interface
for constructing an O-linear comparison on a nonaffine base. The new linear version keeps the
same differential, augmentation and term formulas and adds exactly the coordinatewise local
scalar formula. It does not assert that arbitrary old witnesses satisfy this extra formula;
its proof constructs the canonical witnesses. No existing interface was modified.

The old Čech resolution index universe equals the scheme universe. Direct use with `Fin r`
in a universe-polymorphic theorem caused elaboration to run out of heartbeats. Reindexing the
new cover by `ULift.{u} (Fin r)` meets the existing interface and compiles in seconds, without
changing the assigned theorem's universes or altering any library definition.

Edge cases checked in the statements and proof: r=0, q=0 and positive q, zero coefficients,
empty intersection, nonaffine T', and arbitrary supplied cartesian square. Empty families give
zero Čech products even without a covering condition in the section-complex lemma. For the
resolution, an empty cover forces the source empty. The geometric lemma concerns affine
morphisms over arbitrary T', not an incorrectly asserted affine total source.

Searches were run through msearch for all three new nodes and by rg in both library roots.
LeanSearch was unavailable and is recorded as unavailable. Loogle found homologyMapIso;
LeanFinder and grep found affine-morphism tools but no complete section-complex comparison or
locally scalar-compatible Čech resolution. Blueprint searches for Čech/base change, affine opens,
scalar and 01FK found no exact duplicate of the new refinements. The affine-section comparison
node from another unit is used as a generic algebraic tool by the section-complex plan;
the unit's own Čech route is retained.

Sources checked: [Stacks 02KE](https://stacks.math.columbia.edu/tag/02KE),
[01S5](https://stacks.math.columbia.edu/tag/01S5),
[01KP](https://stacks.math.columbia.edu/tag/01KP),
[01EO](https://stacks.math.columbia.edu/tag/01EO), and
[01FK](https://stacks.math.columbia.edu/tag/01FK), together with the existing blueprint
Čech resolution and its recorded Lean declarations. The affine tensor calculation is used on
complex terms; no flatness-free interchange of tensor and homology is claimed.

## New nodes

`lem-pc-finite-affine-cech-intersection-base-change`, in
`FiniteAffineCechIntersectionBaseChange.lean`: proved Mathlib geometry for one affine open,
with no coefficient, cover or cohomology hypothesis. Both inclusion and projection are affine.

`lem-pc-linear-cech-sheaf-resolution`, in `LinearCechSheafResolution.lean`: remaining
construction/exactness step for any module and any open cover, explicitly retaining local
scalar actions. It contains no morphism of base schemes or higher-direct-image conclusion.

`lem-pc-finite-affine-cech-section-base-change`, in `FiniteAffineCechSectionBaseChange.lean`:
remaining ordinary section-complex calculation, for any Čech complex with the listed term,
differential and local scalar formulas. It uses no augmentation or cohomological acyclicity
and therefore is strictly a separate part of the comparison proof.

The assigned node's proof, proof_deps and proof_origin are updated to the compiled reduction.
No change record is needed: no existing definition, signature or public visibility changed.

## Second reading by F1

1. **Interfaces: pass.** Read the complete diff of the assigned module and compared its
   theorem signature byte for byte with the repository. The signature, original docstring,
   public imports and namespace are unchanged. There are three new modules and no adapted
   existing modules, no changed definition, and no change record. The existing node differs
   only in `proof`, `proof_deps`, and `proof_origin`.
2. **Proof/kernel: pass as a decomposition.** Independently compiled all four files in import
   order, without errors or warnings. A scratch `#print axioms` audit returned only
   `propext`, `Classical.choice`, `Quot.sound` for the geometric lemma, and those plus
   `sorryAx` for the two declared holes and the assigned theorem. Read all four private
   acyclicity helpers against the source affine-morphism proof: they use flasqueness,
   exact forgetting to abelian sheaves, affine section surjectivity and dimension shifting.
   The geometry proof uses cartesian cancellation/pasting and affine cancellation along a
   separated map. No prohibited declaration or hollow definition occurs. The resolution
   witness and term isomorphisms are eliminated inside a proposition proof; they define no
   arbitrary public data. Exactly the two reported public theorem holes remain.
3. **Split statements: pass.** Checked the linear-resolution formula on arbitrary opens,
   the section-complex lemma without a covering assumption, r=0, r=1, zero coefficients,
   q=0, empty intersections and a nonaffine new base. Full tuples always have p+1 entries,
   so image/intersection commutation never uses an empty intersection. The finite ordered
   versus usual comparison applies to a family covering its union, including the empty
   union; it does not need to cover X'. Local scalar compatibility, unlike global-ring
   linearity alone, makes the section isomorphisms O-linear. Both holes are true and
   strictly separate parts of the original argument: the resolution lemma has no base
   morphism, and the section lemma has no augmentation, resolution or derived image.
   Reviewed the existing construction/local-quasi-isomorphism and ordered-comparison
   interfaces, and searched both Lean roots with different scalar/linearity/base-change
   terms. Additional msearch LeanFinder, Loogle and grep queries found no exact replacement;
   `exists_cech_sheaf_resolution` lacks the extra scalar formula, so applying it alone cannot
   close the new hole. The canonical construction still requires work, not a short proof.
   Checked [Stacks 02KE](https://stacks.math.columbia.edu/tag/02KE) for the termwise tensor
   calculation and [Stacks 01FM](https://stacks.math.columbia.edu/tag/01FM) for the ordered
   homotopy equivalence. The two holes have complete construction/proof docstrings and nodes.
4. **Route/pruning: pass after import cleanup.** The proof first uses proved Mathlib geometry
   and the proved generic acyclic-resolution criterion; the two new holes supply precisely
   the missing local-scalar construction and section calculation. The private affine
   acyclicity proof avoids the documented source import cycle. Reviewed all six old direct
   proof dependencies: all six removals are listed in `No longer needed`, with the model
   retained as a statement dependency and ordered comparison retained below the new lemma.
   The unit `sk-thm-picard-coherence` has empty realized arrays; its affine-Cech and acyclic
   resolution route is kept. No global module pruning or net hole reduction is claimed.
5. **Nodes: pass.** Read all four delivered nodes, compared the existing node's diff,
   verified each `proof_deps` equals the union of step `uses`, checked sources, universes,
   chapter/unit, creation metadata, and exact Lean signature records. The source affine
   vanishing node is used via its reproduced proved dimension-shifting argument, explicitly
   recorded in the assigned node. The two new statements retain their construction and
   calculation proof plans; none merely renames the comparison conclusion.

Changed: narrowed `LinearCechSheafResolution` public imports to signature dependencies,
kept its construction/local-exactness dependencies private, added the missing private
proof-plan imports in `FiniteAffineCechSectionBaseChange`, and corrected the latter's
source explanation to distinguish Tag 01FK from Tag 01FM. No proof or statement changed.
Hole accounting remains one original hole closed and two added (decomposition, net -1).
