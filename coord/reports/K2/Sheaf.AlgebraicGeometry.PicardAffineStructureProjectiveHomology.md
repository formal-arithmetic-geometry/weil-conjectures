## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.picard_affine_structure_projective_homology`
without changing its signature or existing public imports. The proof now:

1. Extracts the upper support bound from `hb`, derives flatness from projectivity, and
   applies the proved `CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`.
2. Applies the new geometric comparison `picard_affine_projective_base_change`.
3. Uses the proved `tilde_preservesHomology`, `homologyFunctorFactors`, and `tilde.isoTop`
   to transport that derived isomorphism to an isomorphism of B-module homology objects.
4. Proves negative vanishing using the generic
   `Functor.isGE_rightDerivedFunctor_obj_singleFunctor` and preservation of zero objects.
5. Identifies H0 using `homologyRightDerivedFunctorObjSingleFunctorIso` and
   `rightDerivedZeroIsoSelf`, the supplied `hO`, and the proved tensor-unit isomorphism.
   Finally `tildeSelf` and `toTildeΓNatIso` identify sections of the structure sheaf with B.

The new module is `Sheaf.AlgebraicGeometry.PicardAffineProjectiveBaseChange`. It states
only an isomorphism of derived objects. It assumes K-flatness, without boundedness or
projectivity; assumes flatness, quasi-compactness and separatedness, without properness
or local finite presentation; and does not assume `hO`. Thus it isolates the geometric
comparison, independently of the connective and H0 conclusions of the assigned theorem.
Its proof plan uses canonical flat-invertible base change, exact open-site transport,
and the affine derived-pullback formula.

All added imports in the assigned module are private proof imports:
`PicardAffineProjectiveBaseChange`, `AffineBaseChangeTildeCoordinates`, `BoundedFlatKFlat`,
`TensorPullbackStructureSheaf`, the generic `RightDerivedFunctor.PlusCompatibility`, and
Mathlib's `GrothendieckCategory.EnoughInjectives`. Each supplies a declaration or instance
used in the proof. No existing definition, signature or visibility was changed, and no
consumer adaptation or change record is needed.

Both sandbox modules compile without warnings through `lcompile.py`. Sources checked:
[0A1D](https://stacks.math.columbia.edu/tag/0A1D),
[08DW](https://stacks.math.columbia.edu/tag/08DW),
[08FE](https://stacks.math.columbia.edu/tag/08FE),
[06Z0](https://stacks.math.columbia.edu/tag/06Z0), and
[064K](https://stacks.math.columbia.edu/tag/064K).

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.picard_affine_structure_projective_homology`
(node `lem-sc-picard-affine-structure-projective-homology`). Its complete Lean proof
combines a geometric comparison with proved algebraic and right-derived-functor results.
There are no remaining sorries in the assigned module.

Added exactly one hole:
`AlgebraicGeometry.Scheme.picard_affine_projective_base_change`
(node `lem-sc-picard-affine-projective-base-change`), in its own new module.
Its entire proof is `by sorry`; its docstring and DAG node contain the geometric argument.
This is a decomposition, not a net hole reduction: one hole closed and one added, net zero
before any import-closure effects. No auxiliary theorem claims either clause of the
original conclusion, and the structure-unit hypothesis is used only in the completed proof.

The new statement was checked on zero complexes, the zero coefficient ring, empty affine
opens, identity scalar extension, and non-flat scalar extensions. The K-flat hypothesis
is essential for ordinary extension to compute derived extension. No scalar-map flatness
or termwise finite generation is used. No data definition chooses an arbitrary unproved
existence witness; all isomorphism witnesses are used only inside the theorem proof.

## No longer needed

No original imports were removed: the input had only the imports needed by its statement.
The following original planned proof dependencies are no longer needed by this route:

- `lem-sc-flat-derived-structure-unit` / `Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit`:
  its residue-field lift is unnecessary; generic connective right-derived image and the
  supplied ordinary adjunction-unit hypothesis suffice.
- `lem-pc-rf-perfect-base-change` / `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`:
  the new geometric comparison needs only canonical base change for a flat family and
  the invertible structure module, not perfectness of the direct image.
- `lem-pc-affine-localized-derived-sheafification` /
  `Sheaf.AlgebraicGeometry.AffineLocalizedDerivedSheafification`: full module-derived
  sheafification is unnecessary; the new comparison uses the exact localized-site
  transport directly, and the assigned module uses exact tilde on homology.

These are route-level pruning statements, not claims that the modules are unreachable
from every other target. Their lower-level replacements are named in the updated nodes.
No unit statement or realized unit step was bypassed (`sk-prop-av-cube` has no realized
node attached to this item).

## Where the brief, the DAG or earlier work was wrong

The three initial dependency declarations do not directly yield the concrete scalar
extension comparison needed by the input signature. In particular the full-functor
statement of `affine_localized_derived_sheafification` alone is not an exact homology
comparison, and `exists_flat_derived_structure_unit` concerns residue fields, whereas
this theorem quantifies over all commutative coefficient rings. The completed proof
uses the generic right-derived comparison and proves the affine homology transport.
The uncompleted geometric glue is isolated explicitly rather than assumed from those
interfaces. The original theorem itself is not disputed and its signature is unchanged.

The ancestor helper returned no ancestor for this recently created input node. Following
its recorded parent `lem-sc-picard-affine-structure-projective-model` gives the blueprint
ancestor `thm-sc-theorem-of-cube`, recorded in the new node. Blueprint searches for
“affine K-flat”, “projective model”, and “structure image” found no duplicate of the new
geometric comparison. Mathlib searches are recorded with actual outcomes; LeanSearch
returned an internal-server error, recorded as unavailable. LeanFinder found flatness
and ordinary adjunction tools, and grep found general K-projective and tilde units.

The K-flat and exact-tilde declarations filed in `sk-thm-picard-semicon` are generic tool
lemmas. Their use does not replace the cube unit's argument.

## New nodes

`lem-sc-picard-affine-projective-base-change`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-affine-projective-base-change.json`, records
`AlgebraicGeometry.Scheme.picard_affine_projective_base_change` in the new module
`Sheaf.AlgebraicGeometry.PicardAffineProjectiveBaseChange`. It is the geometric
model-comparison part of the argument, prior to applying any homology functor. Its
source is Stacks Tags 0A1D, 08DW(2), 08FE and 06Z0. The node names the existing
restriction, exact localized-site transport, pullback-composition, flat-invertible
base-change, flat-module pullback and affine K-flat comparison statements. No change
record was created because all existing interfaces are unchanged.

## Second reading by K2

1. Compared both delivered modules with the repository versions. The existing theorem signature and all existing public imports are byte for byte unchanged; the added base-change theorem is a separate declaration and module. Verdict: pass.

2. Compiled both sandbox modules with `lcompile.py --all`; compilation completed without errors or warnings. The assigned module has no remaining `sorry`; the only remaining `sorry` is the named geometric comparison theorem, with its docstring and node. Verdict: pass.

3. Checked the added statement against the proof interface and edge cases recorded in the report. It is a strictly smaller geometric comparison, with no boundedness, projectivity, finite-presentation, or structure-unit assumptions. Its proof is explicitly documented and the node records its dependencies and source. Verdict: pass.

4. Reviewed the proof from the target downward. It uses the new geometric comparison, K-flatness, exact tilde transport, and generic right-derived results; the three superseded planned dependencies are documented as no longer needed. No import can be removed without losing a declaration used by the proof. Verdict: pass.

5. Compared both DAG nodes with the Lean declarations and proof route. The `proof`, `proof_deps`, `proof_origin`, unit, and module records agree; the unit route is retained. Verdict: pass.

Changed nothing during this second reading; only this review section was appended.
