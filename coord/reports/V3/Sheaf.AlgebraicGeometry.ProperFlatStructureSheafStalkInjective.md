## What changed

Proved `AlgebraicGeometry.injective_structureSheafMap_stalk_of_proper_flat_fiber`
in `Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkInjective` with its original
signature. Added two proved private helpers: `flat_stalk_injective` and
`structure_unit_stalk_injective`. The proof uses only the nonemptiness consequence
of the fibre hypothesis and faithful flatness of a flat local stalk homomorphism;
properness and finite presentation are retained in the unchanged public statement.
The chosen unit is compared to the ordinary structure map by the already proved
`Scheme.Modules.tensorPullbackObjUnitToUnit_isIso`. Added its module as a proof-only
import and updated the item's DAG proof, dependencies and origin.

The empty-fibre case is excluded explicitly by zero versus one in the residue-field
section ring. The argument allows arbitrary nonreduced bases and fibres and does
not require quasi-coherence of an additional coefficient module. No definitions,
public signatures or visibility changed. The unit route of `sk-prop-av-cube` is
unchanged; this auxiliary node is not a realized unit step.

Searches: leanfinder query “stalk map of flat morphism of schemes is injective at a
point in its image” found `Flat.stalkMap` and the relevant local-ring interfaces;
loogle `AlgebraicGeometry.Scheme.Hom.stalkMap` found the germ/stalk formulas.
Ripgrep searches in the library and Mathlib found the local-ring argument in
`Mathlib.AlgebraicGeometry.Morphisms.Flat.epi_of_flat_of_surjective`, and the proved
`Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf` comparison. The actual germ
calculation is written and compiled here, without a new holed bridge theorem.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.injective_structureSheafMap_stalk_of_proper_flat_fiber`
(node `lem-sc-proper-flat-structure-sheaf-stalk-injective`). Added zero holes; split
off zero statements. The two private helpers are completely proved. No `sorry`
remains in the delivered module. This is a proof, not a decomposition.

## No longer needed

Removed proof-only imports:
- `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`
  (`lem-pc-rf-perfect-base-change`).
- `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`
  (`lem-sc-perfect-finite-free-residue-model`).

Neither node nor its perfect-complex descendants is needed by this injectivity
proof. They may still be reached by the separate surjectivity proof and other
library modules, so this report does not claim global removal from target closure.
All original public imports remain because they supply the unchanged statement's
scheme properties, fibre construction, chosen adjunction and module stalk map.
The new proof-only import is `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`
(node `lem-weil-pbc-module-pullback-structure-sheaf`), a proved comparison used as a
tool of another unit; no unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old DAG plan was unnecessarily strong for injectivity: it constructed a
rank-one perfect model to establish a bijective degree-zero map. Injectivity
already follows from flatness at one point over s. The fibre hypothesis guarantees
that point exists. No mathematical statement was found false and no interface
repair or forced adaptation was needed.

## Second reading by V3

1. **Interface: PASS.** Read the complete repository/sandbox diff. The existing
   theorem's signature is byte for byte identical, including the properness,
   flatness, local finite presentation and fixed-fibre `IsIso` hypotheses, and
   the exact `Classical.choose` adjunction in the conclusion. Only two private,
   proved helpers were added; no definition or visibility changed. No change
   record or forced adaptation is needed. Read Stacks Tag 0E62
   (https://stacks.math.columbia.edu/tag/0E62): its proper, flat, finitely presented
   criterion supplies the source context; this auxiliary result proves only
   injectivity at the fixed point. Proper plus locally finitely presented implies
   finitely presented, and the new underived argument needs only flatness and
   nonemptiness of the fixed fibre.
2. **Proof and axioms: PASS.** Compiled the delivered module through `lcompile.py`
   without errors or warnings. Compiled a scratch copy with `#print axioms` for
   `flat_stalk_injective`, `structure_unit_stalk_injective`, and
   `injective_structureSheafMap_stalk_of_proper_flat_fiber`: all three use exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Searched the
   delivered Lean for forbidden declarations and holes: none. Read the empty-fibre
   contradiction (zero equals one upstairs, impossible under the injective map
   from the nontrivial residue-field section ring), the two germ restrictions,
   and the final composition identity. Equality after the chosen unit is sent
   through the comparison and cancelled using ordinary stalk injectivity; no
   inverse comparison or extra faithfulness hypothesis is silently required.
   The existing adjunction existence theorem specifies its unit formula and
   determines the adjunction; no arbitrary data from an unproved existence
   statement is introduced.
3. **Split statements: PASS, none.** No new public statement or new hole was
   split off. The private flat-stalk helper is the argument in Mathlib
   `Morphisms/Flat.lean:157-167`, using `Flat.stalkMap`, locality, faithful
   flatness and its injectivity theorem. Checked the image-point helper directly
   against the section and germ formulas. The identity morphism and nonreduced
   local rings cause no exception; an empty fibre is excluded by the hypothesis,
   while an empty base has no point `s`. No reducedness or integrality is used.
4. **Route and pruning: PASS.** Independently searched the library for
   `injective.*stalk`, `stalk.*injective`, `nonempty.*fiber` and `fiber.*nonempty`,
   and read Mathlib's flat epimorphism proof. No existing theorem replaces the
   full chosen-unit stalk calculation. Read both `TensorPullbackAdjunction` and
   `TensorPullbackStructureSheaf`: the latter is already proved and supplies the
   exact comparison identity used. Its new import is proof-only. The retained
   public imports supply the unchanged statement and stalk-map interface.
   Both old proof dependencies, `lem-pc-rf-perfect-base-change` and
   `lem-sc-perfect-finite-free-residue-model`, are removed and reported above.
   Read `dag/units/sk-prop-av-cube.json`: this auxiliary node is not among its
   realized statement or steps (the recorded lists are empty), and this delivery
   changes no unit record or chapter route. The comparison theorem is used as
   a tool, not to replace the cube theorem's unit-level argument.
5. **DAG agreement: PASS.** Compared the existing node field by field: only
   `proof`, `proof_deps`, and `proof_origin` differ. The four proof steps match
   respectively fibre nonemptiness, the three-line Mathlib flat-local argument,
   the explicit germ calculation, and composition with the adjunction comparison.
   The union of their `uses` is exactly the recorded `proof_deps`, namely the
   tensor adjunction and structure-sheaf comparison nodes. There are no new nodes
   requiring additional fields. The old statement, sources, unit and Lean
   signature record remain unchanged.

Second reading changed only this report by adding the independent review and
validation evidence. No proof repair was needed. Net holes closed: one; holes
added: zero; split off: zero. Pruning claimed here concerns the two removed
imports, not an unmeasured global target-closure reduction.
