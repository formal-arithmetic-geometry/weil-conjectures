## What changed

Replaced the whole proof hole of
`AlgebraicGeometry.Etale.exists_constantModulePushforward_germ_eq_zero` by a compiling
proof. Its signature, universes, hypotheses, and conclusion are unchanged.

The proof represents the germ using Mathlib's `toPresheafFiber_jointly_surjective`,
uses `toPresheafFiber_eq_iff'` to shrink until the image section is zero, and constructs
an affine pointed refinement in the fully proved private `affine_point_refinement`.
The latter chooses an affine open containing the image of the geometric point and
factors its map through the open immersion. Restriction preserves the original germ
by the stalk cocone equation. Sectionwise continuity supplies an eventual zero
section, and naturality plus linearity sends that equality back to the required zero
germ. No geometric-point data is selected from an unproved theorem.

Added `Sheaf.AlgebraicGeometry.ConstantModulePushforwardAffineSectionVanishing`,
with one public sectionwise continuity theorem. This isolates precisely the local
section argument of parent proof steps 2--4. It has a fixed affine etale test object,
actual sections, and section equalities; it has no point, stalk, germ, colimit of direct
images, or arbitrary presentation. Thus it is a strictly separate part of the argument,
not the parent under a new name. The main module combines it with fully proved germ
representation, zero detection, affine refinement, and naturality.

Updated the parent's node proof, dependencies, and origin. The new node records the
remaining coefficient/canonical-map identifications and application of abelian section
continuity. The two Lean modules compile through the required `lcompile.py --all`.
The unit `sk-thm-p1` and its realized statement and steps are unchanged.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.exists_constantModulePushforward_germ_eq_zero`
(node `lem-weil-pbc-constant-module-pushforward-germ-vanishing`). No `sorry` remains
in the item's module. The private `affine_point_refinement` is also fully proved.

Added one hole, whose proof is exactly `:= by sorry`:
`AlgebraicGeometry.Etale.exists_constantModulePushforward_affine_section_eq_zero`
(node `lem-weil-pbc-constant-module-affine-section-vanishing`), in the new module
`Sheaf.AlgebraicGeometry.ConstantModulePushforwardAffineSectionVanishing`.
Its docstring gives the source and the complete natural-language local section proof.

This delivery is a decomposition: one upper hole closed, one strictly local section
hole added, net zero holes closed. It does not claim an axiom-free proof of continuity.
The germ manipulation and affine refinement are complete Lean proofs.

Edge cases checked in the statement and proof: the zero module uses the same linear
zero identities; cofilteredness excludes an empty indexing category; empty stage/limit
fibre products have zero module sections and remain covered by continuity; singleton
systems reduce to their limit isomorphism. The affine representative retains a
geometric point, so its nonemptiness is constructed rather than assumed.

## No longer needed

Removed the direct proof imports `WeilConjectures.ConstructibleSheaf.Defs` and
`WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity` from the item's module.
The former is already exposed by the unchanged public functoriality import. The latter
is relocated to the new section module: it remains needed for the unresolved local
section proof, so its module is not globally pruned.

The former direct proof dependencies removed from the parent are:
`lem-weil-pbc-constant-module-pushforward-functoriality`,
`lem-weil-pbc-etale-section-continuity`,
`lem-weil-pbc-filtered-category-exists-directed-final`,
`lem-weil-pbc-qcqs-morphism-permanence`, and
`lemma-constructible-pullback-constant`.

The parent now needs only the geometric-stalk node and the new section node as proof
dependencies. Its former direct dependencies on qcqs permanence, constant-sheaf pullback,
and constant-module functoriality belong to the local section node or the unchanged
statement imports. Their modules are not claimed globally unnecessary.

The explicit directed reindexing step and direct dependency
`lem-weil-pbc-filtered-category-exists-directed-final` are unnecessary here, since the
existing abelian section-continuity theorem accepts a small cofiltered category directly.
This is removal of a direct planned step, not a claim that the node is unreachable from
all other targets. No whole module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier germ plan left stalk representation, affine refinement, coefficient
comparison, and local continuity in one hole. The first two and the final passage back
to germs are now implemented. The local source file
`SectionContinuity.exists_unitComparison_app_eq_zero_of_isLimit` accepts a general
small cofiltered category, so the parent's proposed extra directed reindexing is not
needed at this level. Its hypotheses concern qcqs total schemes and a quasi-separated
base; they cannot be discharged on X without extra assumptions. The remaining section
node therefore uses the fibre-product system over the affine test scheme U, which is
quasi-separated. No assumption on X is added.

The remote clone contains only the literature lists. Read the primary sources online:
[Stacks Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1) and
[Stacks Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ).
No statement correction or change record is needed.

## New nodes

`lem-weil-pbc-constant-module-affine-section-vanishing`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-constant-module-affine-section-vanishing.json`,
with Lean module `Sheaf.AlgebraicGeometry.ConstantModulePushforwardAffineSectionVanishing`
and declaration
`AlgebraicGeometry.Etale.exists_constantModulePushforward_affine_section_eq_zero`.
It states eventual vanishing of an actual constant-module section on a fixed affine
etale test object, corresponding to steps 2--4 of the parent's plan. The node includes
three search kinds, its literature source, a complete proof plan, and an exact Lean
signature. No new definition, arbitrary witness choice, or change record was added.

## Second reading by V3

1. Compared every delivered module with the repository. The only existing module
changes its proof, adds a fully proved private helper, and replaces two plain proof
imports by the new plain proof import. The existing theorem signature is byte-for-byte
identical, as are the public imports and existing docstring. No definition, hypothesis,
conclusion, or target statement changed; no change record is required. Verdict: pass.

2. Compiled both modules in import order with `lcompile.py --all`: clean, with no
errors or warnings. Inspected both complete files: exactly one named public theorem
has `:= by sorry`; no forbidden declaration or hollow definition is present.
A scratch-copy `#print axioms` check gives only `propext`, `Classical.choice`, and
`Quot.sound` for `affine_point_refinement`; the parent and new section theorem also
have `sorryAx`, as expected from the single unresolved section theorem. The helper
constructs the refinement from an actual affine open and the geometric-point lift;
it does not choose data from an unproved existence theorem. Verdict: pass as a
one-for-one decomposition, not an axiom-free proof.

3. Read the new affine section statement, docstring, and node against Stacks
[09Z1](https://stacks.math.columbia.edu/tag/09Z1) and
[09YQ](https://stacks.math.columbia.edu/tag/09YQ). Base-changing the system to affine U
makes all total schemes qcqs without assuming X quasi-separated. Constant coefficients
pull back canonically, coefficient forgetting reflects zero, and section continuity
supplies the arrow in the stated conclusion. Checked zero coefficients, empty fibre
products, and a singleton index; none requires an added assumption. The statement is
the fixed-neighborhood section step, without any germ representation or shrinking,
and is strictly a part of the parent argument. Independent leanfinder search for
locally constant section continuity, loogle search for the point-fibre API, launcher
grep, and local `rg` found no exact noncircular replacement. Structure-sheaf continuity
and profinite locally constant descent do not supply this theorem directly. The
existing abelian section theorem still requires coefficient and canonical-map
identifications; these cannot be completed by a short application. Verdict: pass;
one sourced, documented section hole remains.

4. Read the proof from its conclusion down through the naturality calculation,
section theorem application, zero detection, and germ representation. The point API
already gives the shortest stalk reduction; the affine refinement uses the standard
open-immersion lift. The similar affine refinement in EtaleLocalRingTriples is private
and cannot replace this helper. Public imports are needed by the existing signature;
the new section module and its section-continuity import are plain proof imports.
The removed direct dependencies are now explicitly enumerated above. No whole module
is claimed globally pruned. Read `dag/units/sk-thm-p1.json`: neither this parent nor the
new local helper replaces a realized unit statement or step; its route stays intact.
Verdict: pass.

5. Compared parent node changes with the repository: only proof, proof_deps, and
proof_origin differ. Its steps describe the Lean reduction exactly. Both nodes have
proof_deps equal to the union of their steps' uses. Checked the new node's required
fields, source, searches, creation record, chapter/unit, and verbatim Lean signature.
Its proof plan records the remaining local continuity argument. Verdict: pass.

Second reading changed only this report: made the five removed parent proof dependencies
explicit and added these independent review and axiom-check results. No Lean proof,
statement, import, or node repair was needed.
