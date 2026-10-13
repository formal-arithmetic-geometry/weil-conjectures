## What changed

Replaced the sorry in AlgebraicGeometry.Scheme.affineRegularStalkGerm_scalar by
an explicit germ calculation. It unfolds the constructed unit germ, uses
TopCat.Presheaf.stalkFunctor_map_germ_apply, applies the sectionwise scalar identity,
and uses PresheafOfModules.germ_smul. The original statement, visibility, definitions,
and public import are unchanged. Added the proof-only import
Sheaf.AlgebraicGeometry.AffineScalarSectionAction and its new node.

The remaining affine-chart calculation is isolated as
AlgebraicGeometry.Scheme.affineScalarEnd_section_action. It concerns arbitrary sections
over U and contains neither a point nor a stalk nor the unit germ. It is the
sectionwise part of the original two-step argument, not the original statement renamed.
Both delivery modules compile with the prescribed lcompile.py.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.Scheme.affineRegularStalkGerm_scalar
(lem-sc-affine-regular-stalk-scalar), by a proof from the new sectionwise theorem.
Added one hole: AlgebraicGeometry.Scheme.affineScalarEnd_section_action
(lem-sc-affine-scalar-section-action), in its own new module, with a complete proof
in words. The item's module contains no sorry.

This is a decomposition: one upper hole closed and one strictly sectionwise hole
added, net zero holes closed. It does not claim an axiom-free proof of the original
result. The remaining theorem needs the calculation through tilde, restriction by
isoSpec, the inverse over equivalence, and pushforwardOver. The germ step is finished.

Edge cases checked mathematically for the new statement: a = 0 gives the zero map;
a = 1 gives the identity; m = 0 gives zero; on the empty affine open the section
modules are zero. No reducedness, domain condition, or nonempty-open condition is used.
The unit's statement and route remain unchanged.

## No longer needed

No imports or modules are pruned. The original public import supplies definitions in
the unchanged statement. The direct proof dependency on
lem-pc-affine-perfect-module-model is removed from the item's proof_deps: its module
remains transitively required for the definition of affinePerfectSheafification, and
the new section-action node still refers to that construction. In particular the
module Sheaf.AlgebraicGeometry.AffinePerfectModuleModel cannot be pruned globally.
No other nodes are established as no longer needed.

## Where the brief, the DAG or earlier work was wrong

The previous blocked attempts never elaborated the saved germ reduction. The shared
snapshot still lacks AffineFreeBasisGerms.olean. For this attempt the unchanged
repository source of that module was copied into the sandbox and compiled locally
with the permitted lcompile.py --all. Its local artifacts in .lbuild allow the two
delivery modules to compile. The dependency source copy was then removed from the
sandbox's lean/ directory; no dependency edit or rebuild of the shared library is
part of this delivery. The second reader must retain these artifacts, or repeat the
same sandbox-only compilation of the unchanged dependency if the snapshot is still
missing it. No shared compiled file was written.

The saved attempt needed an explicit change exposing the unit germ on the right
before germ_smul could rewrite it. Its remaining section goal is the new node above.
The source literature files are not downloaded in this checkout; the new node extracts
the sectionwise step already documented in the original node and declaration, with
Mathlib's actual restriction and tilde constructions read to check the transport.
Searches (logged in searches.jsonl) found tilde.toOpen_map_app and generic sheafification
scalar laws, but no theorem already stating the affine-chart and direct-image identity.
The blueprint scalar and affine-scalar searches found no duplicate blueprint statement.

## New nodes

lem-sc-affine-scalar-section-action, in
lean/Sheaf/AlgebraicGeometry/AffineScalarSectionAction.lean, states the action of the
sheafified coordinate scalar endomorphism on all sections over its affine chart after
ordinary direct image. It isolates the scalar transport calculation before taking
any germ. The original node now records the actual Lean germ argument and this
new dependency. No change records or forced adaptations are needed.

## Second reading by P2

1. PASS: Compared the existing module and node against the repository with diff.
   The sole existing declaration has exactly the original signature and docstring;
   only its proof and a plain proof-only import change. Removed an accidental extra
   space before its proof delimiter. No definitions, targets, visibility, or public
   imports change. The new module's public import supplies its signature's data.
2. PASS as a decomposition: Both delivery modules compile locally with lcompile.py
   --all. An independent scratch-copy axiom check shows only propext,
   Classical.choice, Quot.sound and sorryAx for the two theorems. The constructed
   affineRegularStalkGerm and affinePerfectSheafification use only the three permitted
   axioms, without sorryAx. The only delivered sorry is the whole proof of the named
   affineScalarEnd_section_action; there are no forbidden declarations or hollow data.
3. PASS: The split-off theorem is the sectionwise transport step, not the stalk
   assertion renamed. It omits the point, germ and unit-section comparison and applies
   to arbitrary sections. Checked a = 0, a = 1, m = 0 and the empty chart. Read
   tilde.map, tilde.toOpen_map_app, restrictFunctor, overEquiv, pushforwardOver and
   isoSpec_hom_appTop: restriction uses appIso.inv and direct-image scalars use
   prod.snd, as its proof in words requires. Its source, docstring and node match.
   Independent leanfinder, loogle and grep searches used coordinate-module functor,
   multiplication-endomorphism, tilde/map and map_smul terminology (searches.jsonl).
   Also searched the project's affine modules and upstream Modules/Sheaf and
   Modules/Tilde sources. Found localization and restriction scalar identities,
   but no existing theorem for this composite action. AffineOpenRealizationScalar
   concerns derived comparisons and does not provide this sectionwise result.
   Completing the open chart-transport calculation is not a few-minute application
   of a found result, so it remains explicitly open.
4. PASS: The proof takes the direct stalk-map-on-germs route followed by germ_smul;
   the section calculation is precisely the first step of the original node's plan.
   Imports are needed. No longer needed names the only old proof dependency removed,
   lem-pc-affine-perfect-module-model, and explains its continued transitive use.
   No module is pruned. The sk-prop-av-cube unit and its realized fields are unchanged;
   this refinement stays below its route. Net holes closed is zero.
5. PASS: Existing node changes are confined to proof, proof_deps and proof_origin.
   These describe the actual germ reduction. The new node has matching verbatim
   Lean statement, source, statement dependencies, proof steps and their union,
   proof_origin, search records, split status, created record, blueprint provenance,
   chapter, unit and Lean record. No statement-change record is needed.

Second-reading changes: restored byte-for-byte signature whitespace and added this
review record. No mathematical proof or statement repair was necessary.
