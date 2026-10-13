## What changed

Repair of the returned landing: generalized the private `homObjMap_add_right`
helper in place from one shared universe and `SmallCategory` to independent site and value
universes. The site is in universe `v`, while ring and module sheaves are in
`max u v`, allowing values in a larger universe than the site. Its unchanged
sectionwise proof gives the original small-site case used by the cone calculation.
This follows the return's permitted generalization alternative: the neighboring
helper is private, and importing its module would create a cycle because
`HomComplexMappingCone` imports this differential module. No existing public
signature, proof-dependency import, or target changed. The earlier reading is retained below; the final section records the repair's
independent second reading.


Proved `CategoryTheory.homComplex_mappingCone_differential` in
`Sheaf.Algebra.Homology.HomComplexMappingConeDifferential`, preserving its statement,
visibility and existing docstring. The second reading narrowed the cone import
and made the proof-only tactic import private. Added four proved private helpers:
`homObjMap_add_right`, `homObjMap_neg_right`, `homObjMap_comp_id_right`, and
`cone_sum_identity`. The proof uses product joint monicity, the differential and map
clauses of `homComplex_projections_exists`, and Mathlib's cone differential formulas.
It compares sums into the cone directly. Updated the node's proof and proof origin
accordingly; its sole proof dependency remains unchanged.

The launcher searches were run with LeanFinder (8 mapping-cone cochain hits, none an
internal sheaf Hom comparison), Loogle (`"homObjMap"`, no hits), and grep
(`homComplex.*mappingCone|mappingCone.*homComplex`, only the Mathlib triangulated
file). Local searches found the projection specification and analogous sectionwise
internal Hom additivity proofs. The unit's realized statement and steps are empty;
this calculation does not bypass a realized unit step.

The repaired single-file launcher compile passed without warnings in 41.3 seconds.
The generalized helper was also checked in isolation. The duplicate-statement
landing guard passed after generalization.
The proof introduces the statement's existing let bindings rather than expanding
and reconstructing them, avoiding repeated elaboration of the chosen Hom functor.

## Proved and sorry left

Closed the sole hole: `CategoryTheory.homComplex_mappingCone_differential`
(node `lem-sc-hom-complex-mapping-cone-differential`). No `sorry` remains in the
item, and none was added in another module. This is a proof, not a decomposition.
All four private helpers are proved. No definition or existing signature changed.

## No longer needed

Replaced `Mathlib.Algebra.Homology.HomotopyCategory.MappingCone` with the
smaller statement dependency `Mathlib.Algebra.Homology.HomotopyCofiber` and
plain `import Mathlib.Tactic.Abel` (used only by the private additive helper).
No Sheaf dependency nodes or modules were removed. The existing sole proof
dependency `lem-sc-hom-complex-projections` is used through its product, differential,
and map clauses. The planned second postcomposition with internal Hom of cone
projections is unnecessary; direct expansion through cone inclusions proves the
component equality without adding a lemma for their joint monicity.

## Where the brief, the DAG or earlier work was wrong

The landing guard rejected the original private additivity helper as a duplicate
of the same statement in `HomComplexMappingCone`. The repair generalizes its
site and value universes in place; neither duplicating the original
small-site statement nor importing the downstream module is needed.
No disputed mathematical statement or incorrect dependency was found. The DAG's cone-projection
argument is valid but longer than necessary; the updated proof records the direct
cone-inclusion calculation. Equal integer indices require a generalized component
formula in Lean, since dependent projection arguments cannot be rewritten as
ordinary nondependent expressions. Zero objects, zero maps, empty sites, and
unbounded complexes require no additional cases or hypotheses.

## Earlier second reading (a previous round; superseded)

1. Compared the sole delivered Lean module and existing node against the repository.
   The existing theorem signature is byte-for-byte identical (including the indexed
   component hypothesis); no definition, visibility, or other existing declaration
   changed. Removed one extra space the first worker had added before `:=`.
2. Read the full proof: `hπ.1` supplies product joint monicity, `hπ.2.1` the
   differential formula, and `hπ.2.2` the map formula. Checked the generalized
   component equation `hc`, the four cone differential formulas, the successor
   sign, and the final additive identity. Compiled the final proof with explicit
   `#print axioms` for the theorem and all four helpers: only `propext`,
   `Classical.choice`, `Quot.sound` (the additive helper uses only `propext`).
   No `sorry`, forbidden declaration, or new data construction occurs. The
   existing chosen projection family is used only via its full specification.
3. No split-off statements, new nodes, or holes were added. The private additivity
   and negation lemmas are proved sectionwise; the identity-composition helper
   is a direct rewrite and the additive helper is proved by `abel`. Their claims
   include zero morphisms and the trivial additive group. The component argument
   also covers negative degrees, zero complexes, and empty sites without extra
   assumptions.
4. Independently searched with launcher grep, Loogle and LeanFinder for cone
   preservation and its differential, and searched the library for internal Hom
   additivity. Mathlib's `mapHomologicalComplexObjIso` concerns applying an
   additive functor termwise, whereas the present Hom complex takes products of
   shifted terms; it does not directly prove this comparison. The neighboring
   private additivity helper cannot be imported. The shortest available route is
   the direct product-component calculation already used. Narrowed the public
   MappingCone import to HomotopyCofiber, retaining the abelian/sheafification
   instance imports needed to elaborate the statement, and adding only a plain
   Abel tactic import. The old proof dependency remains used; no dependency node
   was pruned. Checked `sk-thm-picard-duality.json`: its realized statement and
   step arrays have no nodes, so this local calculation bypasses none. Read the
   source Hom differential in [Stacks 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
   and the derived-Hom context in [08J7](https://stacks.math.columbia.edu/tag/08J7)
   online because the cited local source file is absent.
5. The existing node changes only `proof` and `proof_origin`; its unchanged sole
   `proof_deps` entry names exactly the projection specification used. Its three
   proof steps describe the actual product reduction, cone-inclusion expansion,
   and sign/additive calculation. There are no new-node metadata obligations.

Changes made by this reading: restored exact signature whitespace, replaced
broad `simpa [hf, F, proj, π]` in `hm` with identity-only rewrites to avoid
unfolding the chosen Hom functor, and narrowed the cone import with a private
proof-only tactic import. An initial import-narrowing attempt timed out; after
the simplification change the final axiom-check compile passed in 53.3 seconds.
The mathematical proof and DAG route remain the first worker's.

Import visibility change record: `coord/changes/homComplex_mappingCone_differential-imports.md`.
The sole direct importer independently publicly imports MappingCone; all 332
transitive users keep that API, with no forced adaptation or target review.


## Second reading by W3

1. **Interfaces: pass.** Diffed the only delivered Lean module and node against
   this repository. A programmatic comparison confirms that the entire existing
   theorem signature is byte-for-byte identical. No existing definition,
   visibility, hypothesis, or conclusion changed. The public cone import change
   has its existing change record; the only direct importer independently imports
   MappingCone publicly, so its downstream API is preserved.
2. **Proof and axioms: pass.** Read the complete repaired proof and regenerated a
   scratch copy from the current module, with `#print axioms` for the theorem and
   all four private helpers. Launcher compilation passed without warnings in
   36.3 seconds. The theorem, additivity, negation and identity helpers use only
   `propext`, `Classical.choice`, `Quot.sound`; `cone_sum_identity` uses only
   `propext`. No sorry or forbidden declaration occurs. Product joint monicity,
   the differential/map specification, cone inclusion formulas and successor sign
   give precisely the required equation. No new data is chosen; the existing
   projection family is constrained by its full limit and compatibility clauses.
3. **Split statements: pass (none).** The delivery closes
   `CategoryTheory.homComplex_mappingCone_differential` and adds zero holes.
   Checked the repaired additivity helper over site universe `v` and value
   universe `max u v`: its sectionwise extensional proof works for arbitrary
   precomposition, zero morphisms and zero modules and specializes to `u = v`.
   The remaining helpers are elementary proved identities, not renamed holes.
   Integer degrees, including negative degrees, and empty sites impose no extra
   assumptions. The neighboring small-universe additivity lemma is private in a
   module importing this item, so importing it would introduce a cycle.
4. **Route and pruning: pass.** Independently searched Mathlib via launcher grep
   for `homObjMap.*(add|neg)|mapHomologicalComplexObjIso`, Loogle for
   `"homotopyCofiber", "d"`, and local library searches for the internal Hom
   helpers and the item's importers. Read `mapHomologicalComplexObjIso`: it
   applies an additive functor termwise, whereas this Hom complex uses products
   over shifted degrees, so it does not replace the present argument. The
   direct product-component proof is appropriate. The retained statement and
   instance imports support the signature; Abel is a plain proof-only import.
   The sole old proof dependency `lem-sc-hom-complex-projections` remains used;
   there are no removed dependency nodes to add to `No longer needed`.
   Checked the unit's `realized` record: its statement and step arrays are empty,
   and no realized unit route is bypassed.
5. **DAG: pass.** JSON comparison shows that only `proof` and `proof_origin`
   changed. The three steps match the actual component reduction, cone
   expansion, and additive/sign calculation, including the repaired helper's
   universes. `proof_deps` is unchanged and equals the union of step uses.
   There are no new nodes or split-off metadata obligations.

Changes made in this reading: refreshed the stale report wording and recorded
this independent review of the repaired helper. No Lean or DAG repair was needed.
