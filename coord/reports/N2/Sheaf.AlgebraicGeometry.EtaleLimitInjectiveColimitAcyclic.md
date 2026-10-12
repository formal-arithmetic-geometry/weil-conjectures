## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.EtaleLimitInjectiveColimitAcyclic`
by a complete Lean proof from the finite scheme Čech-complex comparison. The signature
and public imports are unchanged. The second reader removed the redundant proof-only
`Mathlib.Algebra.Category.Grp.AB` import, already public through the source-library
`CohomologyColimit` import. The proof constructs the qcqs basis and its finite
covering predicate, proves refinement cofinality and nerve closure using the existing
proved source library, obtains stage Čech complexes, applies stage injectivity, and
passes their vanishing through exact filtered colimits. It then applies the existing
étale Čech criterion and transports terminal evaluation to global Ext cohomology.
Two proved local helper proofs establish homology preservation by filtered complex colimits;
their proof pattern is the existing coefficient-size proof in EtaleInjectiveColimitAcyclic,
with explicit AB5 universe shrinking for the smaller tail index.

Added `Sheaf.AlgebraicGeometry.EtaleLimitFiniteCechComplexColimit`, containing only the
remaining finite-complex comparison. It applies to arbitrary compatible coefficients,
without injectivity and without a cohomology-vanishing conclusion. Its diagram and
cocone exist only within a theorem proof; no definition chooses data from it.
Updated the parent node's proof route and added the matching comparison node.

Both delivery modules compile with no warnings through lcompile.py. No existing
statement, definition or visibility changed; no forced adaptations are needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etale_limit_injective_colimit_acyclic`
(node `lem-weil-pbc-etale-limit-injective-colimit-acyclic`). The item now has zero
local sorries; both private homology-colimit helpers are completely proved.

Added and left: `AlgebraicGeometry.Etale.etale_limit_finite_cech_complex_colimit`
(node `lem-weil-pbc-etale-limit-finite-cech-complex-colimit`), exactly `:= by sorry`
in its own new module. This is a decomposition: one upper hole closed, one strictly
lower complex-comparison hole added, net zero local holes. Existing imported holes
are not claimed as proved. The remaining lemma states no injective acyclicity;
all use of injectivity, homology exactness, the Čech criterion, and global-cohomology
identifications is real Lean in the item.

Edge cases checked before stating the comparison: empty covering (necessarily empty
U, hence zero complexes), empty scheme, zero coefficient system, singleton index,
finite index types lifted to the coefficient universe, and the nonempty directed tail.
No order antisymmetry is used. Every positive degree is handled by the homology proof;
the comparison itself includes degree zero and makes no higher-continuity assumption.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`
- `Sheaf.CategoryTheory.SiteInjectiveCechAcyclic`
- `Sheaf.CategoryTheory.SiteCechVanishingCriterion`
- `Sheaf.CategoryTheory.ColimitSiteSections`
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`
- `Mathlib.CategoryTheory.Sites.SheafOfTypes`
- `Mathlib.Algebra.Category.Grp.AB` (second reading; already publicly imported by
  `WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit`)

The affine-site presentation, affine restriction, section comparison and finite-product
commutation move below the new complex-comparison item; they are not claimed globally
pruned. Generic site injective Čech acyclicity remains beneath the imported étale
specialization. The generic SiteCechVanishingCriterion is replaced by the already-proved
étale criterion, so `lem-weil-pbc-site-cech-vanishing-criterion` is no longer needed on
this branch. The separate `lem-weil-pbc-etale-qcqs-cofinal-finite-coverings` is replaced
by the already-proved, more directly usable source-library finite-sieve refinement and
finite-nerve closure. The auxiliary existence theorem `lem-weil-pbc-limit-affine-transition`
is not used by the parent: the limit is already supplied, and Mathlib proves affine
projections and compactness of that exact cone. Its module is still imported beneath
the existing affine-site presentation. `lem-weil-pbc-pretopology-sheaf-condition` is
not directly used by the parent; all sheaf and topology interfaces are existing ones.
No whole-target-closure pruning count is claimed.

For completeness, these are all old parent `proof_deps` removed as direct edges:

- `lem-weil-pbc-affine-etale-site-colimit`
- `lem-weil-pbc-affine-etale-site-topos`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`
- `lem-weil-pbc-site-injective-cech-acyclic`
- `lem-weil-pbc-site-cech-vanishing-criterion`
- `lem-weil-pbc-colimit-of-sites-sections`
- `lem-weil-pbc-filtered-colimits-commute-finite-limits`
- `lem-weil-pbc-pretopology-sheaf-condition`

`lem-weil-pbc-filtered-colimit-abelian-groups-exact` remains a direct dependency.
The first three, section continuity and finite-limit commutation remain below the
comparison, and generic injective Čech acyclicity remains below its étale specialization.
These are removed direct edges/imports, not a claim that all nine modules disappear
from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies give an abstract strict site system rather than the required
small étale scheme Čech complexes with these upperStar and eG identifications. The
missing glue is isolated as the complex comparison, instead of assuming pulled-back
stage injectives remain injective (which need not hold), or invoking higher-degree
continuity circularly. The original global vanishing statement is unchanged.

The proof follows Stacks sites-cohomology.tex, lemma-colimit (09YP), especially the
complex-colimit display, and the qcqs scheme realization in 09YQ. The new comparison's
remaining task is descent and degree-zero continuity as in 09YN, including compatibility
with face maps. The unit sk-thm-p1 route and all its realized nodes are unchanged.
Blueprint searches for Cech colimit and complexes, plus repository searches, found the
abstract ColimitSiteCechComplex theorem; it is a prerequisite of the scheme comparison,
not a duplicate of the new statement. The fixed-scheme EtaleInjectiveColimitAcyclic result
requires injectives on the limit scheme and therefore does not directly apply here.

## New nodes

`lem-weil-pbc-etale-limit-finite-cech-complex-colimit` states the finite scheme Čech-complex
comparison for arbitrary compatible coefficients over the directed tail. It is the
complex-comparison substep of the parent, with no injectivity or vanishing assumption
or conclusion. Its docstring and node describe descent, cover surjectivity, fibre-product
identifications, canonical section units, naturality, and the finite-product colimit
argument. The statement has been compiled and checked on the edge cases listed above.
No change record is needed because no existing interface changes.

## Earlier second reading (a previous round; superseded)

1. **Interfaces: pass.** Diffed the existing module against the repository. The
   full `etale_limit_injective_colimit_acyclic` signature is byte-identical, including
   the nonempty directed preorder, prescribed limit cone, qcqs stages, affine maps,
   coefficient identity/composition equations, the prescribed `G` arrows, arbitrary
   colimit cocone, stage injectivity and every degree `n + 1`. Its docstring and
   public imports are unchanged. The other delivered module is new. No definitions
   or existing visible declarations changed; no change record is needed.
2. **Proof/kernel checks: pass with the declared remaining holes.** Compiled both
   modules in import order using `lcompile.py --all`, with no errors or warnings.
   Scanned both complete sources: no forbidden axiom/unsafe/opaque/FFI declarations,
   no holed definitions, zero sorries in the parent, and exactly one `:= by sorry`
   in the named comparison theorem. Scratch copies with `#print axioms` show only
   `propext`, `Classical.choice`, `Quot.sound` for each private homology helper;
   the parent and the comparison additionally use expected `sorryAx`. Read the
   AB5 universe shrinking, componentwise short-complex cocone and its naturality,
   evaluation at the three homology terms, tail directedness, transport through
   `eA`/`eK`, and terminal evaluation/right-derived/Ext isomorphisms. All concern
   the actual complexes and sheaf of the unchanged statement. The existential
   comparison data is eliminated inside a proof of a proposition and defines no
   library data; the chosen element of `I` comes from the proved nonempty instance.
3. **Split comparison: pass as a decomposition.** Read the complex-colimit display
   in [09YP](https://stacks.math.columbia.edu/tag/09YP), the compatible coefficient
   section comparison in [09YN](https://stacks.math.columbia.edu/tag/09YN), and the
   affine-site reduction in [09YQ](https://stacks.math.columbia.edu/tag/09YQ).
   The new lemma isolates descent of a finite covering and its complex comparison
   for arbitrary coefficients; it assumes no injectivity and asserts no positive
   vanishing. Its proof docstring supplies finite-presentation descent, eventual
   surjectivity, base change of the finite family, canonical section maps commuting
   with faces, and finite products in each degree. One stage suffices for the finite
   covering data and therefore all its iterated fibre products; no common bound
   for infinitely many degrees is required. Checked empty `K` (the covered `U` is
   empty and all degree products are zero groups), empty limit, zero coefficients,
   singleton `I`, finite `K` in the larger universe, and a preorder without
   antisymmetry. The tail contains its base point and has explicit common upper
   bounds. Independent searches used LeanFinder for “Cech complex comparison for
   abelian sheaves under affine inverse limits of qcqs schemes”, Loogle for
   `cechComplexFunctor` (not indexed there), and grep for complex/colimit, together
   with repository/upstream `rg` for Čech-colimit and homology preservation. Read
   `ColimitSiteCechComplex` and `EtaleInjectiveColimitAcyclic`: the former requires
   strict abstract-site/coefficient transport absent from the scheme input; the
   latter requires injectivity on the fixed limit scheme. Neither closes the new
   comparison. No few-minute proof of this remaining transport was found.
4. **Route/pruning: pass after report completion.** Read the imports' actual
   declarations, including the finite affine refinement and qcqs nerve closure in
   source `CohomologyColimit`, the étale Čech criterion and injective specialization,
   and the Ext/derived comparison. The parent applies those declarations directly,
   constructs its covering predicate and refinement factors, then proves exact
   filtered homology transfer. It never assumes inverse images preserve
   injectivity, and never invokes positive-degree continuity. The complete list
   of removed old dependency edges is now recorded above. Removed one duplicate
   proof import (`Mathlib.Algebra.Category.Grp.AB`), then recompiled successfully.
   Read `dag/units/sk-thm-p1.json`, including every `realized` entry: the item is
   below the unit's steps and the reduction keeps their route and nodes intact.
5. **DAG/Lean agreement: pass after repair.** Both node `lean.statement` records
   match the source signatures exactly. The existing node changes only `proof`,
   `proof_deps`, `proof_origin`; its steps track the actual finite-cover criterion,
   comparison, stage injectivity, exact-colimit and Ext proof. Changed its first
   step from elementary to non-elementary and cited existing affine-projection,
   qcqs-permanence, affine-qcqs and étale-site nodes: finite refinement and nerve
   closure are proved library inputs, not elementary assertions. All dependency
   node IDs exist. The new node has its matching theorem/module, complete source
   and proof plan, proof-dependency union, searches, split status, creation,
   blueprint ancestry, chapter and unit. Added its blueprint marker to the new
   module docstring. No unit or chapter record is changed.

Second reading changed: one redundant proof import removed, parent DAG first-step
classification/dependencies corrected, complete removed-edge list added to the report,
and new module-docstring blueprint marker added. No proof body or signature needed
repair. One original hole closed and one strictly lower hole added remains a
**decomposition**, not a net reduction of holes or an axiom-free proof of the target.


Repair applied for the returned import-prune error: the existing module `Sheaf.AlgebraicGeometry.FiniteEtaleCechFilteredColimit` already contains word-for-word top-level declarations for the two homology-preservation helper statements. The repaired target no longer declares either duplicate; it proves the same helper facts as local `have` terms within the target proof, preserving the target signature and complete proof while avoiding duplicate library declarations.

## Second reading by N2

1. **Interfaces: pass.** Compared both delivered modules with the repository version. The
   existing target theorem signature is byte-identical and its public imports and docstring
   statement are unchanged. The additional module is new and its theorem is recorded by a
   matching split node. No existing definition or visible declaration was changed.

2. **Proof and kernel checks: pass.** Compiled both modules in import order with lcompile.py;
   there are no errors or warnings. The target contains no sorry, and the comparison module
   contains exactly the named split theorem's `:= by sorry`. There are no forbidden declarations
   or holed definitions. The completed target proof uses only the permitted ordinary axioms,
   while the split theorem necessarily contributes `sorryAx` until its node is proved.

3. **Statements and decomposition: pass.** The split comparison is strictly simpler than the
   target: it asserts only finite Cech-complex continuity for arbitrary coefficients, with no
   injectivity, homology vanishing, or cohomology conclusion. Its docstring gives the descent,
   nerve, face-map, and finite-product argument and records the edge cases. Repository and
   Mathlib searches found no existing declaration that supplies this scheme comparison.

4. **Route and pruning: pass.** The target follows the unit route through finite qcqs covers,
   the comparison, stage injective Cech acyclicity, filtered-colimit homology, the etale
   vanishing criterion, and the derived Ext identification. The report records all removed
   direct dependencies and the redundant AB import; the new comparison module retains the
   lower-level imports it actually needs.

5. **DAG agreement: pass.** Both node Lean records match the theorem signatures verbatim. The
   target node's proof steps and dependency union describe the implemented route, and the new
   split node contains its source, proof plan, searches, creation data, blueprint, chapter, and
   unit. The unit's realized route is unchanged.

Changed during this second reading: added this complete review section to satisfy the stage-3
report contract. No Lean proof, theorem signature, node statement, or import was changed.
