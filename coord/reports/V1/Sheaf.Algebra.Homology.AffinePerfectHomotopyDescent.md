## What changed

Replaced the one sorry in `CochainComplex.affine_perfect_homotopy_descent` with a
complete Lean reduction of the existing two-step finite-data argument. Its signature
and visibility are unchanged. Added two modules, each containing one public theorem:
`Sheaf.Algebra.Homology.AffinePerfectGradedHomDescent` and
`Sheaf.Algebra.Homology.AffinePerfectChainMapEqualityDetection`.
Both new interfaces require a bounded source with finitely presented terms and
finitely presented target terms; they do not require projectivity or target boundedness.
The original theorem derives these hypotheses from its finite-projective assumptions.

The proof calculates the boundary of the given homotopy as the extension of `f - g`,
descends only its degree-minus-one graded components, proves that scalar extension
commutes with the boundary operation, and detects equality with `f - g` at a common
later stage. It constructs the final homotopy from Mathlib's `nullHomotopy'`, maps it
through scalar extension and the canonical comparison morphisms, and uses
`Homotopy.equivSubZero`. The preservation of subtraction, zero and homotopies is
proved locally. In particular no coherence or differential identity was put into
the graded-component descent hole.

Added proof-only imports for the two new modules and
`Mathlib.CategoryTheory.Adjunction.Additive`. The additivity instance is proved from
`ModuleCat.extendRestrictScalarsAdj`; no new axiom, public definition, or changed
existing interface is involved. Updated the original node's proof, proof dependencies,
and proof origin to match this route. The second reader removed an unused
public ModuleCat.Abelian import. No forced adaptations.

Sources read: Stacks Tag 09RE, affine proof of (1), and Tag 05N7, clauses (2) and (3),
from their official pages https://stacks.math.columbia.edu/tag/09RE and
https://stacks.math.columbia.edu/tag/05N7. Read the finite-presentation dependency's
statement, node and proof sketch, the scalar-extension definition and Mathlib's
homotopy constructors and boundary compatibility lemmas. The unit
`sk-thm-picard-semicon` has no realized nodes that this reduction bypasses; its route
has not changed.

## Proved and sorry left

Closed the original hole in `CochainComplex.affine_perfect_homotopy_descent`
(node `lem-pc-affine-perfect-homotopy-descent`). There are no sorries in the item's
module, including its private helpers.

Added exactly two named holes, each in a separate new module, with a complete proof
in words and a node:

- `CochainComplex.affine_perfect_gradedHom_descent`
  (`lem-pc-affine-perfect-graded-hom-descent`): descend graded components with their
  canonical scalar-extension equalities. This statement has neither prescribed
  endpoint chain maps nor a homotopy equation.
- `CochainComplex.affine_perfect_chainMap_equality_detection`
  (`lem-pc-affine-perfect-chain-map-equality-detection`): detect equality of chain
  maps given at two stages. This statement constructs no homotopy or graded data.

This is a decomposition, not a sorry-free proof: one upper hole closed, two lower
holes added, net -1 holes before other groups' changes. Both still use the existing
`ModuleCat.finitePresentation_descent_directedColimit`, which was already sorry;
that existing hole is untouched. The main theorem still depends on sorry through
the two new statements. Every remaining proof is exactly `:= by sorry`.

Compilation through `lcompile.py --all` checks the three modules in import order.
The main proof and both interfaces compile with no warnings. No Lake or library
build was run. The required `deliver3.py --no-push` is the final delivery check.

## No longer needed

Removed the item's direct proof-only import of `Sheaf.Algebra.FinitePresentationColimit`.
Its node `lem-pc-fp-module-map-descent-affine` and the elementwise filtered-ring
colimit node `lem-pc-filtered-colimit-commrings-elementwise` are no longer direct
proof dependencies of this item; they remain needed below both new nodes. Thus
this delivery claims no globally pruned existing module or node.

No extra chain-map descent, graded object descent, differential descent, derived-Hom
comparison, posetal-reflection interface, or source-library theorem is imported.
The graded-component module imports only its statement prerequisites and the
existing finite-presentation dependency; in particular it does not import
`ScalarExtensionHom` or the Homotopy module, since its signature uses only the
explicit canonical comparison morphisms. The equality-detection module likewise
needs no Homotopy import. The second reader also removed the unused public import
`Mathlib.Algebra.Category.ModuleCat.Abelian`; ModuleCat preadditivity and the
scalar-extension constructions already come from ScalarExtensionHom. The item
compiles cleanly without this import. Its sole direct caller imports ModuleCat.Abelian
itself, so it does not rely on this transitive import.

## Where the brief, the DAG or earlier work was wrong

The existing finite-presentation theorem assumes a partial order, whereas this
item assumes only a preorder. Its maps clause is also componentwise and its
equality clause compares maps at one stage, not two. These are genuine glue steps,
now explicitly recorded in the two new nodes: pass through the equivalent posetal
reflection (or use the matrix proof with directedness alone), choose common upper
stages, and use canonical scalar-extension associativity.

The original route was mathematically sound. No statement is disputed or weakened.
The target-module signatures are untouched, and no definition with unproved data
was introduced. Edge cases checked in words: an empty source support interval
(all components are zero); nonantisymmetric indexing preorders (equivalent indices
give inverse ring isomorphisms); distinct or mutually comparable stages; and
noninjective transition ring maps (eventual, rather than present-stage, equality
is exactly what is needed). Target boundedness is unnecessary for the two steps;
only finitely many target terms are involved.

The repository copy does not contain its listed Stacks TeX files; the official
pages were read instead. Also `tools/blueprint_refs.py ancestor` returns None for
this item because an earlier `created.item` is a module name rather than a node id.
The new nodes retain the explicit, existing blueprint ancestry of the original
node, `lem-pc-rf-perfect-base-change`, via the homotopy-descent and affine-Hom nodes;
no unrelated blueprint route was substituted. Searches of blueprint statements
for homotopy, graded maps, chain-map equality and finite presentation found no
existing blueprint statement giving either new interface. LeanFinder and Mathlib
source searches were run and recorded; LeanSearch returned Internal Server Error,
which is recorded as unavailable, not as evidence of absence.

## New nodes

`lem-pc-affine-perfect-graded-hom-descent`, module
`Sheaf.Algebra.Homology.AffinePerfectGradedHomDescent`, makes original proof step 1
precise. It descends a family of degree-minus-one component maps, with the precise
comparison on each component. Its node gives the finite interval, the map-descent
applications, common-stage transport, zero extension and preorder treatment.

`lem-pc-affine-perfect-chain-map-equality-detection`, module
`Sheaf.Algebra.Homology.AffinePerfectChainMapEqualityDetection`, makes original
proof step 2's equality-detection portion precise. It compares chain maps at
possibly distinct stages, reduces to the finitely many source components and
returns equality at a common upper stage. The final homotopy construction remains
proved in the original module, not transferred to this node.

Change record: `coord/changes/AffinePerfectHomotopyDescent-imports.md`
records removal of the unused public Mathlib import and its effect on the sole
direct caller. No existing signature or public definition changed.

## Second reading by V1

1. Compared the complete item module against the repository with `diff`, then
   compared the substring from the existing theorem name through its final type
   before `:= by`: the signature is byte-for-byte identical. The existing
   docstring is unchanged. Removed one unused public Mathlib import deliberately
   and recorded it under No longer needed. The only new declarations in that
   module are private proof helpers; its homotopy helper is a construction from
   the supplied homotopy using `mapHomotopy`, `compLeft`, and `compRight`, not an
   arbitrary witness chosen from an unproved existence result. No change record
   for a signature or definition is needed; the public-import removal has the
   change record listed above. No forced adaptation is needed. Verdict: no
   accidental interface change.
2. Compiled all three modules in import order through `lcompile.py --all`:
   clean, with no warnings. Read the boundary calculation, including the up-shape
   indices n-1 and n+1, the use of `h.comm`, and the subtraction orientation.
   The transported boundary is proved by Mathlib's map/precomposition/
   postcomposition identities; the detected equality is then used with the
   explicitly constructed `nullHomotopy'` and `equivSubZero.symm`.
   A scratch copy with `#print axioms` for all three public theorems reports
   precisely propext, Classical.choice, Quot.sound, and sorryAx. The only two
   delivered sorries are the two named split theorems listed above. No forbidden
   declaration or hollow definition occurs. Verdict: valid reduction, dependent
   on two documented holes, not a complete proof.
3. Read both new modules and both entire new nodes, and the actual statement of
   `ModuleCat.finitePresentation_descent_directedColimit`. Also read official
   Stacks Tags 09RE (affine proof of (1)) and 05N7 (2),(3). Graded descent uses
   exactly one map E^m -> K^(m-1) per supported source degree; the Rel argument
   introduces no extra data because it is a proposition. Equality detection
   first transports the two maps to a common stage, uses the equality clause
   on each supported source degree, then takes a finite common upper bound.
   Tensor generators identify the map-descent comparisons with the displayed
   L and R: `extendScalarsComp_hom_app_one_tmul`, read at lines 1006-1009 of
   ChangeOfRings. Its associativity lemmas at lines 1014-1042 justify the
   subsequent transports. Finite presentation survives these base changes
   by `instFinitePresentationTensorProduct`. The i₀ parameter makes the index
   nonempty; antisymmetrization handles a genuinely nonantisymmetric preorder.
   Tested the zero source, reversed/empty bounds, one supported source degree,
   distinct starting stages, and noninjective ring maps: zero sources give
   automatic equalities, and no present-stage injectivity is assumed.
   Both statements are true and are strictly separate portions of the argument:
   the first has no differential equation, and the second constructs no graded
   family or homotopy. Neither merely renames the item. Searches with different
   wording through msearch LeanFinder, Loogle, and grep, and rg of repository
   Sheaf/WeilConjectures and the upstream algebra/geometry sources, found no
   exact existing theorem. The existing finite-projective graded-model theorem
   descends objects, not maps between fixed base changes, and cannot replace
   either interface. The Loogle base-change-Hom candidate assumes flatness,
   which the arbitrary transition maps here do not have. Closing either split
   requires substantial finite-data/coherence formalization, not a short
   application of an existing result. Verdict: retain both split statements.
4. Followed the proof downward: finite projectivity supplies finite presentation;
   graded data descend before differential identities are enforced; boundary
   functoriality and the final homotopy construction remain proved in the item.
   The new imports are private proof imports, while each new module publicly
   imports its statement prerequisites. The removed direct finite-presentation
   import is still used below the split nodes. Compared the old proof_deps:
   both old nodes are explicitly named under No longer needed, with no claim
   that their modules are globally pruned. Read
   dag/units/sk-thm-picard-semicon.json: realized.statement is empty and its sole
   realized step is empty; this reduction does not bypass a realized unit node.
   Verdict: the finite-data route is kept and no shorter applicable route found.
5. Compared the existing node JSON: only proof, proof_deps, and proof_origin
   changed. Its four steps agree with the Lean, and their uses have union exactly
   the two new proof dependencies. For each new node, the recorded Lean signature
   equals the module text byte-for-byte; source, statement dependencies, proof
   steps, search records, created metadata, blueprint ancestry, chapter, unit,
   and Lean record are present. Their proof_deps name the existing map/equality
   descent and elementwise criterion, including the preorder glue explicitly.
   Verdict: the nodes describe the actual reduction and remaining work.

Removed the unused public Mathlib.Algebra.Category.ModuleCat.Abelian import from
the item and verified the item compiles without it; the direct caller imports
that module explicitly. Removed redundant blank lines in the two new module
import blocks and added this independent review. The original proof and both
split statements were retained.
Scratch axiom checks are outside the delivery's lean directory. Hole accounting
remains one original hole closed, two holes added: a decomposition with net -1.
