## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.exists_localImmersionLocus` without
changing its signature or existing docstring. Added the proof-only imports
`Mathlib.AlgebraicGeometry.Gluing` and
`Sheaf.AlgebraicGeometry.CompatibleImmersionGluing`.

The proof derives compatibility directly from the local representing criteria,
uses Cartesian descent charts, proves the global immersion property by target
locality, derives the local factorization criterion from the pullback universal
property, and proves both directions of the global criterion. A proved private
helper glues local factors through a monomorphism using `Scheme.Cover.glueMorphisms`
and verifies their composite using `Scheme.Cover.hom_ext`.

Updated the assigned node's proof, proof dependencies and proof origin to match
this route. No existing definition, statement or visibility changed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.exists_localImmersionLocus`
(node `lem-sc-local-immersion-locus`). Its module has no sorry left. The private
`exists_factor_of_locally_factors` helper is completely proved.

Added one hole: `AlgebraicGeometry.Scheme.exists_gluedCompatibleImmersionCharts`
(node `lem-sc-compatible-immersion-gluing`), in its own module. Its proof is exactly
`by sorry`. It asserts only geometric descent with Cartesian charts: it has no
predicate, base-change-stability hypothesis, source-locality hypothesis, global
immersion conclusion, or global factorization criterion. Those latter conclusions
are derived by the assigned module's actual Lean proof, so this is a decomposition
(1 upper hole closed, 1 lower hole added; net 0), not a sorry-free geometric proof.

Both modules compiled together with lcompile.py without errors or warnings.
The empty-S case of the new lemma uses the empty scheme and a vacuous chart
condition. Empty local representatives are allowed. For empty T the final proof
uses a vacuous pointwise cover, including the empty family in the gluing helper.
For coincident or nested U_i, compatibility gives unique comparison maps by
monomorphy, so duplicate charts and triple overlaps pose no extra hypothesis.

## No longer needed

No import was removed: the original module had only its statement import.
No module or node was pruned from the transitive proof route. The assigned node
no longer directly cites `lem-weil-pbc-glue-schemes`, but that dependency remains
needed by the new geometric descent node. The morphism-gluing Mathlib leaf
`lem-weil-pbc-scheme-morphism-gluing` is now explicitly cited because the Lean
proof uses its recorded `Scheme.Cover.glueMorphisms` and uniqueness declarations.

## Where the brief, the DAG or earlier work was wrong

The original module did not import its DAG proof dependency, which is a Mathlib
leaf for explicit scheme gluing data rather than a theorem constructing the
compatible charts from the given predicate. This was the missing geometric
interface, not an unavailable declaration. Mathlib's RelativeGluingData requires
an equifibered diagram over a locally directed cover; LocalRepresentability
requires a sheaf and relatively representable open charts. Neither directly
accepts the present factorization-compatibility hypothesis. These APIs were read
before separating out the chart construction.

No mathematical error or target-statement change was found. The unit route stays
unchanged. The ancestry helper reports None for this recently created item
because its created.item is a module name; the new node preserves the existing
node's explicit blueprint ancestry, adding the assigned node to via.

## New nodes

`lem-sc-compatible-immersion-gluing`, module
`Sheaf.AlgebraicGeometry.CompatibleImmersionGluing`, isolates the Cartesian-chart
construction of the omitted patch-gluing argument in Stacks Tag 0BDL, using Tags
01JB and 01JC. The docstring and node spell out inverse-image overlaps, unique
comparison isomorphisms, the cocycle, scheme and morphism gluing, and the equality
of each chart image with the inverse image of its base open. LeanSearch was
unavailable; LeanFinder, source searches of Mathlib and both library roots, and
a search of the whole blueprint found the relevant general gluing APIs but no
duplicate statement. There are no change records or forced adaptations.


## Second reading by K1

1. PASS. Compared the complete diff with the repository module and mechanically
   checked that the existing theorem signature is byte for byte unchanged.
   The original docstring and public visibility are unchanged. The only Lean
   additions are the proved private helper, proof-only imports, the target proof,
   and the separately reported geometric theorem. No change record is required.
2. PASS. Compiled both modules in import order with lcompile.py. A scratch copy
   printed axioms for all three declarations: the private helper uses only
   propext, Classical.choice and Quot.sound; both public theorems additionally
   use sorryAx, accounted for by the single reported geometric hole. No forbidden
   declaration or hollow definition occurs; in fact the delivery adds no definition.
3. PASS. Read the Cartesian-chart lemma from its hypotheses through its complete
   overlap construction. Compatibility applied to an overlap restriction gives
   unique comparison maps; cancellation of the composite immersion proves inverse
   and cocycle equations. Open-chart gluing then identifies each chart with the
   inverse image of its base open. Checked empty base, empty representatives,
   coincident neighbourhoods and nested neighbourhoods. No predicate conclusion
   or global immersion conclusion is assumed. This is a genuine geometric
   subargument, not a renamed copy of the original theorem. Independently searched
   Loogle for relative gluing, LeanFinder for identical subfunctors on base opens,
   and Mathlib and both library roots for descent/gluing and Cartesian-chart APIs.
   Read Mathlib RelativeGluingData and Scheme.GlueData and the library effective
   model chart interfaces: they require additional diagram or descent data and
   do not directly prove this lemma. The hole cannot be closed by a short API
   application. Verified Stacks Tags 0BDL, 01JB and 01JC against the cited argument.
4. PASS. The main proof derives compatibility, target locality and both predicate
   directions rather than assuming them in the new hole. The private helper glues
   factors by monomorphy and verifies the resulting composite by cover hom_ext.
   All imports supply statements or used proof APIs; the added imports are plain
   imports. The sole old proof dependency, lem-weil-pbc-glue-schemes, is retained
   transitively by the descent node, and its removal from the direct dependency
   list is explicitly reported above. No module is pruned. The assigned node is
   below the unit level; the existing unit realized record and its route are
   unchanged. The delivery closes one upper hole and adds one strictly geometric
   hole: decomposition, net zero, with no claim of a sorry-free proof.
5. PASS. Compared both node records with their Lean declarations and arguments.
   The changed existing fields are proof, proof_deps and proof_origin only. The
   new node has its source, detailed proof, dependency union, search records,
   creation record, ancestry, chapter/unit and verbatim Lean statement. The
   original statement and ancestry remain unchanged.

Second reading changed only this report, adding the independent review and its
axiom/search evidence; no repair to the Lean proofs or node records was needed.
