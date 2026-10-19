## Files written

- `dag/nodes/sec-six-functors/lem-coef-slice-cone-prism-simplicial.json`: item, statement; split into nine elementary calculations. Statement unchanged. No Mathlib match.
- No new DAG nodes; zero new Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every step citation.
- `searches.jsonl`: actual searches made in this sandbox; retained in full.
- `check_ordinals.py`: auxiliary finite-case audit, not a Lean file and not part of the delivery commit.

## Attachments

None. Read-only searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id, cone/prism combinations, relative joins and slice/cone notions found no declaration stating the item. There is no attachment claim based on upstream master or on Mathlib.

## WANTED

WANTED: archival copy of Kerodon Proposition 7.3.5.5, https://kerodon.net/tag/0302, final construction of gamma-minus, for lem-coef-slice-cone-prism-simplicial. Read online. The proof is marked agent-written: the source asserts functoriality and cone extension, while this split supplies their explicit verification. Online attempts to open Construction 5.2.3.1 (0242) timed out; the relative-join construction used here was read directly from the existing definition node, whose full degreewise statement suffices for all the calculations.

## What was wrong or missing

The item was an unsplit statement, not an existing proof. Its simplicial compatibility assertion needed the cut-dependent formulas checked even when an operator erases an entire join block. Steps 4–6 now do this for an arbitrary monotone map, proving more than just individual face equations. The item already has the correctly typed composite tau rho. The online source writes the compositions in the other order in the sentence following its ordinal formulas; no change to the item's statement was necessary.

The current inherited ancestor is paragraph 2 of prop-coef-integral-exceptional-adjoint (derived coefficient adjunction), through the finite-grid/enhancement ancestry. I read its master blueprint text and the chapter/unit records. This node supplies the interpolation argument already requested in step 9 of lem-coef-infinity-arrow-join-geometry. It changes no unit route and uses no forbidden SGA reference. The ancestor statement itself is not cited as a black-box theorem.

## Searches and reuse

The sandbox initially contained only brief markers: no item copy, report, searches or completed delivery to reuse. No matching delivery process was running. I retained all six inherited searches in the repository item and added the actual searches run now with msearch.py: LeanFinder with two phrasings; Loogle `SSet, "prism"` and `SSet, "slice"`; focused AlgebraicTopology grep `slice.*cone|cone.*slice|relativeJoin|relative_join|prism`; and LeanSearch for extension of the slice homotopy over its right cone. All services responded. Loogle and focused grep returned no hits. I read the hits: ordinary Cones.extendId (Cones.lean:361), homMk_id, coskeletal rightExtensionInclusion (Coskeletal.lean:49), StrictSegal lift (SimplicialSet/Coskeletal.lean:67), interval inclusions (Monoidal.lean:174,195), and the relative Homotopy structure (RelativeMorphism.lean:87) do not construct this map. The second LeanFinder response mainly gives degeneracy naturality and pointed Kan multiplication faces. Those assume a pre-existing simplicial map or a different Kan-complex construction, and do not establish this item's formulas.

Whole-DAG searches for `0302`, slice-cone and interpolation prism were read, including the parent arrow-join geometry statement and proof. Blueprint searches for prism (zero) and slice (nine unrelated scheme/coefficient statements) found no equivalent blueprint item. The ancestry command confirms prop-coef-integral-exceptional-adjoint. No new node is needed: these are literal finite-ordinal case calculations from the existing definitions, rather than further general lemmas. The existing enhanced-diagram, relative-cone and relative-join definition nodes were all opened and their statements read.

## Not duplicates

No new nodes.

## Review by Q26

I read Kerodon 0302 through its final gamma-minus construction, including its rho and rho-prime formulas and square at a base arrow. The source describes a quasicategory and a full source subcategory; the specific ordinal calculations used here have neither horn fillers nor fullness in their hypotheses. The item's arbitrary simplicial-set generality is justified directly by the displayed formulas, rather than by dropping hypotheses from a theorem application. The definition statements read were def-cbc-enhanced-diagrams-cones (degreewise products, precomposition and the internal functor object), def-coef-infinity-relative-cone (join summands and inverse-image block operators), and def-coef-infinity-relative-join (the pullback equation, inclusions and induced-map coordinates). No new node needs a separate source or statement review.

Step 1 uses the standard-simplex/precomposition convention and the join definition to check the slice operators and the unique cut. Its extension of a composite really preserves the appended last vertex. Step 2 uses the internal functor definition; the order check treats both branches of rho, and explains the actual map on every q-simplex, so equality on vertices of an arbitrary target is never assumed. Step 3 uses precisely the relative-join pullback equation: target evaluation agrees on the initial block and the final block is constant because tau ends at c. It checks the pure factors as well. These cited statements do say each of these things; no universal cone property is invoked.

Step 4 uses the join inverse-image operator to identify the new cut, then proves two equalities of ordinal maps, with all cases listed. Step 5 applies precomposition and the relative-join operator to those actual maps to get equality in every coordinate. Step 6 treats the missing-base case separately, where nu alpha is constant at the appended vertex; this verifies the claim even though there is no new base simplex to compare. It also handles the originally pure final simplex. Neither step silently carries a cut through an operator which removes it. These are elementary substitutions, not an appeal to an uncited simplicial homotopy theorem.

Step 7 uses the relative-join induced-map formula, not merely its pullback existence: postcomposing the three coordinates gives strict naturality for any pointed simplicial map. Step 8 uses the functor-simplex and pure-inclusion definitions to compute the full square as e composed with a monotone Boolean conjunction map. The degeneration of e has ordinal values (0,0,1), so this is the claimed square from identity to e, with identity source side and e as target side. This is an equality of simplicial maps, not an assertion that a square in X is determined by its four vertices. Step 9 uses the pure final inclusion to show the entire apex interval is constant, including its degenerate higher simplices.

I checked all hypotheses at their points of use: smallness is preserved by these degreewise constructions in the fixed universe; only monotonicity of epsilon and alpha is needed for the index formulas; tau's last vertex is c for the pullback equation and the disappearing-base case; h(c)=c' for naturality. The edge cases are n=0; r=-1,0,n; both constant epsilon values; alpha missing either entire block; and repeated alpha values. The auxiliary Python audit exhaustively checked 68,643 restriction cases for n,l at most 5, all cuts, all monotone interval parameters and all monotone alpha, including rho/nu monotonicity and both restriction identities. It passed. The written proof gives the dimension-independent argument; this enumeration is an additional small-case check only.

I checked delivery-errors B–E against the actual files: no new-node statements or Mathlib-leaf claims, no hidden non-elementary theorem or replacement clause node, no dependence on the parent's proof as a cited statement, no cycle introduced, no change of coefficient category or unit route. The additional relative-cone proof citation supplies its actual join operators. Every proof step is below 800 characters; no step exceeds the 2000-character review threshold. The only corrections during self-review were to make the deleted-base case explicit and to give citation excerpts for the internal-functor and relative-join naturality formulas rather than a less specific excerpt.

## What remains unfinished

Nothing in the natural-language split. No Lean was written and no compiler, Lake or build command was run. Remote dry-run and push results follow below when available.
