## What changed

Proved `derived_endpoint_cone_presentation` without changing its signature.
Added proof-only imports of `CommutativeSquareLift` and `ConeSquareUnrotation`.
These two new modules contain proved lemmas, built from Mathlib right fractions,
cone matrices, canonical homotopy equivalences, and shift coherence.
The original node now records these proof dependencies and the implemented route.
All representatives and comparison maps come from proved constructions.

## Proved and sorry left

Closed the sole original hole: `derived_endpoint_cone_presentation`.
Added zero holes. Both new public declarations are proved:
`derived_commutative_square_lift` and `derived_cone_square_unrotation`.
Their private helpers are also proved. No delivered Lean file contains `sorry`.
All three modules compile cleanly with lcompile. The delivery dry run passed
compilation, declaration-axiom probes, and preflight checks apart from the second
reading, which is reserved for the second reader. Nothing was pushed.

## No longer needed

None. The original module had only its necessary Mathlib Basic import and no
stated proof dependencies to prune. Both newly added proof imports are used.
No blueprint unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface change. The previous informal proof was too
compressed to supply the endpoint naturality identities directly. The implemented
route refines right fractions and strictifies with an explicit identity-cone
summand. Unrotation uses one further rotation, shift by -1, the triple-rotation
comparison and shift cancellation; cone-shift signs are included explicitly.
The generic square allows all four complex representatives to vary, so it needs
neither boundedness nor enough injectives. The cone computations and constructions
also cover zero objects.

## New nodes

`lem-pc-derived-commutative-square-lift`, in
`Sheaf.CategoryTheory.DerivedCategory.CommutativeSquareLift`, proves strict chain
representatives of a derived commuting square. Its right-fraction and identity-cone
arguments are entirely proved in Lean.

`lem-pc-derived-cone-square-unrotation`, in
`Sheaf.CategoryTheory.DerivedCategory.ConeSquareUnrotation`, proves the endpoint
naturality of the explicit unrotated cone presentation. The shift-cone and
double-cone naturality equations are proved degreewise. Neither node adds a hole.
There are no change records or forced adaptations.

## Second reading by N2

1. **Unchanged interface — pass.** Read all three delivered modules and diffed
   EndpointConePresentation against the repository. The sole existing declaration's
   signature and its docstring are byte for byte unchanged; only its proof and two
   plain proof imports differ. The other two modules are new. No definition used by
   an existing target changed, and no change record or forced adaptation is needed.
2. **Proof and axioms — pass.** Independently compiled all three files in import
   order through lcompile.py, cleanly (6.8, 6.9 and 3.1 seconds). Searched every
   delivered Lean file for sorry and forbidden declarations: none. Scratch copies
   with #print axioms for derived_commutative_square_lift,
   derived_cone_square_unrotation and derived_endpoint_cone_presentation all report
   exactly propext, Classical.choice and Quot.sound, with no sorryAx. Read the
   private helpers too: the isomorphisms have explicit maps and proved inverse laws;
   the representatives are chosen from proved localization constructions.
3. **New statements — pass.** There are no split-off open statements. Both new
   public lemmas are proved, have complete proof docstrings and matching nodes,
   and are proper parts of the argument, not renamed copies of the item. Checked
   the identity-cone adjustment: its correction restricts to s g' - g r, its cone
   is contractible, and the projection preserves all four localized maps. Checked
   the unrotation comparisons, their shift signs and both endpoint identities.
   Zero complexes, identity arrows and zero arrows require no extra hypothesis;
   the constructions still apply. Independently searched with leanfinder for
   strictification using a contractible direct summand, loogle for the cone-shift
   comparison, and rg/msearch grep for rotation and shift naturality and right
   fractions. Read the related Mathlib cone/rotation declarations and searched
   lean/Sheaf and lean/WeilConjectures. No existing theorem supplying either full
   helper statement or the full item was found. Checked the cited Stacks sections
   online because the local derived.tex is absent: Tags
   [014D](https://stacks.math.columbia.edu/tag/014D),
   [05QK](https://stacks.math.columbia.edu/tag/05QK) and
   [05RR](https://stacks.math.columbia.edu/tag/05RR).
4. **Route and pruning — pass.** The proof first uses Mathlib fractions, homotopy
   quotients, cone maps and triangle isomorphisms; it has no open intermediate
   dependencies. Both new plain imports are used, and Basic is needed by the
   signatures in all three modules. Fractions is correctly a plain proof import.
   The original node had no proof_deps, so No longer needed is complete. Read
   dag/units/sk-thm-picard-semicon.json: its realized statement and step lists are
   empty, and this refinement below the unit level bypasses no realization.
5. **DAG agreement — pass.** Checked all three Lean signatures byte for byte
   against their node lean.statement fields and checked that proof_deps equals the
   union of the proof steps' uses. The existing node changes only proof,
   proof_deps and proof_origin. Its two dependencies are precisely the helper
   lemmas used in the Lean proof. The new nodes contain the required sources,
   searches, provenance, blueprint, chapter, unit and Lean records, and their
   descriptions follow the implemented fraction/identity-cone and unrotation
   arguments.

Second reading changed only this report, recording the independent checks.
No Lean proof, statement, definition, import or DAG repair was needed. Confirmed
one original hole closed and zero holes added; the two new lemmas are fully proved,
so this is a proof, not a decomposition into open obligations.
