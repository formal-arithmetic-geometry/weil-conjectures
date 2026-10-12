## What changed

Proved `AlgebraicGeometry.Scheme.etale_units_stalk_evaluation_injective` with its
signature unchanged. Added the proof-only import
`WeilConjectures.AlgebraicGeometry.Sites.Hilbert90Etale`, which also exposes the
proved neighbourhood tools of `PointFunctions` to this proof. All existing public
imports are needed by the statement and remain. Removed the unused proof imports
`WeilConjectures.CategoryTheory.Sites.Torsor` and
`WeilConjectures.Mathlib.RingTheory.Etale.Field`. Kept the original file-level
`open` command by qualifying the filtered-colimit names inside the proof.

Mathlib represents both stalk elements on one pointed neighbourhood. Restrict it
to the singleton open containing the geometric lift. The existing proved lemmas
`discreteTopology_of_etale_of_unique`, `exists_pointSmallEtale_fiber_ofOpens`, and
`isField_of_etale_of_subsingleton` supply this refinement and its field of global
sections. Evaluation is injective on that field. The assumed evaluation formulas
therefore force equality of the restricted units, and Mathlib's filtered-colimit
equality criterion gives equality of their germs.

Updated the item's DAG proof and proof dependencies to match this route. The unit
`sk-thm-br` has no realized statement or steps assigned to this node, so this local
simplification preserves its route. The original declaration docstring is kept;
a proof comment identifies the simplification.

Searches performed with msearch: LeanFinder for injective evaluation on a pointed
etale neighbourhood; Loogle for `Algebra.Etale.iff_exists_algEquiv_prod`; grep for
etale field neighbourhood lemmas. Local rg found the proved source-library tools
in `Hilbert90Etale` and `PointFunctions`. No new intermediate statement is needed.

## Proved and sorry left

Closed the one hole in
`AlgebraicGeometry.Scheme.etale_units_stalk_evaluation_injective`
(node `lem-sc-etale-units-stalk-evaluation-injective`). No holes remain in the
module, and none were added. This is a complete proof, not a decomposition.

Local single-file compilation passed with no warnings. A separate `#print axioms`
check reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The proof
works for imperfect fields: it never identifies separable and algebraic closures.
Empty neighbourhoods are not used: a geometric lift supplies the point of the
chosen singleton open.

`deliver3.py H4 Sheaf.AlgebraicGeometry.EtaleUnitsStalkEvaluationInjective --no-push`
printed `OK (dry run)`: compilation and preflight passed except for the second
reading, which the tool explicitly reserves for the second reader. Nothing pushed.

## No longer needed

Removed proof imports `WeilConjectures.CategoryTheory.Sites.Torsor` and
`WeilConjectures.Mathlib.RingTheory.Etale.Field`; all three public imports supply
statement data. The torsor proof infrastructure is unused by this argument.
The planned dependency `lem-weil-pbc-finite-separable-extension-etale` and its
module `WeilConjectures.Mathlib.RingTheory.Etale.Field` are not needed as a proof
dependency here, and the node's proof_deps no longer lists it. The shorter argument
also needs no separate affine-chart classification, finite separable representative,
or compositum refinement lemmas. The finite-separable module may still be reached
transitively through the existing library tools; this report makes no claim that
it has left the global target closure.

## Where the brief, the DAG or earlier work was wrong

The DAG plan is mathematically sound but longer than necessary. Both elements can
be represented on one neighbourhood, and its singleton open is already a spectrum
of a field. The source library proves the facts needed for this argument. No false
statement, interface correction, forced adaptation, or new node was required.

The earlier attempt's delivery-tool `ImportError` is resolved. The first retry
identified an unnecessary file-level `open Limits`; it is now removed, with names
qualified inside the proof. No tools were edited or bypassed, and nothing was
pushed. The second-reading section is reserved for the next worker, as instructed.

## Second reading by H4

1. **Unchanged interface: pass.** Compared the sole delivered Lean module with
   the repository using `diff -u`. The entire existing theorem signature,
   declaration visibility, docstring, namespace, and public imports are byte for
   byte unchanged. Only its proof and proof-only imports differ. There are no
   definition changes, change records, or forced adaptations; no relevant open
   change record was found in `coord/changes/`.
2. **Proof and trust: pass.** Independently compiled the module with `lcompile.py`
   without errors or warnings. Compiled its full scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.etale_units_stalk_evaluation_injective`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered
   source contains no `sorry`, forbidden declaration, or data construction from
   an unproved existence theorem. Read the supporting proved lemmas in
   `PointFunctions` and `Hilbert90Etale`: the singleton is open, its lift factors
   through the original geometric point, and its nonempty one-point section ring
   is a field. Pullback composition and field-hom injectivity give precisely the
   required equality of restricted units and hence germs.
3. **Split statements and small cases: pass.** No statement or hole was split
   off. A geometric lift supplies a point even if the original neighbourhood has
   many components; an empty neighbourhood cannot represent a germ this way.
   Neither finite-type compactness nor perfection of K is assumed by the proof.
   An independent LeanFinder search for injectivity of geometric stalk evaluation
   for invertible regular functions returned Zariski germ/structure-sheaf results,
   not this theorem. Local searches likewise found no shorter existing theorem
   usable without circular dependence.
4. **Route and pruning: pass.** The proof uses the existing common-representative
   and filtered-colimit equality lemmas, avoiding a new field-compositum argument.
   `Hilbert90Etale` is a plain proof import; all public statement imports are kept.
   The report lists both removed proof imports and the only old proof dependency
   omitted from the new dependency list,
   `lem-weil-pbc-finite-separable-extension-etale`. No claim is made that its
   module leaves the global import closure. Checked `dag/units/sk-thm-br.json`:
   this node realizes neither its statement nor a step, and this local reduction
   does not replace its Brauer-group injection/Tsen route.
5. **DAG agreement: pass.** Compared the node JSON with the repository. Only
   `proof`, `proof_deps`, and `proof_origin` change. The three proof steps match
   the Lean argument, explicitly naming the existing library tools and Mathlib
   colimit tools. Their `uses` union equals `proof_deps`; the statement, statement
   dependencies, Lean signature record, chapter and unit are unchanged. No new
   node is required.

Second reading changed only this report by adding the independent review above;
the Lean proof and node update needed no repair. One original hole is closed,
zero holes are added, and zero split-off statements remain.
