## What changed

Replaced the proof of `CategoryTheory.ShortComplex.ShortExact.exists_rightDerived_full_long_exact` with a reduction to the existing horseshoe cohomological delta-functor theorem. The proof packages its fields and transports the resulting proposition across the functor-family equality.

## Proved and sorry left

`exists_rightDerived_full_long_exact` is proved. No `sorry` remains in the delivered module; no statements were split off.
The axiom audit reports `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`: the
last comes from the existing open theorem
`CategoryTheory.InjectiveResolution.exists_horseshoe_morphism_lift` in
`Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift`, used by the imported delta-functor.
Thus the local theorem body is closed, but its transitive proof is not yet axiom-free.

## No longer needed

The direct horseshoe resolution import is no longer needed; the proof imports `Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`, which supplies the required delta-functor and exactness data. The following old direct `proof_deps` are no longer directly used by this proof:
- `def-sp-abelian`
- `def-sp-injective-resolutions`
- `def-sp-left-exact-additive`
- `lem-weil-pbc-complex-ses-homology-long-exact`
- `lem-weil-pbc-derived-functor-map-via-lift`
- `lem-weil-pbc-injective-resolution-ses`

They remain relevant to the signature or the imported delta-functor construction;
this is pruning of direct edges, not a claim that their modules leave the target closure.
The removed import is `Sheaf.CategoryTheory.Abelian.HorseshoeResolutions`; the new
proof-only import is `Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`. No public
import changed. No module is asserted to be globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The DAG's five-step direct construction is valid but unnecessarily low-level for this item: `HorseshoeDeltaFunctor` already packages exactly the initial monomorphism and the three exactness clauses needed here.


## Second reading by M1

1. Compared the sole delivered module with the repository version. The universes,
   abelian categories, enough-injectives assumption, additive left-exact functor,
   short exact sequence, and every conclusion are unchanged. Restored an accidental
   extra space before `:= by`; a script checked the existing signature byte for byte.
   No definition or new declaration was added; no change record is needed.
2. Compiled the module locally without errors or warnings. Read the full proof and
   the delta-functor fields: `delta` supplies all degrees, `mono_zero` the initial
   monomorphism, and `exact_middle`, `exact_right`, `exact_left` the three positions.
   Equality transport substitutes the actual derived-functor family. The final
   `simpa only [ShortComplex.map]` changes only the zero-composition proof, by proof
   irrelevance. No forbidden construct or local `sorry` occurs. A scratch copy with
   `#print axioms` compiled and reported only the three permitted axioms and
   `sorryAx` from the pre-existing open horseshoe-morphism-lift dependency.
3. No split-off statements, new nodes, or hollow definitions were added. Checked the
   upstream delta-functor theorem is genuinely stronger (naturality and comparison
   with every horseshoe), rather than a newly renamed version of this item.
   In degree zero the fields include both middle exactness and the initial mono;
   the zero short exact sequence presents no special-case gap.
4. Searched the Lean library for derived-functor exactness and monomorphism lemmas,
   and ran Mathlib `msearch.py ... grep 'rightDerived.*(Exact|Mono)|exists_rightDerived'`.
   The existing upstream `exists_rightDerived_δ_exact` supplies only two positions,
   not middle exactness or the initial mono. The horseshoe delta-functor is an
   appropriate existing packaged route; its construction retains the horseshoe,
   degreewise splitting, cohomology exactness, degree-zero mono and comparison steps.
   The proof-only import is necessary and not public; public signature imports are
   unchanged. Expanded the pruning report to name every removed direct dependency.
   Read `dag/units/sk-thm-p1.json`: this item is below the unit's realized steps, and
   no realized node or chapter/unit route is bypassed or altered.
5. Checked the changed node against the Lean proof: its sole direct dependency is
   `lem-weil-pbc-horseshoe-delta-functor`, and its proof and origin name the actual
   theorem and field extraction. Added the missing `uses` and `elementary` fields
   to its proof step, so the union of step uses equals `proof_deps`. The node's
   statement and Lean record are unchanged; no new-node fields are applicable.

Second reading changed only signature whitespace, one extra blank line, the DAG
proof-step metadata, and the report's explicit pruning and upstream-axiom accounting.
The working proof was retained.
