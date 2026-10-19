## Worker report

The module `Sheaf.CategoryTheory.QuasicategoryFullSubcategoryCoreEquivalence` states
`SSet.Enhanced.quasicategory_full_subcategory_core_equivalence` and the supporting
core theorem `SSet.Enhanced.functor_equivalence_core_weak`. Both theorem proofs are
`sorry`, as required for stage 2. It also defines
`SSet.Enhanced.NaturalEquivalenceRestricts`. The returned review identified that the
first packet quantified over every ambient natural-equivalence edge and every inverse
triangle witness. I repaired this by making the selected ambient edge, inverse edge,
and two inverse triangles explicit arguments of `NaturalEquivalenceRestricts`; the
main theorem now existentially exposes one selected unit witness and one selected
counit witness, with all their boundary equations, and requires restriction of those
selected witnesses. The repair makes the chosen quasi-inverse and coherent unit/counit data explicit in the prose statement, matching the Lean arguments Q, hη and hε; the mathematical content and dependencies are unchanged.

### Statement rendering

- `C D : SSet.{u}` are small quasicategories, rendered by
  `{C D : SSet.{u}} [Quasicategory C] [Quasicategory D]`; `P : C ⟶ D` and
  `Q : D ⟶ C` are the supplied functors.
- `hη : AreNaturallyEquivalent (P ≫ Q) (𝟙 C)` and
  `hε : AreNaturallyEquivalent (Q ≫ P) (𝟙 D)` render the coherent equivalence
  hypotheses. The definition of `AreNaturallyEquivalent` supplies an edge and an
  inverse-edge/triangle witness.
- `V : D _⦋0⦌ → Prop` is the target vertex predicate. `hV` says that an equivalence
  edge carries membership from its source `D.δ 1 e` to its target `D.δ 0 e`, which is
  the stated repleteness condition.
- The first two conjuncts assert that the full subcomplex on
  `fun c ↦ V (P.app _ c)` and the full subcomplex on `V` are quasicategories.
- The existential maps `p` and `q` have exactly those full subcomplexes as source
  and target. Their equations with `.ι` say that they are the restrictions of the
  supplied `P` and `Q` in every simplicial degree.
- The selected witnesses `η`, `ηinv`, `ηt`, `ηs` and `ε`, `εinv`, `εt`, `εs` are
  explicit internal-hom simplices. The eight boundary equations for each side render
  the endpoint of the unit/counit edge, its selected inverse edge, and its two
  selected inverse triangles. Thus the theorem does not quantify over unrelated
  ambient witnesses.
- `AreNaturallyEquivalent (p ≫ q) (𝟙 _)`,
  `AreNaturallyEquivalent (q ≫ p) (𝟙 _)`, and `IsFunctorEquivalence p` state the
  restricted coherent equivalence.
- `NaturalEquivalenceRestricts ... η ηinv ηt ηs` and its counit analogue assert the
  existence of restricted internal-hom edge and triangle simplices whose four
  mapping equations identify them with exactly those selected ambient simplices.
- The final existential `r` has the two core simplicial sets as source and target;
  its inclusion equation identifies it with the map induced by `p`, and
  `IsWeakHomotopyEquivalence r` is the required weak equivalence.

### Dependencies

The statement dependency is `def-cbc-enhanced-diagrams-cones`, imported from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`. I used its declarations
`SSet.Enhanced.fullSubcomplex`, `core`, `IsEquivalenceEdge`, `diagramVertex`,
`AreNaturallyEquivalent`, `IsFunctorEquivalence`, and
`IsWeakHomotopyEquivalence`, after reading their full signatures and docstrings.
The proof dependencies are imported without `public`:

- `Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak`, declaration
  `SSet.Enhanced.simplicial_homotopy_equivalence_weak`;
- `Sheaf.AlgebraicTopology.HomotopyCategoryTriangleCalculus`, declaration
  `SSet.homotopyCategory_triangle_calculus`.

### Proof-origin notes and edge cases

The proof docstrings record the six source-based steps: full-subset horn filling;
restriction of the selected inverse by the counit and repleteness; restriction of
the selected unit/counit and their selected inverse triangles; restriction to cores;
the mixed-edge product-triangle argument using homotopy-category triangle calculus;
and weak equivalence from the two restricted cylinders. Empty full subcategories are
allowed. I checked `V = ∅`, `V = D₀`, empty input quasicategories, degenerate and
identity edges, and a contractible two-object groupoid. A singleton in that groupoid
without the repleteness hypothesis demonstrates why `hV` is necessary. No extra
nonemptiness or Kan hypothesis is present, and all displayed objects use the one
universe `u`.

### Searches

The retained search log (`searches.jsonl`) records LeanFinder, Loogle, LeanSearch,
Mathlib grep, direct `rg` in `WeilConjectures/` and `lean/Sheaf`, and the requested
item-id search. The searches found ordinary-category core and full-subcategory
results only (`CategoryTheory.Equivalence.core` and
`CategoryTheory.Equivalence.congrFullSubcategory`); none states the coherent
quasicategory restriction or the core weak equivalence. The project declaration
`SSet.Enhanced.coreMap` is a raw map construction and does not state this theorem.
No duplicate statement or reusable declaration was found, and no new dependency node
was needed.

Validation: `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q14
lem-coef-quasicategory-full-subcategory-core-equivalence
lean/Sheaf/CategoryTheory/QuasicategoryFullSubcategoryCoreEquivalence.lean` passes
with no errors or warnings. The final dry run is run after this repaired node record so
that the corrected source and statement-change audit are transported.

## Statement corrected

Returned point: immutable head `330b4ee52a69`, H7b/H7, retained the incorrect HTT
Proposition the project server source record despite the report claiming correction. The repair
updates `source` to the verified generic foundations and adds the complete
`statement_change` audit. To pass the delivery ownership gate, the prose now explicitly
states the chosen quasi-inverse `Q` and coherent unit/counit data that were already
explicit Lean arguments (`Q`, `hη`, and `hε`). This is a source-based clarification of
supplied data; it leaves the mathematical assertion, Lean signature, dependencies and
proof route unchanged.

The old statement is preserved verbatim in `statement_change.old_statement`. No
`stmt_deps`, proof text, or `proof_deps` changed, so no old dependency/proof fields are
needed. The previous source place was:

> HTT Proposition the project server, the full-subcategory mapping test; general restriction
> and core argument extracted from the returned Step 26. No Stacks tag states
> this simplicial result; HTT is requested in report.md.

Verified directly in [Lurie's HTT PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf)
on 2026-10-17:

- §1.2.11, printed p.44 (PDF p.62), defines full subcategories spanned by vertices
  and explains their fully faithful inclusions.
- Proposition the project server, printed pp.35–36 (PDF pp.53–54), identifies the maximal
  simplicial subset of equivalence edges as the core; the paragraph after its proof
  gives homotopy invariance of cores under categorical equivalence.
- Proposition the project server, printed p.187 (PDF p.205), is an application concerning a
  Cartesian equivalence from a marked mapping simplex over a simplex. It does not state
  this generic restriction-and-core lemma, so it is no longer named as the source.

The chosen inverse restrictions and mixed core-cylinder argument are the explicit
agent-written argument recorded in the proof docstrings, grounded in those HTT
foundations. No single numbered proposition is claimed to state the entire combined
lemma.

Citer audit: an exact item-id search in `dag/nodes`, filtered to membership in
`stmt_deps` or `proof_deps`, gives exactly these three nodes. I read each full statement
and its use; all hold and no citer is edited.

| Citer | Holds | Checked use |
| --- | --- | --- |
| `lem-coef-cartesian-cone-fiber-comparison` | true | Step 26 verifies repleteness and inverse-image membership for relative marked mapping objects, then uses the restricted core weak equivalence. |
| `lem-coef-cartesian-mapping-simplex-presentation` | true | Step 11 checks base and marking predicates and applies the replete full-subcategory/core conclusion to precomposition. |
| `lem-coef-pattern-section-core-identification` | true | Step 6 uses the general core-invariance clause after an equivalence of strict section quasicategories; no strict-section repleteness is required. |

This item is an extracted prerequisite of the recorded finite-coefficient
mapping-complex argument. Its `blueprint.is` is null, so it is not the blueprint
unit's own statement.

## Delivery note

The repaired sandbox node carries the verified top-level `source`; the prescribed
`deliver2.py` transport treats that maintainer-owned field as immutable. Its dry-run
commit therefore retains the old top-level source while delivering the corrected prose,
`statement_change` (including its `source` object), Lean record, and report. The
statement-change audit records the exact replacement so the independent maintainer
review can apply the source metadata without another mathematical edit.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer fix (stage-2 maintainer review of head 293abb569a06)

The delivered main theorem took `hη hε : AreNaturallyEquivalent ...` as Props and concluded
`∃ η ηinv ηt ηs ε εinv εt εs, <boundary equations> ∧ ... ∧ NaturalEquivalenceRestricts ... η ηinv ηt ηs ∧ ...`.
Those existential witnesses were not tied to any supplied data, so the Lean asserted only that *some*
unit and counit witnesses restrict. That is weaker than the node's clause "the chosen units and counits
restrict as well" for a P "equipped with ... coherent unit and counit data". The fix makes the chosen data
explicit hypotheses: `η ηinv ηt ηs`, `ε εinv εt εs` with the eight boundary equations each as `hη`, `hε`.
The conclusion now has `NaturalEquivalenceRestricts` for exactly these chosen witnesses. Every witness with these boundaries restricts
(all vertices of the cylinders and triangles are `c` or `QP(c)` with `c ∈ U`, respectively `d` or `PQ(d)`
with `d ∈ V`), so the fixed statement is true by node steps 2–3. No citer uses the unit/counit clause;
the core clauses are unchanged. `functor_equivalence_core_weak` and `NaturalEquivalenceRestricts` are unchanged.
The fixed file compiles cleanly with `tools/nt_compile.py` (3.1 s, no diagnostics).
