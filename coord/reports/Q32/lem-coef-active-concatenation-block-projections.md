## Worker report

The delivery states `SSet.Enhanced.active_concatenation_block_projections` in
`Sheaf.CategoryTheory.ActiveConcatenationBlockProjections`. Its proof is `sorry`.
Every helper is a real definition or Prop structure belonging to this assertion.
There are no new independent notions or new DAG nodes.

Read the item's full statement, all six proof steps, all three statement-dependency
statements and their Lean records, and the recorded declarations and docstrings in
EnhancedDiagramsCones, OperadicApproximationRestriction and
ActiveOperadCocartesianConcatenation. Read the symmetric pointed-set primitives in
RelativeSymmetricOperadicAlgebras and the envelope definitions in
ActiveOperadEnvelopeCocartesian. The source HA (September 18, 2017) was successfully
opened online: Construction 2.2.4.1, Remark 2.2.4.3, Corollary 2.2.4.5,
Remark 2.2.4.6 and Proposition 2.2.4.9, printed pages 211–213. The proof is the
item's explicit envelope calculation, rather than an ordinary categorical analogue.

The hypothesis and clause correspondence is as follows.

| Node text | Lean rendering |
| --- | --- |
| Symmetric infinity-operad C^tensor over N(Fin_*) | `{C : SSet.{u}}`, `p : C ⟶ finStarBase.{u}`, `hp : IsSymmetricInfinityOperad p`; the operadic predicate contains the inner-fibration and Segal conditions. |
| Arbitrary finite number s ≥ 0 | `(s : ℕ)`, with no positivity or nonempty-index assumption. |
| Wide active category and inclusion iota | The existing `(activeOperadSubcomplex p).toSSet` and `.ι`, used directly throughout. No duplicate category or inclusion is defined. |
| F is ordered s-fold concatenation | The exhibited `F` is compared to an actual tensor `t` satisfying the dependency's `IsActiveConcatenationTensor p s t`. The equivalence `j` between the canonical envelope color fiber and the active category satisfies `j ≫ .ι = activeConcatenationInclusion p`. The `AreNaturallyEquivalent` clause compares the entire coherent functors after the product of `j`. |
| Object arity r = sum r_j | `HasActiveOrderedBlockForm.object_arity`: each input has arity `r i` and `F.app` has arity `∑ i, r i`. |
| Active tuple maps to the blockwise sum of its pointed maps | `HasActiveOrderedBlockForm.arrow_block_sum`: a whole input edge `h` projects to the component `finStarEdge (γi i)`, its F-image projects to `finStarEdge γ`, and `IsActiveOrderedBlockSum` gives the exact ordered-block value formula. Source and target arities of each component are retained explicitly. |
| Consecutive blocks | `activeBlockOffset r i = ∑ k, if k < i then r k else 0`. Every non-basepoint input is written as this offset plus `k.val + 1`; the output formula uses the corresponding output-block offset. The existing pointed maps already preserve zero. |
| Coherent transformation p_j : iota F ⇒ iota pr_j | `HasActiveCoherentBlockProjections` quantifies `j : Fin s` and one edge `e` of the internal hom, with its source exactly `diagramVertex (F ≫ .ι)` and target exactly `diagramVertex (Pi.π ... j ≫ .ι)`. |
| Component inert over q_j | Evaluating this same `e` at any input vertex gives an edge satisfying `IsSymmetricInertEdge p` and an exact base-map equality with `finStarEdge q`. `IsActiveOrderedBlockProjection` says `q` is inert, is the identity on the jth consecutive block, and sends every other input to zero. |
| Naturality squares and all higher simplices | An edge of the internal hom is the whole simplicial cylinder, not a collection of component edges. Its restriction along any input edge is the naturality square; its restrictions along all higher simplices give the higher compatibilities. No separate objectwise substitute is used. |
| Empty blocks r_j = 0 | All `r : Fin s → ℕ` are permitted. `Fin (r i)` can be empty. An empty selected block has pointed target `Fin 1`, hence all inputs go to zero; inertness has no non-basepoint outputs to test. |
| Unary p_1 is an equivalence | The clause `s = 1 → IsEquivalenceEdge ... e` applies to the very same transformation `e`. Its target is the unique product projection, identifying the one-factor product with the active category. The inclusion is full on these active arrows, so this is the stated equivalence F ≃ id. |
| No projections at s = 0; empty tuple | The index `Fin 0` is empty. The object-arity formula gives zero output arity. `IsActiveConcatenationTensor p 0 t` supplies the actual nullary envelope tensor rather than an arbitrary object over zero. |

The dependency supplies a predicate for tensors, not a chosen functor: it explicitly
forbids choosing an object from its postponed existence assertion. Accordingly this
theorem exhibits an ordered representative `F`, together with the actual envelope
tensor comparison and its coherent block projections. It does not choose data from
an unproved existence theorem or assert that an arbitrary functor with the same
arity formula is concatenation. The order and the naturality are specified
simultaneously for the same representative, as in proof step 4 of the node.

Statement-dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `diagramVertex`, `evaluation`,
  `AreNaturallyEquivalent`, `IsFunctorEquivalence`, `IsEquivalenceEdge` and the
  actual internal simplicial Hom; this module uses Mathlib's `SSet` directly.
- `Sheaf.CategoryTheory.OperadicApproximationRestriction` and its public
  primitives: `IsSymmetricInfinityOperad`, `FinStar`, `finStarBase`,
  `finStarVertex`, `finStarEdge`, `IsFinStarActive`, `IsFinStarInert`,
  `IsSymmetricInertEdge`.
- `Sheaf.CategoryTheory.ActiveOperadCocartesianConcatenation`:
  `activeOperadSubcomplex`, `activeConcatenationProjection`,
  `activeConcatenationInclusion`, `IsActiveConcatenationTensor`.

All stated proof-dependency modules are imported directly. The theorem docstring
carries the six-step proof plan, naming the envelope theorem, Segal classification,
pointwise transport, composition and mapping criteria, and pointwise equivalences.
There is one universe `u`, arbitrary throughout; no extra equality of site or
coefficient universes occurs. `autoImplicit` is false and every variable is bound.

Edge cases checked before finalizing: s=0 (terminal empty product, zero arity and
empty projection family), s=1 (identity block selector and the same transformation
an equivalence), zero-length intermediate and selected blocks, all blocks zero,
active nullary maps from zero inputs to a nonzero output, and degenerate arrows.
There is no active pointed map from a nonzero input set to zero; the block-sum
predicate retains this restriction through the existing active-map predicate.

Searches actually run:

- `msearch.py ... leanfinder "Coherent inert block projections from ordered concatenation in the active category of a symmetric infinity operad"`: eight hits, including composition-block formulas, simplex generator relations and `SSet.StrictSegalCore.concat`; none is a coherent operadic projection theorem.
- `msearch.py ... loogle "SSet, CategoryTheory.Limits.Pi.π"`: zero hits.
- `msearch.py ... grep "operad|FinStar|blockProjection"`: the two Mathlib hits are bibliography entries in PreLie/Basic and Distributive/Monoidal, with no operadic definitions.
- `rg` over upstream WeilConjectures for the item id, activeConcatenation and blockProjection: no hits. Further exact full-name searches for every final helper and the theorem over Mathlib, upstream WeilConjectures and shared lean/Sheaf: no hits.
- Shared Lean and DAG searches for block projections and activeConcatenation found the existing envelope/tensor dependency but no exact theorem. The similarly named monoidal-block-projection-coherence node concerns nonsymmetric planar operation systems, not the active category of a symmetric infinity-operad. No existing declaration was rebound.

Validation: `scompile.py Q32 lem-coef-active-concatenation-block-projections`
compiled BOTH delivered modules, each separately, and recompiled their affected
private overlay dependents. The final run completed with no errors or warnings:
SpaceValuedStraightening (2.6 seconds), KanRelativeNerveLeftFibration,
CompleteAlgebroid, SymmetricMonoidalSegalClassification,
ActiveOperadCocartesianConcatenation, both preliminary files and both final library
files. All compilation used the prescribed wrapper after the initial scratch
probe. No statement correction or disputed mathematical assertion is recorded.

## Dependency modules

`lem-coef-space-valued-straightening`, module
`Sheaf.CategoryTheory.SpaceValuedStraightening`: the recorded source could not be
compiled in the current published overlay. At line 64, `abbrev Diagrams` depended
on `smallSpaces`, now noncomputable; Lean reported `lean.dependsOnNoncomputable`.
The delivery was read from the current server with `scompile.py --source` and
changes only `abbrev Diagrams` to `noncomputable abbrev Diagrams`. All mathematical
definitions, the complete theorem and its proof docstring, and every signature
are retained. Its DAG copy changes only `lean` and includes the required note.
The repaired declaration is already listed in `lean.declarations`.

This is a transitive prerequisite of the item through the existing tensor
interface; it is not an extra assumption on the item. Consumer validation compiled
KanRelativeNerveLeftFibration, CompleteAlgebroid,
SymmetricMonoidalSegalClassification, ActiveOperadCocartesianConcatenation and the
new block-projection statement against this repair. Both delivered modules compile
cleanly. No live Lean file was edited.

## Second reading by Q32

Independent maintainer reading of immutable delivery
`51ab7e021ef6a236a073528686a85ab93c7da502`, 2026-10-17, by Codex.
The original worker did not perform this reading. The independent reader checked
the snapshot, the three statement-dependency nodes and their recorded interfaces,
the delivered transitive dependency repair, the six-step proof docstring, and the
source. No mathematical or Lean change was necessary.

Clause-by-clause results:

- The only hypotheses are an arbitrary simplicial universe `u`, an operad map
  `p` with `IsSymmetricInfinityOperad p`, and `s : ℕ`. The existing operad
  predicate includes quasicategory, inner-fibration, inert lifting and Segal
  axioms. There is no global cocartesian, presentability or positivity assumption.
- The active category and its inclusion are the dependency's
  `activeOperadSubcomplex p` and `.ι`; the finite domain is its actual product.
- Concatenation is the existing envelope operation: `j` is a coherent equivalence
  normalized by `j ≫ .ι = activeConcatenationInclusion p`; `t` satisfies
  `IsActiveConcatenationTensor`; the displayed natural equivalence compares
  `F` with that tensor on whole functors. Existential `F` supplies an ordered
  representative of the operation, whose dependency does not choose a functor.
  It is not an unconstrained functor or data chosen from a postponed existence.
- `HasActiveOrderedBlockForm.object_arity` records each input arity and their
  sum as the output arity. Arity witnesses are determined by the base vertices.
- `arrow_block_sum` records both endpoints, the actual component base arrows,
  the actual image base arrow, and `IsActiveOrderedBlockSum`. Its offset formula
  partitions all non-basepoint inputs into consecutive blocks and gives their
  exact images. Pointedness fixes the omitted basepoint value.
- `HasActiveCoherentBlockProjections` supplies an internal-Hom edge from exactly
  `F ≫ .ι` to exactly the product projection followed by `.ι`, for each `j`.
  Evaluation of this same edge is inert and lies over the specified `q`.
  `IsActiveOrderedBlockProjection` is the identity on the selected block and
  collapses all other inputs. Its explicit inertness uses the recorded predicate.
- An internal-Hom edge is a simplicial cylinder, so restriction to input edges
  and higher simplices gives the claimed squares and every higher compatibility.
  The statement does not replace coherence by separate objectwise choices.
- When `s = 1`, the very same edge is an equivalence in the functor category.
  Its base components are identities, so the inverse edges also lie in the
  active subcategory; the unique product projection identifies the unary domain.
- `s = 0` has no indices and hence no projections. Its arity sum is zero and
  its tensor comparison is with the actual nullary tensor. Zero-length blocks,
  selected empty blocks and all-zero families are allowed without extra binders.
  Nullary active arrows from zero inputs to positive arity and degenerate edges
  are included; activity rules out positive inputs mapping to arity zero.

Source check: opened Lurie's September 18, 2017 Higher Algebra, printed
pp. 211–213, Construction 2.2.4.1, Remarks 2.2.4.3 and 2.2.4.6,
Corollary 2.2.4.5, and Proposition 2.2.4.9. The envelope model, active fiber and
concatenation interpretation agree. The coherent projections are the explicit
Segal-inverse and pointwise-transport argument in the node, not a claim that
Proposition 2.2.4.9 by itself states these projections. Checked the consuming
block-assembly node's steps 4 and 6: they need exactly these cylinders and base
block formulas.

Dependency repair: inspected the immutable commit diff and full delivered
`SpaceValuedStraightening.lean`, including all twelve recorded declarations and
the ten-step proof docstring. Its only substantive source edit is adding
`noncomputable` to `Diagrams`; the trailing blank line is cosmetic. The dependency
node changes only `lean`, records the reason in `lean.note`, and retains the same
mathematics. The main theorem signature and this dependency's signature match
their immutable `lean.statement` strings verbatim. The repair is a permitted
transitive interface repair; it adds no assumption or universe equality.

Independent searches: `rg` for block projections, active concatenation, ordered
block forms and the new declaration names across the group clone's `lean/Sheaf`,
upstream `WeilConjectures` and Mathlib; also inspected the nearby DAG node
`lem-coef-monoidal-block-projection-coherence`. That node concerns nonsymmetric
planar operation systems, not these symmetric active-category projections.
The envelope and pointed-set primitives are reused. No duplicate theorem or
helper was found. The worker's three search kinds are recorded above.

Both delivered files have source/blueprint module and declaration docstrings,
no lines over 100 characters, bound variables with `autoImplicit false`, real
helper data, and exactly one postponed theorem each, with proof `sorry`.
All recorded helpers belong to the relevant owning node. No new independent
notion, silent statement correction, stronger hypothesis, arbitrary-map
substitute or pro-etale substitute was introduced.

Reproduced compilation with the prescribed command:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q32 \
  lem-coef-active-concatenation-block-projections \
  snapshot/lean/Sheaf/CategoryTheory/SpaceValuedStraightening.lean \
  snapshot/lean/Sheaf/CategoryTheory/ActiveConcatenationBlockProjections.lean
```

Exit 0, no errors or warnings. This installed wrapper runs the private side
overlay on the server. It recompiled SpaceValuedStraightening,
KanRelativeNerveLeftFibration, CompleteAlgebroid, SymmetricMonoidalSegalClassification
and ActiveOperadCocartesianConcatenation, then both delivered files separately in
preliminary, sandbox and library modes. Final library checks took 3.0 s for
ActiveConcatenationBlockProjections and 6.7 s for SpaceValuedStraightening, each
under the default 60 s per-file limit. No global build or live Lean edit was run.

Findings and repair: H11, the original second-reading section was only a
placeholder; this complete independent reading replaces it. Restored the five
HA citation numbers obscured as “the project server” in the worker report.
The Worker report and Dependency modules sections remain. No other fault found.
