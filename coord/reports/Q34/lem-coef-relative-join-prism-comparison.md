## Worker report

The module `Sheaf.AlgebraicTopology.RelativeJoinPrismComparison` states
`SSet.Enhanced.relative_join_prism_comparison`, with its entire proof postponed by
`sorry`. Three auxiliary definitions construct the relative domain, the generated
penultimate stage, and the exact coordinate specification of the canonical map.
They have real bodies and introduce no new independent notion or arbitrary map.
There are no other postponed theorems, no new nodes, and no dependency repairs.

The earlier attempt's reported obstruction was a mistaken identification of stage-1
review with stage-2 completion. The current base node is `status: split`, reviewed
in stage 1 by NV, and has no `lean` record or `reviewed_lean`. This delivery preserves
that split and its entire mathematical statement and proof plan. It only adds the
Lean record and two already landed statement dependencies that own constructions
used in the signature: `lem-coef-infinity-pushout-join-saturation` and
`lem-coef-infinity-slice-right-fibration`. No resplitting is attempted.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Small simplicial sets in an arbitrary universe: `universe u`, `{B : SSet.{u}}`
  and `(K : SSet.{u})`. There is no finiteness, inhabitation, Kan-complex, or
  quasicategory instance. All variables and universes are explicitly bound, and
  the file sets `autoImplicit false`.
- The arbitrary simplicial subset `A ⊆ B`: `(A : B.Subcomplex)`, with its actual
  underlying simplicial set and inclusion `A.ι`. This is exactly the node's
  subset formulation, rather than an additional choice of an inclusion map.
- The dimension `m ≥ 0`: `(m : ℕ)`, including zero, with no positivity assumption.
- Standard simplices, horns and products use the dependency's Mathlib `SSet`,
  `Δ[m]`, `boundary m`, and the Cartesian monoidal product `⊗`. The Mathlib product
  is literally the product of the two sets of simplices in every degree.
- The ordered join is the existing `SSet.Enhanced.orderedJoinFunctor`. Its
  terminal-augmentation/ordinal-concatenation construction has the pure-factor
  summands and the mixed `X_a × Y_b` summands with `a+b+1=r` stated in this node;
  it is not a second join definition. Its operators restrict the ordered blocks.
- The convention `∂Δ⁰ = ∅` is Mathlib's `SSet.boundary_zero`. The boundary consists
  of nonsurjective ordinal maps, so every degree of `boundary 0` is empty.
- The ambient `T` is `orderedJoinFunctor.obj (B, K) ⊗ Δ[m]`.
- The stated relative union `D` is `relativeJoinPrismDomain A K m`. It takes
  `Subcomplex.range (orderedJoinFunctor.map (A.ι, 𝟙 K))`, the image of the actual
  join inclusion, then `unionProd (boundary m)`. Thus it is precisely
  `((A ⋆ K) × Δ[m]) ∪ ((B ⋆ K) × ∂Δ[m])`. Image, product, and union are Mathlib's
  degreewise operations. The explicit type annotation on the pair of morphisms
  only guides elaboration of the underlying subcomplex as a simplicial set.
- The generated subcomplex `Z` is `relativeJoinPrismStage A K m`: `D` joined with
  the supremum of `Subcomplex.ofSimplex s` for exactly the qualifying simplices.
  The condition ranges over every vertex index `j` and every vertex `b` of `B`.
  Its antecedent says that the `j`th vertex of `s.1` is the pure leading vertex
  `orderedJoinInl B K b`; its conclusion is `s.2 j < Fin.last m`. In the ordered
  join the leading and final vertex sets are disjoint, so this tests precisely
  all vertices in the leading `B` block, including repeated ones. The supremum
  is exactly generation as a subcomplex, without assuming closure as extra data.
- The relative union `R` is written directly as `A.unionProd (boundary m)`;
  its underlying simplicial set and canonical inclusion are used in the pushout.
- The final comparison has exactly the node's source and target:
  `φ : orderedJoinFunctor.obj (B ⊗ Δ[m], K) ⟶ T`. Its existence is asserted in the
  conclusion, and is not an assumption. `RelativeJoinPrismCoordinates B K m φ`
  fixes its full first projection as `orderedJoinFunctor.map (fst B Δ[m], 𝟙 K)`;
  fixes its second projection on the entire leading factor as `snd B Δ[m]`;
  and fixes that projection on the entire final factor as the constant simplex
  at `Fin.last m`. Every vertex of a mixed join simplex belongs to one of these
  two pure blocks. A simplex of `Δ[m]` is a monotone ordinal map, hence determined
  by its vertex values. These three equalities therefore determine `φ` uniquely
  in every degree and say exactly "retain the leading coordinates, concatenate
  constant final coordinates m". The existential is a statement of the canonical
  construction with its exact characterization, not a freely varying comparison
  or a `Nonempty` choice. There is no definition choosing data from this theorem.
- Injectivity of that canonical map is `Mono φ`, equivalent here to degreewise
  injectivity, since simplicial sets are presheaves of sets.
- The first conclusion is `innerAnodyneExtensions` of the canonical
  `Subcomplex.homOfLE` from `D` to `Z`. The proof term `le_sup_left` is the lattice
  inclusion of `D` into its displayed union. It adds no hypothesis or conclusion.
  Mathlib's `innerAnodyneExtensions_eq_retracts_transfiniteCompositions` identifies
  this class with the weakly saturated inner-horn closure specified by the node,
  including isomorphisms, pushouts, small transfinite compositions, and retracts.
- The final conclusion is the node's explicitly offered pushout formulation:
  `∃ ρ : R ⋆ K ⟶ Z, IsPushout ρ (orderedJoinFunctor.map (R.ι, 𝟙 K)) Z.ι φ`.
  Its bottom and right arrows are the actual inclusions/comparison; its top
  rightward arrow is the actual join of `R.ι` with the identity of `K`.
  Commutativity forces `ρ ≫ Z.ι` to equal that arrow followed by `φ`, exactly
  specifying the restriction to `Z`; because `Z.ι` is monic, `ρ` is unique.
  `IsPushout` supplies the full universal property, equivalently invertibility of
  the canonical map from `Z ⨿[R ⋆ K] ((B × Δ[m]) ⋆ K)` to `T`, as required.

Dependency declarations read and used:

- `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`: its public Mathlib `SSet`,
  `stdSimplex`, simplicial Cartesian product, and subcomplex interfaces. The
  recorded `coneCategory` and its docstring were read; no cone or mapping-space
  hypothesis is needed for this node's unmarked simplicial statement.
- `lem-coef-infinity-pushout-join-saturation`, module
  `Sheaf.AlgebraicTopology.PushoutJoinSaturation`:
  `SSet.Enhanced.orderedJoinFunctor`, including its full construction and
  normal-form docstring. Imported publicly through the next module.
- `lem-coef-infinity-slice-right-fibration`, module
  `Sheaf.CategoryTheory.JoinSliceRightFibration`:
  `SSet.Enhanced.orderedJoinInl` and `orderedJoinInr`, with their full definitions
  and docstrings. Only these constructions are used, not its slice theorem.
- Proof import `Sheaf.CategoryTheory.RightAnodyneProduct`:
  `SSet.rightAnodyneExtensions_pushoutProduct`, recorded by
  `lem-coef-infinity-right-anodyne-product`. Its full signature and proof
  docstring were read; step 5 uses precisely its right-horn orientation.
- Proof import `Sheaf.AlgebraicTopology.AnodyneCocones`:
  `SSet.Enhanced.anodyne_cocones`, recorded by
  `lem-coef-infinity-anodyne-cocones`. Its full signature and docstring were read;
  step 6 uses its first, pushout-join clause after reversing the two blocks.
- Direct Mathlib boundary import:
  `Mathlib.AlgebraicTopology.SimplicialSet.Boundary`, `SSet.boundary` and
  `boundary_zero`; other reused primitives include `Subcomplex.range`,
  `Subcomplex.unionProd`, `Subcomplex.ofSimplex`, `Subcomplex.homOfLE`,
  `CategoryTheory.CartesianMonoidalCategory.fst`/`snd`, and `IsPushout`.

Edge cases checked before writing:

- `m = 0`: no leading vertex has coordinate below zero, so the generators
  outside `D` can only have an empty leading block. They are already in `D`.
  Thus `Z = D`, the first map is an identity up to its subcomplex equality,
  `R = A × Δ⁰`, and the final map is the canonical join/prism isomorphism.
- `K = ∅`: the join is `B`; the extra qualifying simplices have coordinates
  avoiding `m` and hence lie in the boundary. Thus `Z = R`, and the final
  pushout is the identity attachment of the full product.
- `B = ∅`: also `A = ∅`, the join is `K`, and `D = T` because `∅ ⋆ K = K`.
  In this case `Z = T`; `φ` is the constant-coordinate inclusion of `K` at `m`.
  The top arrow `R ⋆ K → (B × Δ[m]) ⋆ K` is an isomorphism, so the square is
  still a pushout. This checks why the conclusion must not require `φ` itself
  to be surjective or an isomorphism in general.
- `A = B`: `D = Z = T` and `R = B × Δ[m]`; the top arrow of the pushout is the
  identity. `A = ∅` retains all pure `K` simplices, as required by the join.
- `B = K = Δ⁰`, `A = ∅`, `m = 1`: `D → Z` adds the first triangle through an
  inner horn; the final attachment supplies the other triangle of the square.
  Constant and degenerate simplices are included in the vertex test; no
  nondegeneracy or finite-dimensional hypothesis appears.

Searches for reuse (2026-10-17):

- `msearch.py` LeanFinder, query "Relative ordered simplicial join prism
  comparison inner anodyne inclusion and final pushout": eight hits, including
  individual two-dimensional horn pushouts, `modelCategoryQuillen.J`, and
  subcomplex bicartesian-square/multicoequalizer interfaces. None states the
  relative join-prism comparison; their displayed signatures were inspected.
- `msearch.py` Loogle, query `"innerAnodyneExtensions", "join"`: zero hits.
- `msearch.py` grep, query `prism|orderedJoin|join.*prod`, subdirectory
  `AlgebraicTopology`: zero hits.
- `msearch.py` LeanSearch, query "The relative ordered join prism comparison is
  inner anodyne before its final join pushout": eight hits, all generic pushout
  comparison, lifting-property, or relative-cell-complex interfaces. None
  defines the two subcomplexes or states this comparison.
- `rg` of project `lean/Sheaf`, upstream `WeilConjectures`, and Mathlib for the
  chosen helper/theorem names: no collision. Searches for the item id and
  `relativeJoinPrism`, `relative_join_prism`, `JoinPrism`, and `join.*prism`
  found only the different interval-to-right-cone prism and its consumers.
  Those map `K × Δ¹` into `K ⋆ Δ⁰`; they do not state the comparison here.
- `rg` for ordered joins found the existing `orderedJoinFunctor` and pure-block
  inclusions, which this delivery reuses. `rg` for `innerAnodyneExtensions` found
  Mathlib's class and its small-object/weak-saturation characterization, which
  this delivery reuses. The upstream name table had no ordered-join or prism
  comparison match. These are searches for an existing statement and reusable
  constructions, not claims that the underlying simplicial primitives are absent.

Source check: opened the official
[Higher Algebra PDF](https://people.math.harvard.edu/~lurie/papers/HA.pdf), proof
of B.1.9, printed pp. 1478--1480, especially the displayed threshold filtrations
in (B1 prime)/(C2 prime), the intermediate inner-anodyne join attachments, and
the final `i=m` attachment. The node explicitly states a relative generalization;
its supplied eight-step degreewise proof treats arbitrary `A ⊆ B` and is recorded
in full in the theorem docstring. No source correction is needed.

Validation: the prescribed `scompile.py Q34 lem-coef-relative-join-prism-comparison`
compiled both its sandbox and final module-path forms cleanly, without errors
or warnings. The initial elaboration issue in the product-category morphism was
fixed by giving its source and target explicitly, and the Cartesian projections
by opening their owning namespace. No source outside this item's sandbox was
edited. The required delivery dry run follows this report.


## Second reading by Q34

I independently read the base node, the sandbox node and entire Lean module,
`coord/brief-stage2.md`, delivery-errors H, and the statements and source modules
of every statement/proof dependency. No repair note exists for this item. The
node has no `statement_change`; its mathematical statement and all eight proof
steps are unchanged. This reading found no mismatch requiring a Lean edit.
Only this report section was added.

Object, hypothesis and conclusion checklist, in the node's order:

1. **Small simplicial sets and degreewise operations.** `{B : SSet.{u}}`,
   `(A : B.Subcomplex)`, `(K : SSet.{u})`, and `universe u` introduce exactly
   the arbitrary small sets and genuine simplicial subset. Mathlib's Cartesian
   `⊗` has pairs of simplices degreewise; `Subcomplex` and `IsPushout` supply
   actual subobjects and the categorical pushout, computed degreewise in this
   presheaf category. Verdict: exact; there is no additional instance assumption.
2. **Ordered join with empty and mixed blocks.** Opened
   `Sheaf.AlgebraicTopology.PushoutJoinSaturation`: `joinAugmentation` is the
   right Kan extension giving one empty simplex, and `orderedJoinFunctor` is
   left Kan extension along ordinal concatenation. Its normal forms are the
   node's pure `B`, pure `K`, and mixed pairs, with the initial block first.
   Opened `JoinSliceRightFibration`: `orderedJoinInl` and `orderedJoinInr`
   are convolution generators with the other block empty. These definitions
   require no quasicategory instance. Verdict: the same existing join and
   inclusions, with no private replacement or strengthened hypotheses.
3. **Nonnegative dimension and empty zero boundary.** `(m : ℕ)` includes zero.
   Opened Mathlib `Boundary.lean`: `boundary_zero` states `boundary 0 = ⊥`.
   Verdict: exact, with no positive-dimension restriction.
4. **Ambient prism T.** Every helper uses
   `orderedJoinFunctor.obj (B, K) ⊗ Δ[m]`. Verdict: exactly `(B ⋆ K) × Δᵐ`.
5. **Relative domain D.** `relativeJoinPrismDomain A K m` takes the image of
   `orderedJoinFunctor.map (A.ι, 𝟙 K)` and its `unionProd (boundary m)`.
   Opened Mathlib `Monoidal.lean`: `S.unionProd T` is `(⊤.prod T) ⊔ (S.prod ⊤)`.
   Thus this is precisely the two specified subsets of T. Using the image
   expresses the actual join inclusion as a subcomplex, without a chosen map.
   Verdict: exact, including all pure K simplices when A is empty.
6. **Generated stage Z.** `relativeJoinPrismStage` is D joined with the supremum
   of `Subcomplex.ofSimplex s` over all n and qualifying s. Mathlib's
   `ofSimplex` is `Subfunctor.ofSection`, so this implements generation, not
   merely selection of vertices. The `∀ j b` implication tests whether vertex
   j of the first coordinate is `orderedJoinInl B K b`, and then requires
   `s.2 j < Fin.last m`. Disjoint pure-block normal forms make this exactly
   the test on all leading-block vertices, including repeated vertices.
   A pure final-block simplex satisfies the test vacuously. Verdict: exact.
7. **Relative product R.** `(A.unionProd (boundary m)).toSSet` and its `.ι`
   give `(A × Δᵐ) ∪ (B × ∂Δᵐ)` and its actual inclusion. The comparison
   square uses the join of that inclusion with `𝟙 K`. Verdict: exact.
8. **Canonical comparison and injectivity.** The existential φ has source
   `orderedJoinFunctor.obj (B ⊗ Δ[m], K)` and target T. Its
   `RelativeJoinPrismCoordinates` equations fix the first projection to the
   join of `fst B Δ[m]` with `𝟙 K`, fix the second projection on the entire
   leading factor to `snd B Δ[m]`, and fix it on the entire final factor to
   the constant simplex at `Fin.last m`. For any mixed simplex, restricting
   to a vertex lands in one of these two pure factors. Hence all vertex
   coordinates are forced. A simplex in Δᵐ is a monotone map of ordinals
   determined by those coordinates, so the equations uniquely specify the
   node's concatenation map in every degree. `Mono φ` is degreewise
   injectivity for presheaves of sets. Verdict: exact canonical map asserted
   to exist and be injective, rather than an assumed arbitrary map. No
   definition extracts data from this postponed existence theorem.
9. **First conclusion.** `innerAnodyneExtensions (Subcomplex.homOfLE
   (le_sup_left : relativeJoinPrismDomain A K m ≤ relativeJoinPrismStage A K m))`
   is precisely the displayed inclusion. Opened Mathlib's inner-anodyne
   `Basic.lean`: although its definition uses LLP against inner fibrations,
   `innerAnodyneExtensions_eq_retracts_transfiniteCompositions` identifies
   it with the retract closure of small transfinite compositions of pushouts
   of coproducts of inner horns. The isomorphism and closure instances give
   exactly the weak saturation requested. Verdict: exact.
10. **Final pushout.** `∃ ρ, IsPushout ρ (orderedJoinFunctor.map (R.ι, 𝟙 K))
    Z.ι φ` uses the correct four objects and arrow orientation. Its
    commutativity forces ρ to be the restriction of the specified φ along
    the join inclusion; since Z.ι is monic, that restriction is unique.
    Its universal property is the node's explicitly equivalent assertion
    that the canonical map from `Z ⨿[R ⋆ K] ((B × Δᵐ) ⋆ K)` to T is an
    isomorphism. Verdict: every clause present, with no extra conclusion.
11. **Quantifiers and exclusions.** All choices are quantified over arbitrary
    B, A, K, m before the existence of φ and ρ. The inner-anodyne conjunct
    is independent of these existential witnesses. There is no finiteness,
    nonemptiness, quasicategory, Kan, or extra universe-equality condition.
    A common arbitrary u represents all small inputs in any containing
    universe. Verdict: the node's full scope is retained.

Source check: independently opened the official
[Higher Algebra PDF](https://people.math.harvard.edu/~lurie/papers/HA.pdf),
the proof of B.1.9, especially (B1 prime), printed p.1478, and (C2 prime),
printed pp.1479--1480. The first specializes the leading block to the cone
point; the second uses a simplex and its boundary. Both use a threshold on
leading coordinates, a boundary alternative, inner-anodyne stages for i<m,
and a final join attachment at i=m. The source treats m=0 separately. The
node explicitly gives an agent-written relative generalization to arbitrary
A contained in B; I checked its eight-step argument rather than treating
that generalization as a literal theorem of the PDF. Its degreewise coverage
and intersection tests justify the generalization without the surrounding
marked-pattern hypotheses. The Lean states only this unmarked comparison.
There is no relevant Stacks tag and no inherited ring, characteristic,
Noetherian, or geometric hypothesis to import.

Dependency and proof-documentation check: opened the signatures and docstrings
of `EnhancedDiagramsCones.coneCategory`,
`SSet.rightAnodyneExtensions_pushoutProduct`, and
`SSet.Enhanced.anodyne_cocones`, as well as the join declarations above.
The product theorem uses a right-anodyne first input and arbitrary monic
second input. The first cocone clause uses the right-anodyne map in the
first join factor. This matches steps 4--6 after reversing vertex orders;
no extra fibrancy assumption is hidden there. The theorem docstring contains
all eight node steps, including coverage and the exact old-stage/final
intersection tests. Both proof modules are imported non-publicly. There are
no new definition nodes or dependency modules to audit under H12/H13.
The two added statement dependencies already own the reused join and block
inclusions and already have landed records, as permitted by §5.

Edge cases checked independently:

- m=0: the boundary is empty; no leading vertex can have coordinate <0.
  Only pure K generators qualify and they already belong to D. Thus Z=D,
  the first inclusion is an identity, and φ is the canonical isomorphism
  `(B × Δ⁰) ⋆ K ≅ (B ⋆ K) × Δ⁰`. R is `A × Δ⁰`.
- K empty: the join reduces to B, D=R, and the qualifying leading coordinates
  avoid m, so they are already in the boundary. Thus Z=R and the final
  attachment recovers the whole product.
- B empty: A is empty, but `A ⋆ K = K`, so D=Z=T. The top join inclusion
  is an isomorphism and the square is a pushout; φ itself need only be
  the constant-coordinate inclusion of K at m. No surjectivity is asserted.
- A=B: D=Z=T and the top arrow is an identity. A empty still contributes
  the pure K factor. These include the entirely empty case.
- B=K=Δ⁰, A empty, m=1: the intermediate attachment is the inner-horn
  triangle; the last join attachment supplies the other prism triangle.
  Degeneracies and repeated vertices satisfy the same test. There is no
  finite-dimensional restriction, and every u is bound explicitly.

Independent reuse searches (2026-10-17), using different phrases:

- LeanFinder via `msearch.py`: "Simplicial sets ordered concatenation join
  times standard simplex relative inner horn filtration pushout" returned
  eight hits: the three two-dimensional horn pushout facts, a strict Segal
  concatenation, horn inclusions/colimits, and Quillen J. Their displayed
  types do not state the relative filtration or final comparison.
- Loogle via `msearch.py`: `"SSet", "innerAnodyneExtensions"` returned twelve
  hits, including closure instances, the LLP/RLP characterization, and
  regular-pairing criteria. These confirm reuse of Mathlib's class; none
  states this join-prism result.
- LeanSearch via `msearch.py`: "The union in a simplicial join times a
  simplex is obtained by inner anodyne attachments and a final join pushout"
  returned eight hits. `Subcomplex.BicartSq.isPushout` is the generic
  subcomplex union interface, with other hits for horns, skeletons, standard
  simplices and realization; none is this theorem.
- `rg` across Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  for `join.*prism|prism.*join|relativeJoinPrism|relative_join_prism` found
  only different cylinder/cone constructions and consumers in the project.
  I opened `CoconeRestrictionInitial.rightJoinPrismSimplex`: it maps a
  cylinder K × Δ¹ into the right cone, so is not the present comparison.
  The upstream name table has no ordered-join/prism comparison match.
  Searches for ordered joins found the landed construction that this file
  correctly reuses. No definition or statement should be replaced by an
  `existing: true` record.

Validation: independently ran the prescribed `scompile.py` on the only
module. Both sandbox and final library-path forms compiled cleanly (2.3 s
and 2.4 s), with no diagnostics. Checked mechanically that `lean.statement`
equals the theorem signature verbatim; there is exactly one `sorry`, as the
entire named theorem proof; no line exceeds 100 characters. All three helper
definitions contain real data/formulas and each declaration has its source
and blueprint docstring. No unbound variable, local notation, private copy,
or file-local instance occurs. The sandbox node differs from the base only
in `lean` and the two permitted added landed `stmt_deps`. No statement
correction or citer audit is needed. No mismatch was found and no correct
Lean was rewritten. Delivery dry run and final push are performed below.
