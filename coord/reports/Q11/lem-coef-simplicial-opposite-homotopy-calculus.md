## Worker report

The module `lean/Sheaf/AlgebraicTopology/SimplicialOppositeHomotopyCalculus.lean`
states `SSet.simplicial_opposite_homotopy_calculus` with proof `sorry`.  It uses
Mathlib's existing covariant involution `SSet.opFunctor`/`SSet.op`, rather than defining a
second opposite construction.  All variables and universes are explicit.

The theorem renders the node statement clause by clause as follows:

1. `∀ K, Nonempty (opFunctor.obj (opFunctor.obj K) ≅ K)` records the covariant involution.
2. For every positive-dimensional horn (`1 ≤ n`),
   `Nonempty (Arrow.mk (opFunctor.map (horn n i).ι) ≅ Arrow.mk (horn n i.rev).ι)` is the
   standard simplex-reversal identification, sending horn `i` to horn `n-i`.
3. `KanComplex K ↔ KanComplex K.op` records preservation and reflection of Kan complexes.
4. `modelCategoryQuillen.J.rlp p ↔ modelCategoryQuillen.J.rlp (opFunctor.map p)` records
   preservation and reflection of Kan fibrations (the recorded Kan dependency identifies
   this right lifting class with Kan fibrations).
5. `innerFibrations p ↔ innerFibrations (opFunctor.map p)` records preservation and reflection
   of inner fibrations.
6. `K.Quasicategory ↔ K.op.Quasicategory` records the quasicategory consequence for the
   terminal map.
7. `Enhanced.IsWeakHomotopyEquivalence p ↔ Enhanced.IsWeakHomotopyEquivalence
   (opFunctor.map p)` records weak homotopy invariance and reflection.
8. The existential family `Φ A C : Fun(Aᵒᵖ,Cᵒᵖ) ≅ Fun(A,C)ᵒᵖ`, together with the two displayed
   equations for precomposition in `A` and postcomposition in `C`, records the natural
   internal-functor simplicial isomorphism and its compatibility with composition.
9. `Nonempty (hoFunctor.obj K.op ≅ Cat.of ((hoFunctor.obj K)ᵒᵖ))` records the natural
   homotopy-category comparison `h(Kᵒᵖ) ≅ (hK)ᵒᵖ`.
10. The two enlarged-universe `hoFunctor` test predicates are equivalent for `f` and
    `opFunctor.map f`; this is the categorical-equivalence preservation/reflection clause
    for arbitrary domains and codomains.
11. The final existential supplies one Joyal model witness `M`, with the exact recorded
    cofibration and categorical-equivalence test interfaces from
    `SSet.exists_joyal_model_structure`.  Its fibration and weak-equivalence classes are
    invariant under `opFunctor`.  The following pullback iso states degreewise pullback
    preservation, and the final implication states that fibrant vertices and Joyal-fibration
    legs of a cospan remain fibrant with Joyal-fibration legs after taking opposites.

The statement dependencies used are:

- `def-cbc-enhanced-diagrams-cones`: `SSet.Enhanced.*` definitions, internal functor
  simplicial sets, and weak homotopy predicates; imported publicly from
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
- `lem-coef-joyal-model-structure`: `SSet.exists_joyal_model_structure`; imported publicly
  from `Sheaf.AlgebraicTopology.JoyalModelStructure`.
- `lem-coef-kan-quillen-right-proper`: `SSet.KanQuillen.right_proper_kan_quillen` and the
  Kan model's generating horns; imported publicly from
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`.
- `def-coef-infinity-fibrations`: `SSet.Enhanced.cocartesianFibrationOver` interface and
  its public inner-fibration imports; imported publicly from
  `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`.

The stated proof dependencies with available modules are imported privately:
`Sheaf.AlgebraicTopology.OppositeSubdivisionKanZigzag` and
`Sheaf.CategoryTheory.RelativeConeEquivalence`.  The proof dependency
`lem-coef-infinity-cocone-opposite-join-functor` has no Lean record yet, so there is no module
to import; no definition or dependency repair was needed in this delivery.

Edge cases checked before writing:

- Horn reversal is restricted to `n ≥ 1`, while inner horns use Mathlib's positive-dimensional
  `innerFibrations` predicate; outer horns are included in the Kan-complex clause.
- The Kan and Joyal predicates quantify arbitrary simplicial maps, so neither endpoint is
  required to be fibrant or a quasicategory in those preservation/reflection clauses.
- `A`, `C`, and all cospan objects are arbitrary small simplicial sets; no nonemptiness or
  fibrancy hypothesis was added to the functor, hom-category, or pullback clauses.
- The fibrant-cospan implication explicitly includes all three vertices and both legs, and
  the pullback iso is stated for arbitrary cospans, including degenerate/empty degreewise
  pullbacks.
- The involution quantifies all simplicial sets, including the terminal and empty simplicial
  sets.

Searches made:

- `msearch.py ... leanfinder "simplicial opposite preserves Kan complexes inner fibrations
  quasicategories Joyal fibrations and categorical equivalences"`: returned Mathlib
  `SSet.opEquivalence`, `SSet.op`, `SSet.opFunctor`, `SSet.instQuasicategoryOfKanComplex`,
  and the Kan fibration interface, but no theorem for the full invariance package.
- `msearch.py ... loogle "SSet.opFunctor, SSet.Quasicategory, InnerFibration, KanComplex"`:
  zero hits (the tool reported `InnerFibration` as an unknown identifier).
- `msearch.py ... grep "opFunctor|opEquivalence|InnerFibration|KanComplex"
  AlgebraicTopology/SimplicialSet`: found the strict opposite and primitive horn declarations
  in Mathlib, with no full homotopy/Joyal invariance theorem.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/`, plus grep for the item id: found no
  existing declaration of this node or duplicate full theorem.  The only relevant existing
  declarations are the dependency interfaces recorded above.

No `STATEMENT-DISPUTED` flag or node correction is needed.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (delivery 2c2886e6b201, 2026-10-17)

The maintainer's independent reviewer changed the statement in four places. The rest of the worker's clause list still holds.

- Clause 1: `∀ K, Nonempty (K.op.op ≅ K)` is replaced by the natural form `Nonempty (opFunctor ⋙ opFunctor ≅ 𝟭 SSet)`. The node says the construction is a covariant involution, which a separate isomorphism for each object does not express. Mathlib's `SSet.opFunctorCompOpFunctorIso` witnesses this form.
- Clause 7 (`Enhanced.IsWeakHomotopyEquivalence p ↔ … (opFunctor.map p)`) is removed. The node's statement does not state it; it appears only in proof Step 2, quoted from `lem-coef-infinity-opposite-subdivision-kan-zigzag`. That node already states it, so keeping it here made the conclusion stronger than the node and stated the same result twice.
- Clause 8: the two naturality equations do not express "compatible with composition". A third equation is added, saying `Φ` intertwines `MonoidalClosed.comp A.op B.op C.op` with `MonoidalClosed.comp A B C` in each degree `n` (through `opObjEquiv`). This is node proof Step 4: the same `r_n` acts on both occurrences of the parameter.
- Clause 9: `∀ K, Nonempty (h(Kᵒᵖ) ≅ Cat.of (hK)ᵒᵖ)` is replaced by the natural isomorphism `Nonempty (opFunctor ⋙ hoFunctor ≅ hoFunctor ⋙ Cat.opFunctor)`. Step 5 needs naturality to identify the restriction functors.
- Pullback clause: `Nonempty ((pullback p q).op ≅ pullback (q.op) (p.op))` holds for any isomorphism of the objects and says nothing about the projections. It is replaced by `IsIso (pullbackComparison opFunctor p q)`, which says the opposite preserves the pullback.

The module also imports `Mathlib.CategoryTheory.Category.Cat.Op` publicly, for `Cat.opFunctor`. The fixed file compiles clean through `tools/nt_compile.py`: no error, no warning, 4.1 s.
