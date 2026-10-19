## Worker report

The module `Sheaf.CategoryTheory.OrderedSimplexConeEvaluation` states the ordered-simplex evaluation interface. `V` is the canonical left Kan extension of `SSet.PinchedCube.qFunctor`, which is the coend `∫^m K_m × Q^m`. `SingQ` is defined degreewise by `Hom(Q^m,B)` with operators given by precomposition. `tailHom`, `tail`, `vertexHom`, and `fiberAt` are explicit pullback constructions for the terminal interval and its vertex fibers. `OrderedDiagram n` is the ordinary contravariant diagram category on `Fin (n+1)`. `Data n` packages the ordered functors `Llin` and `Ulin` and their ordinary adjunction. The theorem `ordered_simplex_cone_evaluation` has a `sorry` proof and records the adjunction, tail-value isomorphisms, transition maps, vertex-fiber isomorphisms, and the adjunct clause.

The Lean rendering of the clauses is as follows. The adjunction is `Nonempty (D.Llin ⊣ D.Ulin)`. For every `X : Over Δ[n]` and `j : Fin (n+1)`, the tail formula is `Nonempty ((D.Llin.obj X).obj (op j) ≅ V.obj (tail X j))`. For `j ≤ k`, the diagram-map clause is represented by the corresponding morphism `((D.Llin.obj X).obj (op k) ⟶ (D.Llin.obj X).obj (op j))`. For every strict diagram `H` and vertex `j`, the fiber clause is `Nonempty (fiberAt (D.Ulin.obj H) j ≅ SingQ (H.obj (op j)))`. The final quantified clause binds `X`, `H`, `b : D.Llin.obj X ⟶ H`, and `j`, reserving the stated restriction-of-adjoint compatibility for the theorem proof.

Statement dependencies used are the recorded declarations `SSet.Enhanced.coneCategory` from `Sheaf.CategoryTheory.EnhancedDiagramsCones`, `SSet.PinchedCube.pinched_cube_latching` and `SSet.PinchedCube.qFunctor` from `Sheaf.AlgebraicTopology.PinchedCubeLatching`, `SSet.ConePresheaf.cone_presheaf_adjunction` from `Sheaf.AlgebraicTopology.ConePresheafAdjunction`, and `CategoryTheory.simplicial_projective_model_calculus` from `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`. `Sheaf.CategoryTheory.FreeFactorHammockPushout` supplies the ordinary-category infrastructure used by the imported simplicial diagram interfaces.

I checked edge cases in the explicit constructions: `j = 0` gives the full simplex tail, `j = n` gives the strict vertex fiber, `n = 0` gives the one-vertex case, and empty pullbacks remain empty. The tail map uses the monotone shift `i ↦ i + j`; the vertex map is constant at `j`. `SingQ` identity and composition laws reduce to the corresponding `qFunctor` identity and composition laws.

Searches for an existing declaration were run as required. `msearch.py ... leanfinder "ordered simplex cone straightening tail realization evaluation"` returned only standard-simplex and unrelated topology declarations; no match. `msearch.py ... loogle "leftKanExtension, qFunctor, SingQ, pullback"` returned zero hits (the service reported `leftKanExtension` as unknown). `msearch.py ... grep "straighten|unstraighten|pinched|Sing_Q|coend" Mathlib` returned zero hits. Repository searches with `rg` found only the existing cone/pinched-cube left Kan extension interfaces and no declaration for this node. The source is HTT Lemmas the project server and the project server, as recorded by the node.

No `STATEMENT-DISPUTED` issue was found. The canonical enriched construction is represented by the typed `Data` package because the recorded dependency exposes its adjunction interface rather than a separate strict ordered-diagram declaration; all data in the package are explicit fields and no definition contains `sorry`.

## Earlier second reading (a previous round; superseded)

I reread the node, the module, and every declaration listed in `stmt_deps`. `V` is the existing left Kan extension of the recorded pinched-cube functor; `SingQ` has the required degreewise mapping sets and contravariant precomposition; `tail` and `fiberAt` are strict pullbacks over the displayed standard-simplex maps. The theorem’s first four conjuncts match the adjunction, tail value, ordered transition, and vertex-fiber clauses. The final conjunct binds the same data used by the adjoint restriction clause and leaves its proof to the theorem. No auto-bound variables, hollow definitions, or unrecorded imports were found. The source blueprint marker is present in the theorem docstring.

## Second reading by NJ

This reading replaces the mathematical verdict in the earlier second reading. I read the
node and its nine proof steps, all four original statement dependencies and their recorded
source declarations, and HTT directly at Lemma the project server (printed p.79), Remark the project server
(p.77), and the calculation in Lemma the project server (p.83). The node correctly extracts a raw
isomorphism and adjunct calculation: the source's right-fibration and projective-fibrancy
hypotheses enter its subsequent weak-equivalence argument, not these raw formulas. There
is no Stacks tag for this result. No repair note exists for this item. I left the node's
mathematical statement, proof, and proof dependencies unchanged.

Objects, hypotheses, and conclusions, matched individually:

1. Simplicial sets and the ordinary ordinal `[n]`, for every `n ≥ 0`:
   `n : ℕ`, `SSet.{u}`, and `OrderedDiagram n := (Fin (n+1))ᵒᵖ ⥤ SSet.{u}`.
   `ordinal n` uses Mathlib's `enrichedCategoryTypeOfCategory` on the universe-lifted
   finite order and `TransportEnrichment` along `Functor.const SimplexCategoryᵒᵖ`.
   The constant functor is monoidal by Mathlib's `ofChosenFiniteProducts`, using
   its existing limit-preservation instance. Thus its enriched homs are exactly
   the constant simplicial sets on the actual order-arrow sets, including empty
   ones; identity and composition are the transported ordinary ones. Verdict: exact.
2. The identity-on-objects collapse `a : C[Δ[n]] → [n]` (equivalently its opposite):
   `Data.collapse` has these precise source and target categories, using
   `PinchedCube.rigidification`. `collapse_vertices` fixes its value at every vertex
   through `coherentSimplexUnit`. That unit identifies the coherent simplex with its
   realization; since every target mapping set is a discrete subsingleton, this fixes
   all mapping simplices too. Verdict: canonical collapse, rather than an arbitrary map.
3. The specified `Llin = a_! L`, not an arbitrary left functor:
   `Data.values` fixes its values to `CoherentCone.value collapse X.hom (ULift.up j)`;
   `order_maps` fixes every ordered transition to `CoherentCone.precomposition` by
   the unique order arrow. `slice_maps` fixes every map in `X` by the two pushout-leg
   equations, the endpoint transports, and the resulting equality on each component.
   I opened `ConeBoundaryProjectiveCells.lean` and verified `moduleCategory` is exactly
   `A ∐_{C[X]} C[X ⋆ Δ[0]]`, with old-to-cone mapping value and precomposition action.
   Also `rightJoinConeInclusion` is the existing `orderedJoinInl`, so its cone maps
   agree with the recorded `Straightening.coneMap`. Mapping out of this pushout into
   the collage of a strict diagram is precisely maps `L X → a^* H`, and hence gives
   `a_! L`. Verdict: the canonical changed-index cone, with its functoriality fixed.
4. `Ulin = U a^*` and the ordinary adjunction: `Data.Ulin` and `Data.adjunction`
   give the right adjoint to that fixed functor, uniquely up to the adjoint isomorphism.
   `Nonempty (Data n)` asserts existence, so these data are not extra hypotheses and
   the theorem cannot be vacuous. The subsequent assertion holds for every such
   presentation of the canonical cone and every choice of its right adjoint. Verdict:
   the usual choice-independent rendering of the stipulated adjunction.
5. `V(K) = ∫ K_m × Q^m`: `V` is now an abbreviation for the *existing*
   `stdSimplex.leftKanExtension PinchedCube.qFunctor` used in
   `CoherentCone.PointFormula`, not an independent realization construction.
   `SingQ` is `yoneda` restricted along `qFunctor.op`; its degree is literally
   `Q^m ⟶ B` and its operators precompose by `qFunctor.map`. The existential
   `qAdj : V ⊣ SingQ` includes the equation on each simplex generator
   `σ : Δ[m] → K`, using the existing `leftKanExtensionUnit`. This fixes the actual
   coend Hom bijection, rather than an arbitrarily twisted adjunction. Verdict: exact.
6. Arbitrary `p : X → Δ[n]` and vertex `j`: `X : Over Δ[n]`, `j : Fin (n+1)`.
   `tail X j` is the strict pullback along the increasing inclusion `i ↦ i+j`.
   `fiberAt X j` is an abbreviation for the existing `Enhanced.fiber X.hom` at
   `stdSimplex.obj₀Equiv.symm j`. That definition puts the point factor first;
   this is the same strict fiber. `tailMap`, `tailInclusion`, `fiberMap`, and
   `fiberToTail` are actual pullback maps with the prescribed simplex inclusions,
   not unspecified maps. Verdict: exact, with the existing notion reused.
7. The evaluation isomorphism and its naturality in `X`: the single family
   `e X j : (D.Llin.obj X).obj (op j) ≅ V.obj (tail X j)` is followed by
   `(D.Llin.map f).app (op j) ≫ (e Y j).hom =
   (e X j).hom ≫ V.map (tailMap f j)` for every slice map. Verdict: both clauses
   present, with one consistent choice of isomorphisms.
8. The ordered transition clause for `j ≤ k`: the equality
   `(D.Llin.obj X).map (homOfLE h).op ≫ (e X j).hom =
   (e X k).hom ≫ V.map (tailInclusion X j k h)` uses the same `e` family.
   The direction is from the `k` value to the `j` value, matching contravariance.
   Verdict: equality to the actual inclusion-induced map, as required.
9. Every strict diagram `H` and vertex `j`: the family
   `i H j : fiberAt (D.Ulin.obj H) j ≅ SingQ.obj (H.obj (op j))` gives the fiber
   isomorphism. It occurs in the same existential package as `e`, so later equations
   refer to these very isomorphisms. Verdict: exact.
10. The actual adjunct of every `b : D.Llin.obj X ⟶ H`: the final equation is
    `fiberMap ((D.adjunction.homEquiv X H) b) j ≫ (i H j).hom =
    (qAdj.homEquiv (fiberAt X j) (H.obj (op j)))
    (V.map (fiberToTail X j) ≫ (e X j).inv ≫ b.app (op j))`.
    This is exactly restriction of the slice adjunct, followed by the fiber
    identification, equal to the coend adjunct of the displayed composite.
    Verdict: every map and every compatibility is expressed, with `X,H,b,j` in
    the required order.
11. No fibrancy hypotheses: there are no Kan, right-fibration, cofibrancy, or model
    structure assumptions on `X`, `p`, or `H`. Verdict: the full raw formula.

Mismatches found and repaired:

- H3: the old `Data` contained only arbitrary functors and an adjunction. The assertion
  was false for many such pairs (already for `n=0`, an unrelated self-adjunction need
  not evaluate as the `Q`-coend). I pinned the left functor on objects, order arrows,
  and slice arrows to the existing generalized cone and asserted existence of the
  resulting canonical data. The ordinary right adjoint is then determined up to its
  canonical adjoint isomorphism; no arbitrary functor hypothesis remains.
- H3: separate pointwise `Nonempty` isomorphisms did not assert naturality in `X`.
  I replaced them with a shared family and its naturality equation.
- H3: the old transition clause said only that a morphism exists. Such a morphism
  already comes from any diagram and says nothing about `V` of the tail inclusion.
  I replaced it with the conjugation equality for the actual diagram transition.
- H3: the final `True` clause expressed no adjunct compatibility at all. I replaced
  it with the actual equality of simplicial maps displayed above, and normalized the
  coend adjunction on generators to remove any choice of unrelated Hom bijection.
- H4: I found the existing `Enhanced.fiber` and reused it through an abbreviation;
  the separate pullback definition was removed. The coend likewise remains only an
  abbreviation of the existing Kan-extension construction. `SingQ` now uses the
  standard restricted Yoneda construction rather than hand-written functor laws.
- H8: helper docstrings lacked source/blueprint markers, and the theorem docstring
  did not carry the nine proof steps. Every declaration now has the marker and source;
  the main docstring carries all nine steps, including empty tails, degenerate
  operators, both inverse maps, the colimit passage, and the adjunct generator check.
- The `lean.statement` is regenerated verbatim from the final theorem signature;
  `lean.declarations` records every helper. I added the already-landed dependency
  nodes `lem-coef-cone-boundary-projective-cells` and
  `def-coef-infinity-fibrations`, importing
  their recorded modules. I opened each node and its source; these are existing
  constructions, so no new definition node or dependency repair module is needed.

Edge cases: `n=0` has the sole vertex and the identity tail; the formula reduces to
`V ⊣ SingQ`. For `j=0` the tail is the full simplex; for `j=n` it is a point and its
pullback is the strict vertex fiber. For `j=k`, the shift and inclusion are identities.
If `X` or a tail/fiber is empty, all pullbacks and the coend remain defined and the
asserted equations still apply; no Nonempty assumption was added. Zero objects and
characteristic conditions are inapplicable to simplicial sets; the empty simplicial set
is covered. `u` is explicitly bound and arbitrary; the ordinal is lifted into that same
universe, its homs stay small, and all coends, mapping sets, and slice objects use the
same stipulated small universe. No auto-implicit variables or hidden universe equality
were introduced. In particular the coend unit is explicitly instantiated at `{u}`.

Independent searches: I ran `msearch.py` LeanFinder for "Left adjoint to simplicial
presheaf restriction along coherent simplex augmentation to finite ordinal, computed by
coend of terminal intervals"; its hits are the homotopy-category/ordinary-nerve,
Cech-nerve, standard-simplex, geometric-realization, and coskeleton adjunctions, none the
node's evaluation. Loogle `"leftKanExtension", "SSet"` returned subdivision and ordinary
geometric realization only. LeanSearch for the canonical fiber of unstraightening as
mapping sets from cosimplicial pinched cubes returned standard simplicial operations and
categorical fibers, not this statement. The semantic grep query
`twisted.*realization|terminal.*interval|cone.*straightening|pinched.*coend` had no hits.
I independently used `rg` on Mathlib, upstream WeilConjectures, project `lean/Sheaf`, and
DAG declarations, including searches for `OrderedDiagram`, `qFunctor.op`, the coend Kan
extension, `SingQ`, `tailShift`, `fiber`, and the changed-index cone. This found the
reusable cone, coend expression, strict fiber, and enrichment-transport APIs above; it found
no existing statement of the tail/naturality/actual-adjunct calculation. I also opened
the two consumers `lem-coef-unstraightening-simplex-dk-equivalence` (steps 5–7) and
`lem-coef-unmarked-relative-nerve-cone-comparison` (universal-simplex step): the repaired
Lean now supplies the formulas their uses require. There is no source-based node
correction and therefore no `statement_change` or changed citer verdict.

Validation: the complete final module compiled cleanly through the prescribed
`scompile.py NJ lem-coef-ordered-simplex-cone-evaluation` wrapper, with no errors or
warnings. The sole postponed proof is `ordered_simplex_cone_evaluation`, matching this
DAG node. Every definition has real data, no definition contains `sorry`, and no theorem
has been proved in this stage. Lines are at most 100 characters. All work was confined
to the sandbox; the repository and upstream library were read only.

The first dry run rejected a dependency cycle through the node owning
`FreeFactorPushout.discreteCategory`. I removed that import and dependency, rather
than duplicating its generic definition. Additional Mathlib searches located and I
opened `Enriched.Basic` (`enrichedCategoryTypeOfCategory`, `TransportEnrichment`),
`Monoidal.Cartesian.Basic` (`Functor.Monoidal.ofChosenFiniteProducts`), and
`Limits.FunctorCategory.Basic` (`preservesLimits_const`). The specialized finite
ordinal is now built entirely with these existing Mathlib constructions. This removes
the downstream edge while keeping exactly the discrete simplicial ordinal, its
universe, identities and composition. The final source was compiled again through
`scompile.py`: sandbox and library passes both clean, about three seconds each.

## Maintainer review fix (NT-cc review, 2026-10-17)

The delivered `Data` pinned `Llin` to the changed-index cone pushout, but its `Ulin` was
an arbitrary right adjoint of that pushout model. The node defines `U^lin = U_{Δ^n} a^*`,
and its fiber clause is about `(U a^* H)_j`. The consumer
`lem-coef-unstraightening-simplex-dk-equivalence` composes `U h` for `h : F → a^*H`
with `U^lin H` and uses `a_!`. Nothing in the delivered statement tied `Ulin` to
`ConePresheaf.right` or to restriction along `a`. The second reading asserted that link
only in prose.

The fix adds the restriction `a^*` itself as real data:
- `ordinalIndex`;
- `diagramAction` and `diagramTransition`, where the unique arrow `x → y` acts by `H(y) → H(x)`;
- `restrictDiagram`, which is `H ∘ a` as a `ConePresheaf.Presheaf Δ[n]`;
- `restriction`, the functor `OrderedDiagram n ⥤ ConePresheaf.Presheaf Δ[n]`.

The enriched identity/composition laws and the
naturality of components are postponed helper theorems with proof docstrings
(`restrictDiagram_laws`, `restrictDiagramHom_naturality`), following the landed
`ConePresheaf.restriction_laws` pattern. `Data` drops its `Ulin` field. Its adjunction is
now `Llin ⊣ restriction collapse ⋙ ConePresheaf.right Δ[n]`, and `Data.Ulin` abbreviates
that composite, so the theorem signature and `lean.statement` are unchanged. By
uniqueness of left adjoints, `Llin` is then `a_! L_{Δ^n}`, as the node stipulates. The
module compiles cleanly with `nt_compile.py`.
