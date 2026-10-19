## Worker report

The module `Sheaf.CategoryTheory.CoherentVertexEquivalenceLifts` defines `vertexDiscrete J` as
`∐ (fun _ : J _⦋0⦌ => Δ[0])`, its canonical vertex inclusion by `Sigma.desc`, and
`coherentVertexLiftSpace`. The latter is the strict pullback of the initial-endpoint and
restriction maps on `(ihom Δ[1]).obj E`, where `E` and the target are the cores of the two
internal functor simplicial sets. This pullback is degreewise the maps
`h : Δ^n × Δ^1 → Fun(J,D)^≃` with initial value `d` and restriction `e pr₂`.

The theorem `coherent_vertex_equivalence_lifts` states, for a core vertex `d`, an edge `e`
whose initial endpoint is the restricted `d`, that the lift space has a vertex, is a Kan
complex, and is contractible. The `Nonempty` conjunct renders the nonempty clause;
`KanComplex` and `IsContractible` render the remaining clauses. A vertex of the pullback
has the terminal endpoint and equivalence path described in the node, and simplicial maps
of the pullback render all parameter restrictions.

The sole statement dependency is `def-cbc-enhanced-diagrams-cones`, used through
`SSet.Enhanced.core`, `coreMap`, `evaluation`, `diagramVertex`, `IsContractible`, and the
simplicial-set primitives. Proof-plan imports are `Sheaf.CategoryTheory.IsofibrationExponentiation`,
`Sheaf.CategoryTheory.CoreKanFibration`, Mathlib's
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct`, and
`Sheaf.AlgebraicTopology.KanQuillenModelRightProperCore`.

Edge cases checked: `J` may be empty (the coproduct is the initial simplicial set),
`J = Δ[0]`, and a discrete `J`; the coproduct and pullback remain well-typed. Dimension
zero is included by `Nonempty (L _⦋0⦌)`, while `KanComplex` uses all positive horns.
The terminal diagram is not fixed by the pullback.

Searches: the target's recorded LeanSearch, Loogle/LeanFinder, and Mathlib grep searches
were reread and had no exact match; `rg -l 'lem-coef-coherent-vertex-equivalence-lifts'
dag/nodes` found only this node and its one proof citer. `rg -n 'vertexDiscrete|coherentVertexLiftSpace'
lean/Sheaf` found no prior declaration. `scompile.py` compiled the module cleanly with no
errors or warnings.

## Statement corrected

The corrected wording binds `d` as a vertex of the core `Fun(J,D)^≃` instead of as a diagram
`d : J → D`. This is a clarification equivalent to the original: by the core definition of
`def-cbc-enhanced-diagrams-cones` every vertex lies in the core (its only edge is degenerate,
an equivalence with degenerate 2-simplex witnesses), so core vertices are exactly the diagrams
`J → D`. The delivered justification (that a diagram with a non-equivalence edge would make the
lift space empty) was wrong, because the edges of `d` as a diagram are not edges of the core;
the maintainer's reviewer replaced it in `statement_change.what`. The only citer,
`lem-coef-right-fibration-section-limit`, holds unchanged (`holds: true`).

## Second reading by N6

I reread the corrected node, its source place, the dependency declaration, and the citer.
The Lean binders introduce the simplicial sets `J,D`, the quasicategory instance, the core
vertex `d`, the core edge `e`, and the source equality. `vertexDiscrete` and
`vertexInclusion` render the displayed coproduct and restriction. The pullback definition
renders both equations in every simplicial degree. The theorem's three conjuncts render
nonemptiness, Kan filling, and weak contractibility, and the pullback leaves the terminal
diagram free. The correction is necessary and the citer remains valid.

Maintainer review fix (2026-10-18): `statement_change.what`, the citer note and `lean.note` were
corrected as described under "Statement corrected"; the Lean module is unchanged. A Lean check
(`x ∈ (core C).obj (op ⦋0⦌)` for every vertex `x` of every simplicial set `C`) compiled cleanly.
