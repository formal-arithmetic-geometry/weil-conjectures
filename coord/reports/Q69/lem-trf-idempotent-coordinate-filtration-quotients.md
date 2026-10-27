## Worker report

The module `Sheaf.RingTheory.IdempotentCoordinateFiltrationQuotients` states
`DirectSum.idempotent_coordinate_filtration_quotients`. Its only theorem proof is `sorry`.
The node is unchanged except for `lean`. There are no new nodes or dependency repairs.

Source read: `literature/stacks-project/algebra.tex`, Tag 058X,
`theorem-kaplansky-direct-sum`, especially the induced filtration on the summand
at lines 20489–20499 and coordinate construction at lines 20500–20533.
The docstring supplies all seven elementary proof steps of the node.

The two public helper abbreviations are real constructions belonging to this node:
`idempotentCoordinatePiece R J N e A` is exactly
`e.range ⊓ coordinateSubmodule R J N A`; `idempotentCoordinateQuotient R J N e A B`
is the quotient of the piece on `B` by the comap of the piece on `A` along its subtype.
The latter is exactly the recorded quotient-module convention for nested submodules.
They introduce no extra structure or selected mathematical data.

Hypothesis correspondence:

- `R : Type u`, `[CommRing R]`, `J : Type v`, `N : J → Type w`, the additive-group
  and module instances give precisely the commutative ring and family of modules.
- `hN` asserts, for every coordinate module, existence of an at most countable
  generating subset: `G.Countable ∧ Submodule.span R G = ⊤`. Span is generation
  by finite linear combinations, without countability of the ring or underlying module.
- `DirectSum J N` is the dependency's direct sum; `e` is linear and
  `he : e.comp e = e` is precisely idempotence. Its range is `P`.
- `κ : Ordinal.{t}` and `A : Set.Iic κ → Set J` give an arbitrary set ordinal and
  exactly the stages through `κ`. Its universe `t` is independent of all other universes.
- `hA : Monotone A`, `hzero`, and `htop` are the increasing family and its endpoints.
- `hlimit` states equality with the set union over all earlier stages at every
  nonzero limit. `Order.IsSuccLimit μ.val` excludes zero as required for ordinals.
- `hinvariant` states `e(M_A) ⊆ M_A` at every stage, element by element.
- `hcountable` is countability of the successor difference, for every `α < κ`.

Conclusion correspondence:

- The first conjunct is `P_α = (M_{A_α}).map e`, exactly `P_α = e(M_{A_α})`.
- The second is monotonicity of the pieces. The third and fourth give endpoints
  bottom and `e.range`. The fifth gives equality of underlying sets with their
  earlier-stage union at every nonzero limit, rather than just equality with a supremum.
- At each successor, `hle` names the already asserted inclusion of the two pieces,
  and `r` is an R-linear map between them. Its value formula uses Mathlib's actual
  coordinate-erasure map `DFinsupp.filterLinearMap R N (fun j => j ∈ A_α)`, followed
  by `e`. The formula is in the ambient direct sum to avoid a proof-dependent cast.
  The equation `r.comp (Submodule.inclusion hle) = LinearMap.id` is precisely that
  this specified map retracts the inclusion.
- `q` has domain the coordinate submodule on the successor difference and codomain
  exactly `P_{α+1}/P_α`. For every input `z`, its value clause supplies `p` in the
  successor piece with ambient value `e z` and asserts `q z = mkQ p`. Thus the map
  is the canonical `z ↦ e(z) + P_α`; it is not an arbitrary surjection or a stronger
  assumption. Existence of `p` is asserted, so the formula is not vacuous.
- `Function.Surjective q` gives the claimed surjectivity.
- The universal `G` clause assumes countability and spanning only for coordinates
  in the difference. The set inside `q '' ...` is exactly all canonical coordinate
  inclusions `lof R J N j g`, viewed in the domain of `q` through subtype equality.
  It asserts both countability and full span of their images, for every such choice.
  `G` is syntactically defined on all of `J`, with no condition outside the difference;
  any family on the difference extends by the empty set outside it. This renders
  exactly the original quantification and does not restrict the generating subsets.
- The final existential `S` explicitly states countable generation of each quotient.
  No condition that `e` commutes with coordinate erasure appears anywhere.

Dependency declarations read and used:

- `def-trf-coordinate-submodule`: `Sheaf.RingTheory.CoordinateSubmodule`,
  `DirectSum.coordinateSubmodule`, full construction with coordinates vanishing off `A`.
- `def-weil-pbc-direct-sum-modules`: recorded Mathlib match,
  `Mathlib.Algebra.DirectSum.Basic` and `.Module`: `DirectSum`, its module instance,
  `DirectSum.lof`, `DirectSum.component`, `DirectSum.induction_on`.
  The statement uses `DirectSum`, its instances and `lof`; finite-support induction
  and componentwise operations are the indicated proof route.
- `def-weil-pbc-quotient-module`: recorded Mathlib match,
  `Mathlib.LinearAlgebra.Quotient.Defs` and `.Basic`: `Submodule.hasQuotient`,
  `Submodule.Quotient.module`, `Submodule.mkQ`, `Submodule.mkQ_surjective`,
  `Submodule.ker_mkQ`. The quotient and map use precisely these constructions.
- Additional existing Mathlib operations: `DFinsupp.filterLinearMap`, `Submodule.map`,
  `Submodule.comap`, `Submodule.inclusion`, `Submodule.span`, `Set.Countable`,
  `Ordinal`, and `Order.IsSuccLimit`.

Edge cases checked mathematically before and during the statement pass:

- `J = ∅`: the direct sum and every image piece are zero. The statement permits
  any admissible `κ`; all quotient claims reduce to the zero module.
- `κ = 0`: the two endpoint assumptions force `J = ∅`; there are no successor
  clauses and no nonzero limit clauses. No nonemptiness assumption was introduced.
- Zero summands and the zero ring are allowed. `htop` concerns the coordinate index
  set itself, so zero summands do not accidentally cause premature exhaustion.
- `e = 0`: all image pieces and quotients vanish. `e = id`: these are the original
  coordinate pieces with coordinate-erasure retractions.
- Empty successor difference: its coordinate submodule is zero, the displayed image
  generating set is empty, and the quotient is zero. Empty generating subsets of
  zero coordinate modules are accepted.
- Noncommuting test over `ℤ²`: `e(x,y) = (x+y,0)` is idempotent and preserves the
  first-coordinate submodule, but does not commute with projection onto it.
  The formula `e π_A` still retracts the image piece as claimed.
- At a nonzero limit an empty support is handled at stage zero. Nonempty finite
  support is handled by the maximum of finitely many earlier stages.
- The ring, coordinate set, coordinate modules, and ordinal have independent universes.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder` query: “An idempotent on a direct sum has split invariant
  coordinate filtrations and countably generated successor quotients”. Eight hits,
  including `DirectSum.idempotent`, `DirectSum.decompose_eq_mul_idempotent`,
  `IsModuleFiltration`, and `Ideal.Filtration.Stable`; none gives this statement.
- `msearch.py ... loogle` query: `LinearMap, IsIdempotentElem, Submodule`. Twelve hits,
  including `LinearMap.IsIdempotentElem.mem_range_iff` and projection/complement
  lemmas, but no coordinate filtration or countable quotient-generation assertion.
- `msearch.py ... leansearch` query: “idempotent invariant coordinate filtration split
  retraction countably generated successor quotient”. Eight hits concerning categorical
  splitting, filters and measurable filtrations; none matches this algebraic statement.
- `msearch.py ... grep` query: `idempotent|filtration|CountablyGenerated`, restricted
  to `LinearAlgebra`. Hits in Projection, Trace, Hadamard, WithConv and Span/Basic
  concern individual projections and not this transfinite statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for `coordinateSubmodule`,
  idempotent/filtration combinations and countable generation found the existing
  coordinate submodule and adjacent support/closure/transfinite-construction lemmas.
  `ProjectiveKaplanskyDirectSummand` states the later decomposition, not this lemma.
- `rg` for the exact node id in `lean/WeilConjectures` returned no hit. Name searches
  for all three new declarations in the project, Mathlib and `dag/lean_names_upstream.json`
  found no existing full-name declaration.

Validation: `scompile.py Q69 lem-trf-idempotent-coordinate-filtration-quotients` compiled
both the sandbox probe and the final library module successfully, without warnings.
An initial compile exposed an ordinal-zero elaboration ambiguity and an inferred ambient
rather than subtype binder for `z`; both were made explicit before the passing compile.
No statement dispute or node correction is needed.

## Second reading by Q69

I reread the node, Tag 058X and the final file in a separate pass. This is a worker
self-check; the dispatch forbids starting other agents, and the maintainer supplies
the independent review after delivery. The source's intersections, endpoints, limit
unions, retraction formula, quotient surjection, arbitrary chosen generator images,
and countable-generation conclusion are all present as detailed above. The quotient
comap is along the successor piece's subtype, so it is a submodule of the correct
numerator. The generator set is the image of genuine coordinate inclusions in the
new-coordinate domain. The existential retraction and quotient maps have explicit
value formulas determining them, with existence of each subtype representative
included. No commutation, freeness, projectivity, countability of the ring, strict
increase, or nonempty increment was added. This pass required no further changes.
