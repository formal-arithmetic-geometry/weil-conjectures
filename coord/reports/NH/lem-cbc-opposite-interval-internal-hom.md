## Worker report

The module `Sheaf.CategoryTheory.OppositeIntervalInternalHom` uses the recorded
statement dependency `Sheaf.CategoryTheory.EnhancedDiagramsCones`, specifically
`SSet.Enhanced.evaluation` and the Mathlib simplicial-set primitives imported by
that module.  It defines `SSet.Enhanced.rho`, the canonical pullback corner map
`Fun(I,E) -> Fun(I,B) ×_{ev_a,B} E`, by `pullback.lift`.  The theorem
`SSet.Enhanced.oppositeIntervalInternalHom` states the complete node assertion
with proof `sorry`.

The universe is an explicit `u`, and every simplicial set is `SSet.{u}`.  The
witness `R` is a family of isomorphisms
`((ihom Δ[1]).obj E).op ≅ (ihom Δ[1]).obj E.op`.  For the node's displayed
formula, the Lean binders `n m`, `α`, `i : [m] ⟶ [1]`, and
`θ : [m] ⟶ [n]` render its arbitrary simplex and both operators.  The local
terms `irev := SimplexCategory.rev.map i` and
`θrev := SimplexCategory.rev.map θ` render the two reversed operators, and the
equality
`((R E).hom.app (op [n]) α).app (op [m]) (Quiver.Hom.op θ)
(stdSimplex.objEquiv.symm i) = opObjEquiv.symm ((α.app (op [m])
(Quiver.Hom.op θrev)) (stdSimplex.objEquiv.symm irev))`
is exactly the coordinate formula, including the `opObjEquiv` identification.

The first endpoint clause is the Lean equality
`(R E).hom ≫ evaluation Δ[1] E.op 0 =
opFunctor.map (evaluation Δ[1] E 1)`, and the second is the same equality
with `0` and `1` interchanged.  Thus both evaluations are retained and the
endpoint exchange is explicit.

For every map `p : E ⟶ B`, the naturality clause is
`opFunctor.map ((ihom Δ[1]).map p) ≫ (R B).hom =
(R E).hom ≫ (ihom Δ[1]).map (opFunctor.map p)`.  This is the strict
postcomposition compatibility required by the node.

The pullback clause uses `IsPullback` with projections from the opposite of the
endpoint-zero pullback.  Its first projection is transported through `(R B).hom`
to the endpoint-one internal hom, while the second projection is transported by
`opFunctor.map`; the two maps into `B.op` are evaluation at endpoint one and
`opFunctor.map p`.  The final clause supplies an isomorphism `T` from that
opposite pullback to the endpoint-one pullback, characterizes both projections
of `T` by these equalities, and states
`opFunctor.map (rho p 0) ≫ T.hom = (R E).hom ≫ rho (opFunctor.map p) 1`.
This is the required identification of the two corner maps.

The helper `rho` has no postponed data: its map is a real `pullback.lift`, with
its compatibility proof discharged by the categorical naturality tactic.  The
main theorem has only the expected `sorry` proof.  No Kan condition, horn
filler, nonemptiness, or other extra hypothesis is present.  The empty and
singleton simplicial-set cases are included because `E` and `B` are arbitrary;
`p` may be an identity or any simplicial map, and `m`, `n` include zero.

The only statement dependency is:

* `def-cbc-enhanced-diagrams-cones` — module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declaration
  `SSet.Enhanced.evaluation` (with the same module also providing the internal
  hom and degreewise cone conventions).

Searches for an existing declaration were made before writing the module:

* `msearch.py ... leanfinder "opposite of simplicial internal hom on interval
  exchanges endpoint evaluations"`: hits included `SSet.op_map`,
  `SSet.op_σ`, `SimplexCategory.rev_map_apply`, and standard-simplex lemmas,
  but no interval internal-hom isomorphism or endpoint/corner theorem.
* `msearch.py ... loogle "SSet.opFunctorCompOpFunctorIso,
  SSet.op_map, CategoryTheory.expComparison"`: zero hits.
* `msearch.py ... grep "op.*ihom|ihom.*op|op.*internalHom|internalHom.*op"
  AlgebraicTopology/SimplicialSet`: only unrelated internal-hom lifting lemmas
  in pushout-product files.
* Direct `rg` in Mathlib found `SSet.opFunctor`, `SSet.op_map`,
  `SSet.opFunctorCompOpFunctorIso`, and `CategoryTheory.expComparison`; direct
  `rg` in the project found no declaration for this node.  Their signatures
  were read and none includes the displayed interval reversal, endpoint swap,
  and pullback-corner compatibility together.

No statement correction, new definition node, dependency module, or
`STATEMENT-DISPUTED` marker is needed.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
