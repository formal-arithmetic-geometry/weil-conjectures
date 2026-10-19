## Worker report

The module `Sheaf.CategoryTheory.InnerFibrationEquivalenceOuterHornLift` states
`SSet.Enhanced.inner_fibration_equivalence_outer_horn_lift`. It uses the existing
simplicial-set primitives `SSet`, `SSet.horn`, `SSet.Λ`, `SSet.Δ`, and
`SSet.InnerFibration`, together with `SSet.Enhanced.IsEquivalenceEdge` from the
recorded dependency module `Sheaf.CategoryTheory.EnhancedDiagramsCones`.

For the node's hypotheses and clauses, the Lean rendering is as follows.

* “small quasicategories `E` and `B`” is rendered by the explicit universe
  `E B : SSet.{u}` and typeclass hypotheses `[Quasicategory E] [Quasicategory B]`.
* “`p : E → B` is an inner fibration” is rendered by the explicit map
  `(p : E ⟶ B)` and `[InnerFibration p]`; Mathlib's class is the right lifting
  property against every inner horn.
* For the initial outer horn, `n ≥ 2` is `(hn : 2 ≤ n)`, `β : Δ[n] → B` is
  `(β : Δ[n] ⟶ B)`, and `a : Λ[n,0] → E` is the displayed horn-map binder.
  The condition that `a` lies over `β` is the exact equality
  `a ≫ p = Λ[n, 0].ι ≫ β`.
* The edge `[0,1]` is the canonical `SSet.horn.edge n 0 0 1` (converted from its
  degree-one simplex to a map by `SSet.yonedaEquiv.symm`), and its image under
  `a` is tested by `IsEquivalenceEdge E`.
* The filler is `tildeβ : Δ[n] ⟶ E`, with both required equalities
  `Λ[n, 0].ι ≫ tildeβ = a` and `tildeβ ≫ p = β`.
* The dual final-horn clause repeats the same binders and equalities with
  `Λ[n, Fin.last n]`; its distinguished edge is the canonical edge from
  `n - 1` to `n`, and the same `IsEquivalenceEdge` condition and two exact
  filler equalities are required.
* The statement contains no Kan hypothesis on `B` and no extra outer-horn
  lifting hypothesis. The proof is `sorry`, as required for stage 2.

The dependency declaration used is:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declaration
  `SSet.Enhanced.coneCategory` (with the module's helper declaration
  `SSet.Enhanced.IsEquivalenceEdge`). The dependency node's recorded module
  supplies the equivalence-edge notion used in the statement; no private copy
  is introduced.

Edge cases checked: `n = 2` is admitted by `2 ≤ n`; the initial edge exists in
`Λ[2,0]` and the final edge exists in `Λ[2,2]`; `Fin.last n` and `⟨n-1, _⟩`
are well typed for every `n ≥ 2`; the horn edge cardinality side conditions
were reduced to `Finset.card_le_two.trans hn`; and no nonemptiness or Kan
condition was added. The identity map and maps to a terminal simplicial set
satisfy the shape of the statement, while the equivalence-edge hypothesis is
retained exactly as in the source.

Searches for an existing declaration were made with the required tools:

* `msearch.py ... leanfinder "relative outer horn lifting inner fibration equivalence edge"`:
  returned absolute horn-filling and all-horn fibration declarations, but no
  relative outer-horn theorem.
* `msearch.py ... loogle "SSet.Quasicategory, SSet.InnerFibration"`:
  returned Mathlib's inner-fibration/quasicategory declarations only; no match
  for this relative equivalence-edge statement.
* `msearch.py ... grep "outer.?horn|equivalence.*horn|InnerFibration"
  AlgebraicTopology/Quasicategory`:
  found only `SSet.InnerFibration` and inner-horn infrastructure.
* Repository `rg` searches for `outer horn`, `InnerFibration`, and
  `equivalence.*horn` found the separate absolute theorem
  `SSet.Enhanced.equivalence_iff_outer_horn_filling`, but no declaration with
  a map `p : E ⟶ B` and the two prescribed relative equalities.

## Earlier second reading (a previous round; superseded)

I reopened the node and the module. The two conjuncts match the two source
clauses: each binds `n ≥ 2`, a base simplex, and a horn map over that simplex;
each tests exactly the extremal edge for `IsEquivalenceEdge`; and each returns a
simplex whose horn restriction and projection to the base are the two stated
equalities. The initial edge uses vertices `0,1`, while the final edge uses
`n-1,n`. The `InnerFibration` and quasicategory hypotheses are explicit, and
no Kan or unrelated outer-horn assumption appears. The file compiles cleanly
with `scompile.py`; no mismatch was found.

## Second reading by NZ

I read the shared node and sandbox node, the complete sandbox module, and the
statement dependency `def-cbc-enhanced-diagrams-cones` with its actual module
`Sheaf.CategoryTheory.EnhancedDiagramsCones`. I also opened Mathlib's
`Quasicategory/Basic.lean`, `Quasicategory/InnerFibration.lean`, and
`SimplicialSet/Horn.lean`. There is no maintenance repair note for this item.
The sandbox node differs from the shared node only in `lean`; there is no
statement correction, new node, or dependency module in this delivery.

Source reading: the node cites **Kerodon**, not Stacks. I opened
https://kerodon.net/tag/01H0, Proposition the project server, including its full proof.
It assumes an inner fibration between quasicategories and an equivalence in
the total quasicategory, and produces a final-outer-horn filler over the
specified base simplex. There are no additional standing Kan, nonemptiness,
or size restrictions there. Reversing the simplex orders gives the initial
version. The node's six proof steps expand this proof. The source is online;
WANTED: an archived copy of Kerodon Proposition the project server and its linked results.

The node's object/hypothesis/conclusion checklist and its Lean rendering:

1. Small simplicial sets `E` and `B`: `{E B : SSet.{u}}`, for arbitrary `u`.
   Verdict: the same objects, with no finiteness restriction. Both belong to
   the node's ambient universe, as do the standard simplices and horns.
2. Both objects are quasicategories: `[Quasicategory E] [Quasicategory B]`.
   Verdict: exact. Mathlib's class quantifies over all inner horns in every
   dimension at least two; it imposes no outer-horn condition.
3. The specified simplicial map is an inner fibration: `(p : E ⟶ B)` and
   `[InnerFibration p]`. Verdict: exact. I read `innerHornInclusions`,
   `innerFibrations := innerHornInclusions.rlp`, and the class definition;
   this is precisely the right lifting property stated by the node.
4. Initial case: arbitrary `n ≥ 2`, base simplex, and initial horn map:
   `∀ (n : ℕ), (hn : 2 ≤ n) → ∀ (β : Δ[n] ⟶ B)
   (a : (Λ[n, (0 : Fin (n + 1))] : SSet.{u}) ⟶ E)`.
   Verdict: exact quantification, with the base simplex chosen before the
   filler and no replacement of that simplex.
5. The initial horn lies over that base simplex:
   `a ≫ p = Λ[n, 0].ι ≫ β`. Verdict: exactly the commutative lifting square.
6. Its edge `[0,1]` is an equivalence in `E`: `IsEquivalenceEdge E` applied
   to the image under `a` of `SSet.horn.edge n 0 0 1`.
   Verdict: exact. I read `horn.edge`: its underlying edge is
   `stdSimplex.edge n a b hab`, with those two ordered endpoints.
   `yonedaEquiv.symm` converts that simplex to its representing map;
   composition with `a` and `yonedaEquiv` returns its degree-one image.
   The dependency's `IsEquivalenceEdge` is explicitly the existence of an
   inverse and two 2-simplices whose long edges are the source and target
   identities. It is listed among that node's `lean.declarations`, so the
   recorded main declaration `coneCategory` is not mistaken for this notion.
7. Initial conclusion: `∃ (tildeβ : Δ[n] ⟶ E),
   Λ[n, 0].ι ≫ tildeβ = a ∧ tildeβ ≫ p = β`.
   Verdict: both required equalities, strict and for the original `a` and `β`.
8. Final case: the second conjunct binds the same `n`, `hn`, `β`, and horn
   map with index `Fin.last n`; its square is
   `a ≫ p = Λ[n, Fin.last n].ι ≫ β`.
   Verdict: exactly the final outer horn, without assuming a filler for any
   other outer horn.
9. The final distinguished edge is `[n-1,n]`: `horn.edge n (Fin.last n)
   ⟨n - 1, by omega⟩ (Fin.last n) (Fin.le_last _) ...`, followed by the same
   Yoneda conversion and `IsEquivalenceEdge E` test. Verdict: exact endpoints
   and the same inverse-triangle notion as the initial clause.
10. Final conclusion: `∃ (tildeβ : Δ[n] ⟶ E),
    Λ[n, Fin.last n].ι ≫ tildeβ = a ∧ tildeβ ≫ p = β`.
    Verdict: both exact equalities, with all quantifiers in the node's order.
11. No Kan condition on `B` and no unrelated outer-horn lifting assumption:
    neither appears in the signature. Verdict: exact. No arbitrary map,
    unmentioned instance, chosen filler, or equivalence of replacement
    objects has been supplied as a hypothesis.

Edge cases: `n = 0,1` are deliberately excluded by the source's `2 ≤ n`;
`n = 2` is included in both conjuncts. At `n = 2` the initial distinguished
edge is `01` in the horn consisting of `01` and `02`, and the final edge is
`12` in the horn consisting of `02` and `12`. The cardinality proofs use
only `card {i,a,b} ≤ 2 ≤ n`, not `3 ≤ n`. For all admitted `n`, `n-1` is
well defined, strictly below `n`, and `1 : Fin (n+1)` is the vertex one.
Empty quasicategories are allowed: no `[Nonempty ...]` appears; when the
horn cannot map to an empty total object, the corresponding universal
implication is vacuous as it is in the node. Identity maps, terminal bases,
and non-Kan quasicategory bases are included. There is no index set, ring,
scheme, characteristic, or additive zero object in this statement. The
universe `u` is explicit and arbitrary; there is no unbound variable or
additional smallness instance.

Independent duplicate searches (different wording from the worker), through
the prescribed `msearch.py NZ lem-cbc-inner-fibration-equivalence-outer-horn-lift`:

- LeanFinder: `An invertible edge is relatively cartesian and cocartesian
  for every inner fibration of simplicial sets`. Eight hits: Quillen
  all-horn fibrations, strict Segal objects, and absolute inner-horn filling.
  I read `CategoryWithFibrations.lean`: its lifting instance requires a
  Quillen fibration, a stronger condition than the node's inner fibration.
- LeanSearch: `Lift an extremal horn through an inner fibration over a fixed
  simplex if its last or first edge is invertible`. Eight hits, including
  `Quasicategory.hornFilling`, `KanComplex.hornFilling`, and general fixed-bottom
  lifting infrastructure. These do not assert the relative outer-horn result.
- Loogle: `SSet.InnerFibration, SSet.horn`. Zero hits.
- Tool grep in `AlgebraicTopology`:
  `invertib.*horn|horn.*invertib|outer.*lift|01H0`. Zero hits.
- Direct `rg` with
  `invertib.*horn|horn.*invertib|outer.*lift|cartesian.*equivalence|equivalence.*cartesian|01H0`
  on upstream `WeilConjectures`, Mathlib `AlgebraicTopology`, and the shared
  `lean/Sheaf`, and a declaration-name/tag search in `dag/lean_names_upstream.json`.
  I opened the nearest project candidates: `equivalence_iff_outer_horn_filling`
  has no specified map to a base; `invertible_prism_extension` is also an
  absolute extension statement; `IsCartesianEdge` and `IsCocartesianEdge`
  merely define the lifting predicates and do not assert that equivalence
  edges satisfy them. None is an existing declaration of this node.

Mismatch found and repaired: **H8**. The previous proof docstring gave an
unspecified successive-inner-horn argument, in the opposite order, instead
of the node's six-step proof. I replaced it with those six steps: the final
horn's ordered-join union (including `n=2`); relative coslice pullback and
its two left fibrations; construction of the edge with target `ρ(Y)`;
conservativity followed by a prescribed-target lift; unwinding both exact
equalities; and the initial-horn dual by order reversal. Both proof dependency
nodes currently have no Lean attachment, so their imports cannot yet be
added; their node ids are explicitly named in the docstring. The already
stated proof/statement dependency `EnhancedDiagramsCones` is imported.

No signature or natural-language node statement was changed. No definition
was added, hollow or otherwise, and the single theorem still has the whole
proof `by sorry`, as stage 2 requires. Both module and theorem docstrings
name the source and blueprint id. All Lean lines are at most 100 characters.
The node's `lean.statement` is byte-for-byte the signature before `:= by`.

Validation: reran `scompile.py NZ
lem-cbc-inner-fibration-equivalence-outer-horn-lift
lean/Sheaf/CategoryTheory/InnerFibrationEquivalenceOuterHornLift.lean` after
the repair. Both the sandbox probe and the library-path compile passed
with no errors or warnings (2.1 s and 2.2 s respectively), under the normal
60-second limit. This is the only delivered Lean file.
