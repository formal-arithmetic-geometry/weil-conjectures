## Worker report

The module `Sheaf.AlgebraicGeometry.GroupSpaceUnramifiedBaseLocus` states
`AlgebraicGeometry.AlgebraicSpace.groupSpace_unramified_base_locus`, with one
postponed theorem and no definitions or proofs. The natural-language proof in its
docstring follows all five DAG steps. The source was read in
`literature/stacks-project/spaces-groupoids.tex`, lemma-open-over-which-unramified-or-lqf
(Tag 0DSJ(1)), including the preceding identity test and base-change group lemma.
The node's statement is unchanged; two already-landed statement dependencies are added.

Clause-by-clause correspondence:

- Scheme S and spaces B,G over S: `{S : Scheme.{u}} (B G : AlgebraicSpace S)`.
- The morphism q: `(q : G ⟶ B)`.
- Multiplication over B, unit, inverse and group identities: `GrpObj (Over.mk q.hom)`
  in the explicit `Over.cartesianMonoidalCategory B.obj`. This is the category of
  fppf sheaves over the sheaf B. Its product is the sheaf fibre product, its terminal
  object is B, and its arrows are sheaf morphisms over B. `GrpObj` extends `MonObj`
  (multiplication, unit, associativity and unit identities) with inverse and both
  inverse identities. Because G and B are algebraic spaces these are exactly the
  algebraic-space group operations in the node. No commutativity is required.
- Local finite type: `hlft : MapIsLocally (@LocallyOfFiniteType) q`.
- Existence of an open base subspace: `∃ (V : AlgebraicSpace S) (v : V ⟶ B)` and
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) v.hom.hom`.
  This is the existing scheme-test definition of open immersion; open immersions
  are monomorphisms, so representatives have the same inclusion meaning as open
  subfunctors. No independent notion of openness is defined.
- Unramified restriction: `MapIsLocally (@IsUnramified)
  (enlargedFibreProductFst v q)`. The source is V ×_B G, canonically the node's
  G ×_B V with factors reversed, and the displayed arrow projects to V.
- Largest open, including every W: the first universal clause takes every open
  `w : W ⟶ B` with unramified restriction and concludes `∃ i : W ⟶ V, i ≫ v = w`.
  Uniqueness of this factorization follows from the open immersion being monic.
- Every arbitrary base change: `∀ (B' : AlgebraicSpace S) (h : B' ⟶ B)`.
  `enlargedFibreProductFst h q` is the projection B' ×_B G → B', the actual sheaf
  fibre product bundled as an algebraic space. Its group structure is pulled back
  by Mathlib's standard `Over.pullback`/`Over.grpObjMkPullbackSnd` construction
  (up to the symmetry of the two factors).
- The changed group is locally finite type: the first conjunct under this forall.
- Equality of base opens under base change: the next conjunct explicitly makes
  B' ×_B V admissible, and the final forall says that each open W over B' has
  unramified changed restriction iff it factors through B' ×_B V. Thus this
  pullback is the largest admissible open. This universal characterization is
  precisely equality as open subspaces, independent of chosen representatives.
  The implication specifying openness of W is outside the parenthesized iff.
- Unramified and locally finite type are tested etale locally on both source and
  target by the existing `MapIsLocally` applied to the two recorded scheme notions.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, and its sheaf/morphism convention.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`
  (the exact conjunction of local finite type and open diagonal).
- `Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion` and its public
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, closure used by the bundled fibre products.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`;
  its owning node `def-sfb-space-morphism-properties` is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `enlargedFibreProduct`,
  `enlargedFibreProductFst`; their owning node
  `def-sfb-space-sheaf-fibre-product` is added to stmt_deps. This existing:true definition node
  owns both plain definitions; the enlarged-ringed-site theorem is not used.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`: standard cartesian structure;
  `CategoryTheory.GrpObj` uses multiplication/unit/inverse group laws.
- Proof-only import: `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`,
  `CategoryTheory.stack_chartwise_smooth_etale_calculus`. The two other theorem
  proof dependencies (source locus and group identity test) have no Lean record,
  so their future module imports cannot yet be added. They are named explicitly
  in the proof docstring, with the unchanged DAG proof dependencies.

Edge cases checked: empty S and B (the empty open satisfies the characterization);
trivial group (all of B is the locus); an additive group over a field (no nonempty
unramified base open); an already unramified group (whole base); finite nonsmooth
groups in positive characteristic; disconnected bases; empty W; identity base
change; arbitrary nonflat/nonreduced B' and empty B'. There is no assumption on
characteristic, separatedness, flatness, quasi-compactness or commutativity. Every
scheme and algebraic space uses the same explicit u as the dependency interfaces.
The result agrees with the source; no STATEMENT-DISPUTED or statement correction.

Searches (2026-10-24):

- `msearch.py ... leanfinder` query "A group algebraic space locally of finite type
  has a maximal unramified open in its base compatible with base change": returned
  eight ring/scheme unramified-locus facts, no algebraic-space group base locus.
- `msearch.py ... loogle` query `"GrpObj", "Over"`: seven results, including
  `Over.grpObjMkPullbackSnd` and its unit/multiplication formulas. These provided
  the existing exact group/base-change encoding, not the requested theorem.
- `msearch.py ... grep` query `unramifiedLocus|GroupAlgebraicSpace|groupSpace`:
  nine ring-level unramified-locus hits, no requested statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `GroupAlgebraicSpace|groupSpace|unramifiedBaseLocus`: no existing theorem;
  the regular/commutative group-space modules concern groups over schemes,
  while `FreeFlatGroupSpaceQuotient` demonstrates the Mathlib group object over
  an arbitrary sheaf base. Reused the standard Mathlib cartesian structure directly
  to avoid importing that unrelated theorem. `rg` for `MapIsLocally` and
  `OpenSubspace` found the exact existing chart and open interfaces.
- `tools/blueprint_refs.py search 'group algebraic space'` supplied no additional
  interface. Existing DAG statement dependencies were read along with their Lean
  records; the two additional landed owners were also checked.

Validation: server single-file compilation through `scompile.py`; no local build.

## Second reading by NQ

A separate self-review pass reopened the node and final Lean file; no second agent
was started, as required by the dispatcher brief. The maintainer supplies the
independent review. The pass checked every binder and clause listed above against
Tag 0DSJ(1). It found and corrected two formulation issues before delivery:
(1) the base-changed open now explicitly satisfies unramifiedness, so maximality
cannot describe an inadmissible upper bound; (2) the parentheses now make openness
of W a hypothesis for BOTH directions of the factorization iff. Also removed the
unrelated free-quotient import by specifying the standard Mathlib cartesian
structure directly. The final theorem uses the original spaces rather than
scheme-only bases and quantifies over every h with no extra property. Its single
sorry is the whole theorem proof. There are no private definitions, local instances,
extra axiom assumptions, statement changes or missing mathematical clauses.


## Repair of returned head e4db86ade2f7

H2 repaired: replaced `lem-trf-space-enlarged-etale-ringed-site-model` in stmt_deps
with the already-landed definition node `def-sfb-space-sheaf-fibre-product`.
Read that node's statement and existing:true Lean record and reopened the two
recorded definitions in `EnlargedEtaleRingedSite.lean` at lines 230 and 236.
They are the actual sheaf pullback and its first projection; this theorem uses
those constructions and does not use the enlarged-ringed-site theorem conclusion.
The report's dependency attribution now names the definition owner.

Compared the retained delivery node with current main: only `lean` and the two
added statement dependencies differ. All other node fields remain identical.
The prescribed delivery wrapper rebases this repaired node and report on current
main. The Lean module remains byte-identical to the returned version (SHA256
`da79d08d6f6755a20da4081056ac3137829f3563d79f66faa559b67d299d6ccb`).
The reviewer accepted its mathematical clauses and noted explicit openness of the
pulled-back open as advisory; no Lean change is required for this H2 repair.
