## Worker report

The module `Sheaf.AlgebraicGeometry.AdequatelyAffineAffineTargetBaseChange` states
`CategoryTheory.adequatelyAffine_affineTarget_baseChange`, with exactly one `sorry`.
It defines nothing and proves nothing. The node's mathematical statement is unchanged.

Clause correspondence:

- A field k: `{k : Type u} [Field k]`, the recorded Mathlib `Field`.
- An affine k-scheme T: `(T : Over (Spec (.of k))) [IsAffine T.left]`.
  The object of `Over` includes its structural map to Spec k. Mathlib's
  `IsAffine` says the canonical map to Spec of global functions is invertible,
  equivalently the node's existence of an affine-spectrum presentation.
- Algebraic stacks U and V over k: the two `BasedCategory` binders over
  `Over (Spec (.of k))`, with `hU` and `hV : IsAlgebraicModuliStack ...`.
  Their morphism and object universes `v₁,w₁,v₂,w₂` are independent.
- k-morphisms f and h to T: the two `BasedFunctor` binders to
  `discreteModuli (yoneda.obj T)`. These preserve the map to the category of
  k-schemes and retain the fibred-groupoid data.
- Adequate affineness of f: `hf : ∃ hT, IsAdequatelyAffineMorphism f hU hT`.
  The existing predicate requires algebraicity proof arguments at both ends.
  The scheme target's proof is existentially bound together with the predicate;
  this adds no separate premise beyond saying f is adequately affine. Every
  scheme defines an algebraic stack. The predicate's proof arguments are
  propositionally unique. No replacement adequacy definition is introduced.
- The 2-fibre product is the existing `moduliTwoFiberProduct f h`, whose objects
  are the actual triples with a specified invertible comparison over an identity.
- Its projection to V is exactly `moduliTwoFiberSnd f h`, not an arbitrary map
  or a projection from a chosen equivalent replacement.
- Adequate affineness of that projection: the conclusion is
  `∃ hP : IsAlgebraicModuliStack (moduliTwoFiberProduct f h),
  IsAdequatelyAffineMorphism (moduliTwoFiberSnd f h) hP hV`.
  This binds the necessary algebraicity proof with adequacy, so the caller is
  never asked to assume algebraicity of the product. It is the ambient
  algebraicity implicit in the node's adequately-affine conclusion.
- No flatness, representability, or absolute-diagonal hypothesis appears on h,
  U or V. The qcqs conditions belonging to adequate affineness itself remain
  exactly those in the recorded definition.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, with its full descent, representable
  diagonal and smooth surjective atlas clauses (def-sfb-algebraic-moduli-stack).
- `Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism`:
  `CategoryTheory.IsAdequatelyAffineMorphism` (def-sfb-adequately-affine-morphism).
  Its source was also checked with `scompile.py --source` against the server.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids` (publicly exposed by
  these imports): `CategoryTheory.discreteModuli`,
  `CategoryTheory.moduliTwoFiberProduct`, `CategoryTheory.BasedFunctor`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`:
  `CategoryTheory.moduliTwoFiberSnd`. Added its already landed owning node
  `def-sfb-open-moduli-substack` to stmt_deps under brief-stage2 §5's permission
  to add landed statement dependencies. Only its existing projection is used.

The already stated proof dependencies are imported with ordinary imports:
`StackQcqsMorphism`, `StackQuasiCoherentAlgebra` and Mathlib's `Morphisms.Etale`.
AdequatelyAffineMorphism is a public statement import. The proof dependencies
lem-sfb-affine-target-adequacy-criterion, lem-sfb-algebraic-stack-fibre-products,
and lem-sfb-stack-affine-algebra-direct-image have no recorded declarations in
this checkout; none is needed to type the statement, and none is restated or
assumed as a new hypothesis. Their mathematical uses are retained in the full
five-step proof docstring for stage 3. No import cycle is introduced.

Source read: [Alper arXiv:1005.2398v3](https://arxiv.org/pdf/1005.2398v3),
Proposition 4.2.1(6), printed p.21 (PDF page index 20), together with its proof.
It applies to a 2-cartesian square with arbitrary base-changing stack and assumes
quasi-affine diagonal only on the old target. An affine k-scheme has affine
relative diagonal, so the node is the stated specialization. Remark 4.2.2's
abelian-variety counterexample has target BA, excluded by this affineness premise.

Edge cases checked before drafting: h the identity; empty V or U; empty affine T
(the zero ring is allowed for affine targets, while k is still a field);
non-flat maps induced by R → R/I including nilpotent ideals; stack V = BG with
nonrepresentable map to Spec k; arbitrary field characteristic; unequal endpoint
universes. The binders impose no nonemptiness, flatness, representability,
finite-type, Noetherian, finite-generation, or diagonal restrictions. The proof
uses arbitrary algebras on the product, not just algebras descended from U.

Searches for an existing statement (all through the prescribed msearch.py wrapper,
with its log in searches.jsonl):

- LeanFinder: `An adequately affine morphism of algebraic stacks to an affine
  scheme stays adequately affine after arbitrary stack base change`.
  Eight hits, all scheme-level affine/base-change results; no stack adequacy.
- Loogle: `"AlgebraicGeometry", "IsAffineHom", "baseChange"`.
  One hit, `AlgebraicGeometry.isAffineHom_isStableUnderBaseChange`, which is
  affine scheme morphisms, not adequate affine stack morphisms.
- LeanSearch: `Adequate affineness is stable under arbitrary base change over an
  affine scheme target`. Eight hits about scheme affine morphism properties or
  ring base change, none this theorem.
- Mathlib grep: `adequat|Adequately`. Nine irrelevant word matches, no adequate
  affineness definition or theorem.
- `rg -n 'adequat|Adequately|lem-sfb-adequately-affine-affine-target-base-change'
  lean/WeilConjectures lean/Sheaf`: upstream has no match; Sheaf has the adequate
  affine definition, adequate-moduli-space definition and unrelated consumers,
  but no base-change statement. A separate item-id search upstream has no match.
- `dag/lean_names_upstream.json` and source searches for adequate-affine and
  algebraic-stack fibre-product declarations found no existing theorem.
- Searched the recorded second projection in the project, opened its full
  signature and construction in OpenModuliSubstack, and reused it.

Validation: scompile.py compiled both sandbox and actual library module names
cleanly (10.7 s and 4.3 s respectively). The initial missing-projection diagnostic
was repaired by importing its existing owning module. No new nodes, dependency
repairs, disputed statements, or source-based statement corrections are needed.

## Second reading by Q63

Reopened the node and final module and checked each binder and conclusion again.
This is a self-rereading: the dispatcher's explicit instruction prohibits starting
other agents, and the maintainer performs the independent delivery review.

The field and affine scheme are explicit; both algebraic stacks and both maps
are over the same Spec k; all four stack universes remain separate. The hf
existential packages exactly the recorded adequately-affine predicate and its
scheme-target proof argument. The conclusion uses the actual second projection
and supplies product algebraicity itself. There is no added h or diagonal
hypothesis. The full arbitrary-algebra power-lifting condition comes from the
existing definition, not a new surrogate. The five natural-language proof steps
match the node's five steps. The only discrepancy found on first compilation
was import visibility of the second projection; the owning public import and
its landed node dependency were added. No mathematical clause changed.
