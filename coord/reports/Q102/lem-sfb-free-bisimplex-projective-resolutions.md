## Worker report

The module `Sheaf.AlgebraicTopology.FreeBisimplexProjectiveResolutions` states this
node in five theorem declarations in namespace `AlgebraicTopology.FreeBisimplex`:
`diagram_projectivity`, `projective_resolutions`, `simplex_contraction`,
`product_contraction`, and `tensor_contraction`. All five proofs are `sorry`.
Every helper definition has real data. No node statement, dependency list, or
proof split changes, and no new or dependency node is needed.

Source read: `literature/stacks-project/simplicial.tex`, Tag 08Q3,
`example-simplex-contractible`, lines 4580–4609. It gives the last-vertex
contraction and explicitly discusses reversing it for the first vertex. As the
node says, this is motivation, not a citation for the whole representable and
tensor statement. The full ten agent-written proof steps of the current node
were read and distributed across the five theorem docstrings. Also read the
current blueprint under `literature/blueprint/latest/`,
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), the open direct image clause in the inherited ancestry. The
universal resolution calculation belongs to the intermediate DAG nodes, not to
an additional assertion attributed to that short blueprint paragraph.

Hypotheses and clauses, in the order of the node:

- Delta and I: `SimplexCategory × SimplexCategory` uses the existing category of
  nonempty finite ordered sets and monotone maps. All homological indices and
  simplex dimensions are `ℕ`, including zero. There are no extra hypotheses.
- Arbitrary containing universe: `universe u` and `AddCommGrpCat.{u}`. The indexing
  category is small in universe zero, so every universe u contains it. The
  `ULift` in `representable` raises arrow generators to u; it imposes no equality
  of universes. The covering index `(i : I) × F.obj i` is in universe u.
- E and R: E is literally the covariant functor category into abelian groups.
  `representable i` is `coyoneda.obj (op i)` followed by the existing type lift
  and `AddCommGrpCat.free`. Thus R_i(j) is the free abelian group on arrows i→j,
  with postcomposition as structure maps. `generator α` is its free generator.
  This reuses the free functor, rather than introducing another free-group notion.
- Abelian, pointwise kernels and cokernels: `diagram_projectivity` states
  `Nonempty (Abelian E)` and preservation of finite limits and finite colimits
  by every evaluation functor. In the functor category these are the canonical
  pointwise kernel/cokernel constructions. Its next clauses assert the actual
  detection statements `Epi f ↔ ∀ j, Function.Surjective (f.app j)` and
  `S.Exact ↔ ∀ j, (S.map evaluation).Exact`, so exactness is detected too.
- Natural generator bijection: for every i and F, the equivalence e has the
  stipulated formula `e f = f.app i (generator (𝟙 i))`. Its inverse satisfies
  `(e.symm x).app j (generator α) = F.map α x`. These formulas determine e
  uniquely and express the stated inverse, including its action on each basis
  arrow. They imply naturality in F by postcomposition, and in i by applying
  `F.map` to the indexing arrow; no arbitrary equivalence is substituted.
- Projectivity: `Projective (representable i)` is Mathlib's lifting definition.
  The finite-sum clause quantifies over `S : Type u` with `[Finite S]`, including
  the empty family. The canonical coproduct over all `(i,x)` is explicitly
  asserted projective, with an epic map a onto F. The formula for a sends its
  `(i,x)` identity generator to x. `EnoughProjectives E` is also stated.
- P and Q: `projective_resolutions` supplies actual nonnegative chain complexes
  and degreewise diagram isomorphisms `p n : P.X n ≅ R_(n,n)` and
  `q n : Q.X n ≅ totalTerm n`. `totalTerm n` is the coproduct indexed by all
  pairs `(a,b)` with a+b=n. This is the n+1 summand antidiagonal, not a completed
  product. Existence with these normalized isomorphisms expresses the prescribed
  complexes up to their canonical chain isomorphism; no data definition chooses
  an arbitrary resolution from a sorry theorem.
- P boundary: conjugating `P.d (n+1) n` by the term isomorphisms sends a generator
  α to the finite sum `∑ k : Fin (n+2), (-1)^k.val • generator ((δ k,δ k) ≫ α)`.
  This is alternating precomposition by the diagonal cofaces.
- Q boundary: `totalGenerator a b (a+b) rfl j α` fixes the named summand generator;
  its differential is exactly `totalBoundary a b j α`. That definition sums the
  first cofaces when `0<a`, plus `(-1)^a` times the second cofaces when `0<b`.
  `predecessorCoface` uses the existing coface and transports only equal natural
  number indices. In degree zero both branches return zero, as required.
- Augmentations: εP and εQ go to the constant functor with value `ULift ℤ` and
  send every degree-zero generator to `ULift.up 1`. The witnesses zP and zQ
  assert that they kill degree-one boundaries. They are not arbitrary arrows.
- Projective resolutions: every term of both complexes is asserted `Projective`;
  their augmented short complexes are `Exact`, their augmentations are `Epi`,
  and `P.ExactAt (n+1)` and `Q.ExactAt (n+1)` hold for every n. Thus every
  augmented position is covered, with no acyclicity assertion at unaugmented
  degree zero that would incorrectly kill Z.
- Evaluation on strings: for every p',q', the theorem gives chain isomorphisms
  from evaluated P to the existing `productChains p' q'`, and from evaluated Q
  to the existing `simplexChains p' ⊗ simplexChains q'`, lifted to abelian groups
  in u by `liftComplex`. The displayed formulas normalize their action on every
  generator α, sending it to the corresponding pair of standard-simplex strings
  or the pure tensor in its canonical `HomologicalComplex.ιTensorObj` summand.
  These are isomorphisms of complexes, not unrelated per-degree isomorphisms.
  Both respect augmentations by their normalization on every vertex generator.
- Repetitions retained: both imported complexes are Mathlib alternating-face
  complexes of free modules on all simplices. No normalized quotient is used.
- Product h: `prependString` inserts zero at the first position via
  `Fin.insertNth`; `productCone` extends simultaneous coordinate insertion
  linearly. `productProjection` sends every degree-zero pair to `(0,0)` and
  vanishes in positive degree, precisely eε in degree zero. Thus the chosen
  vertex map e is integral multiplication of that free basis vertex.
  `product_contraction` asserts d h = 1-E at zero, and d h + h d = 1-E at each
  successor degree, with the actual composable differentials written out.
- Single cones: `simplexCone`, `simplexProjection`, and `simplex_contraction p`
  give the identical construction for every p, hence for both p and q. The
  projection is eε at degree zero and zero elsewhere.
- Tensor H: `tensor_contraction p q` supplies maps H and E with formulas on all
  homogeneous pure tensors in the canonical total-complex inclusions.
  The formula for H is precisely `h_p u ⊗ v + (-1)^a E_p u ⊗ h_q v` in the two
  specified summands. The formula for E is precisely `E_p u ⊗ E_q v`.
  These formulas determine their data on generators uniquely; the theorem is
  not a choice of an unconstrained contracting homotopy. It asserts the
  contraction equation in degree zero and every successor degree.
- Surjectivity: `product_contraction` states surjectivity of the degree-zero
  product vertex augmentation; `tensor_contraction` specifies the total
  augmentation by ε(u⊗v)=ε_p(u)ε_q(v) and states its surjectivity. Each
  `simplex_contraction` also includes the single-simplex augmentation.
- Pointwise only: cones are defined for fixed p,q, with no naturality hypothesis
  or conclusion in these variables. The maps of resolutions and augmentations
  are natural transformations because they live in E.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, full class at lines 105–116; imported
  through `Mathlib.CategoryTheory.Abelian.FunctorCategory`.
- `lem-sfb-simplex-lattice-shuffle-boundary`:
  `Sheaf.AlgebraicTopology.SimplexLatticeShuffleBoundary`; the full module was
  read, including `AlgebraicTopology.SimplexLatticeShuffle.simplexChains`,
  `productChains`, `augmentation`, `simplexMap`, `productMap`, and the full
  signature/docstring of `shuffle_boundary_augmentation_naturality`.
  The three actual complex/augmentation definitions are reused unchanged.
  The shuffle theorem itself is not needed to state this resolution node.
- Proof dependency `lem-weil-pbc-abelian-presheaves-evaluation-exact` is a
  Mathlib leaf: `CategoryTheory.Abelian.functorCategoryAbelian` (full definition
  read at lines 96–99), the evaluation finite-limit/colimit preservation
  instances in `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` (225,319),
  and `ShortComplex.Exact.map` in `Mathlib.Algebra.Homology.ShortComplex.Exact`
  (227). The corresponding modules are public dependencies of the statement.
- Proof dependency `def-weil-pbc-free-module`: `Module.Free`,
  `Mathlib.LinearAlgebra.FreeModule.Basic`, full class and set-indexed equivalent
  read at lines 42–53. Imported without public as a proof dependency.
- Proof dependency `lem-weil-pbc-functor-abelian-colimits` is a Mathlib leaf:
  `functorCategoryAbelian` and `functorCategoryHasColimitsOfSize`, the latter
  read at lines 210–212 of `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`.
  The functor-category imports expose these existing constructions.
- Additional existing APIs were read rather than duplicated:
  `AddCommGrpCat.free` and its free/forgetful adjunction,
  `Presheaf.freeYonedaHomEquiv` (a coproduct-of-Z Hom equivalence, only part of
  the node and not an existing match for the entire statement),
  `CategoryTheory.Projective` and `EnoughProjectives`,
  `Functor.mapHomologicalComplex`, and `HomologicalComplex.ιTensorObj`.

Edge cases checked against the formulas: p=q=0 still retains the one repeated
simplex in each degree; the alternating boundary is zero in odd degrees and
identity in positive even degrees, and prepending gives the required cone.
At total degree zero both boundary contributions are omitted and the total
cone identity is dH=1-E. At horizontal degree zero only the first factor's
projection can contribute to the second cone term. At horizontal degree one,
E_p d=0 because the two vertices have opposite coefficients. At higher
horizontal degree the projection term vanishes. These are exactly the tensor
sign cases of proof steps 8–9. Empty finite sums are allowed by `[Finite S]`;
the zero diagram's cover has the zero element in each group but still maps
surjectively onto the zero groups. An initial minimum vertex is retained by
`prependString`, including another copy of zero. Noninjective monotone maps
are allowed in the indexing category. No cone naturality is silently assumed:
a map selecting vertex 1 need not preserve the chosen vertex 0.

Searches performed (actual wrapper log is `searches.jsonl` in the sandbox):

- LeanFinder: "Free representable abelian functors on the product simplex
  category diagonal and tensor projective resolutions with minimum vertex
  contracting homotopies" returned eight Dold–Kan normalization/denormalization
  declarations (`Abelian.DoldKan.N`, `Γ₀'`, `Γ₀.Obj.obj₂`, etc.); no complete match.
- Loogle: `"freeYoneda", "Projective"` returned zero hits.
- LeanSearch: "Free abelian representables in a functor category are projective
  and provide enough projectives" returned `Rep.free_projective`,
  `ModuleCat.projective_of_free`, `ModuleCat.instProjectiveObjFree`, and the
  generic `Projective`/`EnoughProjectives` interfaces. These address individual
  clauses or different categories, not the two specified bisimplex resolutions.
- Wrapper grep: `freeYoneda|ExtraDegeneracy`, subdirectory `AlgebraicTopology`,
  found `Mathlib.AlgebraicTopology.ExtraDegeneracy`; the introductory interface
  and construction source were inspected. Standard-simplex extra degeneracy
  does not state the diagonal and tensor resolution and sign formulas together.
- Direct `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, bisimplex, free Yoneda, product
  chains, and the proposed names found only the recorded shuffle module and
  other-category free Yoneda uses. The project's standard module-presheaf
  free Yoneda and the general Mathlib generator equivalence do not state this
  node. No declaration of the full node was found.

No statement dispute or source correction. `set_option autoImplicit false`
checks that every binder and universe is explicit. Server compilation through
`scompile.py` succeeded for the completed file; only expected sorry diagnostics
are permitted. The delivery dry run and push follow after this report.

## Second reading by Q102

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
