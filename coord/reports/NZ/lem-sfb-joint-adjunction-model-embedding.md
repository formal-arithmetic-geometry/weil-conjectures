## Worker report

The module `Sheaf.CategoryTheory.JointAdjunctionModelEmbedding` states
`CategoryTheory.mono_pi_lift_adjunction_models` and the node's final specialization
`CategoryTheory.mono_pi_lift_adjunction_units`. Both proofs are exactly `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The abelian category A is `{A : Type u₁} [Category.{v₁} A] [Abelian A]`.
- The set I is `{I : Type w}`. No nonemptiness or finiteness assumption is made.
- The family of abelian categories is `{B : I → Type u₂}` with
  `[∀ i : I, Category.{v₂} (B i)] [∀ i : I, Abelian (B i)]`.
  Object, morphism, and index universes are explicit and independent.
- The functors F_i are `F : ∀ i : I, A ⥤ B i`, with
  `[∀ i : I, (F i).Additive]`. The additive structures come from the abelian categories.
- Preservation of kernels is the exact kernel-diagram hypothesis
  `[∀ (i : I) (X Y : A) (f : X ⟶ Y), PreservesLimit (parallelPair f 0) (F i)]`.
  This asks for kernels, without imposing preservation of all finite limits.
  Additivity supplies preservation of zero morphisms, so the mapped parallel pair
  is the kernel diagram of the image morphism.
- The right adjoints and specified adjunctions are `G : ∀ i : I, B i ⥤ A` and
  `adj : ∀ i : I, F i ⊣ G i`. Mathlib's adjunction contains unit and counit
  satisfying the triangle identities, and `Adjunction.homEquiv` is its specified
  natural Hom bijection. Its forward map is exactly unit followed by G.map.
- Joint detection is `hzero : ∀ N : A, (∀ i : I, IsZero ((F i).obj N)) → IsZero N`.
  It asks only for joint detection, not individual faithfulness.
- The fixed object is `(M : A)`. The local objects are `models : ∀ i : I, B i`.
- The specified local isomorphisms are `e : ∀ i : I, (F i).obj M ≅ models i`.
- Only the particular product is assumed to exist:
  `[HasProduct (fun i : I ↦ (G i).obj (models i))]`.
- The canonical u is `Pi.lift (fun i : I ↦
  (adj i).unit.app M ≫ (G i).map (e i).hom)`.
  `Pi.lift_π` gives exactly the prescribed components, with Lean's left-to-right
  composition convention. Its monomorphism property is `Mono` of this exact term.
- The final assertion is stated separately, with product of `(G i).obj ((F i).obj M)`
  and `Mono (Pi.lift ... (fun i : I ↦ (adj i).unit.app M))`. The explicit `f :=`
  supplies the product family, avoiding an elaboration issue between composite-functor
  object notation and the definitionally equal iterated object expression.

Dependency declarations read and used:

- `def-sp-abelian`: `Mathlib.CategoryTheory.Abelian.Basic`, `CategoryTheory.Abelian`.
  Its full class signature and docstring require preadditivity, finite products,
  kernels, cokernels, normal monos and normal epis, equivalent to the node's definition.
- `def-weil-pbc-additive-functor`: `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`,
  `CategoryTheory.Functor.Additive`, whose `map_add` is the required Hom additivity.
- `def-weil-category-product`: `Mathlib.CategoryTheory.Limits.Shapes.Products`,
  `CategoryTheory.Limits.piObj`, `Pi.π`, and `Pi.lift`; read also `Pi.map` and
  the product universal-property equations. Only the node's product construction
  is needed here, not its countable-products terminology.
- Proof dependency `def-weil-preadditive-category`:
  `Mathlib.CategoryTheory.Preadditive.Basic`, `CategoryTheory.Preadditive`, available
  through the abelian/additive-functor imports; its Hom groups and bilinear composition
  are exactly what the proof docstring uses.
- Additional existing Mathlib interfaces: `Mathlib.CategoryTheory.Adjunction.Basic`,
  `CategoryTheory.Adjunction` and `Adjunction.homEquiv`; and
  `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`,
  `CategoryTheory.Limits.KernelFork.mapIsLimit`, read to verify the exact
  interpretation of the kernel-preservation hypothesis.

Edge cases checked mathematically before writing:

- Empty I is allowed. The joint-detection premise then makes every object of A
  zero, so the arrow to the empty product is indeed monic.
- If M is zero or any model is zero, all terms remain defined and the kernel
  argument remains valid; no nonzero assumptions are present.
- Projections from a product of two abelian categories give a jointly detecting
  family with neither functor individually faithful. The hypotheses admit this case.
- Arbitrary infinite I is admitted whenever this particular product exists;
  no preservation of products or existence of all products is assumed.
- The identity-isomorphism specialization preserves exactly the stated product
  existence condition and reduces the components by functoriality.

Searches for an existing exact declaration (2026-10-21):

- `msearch.py ... leanfinder "A jointly zero detecting family of additive kernel
  preserving left adjoints embeds objects into products of right adjoints of
  isomorphic images"`: eight hits, mainly lifted adjunction constructions,
  abelianOfAdjunction and evaluation adjoints. None states this family theorem.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.Mono"`:
  six hits. `Adjunction.unit_mono_of_L_faithful` assumes a single faithful left
  adjoint, and `instMonoCoeEquivHomObjHomEquivOfReflectsMonomorphisms` assumes
  individual reflection of monos. Neither is the present statement.
- `msearch.py ... leansearch "Jointly zero detecting additive functors preserving
  kernels give a monomorphism into a product of right adjoint images"`: eight hits
  on kernel preservation, zero preservation and zero-kernel criteria, none exact.
- `msearch.py ... grep "mono.*(pi|product|unit)|joint.*(mono|zero)" CategoryTheory`:
  25 hits, none an exact declaration. Direct reading of
  `Adjunction/FullyFaithful.lean` and `Generator/Basic.lean` confirmed that
  `unit_mono_of_L_faithful` requires individual faithfulness and
  `ObjectProperty.IsCoseparating.mono_productTo` uses all maps to a coseparating class.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for joint zero detection,
  adjunction/product embedding, the node id, and the proposed names found no
  exact generic theorem or name collision. The upstream constructible-sheaf
  finite-pushforward embeddings are geometric specializations.
- Read the source blueprint's Essentially small paragraph in
  `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
  `sk-lem-brown-hypotheses/sk-lem-brown-hypotheses-small.proof.md` and all six
  proof steps of the node. This is the abstract kernel/adjunction tool isolated
  from the global local-model gluing argument.

There is no mathematical statement dispute. The first compile identified only
an inference issue for the product family in the specialization; explicitly
supplying that family repairs it without changing the mathematical statement.

## Second reading by NZ

I reread the node and both signatures after drafting. This is a second pass by
this worker, not a claim of an independent worker review; the dispatcher explicitly
forbids starting other agents, and the maintainer supplies the independent review.
The general theorem retains A, every B_i, arbitrary I, additive F_i, all-kernel
preservation, specified G_i and adjunctions, joint zero detection, fixed M,
prescribed models and isomorphisms, and only their product's existence.
Its conclusion concerns exactly the unit-then-G(e_i) map. The specialization
has the product of G_i F_i M and the actual units as components, with no extra
hypothesis. The proof docstrings cover kernel formation, adjunction naturality,
zero-image kernel uniqueness, joint detection, difference cancellation, and
identity specialization in the node's order. The only change found necessary
was the explicit product-family argument in the specialized `Pi.lift`.
