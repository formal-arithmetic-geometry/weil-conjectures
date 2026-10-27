## Worker report

The module `Sheaf.AlgebraicGeometry.SingletonStackFiniteFieldHomeomorphism` states
`CategoryTheory.exists_singleton_stack_finite_field_homeomorphism`. Its only new declaration
is this theorem, whose whole proof is `sorry`. No definitions or dependency nodes are added;
the item changes only in `lean`.

Clause-by-clause rendering:

- The ground field is `(k : Type u) [Field k]`, with spectrum `Spec (.of k)`.
- The algebraic stack over that spectrum is
  `F : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))` with
  `hstack : IsAlgebraicModuliStack F`. Its étale-stack, diagonal and smooth-surjective-atlas
  conditions are precisely the recorded general algebraic-stack predicate, not a DM predicate.
- Its field-valued point quotient is the existing `ModuliPoints F`. The imported
  `moduliPointTopologicalSpace` instance is the smooth-atlas topology. The singleton hypothesis
  is `Nonempty (ModuliPoints F) ∧ Subsingleton (ModuliPoints F)`; nonemptiness is retained.
- Reducedness is `hreduced`: a smooth surjective scheme atlas `a` with
  `∀ x : U.left, _root_.IsReduced (U.left.presheaf.stalk x)`. These stalks are the local rings
  specified in the node; there is no independent reduced-stack notion to redefine.
- Local finite type over k is `hlft`: for each smooth surjective scheme atlas,
  `LocallyOfFiniteType U.hom`. This is local finite type on smooth charts. Testing atlases
  suffices: any other smooth chart may be adjoined to an atlas, and local finite type is
  local on the scheme source. No quasi-compactness or global finite-type hypothesis is added.
- A finite extension is the conclusion's `K : Type u`, `Field K`, `Algebra k K`, and
  `Module.Finite k K`. This means finite-dimensional as a k-vector space, with no finiteness
  assumption on the cardinality of either field and no separability assumption.
- The k-morphism pi is a `BasedFunctor F` to
  `discreteModuli (yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))`.
  In particular its codomain has exactly the specified k-structure; it is not an arbitrary
  unstructured spectrum or a point map supplied independently of the stack morphism.
- Every algebraic-stack base change is quantified as a general
  `G : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))` with `IsAlgebraicModuliStack G`, and
  every `g : BasedFunctor G` to that same discrete spectrum. Any stack mapping to Spec K
  acquires exactly this k-structure by composition. The test stack's category universes
  are independent of those of F; schemes and fields follow the existing scheme universe u.
- The conclusion is `IsHomeomorph (moduliPointMap (moduliTwoFiberFst g pi))`.
  The product has the test stack first, so it is `G ×_{Spec K} F`, with its actual canonical
  first projection to G. Swapping the factors identifies this with the node's
  `F ×_{Spec K} G -> G`; neither its underlying map nor its topology is arbitrary.
- No separatedness, representability of pi, inertia finiteness, inertia smoothness,
  neutral-gerbe or rational-point hypothesis occurs.

Dependency declarations read and used:

- Mathlib `Algebra.Field.Defs`: `Field` (the def-weil-field Mathlib match).
- Mathlib `AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `CategoryTheory.IsAlgebraicModuliStack`
  and `IsSmoothModuliAtlas`, including their actual space-base-change conditions.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `CategoryTheory.moduliPointTopologicalSpace`, as supplied by the recorded topology node.
  Its imported `DmStackMorphismProperties` supplies the existing `ModuliPoints` quotient
  and `moduliPointMap`, which work for the general stacks used here.
- Mathlib `AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
  The node's separate quasi-compact notion is not required for this local statement.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `CategoryTheory.discreteModuli`,
  `moduliTwoFiberProduct`, and `moduliTwoFiberFst`; their signatures and docstrings were read.
  This is publicly available through the algebraic-stack and topology imports.
- Mathlib `RingTheory.Finiteness.Defs`: `Module.Finite` renders the explicitly defined
  finite-dimensional extension in the node.

Available proof-dependency modules are imported privately:
`Mathlib.AlgebraicGeometry.Noetherian` (the recorded Mathlib match
`LocallyOfFiniteType.isLocallyNoetherian`),
`Sheaf.AlgebraicGeometry.SpaceFieldDiscretenessCriterion`, and
`Sheaf.AlgebraicGeometry.ReducedQuasiFiniteSpaceFieldDecomposition`.
The other three proof prerequisites (noetherian-singleton-gerbe,
gerbe-smooth-universal-homeomorphism, representable-lft-fppf-source-descent) have no Lean
records or Mathlib matches in the read repository; they are named in the full four-step
proof docstring but are not needed to elaborate the statement. No proof-only prerequisite
is restated. The source text of Stacks 06QK and 06R9 was read locally, including the proofs.
The atlas and decomposition modules' docstrings and full signatures were also read.

Edge cases checked before writing: the empty stack fails singleton nonemptiness;
Spec(k[e]/e²) fails reducedness; Spec K for a finite inseparable extension is permitted;
a positive-dimensional finite-type scheme fails the singleton condition; a non-finite
transcendental field spectrum fails local finite type. Classifying stacks with nontrivial,
possibly nonsmooth inertia and nonneutral gerbes are not excluded. The empty test stack
is included, as are the identity map and general nonrepresentable stack base changes.
The theorem asserts a homeomorphism after all base changes, not merely a homeomorphism
of the initial two singleton spaces.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder "A reduced algebraic stack locally of finite type over a field
  with one point maps universally homeomorphically to the spectrum of a finite field
  extension"`: 8 hits, all scheme facts (including `isField_of_universallyClosed`,
  `finite_appTop_of_universallyClosed`, and `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`),
  no general algebraic-stack statement.
- `msearch.py ... leansearch "Algebraic stack with singleton point space reduced locally
  finite type over field universal homeomorphism finite extension"`: 8 scheme-level hits,
  including `isReduced_of_isReduced_stalk`, no exact match.
- `msearch.py ... loogle '"AlgebraicStack", "Homeomorph"'`: 0 hits.
- `msearch.py ... grep 'AlgebraicStack|singletonStack|singleton_stack|residualGerbe'`: 0 hits.
- `rg` of `lean/Sheaf` and `lean/WeilConjectures` for singleton-stack, reduced-moduli and
  finite-field-stack variants found `SingletonStackFlatLfpFieldCover`, which is a different
  statement about a representable field cover with no finite ground-field extension or
  universal point-homeomorphism conclusion. Its full statement was read; it is not a match.
- Exact item-id and chosen-declaration searches in `lean/WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json` found no existing declaration.

There is no statement dispute or node correction. `scompile.py` compiled this delivered
file both as sandbox and as its library module, cleanly (4.7 seconds and 4.0 seconds).
Only the expected postponed theorem remains.

## Second reading by Q61

Author's separate second pass, not a claim of an independent worker review (the dispatcher
brief explicitly prohibits starting agents). With the node and final Lean signature open,
I rechecked every binder and the conclusion. Nonempty plus Subsingleton really means one
point; reducedness is on every stalk of the chosen smooth atlas; local finite type does
not accidentally impose quasi-compactness. `Module.Finite` concerns dimension, not finite
cardinality, and the target spectrum carries the very same `algebraMap k K`.
The quantification includes general algebraic stacks and every morphism to that spectrum;
the first-factor convention for the existing product API gives exactly the projection
to the test stack. No neutralization, inertia restriction, or separation was inserted.
All variables/universes are explicit and `autoImplicit` is disabled. No mismatch or
required change was found. Independent mathematical review is the maintainer's delivery
review, as specified in the dispatcher brief.
