## Worker report

The module `Sheaf.AlgebraicGeometry.AffineRelationFlatLocalDescent` states
`AlgebraicGeometry.affineRelation_flat_local_descent`, with its sole proof `sorry`.
The helper `affineRelationTensorComparison` constructs the specified comparison by
`Algebra.TensorProduct.lift`; its data are fully defined. It is a canonical map,
not an arbitrary comparison supplied as a hypothesis. Both declarations belong to
lem-a1-affine-relation-flat-local-descent. The node statement is unchanged.

I read Stacks groupoids.tex, proposition-finite-flat-equivalence (03BM), especially
its second proof paragraph, together with the eight-step DAG proof. The theorem's
proof docstring reproduces all eight steps and identifies their dependency nodes.

Hypothesis and conclusion correspondence:

- The commutative rings are `(C A B : Type u) [CommRing C] [CommRing A]
  [CommRing B]`. The inclusion C -> A is `[Algebra C A]` and `hinj`.
  An injective structural homomorphism is the abstract-ring encoding of a subring.
- The map sigma is the structural map of `[Algebra A B]`.
  `[Algebra C B] [IsScalarTower C A B]` identifies its restriction to C with
  the C-structure on B. `tau : A →ₐ[C] B` has the same restriction. This encodes
  precisely two maps agreeing on C, with no injectivity condition on either.
- `hsurj` is surjectivity of `PrimeSpectrum.comap (algebraMap C A)`, exactly the
  point map of Spec A -> Spec C.
- `affineRelationTensorComparison (IsScalarTower.toAlgHom C A B) tau` is phi:
  its lift sends `a ⊗ a'` to sigma(a) tau(a'). This uses the existing algebra
  tensor product on the recorded module tensor product, rather than a second tensor.
- `n`, `f`, and `hspan` are the finite family generating the unit ideal of A.
  `hfree` states finiteness and freeness over `Localization.Away (f i)` of
  `LocalizedModule.Away (f i) B`. Since the A-action on B is sigma, this module
  is canonically B localized at powers of sigma(f i), as in proof step 4 of the node.
  Module localization is the existing fraction construction; its induced scalar
  action is that of the ring localization of B. No algebra-finite-presentation
  condition has been substituted for module finite presentation.
- `D : PrimeSpectrum C → Type v` supplies the local rings D_p. The AtPrime
  algebra instances give C_p -> D_p; the C-algebra and scalar-tower instances
  say the C-action is its composite with C -> C_p. `hfaithful` is exactly faithful
  flatness of C_p -> D_p. The family is supplied as input; no size-restricted
  existential assertion about finding extensions is added to the statement.
- `hlocal` states that `D p ⊗[C] A` is finite free over D_p (equivalently, by
  tensor symmetry, A tensor D_p). Its final conjunct says that the canonical
  base change `Algebra.TensorProduct.map phi (AlgHom.id C (D p))` is bijective.
  The canonical scalar reassociation identifies its source
  `(A tensor_C A) tensor_C D_p` with the node's
  `(A tensor_C D_p) tensor_D_p (A tensor_C D_p)`: it takes
  `(a tensor a') tensor d` to `(a tensor d) tensor (a' tensor 1)`, and the inverse
  multiplies the two D_p-coefficients. Under this identification the map is
  exactly phi_Dp. Bijectivity of this algebra homomorphism means it is an
  isomorphism, including the zero-ring case.
- The first conclusion is bijectivity of the same canonical phi.
  `Module.Flat C A` and `Module.FaithfullyFlat C A` express the two ring-map
  flatness conclusions for the structural map.
- `Module.FinitePresentation C A` is the module notion. Mathlib's
  `Module.FinitePresentation.exists_fin'` gives exactly finite m,n and linear
  maps C^m -> C^n -> A with exactness and a surjection to A, i.e. the stated
  sequence ending A -> 0; this class is equivalent to that presentation.
- The existential `(r, i, p)` with `p.comp i = LinearMap.id` says A is a direct
  summand of the finite free module `Fin r → C`, exactly the node's meaning of
  finite projectivity. A complement is the kernel of p. Rank zero is allowed.
- `(l, g)` with unit ideal span and the two local module predicates is exactly
  the finite standard-open free cover over C. The module localization of A is
  its ring localization at the image of g_i. Ranks may vary with i.
- `(Spec.map ...).IsFiniteLocallyFree` uses the recorded upstream definition:
  finite, flat, and locally of finite presentation. `Surjective` is scheme
  morphism surjectivity of this same q.
- The universal conclusion over all C-algebras T with open immersion
  Spec T -> Spec C covers every affine open, including nonprincipal affine
  opens and the empty open. Its inverse image is expressed as the categorical
  pullback. `Nonempty (... ≅ Spec (T ⊗[C] A))` gives the asserted identification;
  tensor symmetry identifies this coordinate algebra with A tensor_C T.
  `Module.Finite T (T ⊗[C] A)` states the required coordinate-ring finiteness.
- The last existential is an isomorphism Spec B -> pullback q q. Its hom
  followed by `pullback.fst` equals Spec sigma, and followed by `pullback.snd`
  equals Spec tau. Thus the map, and the order of both projections, are fixed.

Recorded statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; the canonical
  ring structure and comparison use `Mathlib.RingTheory.TensorProduct.Maps`,
  `Algebra.TensorProduct.lift` and `Algebra.TensorProduct.map`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`, whose full definition
  extends IsFinite, Flat, and LocallyOfFinitePresentation.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`; exposed
  through `Mathlib.AlgebraicGeometry.Pullbacks`, which supplies scheme pullbacks.

All stated proof dependency modules are imported privately. In particular these
include the standard-cover finite-presentation theorem, the upstream module
finite-presentation descent theorem, the standard free cover theorem, and the
finite-free algebra spectrum theorem. Mathlib proof matches are imported from
LocalProperties.Exactness, Flat.Localization, Flat.FaithfullyFlat.Basic/Algebra,
Flat.EquationalCriterion, Algebra.Module.Projective, and the scheme morphism
modules Finite, Flat, and FinitePresentation. No proof dependency was replaced
by another definition or omitted for an import cycle.

Edge cases checked before writing: C = A = B with both maps identity; zero rings
and empty spectra; n = 0 or l = 0 (a family generates the unit ideal only in the
zero ring); zero rank finite free modules; an arbitrary nonprincipal affine open;
and independently sized local extension rings D_p. There is no Noetherian,
positive-rank, nontrivial-ring, or fixed-rank assumption. With nonzero C, spectrum
surjectivity excludes A = 0. With C = 0, its unital algebras are zero, its spectrum
is empty, and the local conditions and conclusions have their expected meanings.
The theorem does not assume finite generation of A before it is descended.

Searches actually run through msearch.py with this group and item:

- leanfinder: `Descend an affine tensor comparison isomorphism and finite locally
  free module from faithfully flat extensions of every prime localization`:
  8 hits, including Module.mem_freeLocus_iff_tensor,
  Module.FaithfullyFlat.of_specComap_surjective, Module.Flat.of_flat_tensorProduct,
  and Module.FaithfullyFlat.bijective_of_tensorProduct. These are individual tools,
  not the complete statement.
- loogle: `Module.FaithfullyFlat, Module.FinitePresentation`: OK, 0 hits.
- grep: `affine.*relation|flat_local_descent|finite.*locally.*free.*descent`:
  3 irrelevant affine-space hits.
- leansearch: `faithfully flat descent of a tensor comparison and finite locally
  free module from local extensions`: 8 faithful-flatness/tensor descent hits,
  none for the complete theorem.
- rg over lean/WeilConjectures and lean/Sheaf for
  `affine.*relation|flat_local_descent|affineRelation|flatLocalDescent` found
  neighbouring relation-quotient modules but no such descent theorem.
- grep -rn for the exact node id in lean/WeilConjectures found no match.
- rg for both proposed declaration names in both library roots and
  dag/lean_names_upstream.json found no collision.

No new nodes, dependency repairs, statement correction, or statement dispute.

## Second reading by Q96

This is the worker's own second reading; the dispatcher explicitly prohibits
starting other agents. The maintainer performs the independent delivery review.
I reopened the node and the completed module, matched each clause as above,
and checked the order sigma/tau in the two projections. The use of sigma as an
algebra structure retains all pairs of maps in the node. The only changes made
in the first compile pass were correcting the AtPrime import to its actual
`Mathlib.RingTheory.Localization.AtPrime.Basic` module. Tensor reassociation,
tensor symmetry, and the module/ring localization identifications above preserve
the stipulated maps and actions. The direct-summand clause and arbitrary affine
open clause are both present explicitly; no hypothesis or conclusion was dropped.
