## Worker report

Stage 2, Q116, lem-sfb-flat-module-fibre-product-patching. The resumption explicitly
assigns stage 2; the original stage-1 split is already accepted on the current base.
No pre-existing sandbox module or active delivery was present. I preserved every
field of the accepted node and added only its Lean record. The sole module is
`lean/Sheaf/RingTheory/FlatModuleFibreProductPatching.lean`.

The declarations in namespace `ModuleCat.FibreProductPatching` state the two
clauses separately as `flat_patchedModule` and `exists_reconstruction_iso`.
Both proofs are `sorry`, as required for stage 2. The six supporting definitions
have real data built from existing scalar-extension adjunctions and pullbacks;
they introduce the canonical maps of this statement, not independent notions.

I read Stacks `more-algebra.tex`, Situation 08KH
(`situation-module-over-fibre-product`, lines 525ff.) and Tag 0D2I
(`lemma-flat-module-over-fibre-product`, lines 807ff.), including the proof.
I also read the accepted node's six proof steps, statement dependencies, proof
dependencies and stage-1 review. The source's second clause uses L where it means
L'; the accepted node has already resolved that typographical issue. The latest
blueprint unit and direct-image proof are background ancestry; this delivery
changes neither their route nor the accepted algebra argument.

Hypothesis and clause matching:

- `A A' B : CommRingCat` are arbitrary commutative rings. `b : B ⟶ A` is arbitrary,
  and `q : A' ⟶ A` has exactly `hq : Function.Surjective q`. There is no
  nontriviality, Noetherian, nilpotence, finite generation or presentation binder.
- `pullback (C := CommRingCat) b q` is R. I read
  `Mathlib/Algebra/Category/Ring/Constructions.lean:450` and its limit proof:
  its explicit cone is the equalizer subring of B × A' with coordinate operations.
  Thus using the categorical pullback changes no ring or action mathematically.
- `N : ModuleCat B` and `M' : ModuleCat A'` carry precisely the two given module
  structures. `extendScalars b.hom` is A tensor_B N, and `extendScalars q.hom`
  is A tensor_A' M'. For surjective q the latter is canonically M'/IM': use
  `TensorProduct.quotTensorEquivQuotSMul` and A'/ker(q) ≃ A. Tensor symmetry
  identifies the former with the node's N tensor_B A. Hence the binder `φ`
  ranges over exactly the required A-linear isomorphisms, with neither extra
  compatibility hypotheses nor omitted ones.
- `leftMap` restricts the adjunction unit n ↦ 1 tensor n, applies φ, and uses
  the canonical composition of restriction-of-scalars isomorphism. `rightMap`
  restricts m' ↦ 1 tensor m'. The pullback square identity makes their target
  actions the same. Their formula checks are included in the scratch probe.
- `patchedModule` is the module pullback of those two maps. I read
  `ModuleCat/Limits.lean`: its forgetful functor preserves the limits, and the
  module structure on sections acts pointwise. It therefore represents exactly
  P = N ×_M M' with the coordinatewise R-action.
- `flat_patchedModule` assumes `Module.Flat B N` and `Module.Flat A' M'` and
  concludes `Module.Flat R (patchedModule ...)`, the complete first clause.
  This is the recorded dependency `def-weil-pbc-flat-ring-map`'s module notion.
- `transition r f t h L` is defined using the scalar-extension adjunction from
  the unit for t and the canonical scalar-composition isomorphism. On pure
  tensors it is s tensor l ↦ f(s) tensor l. `transitionLeft` uses b and
  `transitionRight` uses q, so they are the two required maps to A tensor_R L.
- `exists_reconstruction_iso` quantifies over every flat R-module L independently
  of N, M' and φ. It gives an isomorphism to the pullback of the two transition
  maps, together with both projection equations equal to the scalar-extension
  units. These equations determine its forward morphism uniquely, so this
  asserts invertibility of the canonical map, not merely the existence of an
  unspecified isomorphism. Tensor symmetry rewrites 1 tensor l as l tensor 1.

The module universes use `max u v`, allowing arbitrarily large modules while
admitting the scalar-extension adjunction without imposing smallness on them.
The standard common universe for bundled rings is arbitrary. Zero rings and
zero modules remain admitted: no `Nontrivial` or nonempty-spectrum hypothesis
occurs. For q the identity the patched module is the expected compatible graph;
for A the zero ring the construction becomes the product situation. These
specializations require no additional assumptions. Reconstruction does not
assume q has nilpotent kernel or b is surjective.

Dependency interfaces read and used: Mathlib `TensorProduct` and its bilinear
universal property (`def-weil-pbc-module-tensor-product`); Mathlib `Module.Flat`
and `iff_lTensor_preserves_injective_linearMap`
(`def-weil-pbc-flat-ring-map`). Statement imports are public. The already stated
proof leaves are imported privately through TensorProduct.Quotient,
TensorProduct.RightExactness and Flat.Tensor (which publicly includes Flat.Basic).
The two non-leaf proof nodes `lem-sfb-patched-module-base-change` and
`lem-sfb-tensor-inclusion-flat-reduction` have no Lean record yet, so there is no
module to import for them. They are proof prerequisites, not missing notions in
this statement; their IDs and uses remain in the proof docstrings. The maintainer
can add their imports when those modules land.

Searches were run with msearch.py and are recorded verbatim in searches.jsonl:

- LeanSearch: "Flat modules patching over a fiber product of rings with a
  surjective map". It returned flat scalar extension, flat descent and
  localization results, not patching across an arbitrary surjective pullback.
- LeanFinder: "Compatible flat modules over a surjective pullback square of
  commutative rings glue to a flat module; flat modules reconstruct from their
  two scalar extensions". No matching declaration.
- Second LeanFinder phrasing: "Milnor square flat module descent and
  reconstruction from tensor products along a surjective ring map". Its
  kernel/tensor and faithfully flat descent hits do not state this theorem;
  in particular kernel/tensor equivalences assuming flatness of a cokernel
  cannot supply the reverse patching flatness implication.
- Loogle: `Module.Flat, TensorProduct`. The hits concern preservation of
  independence, tensor flatness and injectivity, not this ring square.
- Mathlib grep: `fiberProduct|fibreProduct|[Pp]atching|pullback.*[Ff]lat|[Ff]lat.*pullback`
  in RingTheory, yielding only general flat/tensor documentation. Further
  logged searches located scalar extension/restriction and the ring pullback.
- Project searches by the blueprint tag and fibre-product/patching concepts
  in WeilConjectures and Sheaf found no declaration for this node. The existing
  `FibreProductAlgebraFlatPresentation` module cites this node as a proof input;
  it concerns algebras and does not state the module theorem. The upstream-name
  table has no attachment for the item. No duplicate module definition was used.

Validation: the delivered module compiles cleanly on the server in required module
mode, both sandbox and library passes (14.4 s and 2.8 s in the first clean run).
The scratch module checks both comparison-map formulas and the transition formula
on pure tensors, plus the two theorem signatures. It is outside the delivered
Lean subtree. Only the two theorems contain `sorry`; no definition does. All
declarations have the source and blueprint tag, and all lines fit 100 characters.

No new DAG nodes, dependency modules, statement corrections, or unresolved
mathematical disputes. The accepted proof is retained in the theorem docstrings:
steps 1–5 prove flatness and step 6 proves reconstruction.

## Review by Q116

I checked the statement against 08KH and 0D2I with the file open. The first draft
needed the category annotation on ring pullbacks in type positions: otherwise
Lean tried to elaborate a pullback in Type. Adding `C := CommRingCat` fixed that
without changing the mathematics. I then checked the restriction-composition
isomorphisms: both left and right maps are directed into restriction along
R → B → A; the right one uses the pullback equation in the needed direction.
The transition is adjoint to the unit followed by composition restriction,
which produces f(s) tensor l, not an unrelated comparison. The reconstruction
statement's projection equations fix the canonical map even though it is
expressed by an existential isomorphism.

I matched the accepted proof's cited facts with its use: step 1 takes the two
base-change isomorphisms and quotient tensor formula; step 2 uses the tensor
universal property and flatness as injectivity; step 3 uses quotient tensor and
right exactness; step 4 uses precisely the generic tensor-inclusion criterion
after verifying Jd ⊆ c; step 5 uses flat ideal multiplication and the ideal
criterion; step 6 uses exact tensoring with a flat module. The new Lean statements
do not assume the conclusions of any of those steps. They retain the difficult
clauses as postponed theorems, with all source proof steps present for stage 3.

I checked the stage-2 H rules: exactly one module and one node record, no changes
to the accepted natural-language statement or dependencies, no private copies of
TensorProduct or Flat, real definitions for the maps, explicit binders, no local
notation or instances, and no stronger flatness/size/finite-generation condition.
The review is my own self-check, not an independent second reading; the maintainer
performs that review after direct delivery.

## Second reading by Q116

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
