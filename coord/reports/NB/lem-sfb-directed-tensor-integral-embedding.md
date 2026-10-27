## Worker report

Delivered statement: `Algebra.TensorProduct.directed_integral_embedding` in
`Sheaf.RingTheory.DirectedTensorIntegralEmbedding`. This is stage 2: its sole
proof is `sorry`, and there are no new definitions or auxiliary theorems.
The node is unchanged except for its `lean` record.

Read the complete node, all three statement dependencies and their recorded
interfaces, and the stated proof dependency. Read Stacks `algebra.tex`,
`lemma-integral-closure-commutes-colim-smooth` (Tag 0CBF): its proof says that
tensor products and integral closures commute with filtered colimits. The
node supplies precisely the injectivity/integral-image part of that argument;
smoothness is used in its parent application, not in this elementary lemma.

Hypotheses and conventions, individually:

- The commutative rings R, C, B are `R C B : Type u` with three `CommRing`
  instances. `[Algebra R C] [Algebra R B]` supply the two algebra structures;
  `v : C →ₐ[R] B` is exactly the given R-algebra homomorphism.
- The nonempty directed preorder is `I : Type u`, `[Preorder I]`,
  `[Nonempty I]`, `[IsDirectedOrder I]`. The preorder category has a unique
  arrow `homOfLE hij` for every `hij : i ≤ j`. Filteredness follows from
  Mathlib's `CategoryTheory.isFiltered_of_directed_le_nonempty` and is not
  an additional hypothesis.
- The diagram is `F : I ⥤ CommAlgCat.{u, u} R`. Its transition maps are
  `(F.map (homOfLE hij)).hom`. `c : Cocone F` and `hc : IsColimit c` give
  the specified colimit S = `c.pt` and a_i = `(c.ι.app i).hom`. This uses
  an arbitrary specified colimit, rather than silently fixing a choice.
- The one universe `u` contains the index and all ring carriers, exactly
  the common-universe convention of the node. No smallness comparison or
  equality beyond that convention is added.
- Every displayed tensor is Mathlib's `TensorProduct R`, with the algebra
  multiplication from `Mathlib.RingTheory.TensorProduct.Maps` (and its
  imported algebra tensor construction). Thus `(s tensor z)(t tensor w)`
  is `st tensor zw`, with the left algebra acting on the first factor.
- E_i, D_i, E, D are written directly as `(F.obj i) ⊗[R] C`,
  `(F.obj i) ⊗[R] B`, `c.pt ⊗[R] C`, `c.pt ⊗[R] B`.
- f_i and f are the existing `Algebra.TensorProduct.lTensor (S := R)`
  applied to the first tensor factor and `v`. The explicit `S := R`
  selects the common R-algebra homomorphism interface; its underlying map
  is the same map `s tensor z ↦ s tensor v(z)` as the stage-algebra-linear
  interface. No new map or arbitrary chosen map is introduced.
- `h_injective` quantifies injectivity over every stage i.
- `h_integral` says `∀ i x, IsIntegral (F.obj i) (lTensor ... v x)`.
  Quantification over all inputs is equivalent to every element of the
  image being integral, and adds no condition on elements outside the image.

Conclusions, individually and in their Lean order:

1. `Function.Injective (lTensor (S := R) c.pt v)` is injectivity of f.
2. `∀ x, IsIntegral c.pt (lTensor (S := R) c.pt v x)` is exactly integrality
   over S of every image element.
3. The existential `q : c.pt ⊗[R] C →ₐ[c.pt]
   integralClosure c.pt (c.pt ⊗[R] B)` is an S-algebra homomorphism to the
   integral closure in the specified D. `Function.Injective q` supplies
   its embedding property. The following all-input equality identifies
   its composition with the inclusion with f, so q is the restriction of
   that canonical map. The following pure-tensor equality is the node's
   explicit formula `q(s tensor z) = s tensor v(z)`, read in D.
4. The conjunct indexed by `i j hij` is the equality of R-algebra
   homomorphisms `(a_ij tensor 1_B).comp f_i =
   f_j.comp (a_ij tensor 1_C)`, using existing `rTensor`.
5. The final conjunct indexed by i is the corresponding equality for
   each colimit coprojection, `(a_i tensor 1_B).comp f_i =
   f.comp (a_i tensor 1_C)`.
6. There are no flatness assumptions, no domain assumptions, no integrality
   assumptions on v, and no injectivity or integrality assumptions on any
   transition map or coprojection. All tensor maps are canonical existing
   algebra homomorphisms, with no extra map hypotheses.

Dependency declarations read and used:

- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone` and
  `CategoryTheory.Limits.IsColimit`, in `Mathlib.CategoryTheory.Limits.Cones`
  and `Mathlib.CategoryTheory.Limits.IsLimit`, publicly imported through
  the recorded `Mathlib.CategoryTheory.Limits.HasLimits`. Read their full
  signatures: cocone vertex and natural transformation, and universal
  morphism with factorization and uniqueness. The chosen `colimit` and
  its `colimit.ι` interface were read too; using `IsColimit c` retains
  exactly the node's specified cocone.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`
  in `Mathlib.LinearAlgebra.TensorProduct.Defs`; also read `TensorProduct.lift`,
  `TensorProduct.ext'` in `Basic` and `LinearMap.rTensor` in `Map`.
  The commutative algebra specialization and canonical algebra maps are
  the existing `Algebra.TensorProduct.map`, `lTensor`, `rTensor` in
  `Mathlib.RingTheory.TensorProduct.Maps`, with `map_tmul` giving the formula.
- `def-weil-pbc-integral-closure`: `integralClosure` in
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, whose carrier is
  `{x | IsIntegral R x}`; `IsIntegral` in
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs` is a root of a monic
  polynomial over the indicated algebraMap. The full definitions were read.
- Proof-only dependency: `CommAlgCat.filteredColimit_tensorProduct_elementwise`,
  `filteredColimit_tensorProduct_universal`, and
  `filteredColimit_tensorProduct_ringHom` in
  `WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise`.
  Read the entire module and import it privately, as required for stage 3.
  Its representative and eventual-zero clauses have exactly the same
  common index/stage-carrier universe needed here. The proof docstring
  explains transport from its chosen colimit to `c`.

Edge cases checked before writing:

- Empty I is explicitly excluded in the node and exactly by `[Nonempty I]`;
  a singleton constant diagram reduces to the stage hypothesis itself.
- A directed preorder need not be antisymmetric; no `PartialOrder` or
  linear order is required. Distinct comparable-equivalent indices work.
- Zero rings, zero tensors and a colimit that kills all elements are
  allowed. A zero target forces the source tensor to be zero under the
  assumed stage embeddings, by the eventual-zero argument.
- Transition maps may kill nonzero elements: eventual zero, rather than
  transition injectivity, is precisely the kernel argument in the docstring.
- A noninjective v is allowed; for example R = C = integers, B = F_2,
  v the quotient, and all S_i = F_2 gives identity tensor maps. This
  rules out accidentally imposing injectivity on v itself.
- Arbitrary characteristic is retained. Nothing requires nontrivial rings,
  finite generation, flatness, or injective coefficient structure maps.

Searches actually run (all using the prescribed `msearch.py NB` item log):

- LeanFinder: "Stagewise injective tensor algebra maps with integral image
  induce an injective map with integral image over a directed algebra colimit".
  Eight hits, including `TensorProduct.toIntegralClosure_injective_of_flat`,
  `Algebra.TensorProduct.includeRight_injective`,
  `Ring.DirectLimit.lift_injective`, and `Module.DirectLimit.lift_injective`.
  None is this conjunction for arbitrary v and arbitrary algebra colimit;
  flatness/inclusion lemmas add hypotheses or specialize the map.
- Loogle: `Algebra.TensorProduct.map, IsIntegral, Function.Injective`.
  Successful response, zero hits.
- LeanSearch: "Tensor maps injective with integral image at each stage remain
  injective with integral image over a directed colimit". Eight hits:
  direct-limit lifting/injectivity and tensor/direct-limit compatibility;
  none contains the integral-image conclusion or this entire assertion.
- Mathlib grep via msearch, subdirectory RingTheory:
  `(injective.*[Cc]olimit|[Cc]olimit.*injective|integral.*[Cc]olimit|[Cc]olimit.*integral)`.
  Successful response, zero hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the item id, candidate declaration
  names, directed tensor maps and integral/colimit combinations.
  No duplicate was found. `IntegralClosureIndEtaleBaseChange` is the parent
  ind-etale theorem, and `IntegralElementsColimitDescent` descends integral
  tensor generators in the opposite direction; neither states this lemma.
  `FilteredColimitAlgebrasTensorElementwise` supplies only the representative,
  eventual-zero and ring-map ingredients, and is imported for the proof.
- Read Mathlib's tensor map signatures and pure-tensor formula to reuse
  its actual algebra maps, rather than creating a second construction.

Validation: prescribed `scompile.py` compiled both the sandbox and exact library
module paths successfully (1.6 s and 1.5 s respectively); no errors or warnings
were printed. `autoImplicit` is false and the universe and every variable are
explicitly bound. All source lines are at most 100 characters. The JSON
signature is extracted verbatim from the Lean declaration. A comparison with
the source JSON confirms that every other field is unchanged.

No statement dispute, source error, new node, dependency repair, or statement
correction was necessary.

## Second reading by NB

Worker rereading of the completed node and module; the independent review is
performed by the maintainer after delivery, as specified in this dispatch.
No second agent was started.

I reread the hypothesis and conclusion lists above against the actual Lean
signature. `hc` gives the precise specified algebra colimit, not a ring colimit;
`F` gives R-algebra transitions; the directed index is a preorder, not a poset.
The stage integrality base is `F.obj i`, while the conclusion's base is `c.pt`.
The existential q is linear over S itself, despite writing the tensor map f
using its R-algebra interface. Its all-input equality pins down the restriction
and the pure-tensor formula agrees with the node. The two final equalities
are the requested algebra-map equalities, with composition in the written
order. All five proof steps in the node are represented in the declaration's
docstring, including eventual vanishing and preservation of monic equations.
The only replacement in notation is writing the node's E_i, D_i, E, D and f_i,f
using their existing tensor expressions directly. No mathematical mismatch was
found and no statement edit was made.
