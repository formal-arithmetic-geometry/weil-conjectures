## Worker report

The delivery states `RelativeHopf.relativeHopfModuleKernels` in
`Sheaf.RingTheory.RelativeHopfModuleKernels`, with its whole proof `sorry`.
`RelativeHopf.QuotientConclusions` is an explicit conjunction collecting its conclusions.
The new definition node `def-sfb-relative-hopf-module-data` supplies the genuinely missing
relative coaction, morphism, coinvariant and induction predicates. No original statement
is changed, and no dependency record is replaced. There is exactly one postponed theorem,
matching this item; all definitions have actual data and contain no sorry.

Hypothesis and clause correspondence, checked against the entire node:

- The field is `(k : Type u) [Field k]`, using the declaration `Field` recorded by
  def-weil-field (Mathlib.Algebra.Field.Defs). The commutative unital algebra is
  `(H : Type v) [CommRing H] [Bialgebra k H]`. Read Mathlib.RingTheory.Bialgebra.Basic:
  Bialgebra supplies exactly an algebra, algebra-valued comultiplication and counit,
  coassociativity and the two counit identities. It is a packaging of the stated data,
  not an extra hypothesis. Comultiplication and counit are `Coalgebra.comul` and
  `Coalgebra.counit`, equivalently `Bialgebra.comulAlgHom` and `counitAlgHom`.
- The specified antipode is retained as `(S : H →ₐ[k] H)`, with both stated equations
  `hSleft` and `hSright`. `LinearMap.mul' k H`, `Algebra.linearMap k H`, rTensor and
  lTensor render the multiplication, unit, and S tensor 1 / 1 tensor S composites.
  No separate HopfAlgebra structure is assumed or selected.
- A is `(A : Subalgebra k H)`, so is a unital k-subalgebra without a Hopf structure.
  `hA : IsRightCoideal k H A` means comul(a) lies in the range of
  `TensorProduct.map A.val.toLinearMap LinearMap.id`. This is precisely the image
  interpretation of A tensor H, without requiring an arbitrary lift of Delta to A.
- A-plus is the set of a : A with `Coalgebra.counit (a : H) = 0` inside the explicit
  `Ideal.span` defining `augmentationIdeal`. Thus the ideal J is exactly H A-plus.
  `Quotient` is `H ⧸ augmentationIdeal k H A`, and `quotientMap` is the actual
  `Ideal.Quotient.mkₐ` viewed as a k-linear map.
- The theorem returns `hJ : ((augmentationIdeal ...).restrictScalars k).IsCoideal`.
  Mathlib.RingTheory.Coalgebra.Quotient defines this class as counit vanishing and
  `(pi tensor pi) Delta` vanishing on J. Its `Submodule.isCoideal_iff_comul_mem` says
  this is equivalent to exactly epsilon(J)=0 and Delta(J) contained in the sum of
  the two tensor inclusion images stated in the node. The class's alternate
  presentation does not weaken the inclusion assertion.
- Given hJ, Mathlib.RingTheory.Bialgebra.Quotient supplies the canonical quotient
  coalgebra; the comul and counit have real quotient-lift data. The first conjunct
  of QuotientConclusions explicitly states both displayed quotient formulas.
  The quotient ring's scalar action is the required multiplication action; the
  second conjunct states `h • quotientMap t = quotientMap (h * t)`.
- A relative Hopf module is an H-module X, with the compatible underlying k-action,
  equipped with `Coaction k H C X`. Its fields `map`, `coassoc`, `counit`, and
  `compatible` are precisely the three stated identities. `tensorAction` is the
  actual bilinear action `(g tensor h)(c tensor x)=gc tensor hx`, so composing it
  with comul(h) renders the Sweedler formula without choosing finite expansions.
  Tensor associator and left unitor explicitly render the understood identifications.
- `coinvariants ... (quotientMap ... 1) α` is exactly the set given in the node.
  The third conjunct asserts a `Submodule A X` with this carrier; both vector-space
  closure and the restricted A-action are part of that standard structure.
- For every A-module M, the fourth conjunct returns the unique Coaction on the
  actual `H ⊗[A] M` satisfying `IsInduced` and unit coinvariance. IsInduced writes
  alpha(h tensor m) as `TensorProduct.map pi (t ↦ t tensor_A m) (comul h)`.
  The map t ↦ t tensor_A m is the existing TensorProduct.mk, flipped and restricted
  to k. Its H-action is Mathlib's action on the first factor of the tensor.
  `TensorProduct.mk A H M 1` is already the A-linear eta map; its value on every m
  is asserted to be coinvariant. A k-module structure with IsScalarTower k A M is
  only the underlying restricted vector-space structure, available canonically for
  every A-module, with no finite rank, faithfulness or nonzero assumption.
- A relative morphism is `IsMorphism ... α β f`, where f is `X →ₗ[H] Y` and the
  equation is the exact coaction square after restriction to k. The fifth conjunct
  says that every A-linear f induces such a morphism by the existing `f.baseChange H`,
  whose generator formula is h tensor m ↦ h tensor f(m).
- The final conjunct quantifies over every relative morphism f between arbitrary
  modules X and Y. `LinearMap.ker f` is its actual H-submodule, with carrier
  `{x | f x = 0}`; this is also the underlying vector-space kernel. It asserts
  existence and uniqueness of a Coaction κ for which the standard subtype inclusion
  is a relative morphism. The quantified pointwise equivalence on x : ker f states
  exactly R(K)=K intersect R(X) under inclusion. Both coactions have their restricted
  k and H structures; nothing is assumed about H being flat over A.

Definitions and dependencies used:

- def-weil-pbc-module-tensor-product: TensorProduct, TensorProduct.mk, lift, map,
  assoc, lid, and LinearMap.lTensor/rTensor, from the Mathlib.LinearAlgebra.TensorProduct
  modules, exposed by the new data module's public imports.
- lem-weil-pbc-algebra-tensor-pushout-universal-property: the algebra tensor ring,
  componentwise multiplication and algebra maps of Mathlib.RingTheory.TensorProduct.Basic
  and Maps, exposed by the Bialgebra.Quotient import. Read instCommRing,
  tmul_mul_tmul, includeLeft, includeRight, productMap and ext with their source context.
- New definition node: Sheaf.RingTheory.RelativeHopfModuleData, declarations
  IsRightCoideal, augmentationIdeal, Quotient, quotientMap, tensorAction, Coaction,
  coinvariants, IsMorphism and IsInduced, all in namespace RelativeHopf.
- Proof imports are plain imports: Mathlib.RingTheory.Flat.Basic provides the recorded
  Module.Flat.of_free and Module.Flat.lTensor_exact/rTensor_exact; the recorded
  Module.Free.of_divisionRing is in Mathlib.LinearAlgebra.Basis.VectorSpace. Their
  signatures and docstrings were read. These are precisely the field-flatness and
  flat-tensor-exact proof leaves. The theorem's docstring carries all ten proof steps.

Searches: msearch.py leanfinder queried “Relative Hopf modules over quotient coalgebra
by a right coideal subalgebra, induction and kernels” (8 Hopf-axiom/category hits,
no match); loogle queried `"Hopf", "Comodule"` (0 hits); grep queried
`relative.?Hopf|HopfModule|coideal|Coinvariant` (25 hits including the reusable
coalgebra/bialgebra quotient machinery and unrelated representation coinvariants).
LeanSearch queried “relative Hopf module coaction over a quotient module coalgebra”
(8 coalgebra category / Hopf category hits, no relative module definition).
Also searched lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json:
no relative Hopf-module declaration or RelativeHopf namespace. DAG search found this
item, its coideal consumers and a finite-dual-specific Hopf-module theorem, which does
not define general relative modules. Read def-sfb-hopf-action-module-data: its affine
semilinear right coaction is a different notion, not the left quotient-coalgebra
coaction here. `blueprint_refs.py search 'relative Hopf'` found 0 blueprint nodes;
`ancestor` returned None, matching this item's inherited blueprint record. The raw
msearch results are retained as structured results in the new node.

Edge cases checked mathematically: A=k gives J=0 and ordinary Hopf modules;
A=H gives C=k and every element coinvariant, with H tensor_H M identified with M.
M=0 and X=0 are allowed with no Nontrivial or finite-dimensional condition.
For f=0 the kernel is X with the same coaction; for f=id the kernel is zero.
All characteristics and arbitrary rank are allowed. u,v,w,w',z,z' are independent:
M and N, and X and Y, may be in different universes. No auto implicit variables,
no file-local notation, private helper or local instance is used. There is no
hypothesis adding H/A-flatness. Uniqueness of induced coaction is implied by the
formula on spanning tensors, and uniqueness of kernel coaction by tensor-injectivity;
these are not additional mathematical conclusions beyond the specified constructions.

Source checked at https://arxiv.org/html/2301.05480v2, section 2.1, including the
underlying exact-sequence discussion following Theorem 2.1. The named local PDF
`literature/bichon-faithful-flatness_arXiv-2301.05480.pdf` remains WANTED; no literature
files were written. No statement dispute or correction was necessary.

Both delivered files compiled cleanly using scompile.py, individually in dependency
order against the live published build. No project build was run.

## New nodes

`def-sfb-relative-hopf-module-data` defines the coideal predicate, augmentation quotient,
relative coaction and its coinvariants/morphisms, and the formula characterizing induction.
Its source is Bichon section 2.1. It only packages the existing tensor and quotient data
and the missing relative-module notion; it has no proof and no chosen coaction data.
The searches above and the raw search records in the new node found no existing notion.
The more general bialgebra context isolates the operations used in the definitions;
the item's theorem retains its full Hopf hypotheses, including S. The item gains only
this definition node in stmt_deps, and its own node otherwise changes only in lean.

## Second reading by Q38

No second reading by a worker: the dispatcher brief requires direct delivery and no
other agents. The maintainer's independent review is the review of this delivery.
