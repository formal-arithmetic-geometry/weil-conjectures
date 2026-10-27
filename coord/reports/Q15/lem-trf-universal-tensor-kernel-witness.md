## Worker report

The module `Sheaf.RingTheory.UniversalTensorKernelWitness` states
`Module.exists_universal_tensor_kernel_witness`, with its entire proof `sorry`.
It is the single-witness construction in Stacks Algebra Tag 059M, proof of
(2) implies (1), through the first commutative square. I read that proof in
`literature/stacks-project/algebra.tex` and the finite-presentation product input
Tag 059K. Nothing in the node's mathematical statement or dependencies changed;
only its `lean` record is supplied. No new definitions or nodes are needed.

Hypothesis and conclusion correspondence:

- A commutative ring R is `(R : Type u) [CommRing R]`.
- The finitely presented module P is `(P : Type v) [AddCommGroup P]
  [Module R P] [Module.FinitePresentation R P]`.
- The module M is `(M : Type w) [AddCommGroup M] [Module R M]`.
- Its tensor-product Mittag-Leffler property is
  `hM : Module.IsMittagLeffler.{u, w, max u v w, max u v w} R M`.
  Put s = max u v w: this is exactly injectivity of the recorded canonical
  product comparison for every index type in Type s and test family in Type s.
  Both size parameters are explicit. The matrix-coded representative family
  and all its kernel pairs live in Type s, so this instance of the recorded
  definition includes the family used by the source construction.
- The given linear map is `(f : P →ₗ[R] M)`.
- The set-sized witness module is
  `∃ (T : Type (max u v w)) (_ : AddCommGroup T) (_ : Module R T)`.
  This is a genuine set-sized type with existentially supplied module structures,
  rather than a proper-class product or an arbitrary comparison map.
  Finite matrices over R form a set; their quotient modules can be lifted to
  Type s. P tensor each such quotient, its kernel subset and the index of pairs
  all have size s; their product is again in Type s. The arbitrary test Q is
  transported through its finite-presentation isomorphism with a representative,
  so T's size bound does not restrict the test-module universe.
- The witness is `∃ z : P ⊗[R] T`.
- Its membership in the kernel is `LinearMap.rTensor T f z = 0`.
- Every finitely presented test module, in an arbitrary independent universe t,
  is quantified by `∀ (Q : Type t) [AddCommGroup Q] [Module R Q]
  [Module.FinitePresentation R Q]`.
- Every element x in that tensor kernel is `(x : P ⊗[R] Q)` with premise
  `LinearMap.rTensor Q f x = 0`.
- The required map and equality are `∃ q : T →ₗ[R] Q,
  LinearMap.lTensor P q z = x`. Here lTensor is precisely id_P tensor q.
- No `Module.Flat`, projectivity, nonzero, nonempty or other finiteness assumption
  appears. The same T and z precede all Q and x quantifiers.

Recorded dependency declarations read and used:

- `Mathlib.Algebra.Module.FinitePresentation`, `Module.FinitePresentation`:
  finite generators with finitely generated relations. The recorded
  `exists_fin` and `exists_fin'` interfaces explain its equivalence to the
  finite free presentation in def-sc-finitely-presented-module.
- `Sheaf.RingTheory.IsMittagLeffler`, `Module.IsMittagLeffler`:
  injectivity of `TensorProduct.piRightHom R R P Q`. I read its full definition,
  including its independent index universe and `max u v t` test universe.
- def-weil-pbc-module-tensor-product's Mathlib match: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; `TensorProduct.lift` and `ext'`
  in `.Basic`; `LinearMap.rTensor` and `LinearMap.lTensor` in `.Map`.
  The latter two definitions are `TensorProduct.map f id` and `.map id f`.
  Their full signatures/docstrings and pure-tensor equations were read.
- Proof-only import `Sheaf.RingTheory.FinitePresentationTensorProducts`,
  `TensorProduct.piRightHom_bijective_of_finitePresentation`, has the full
  arbitrary-family statement recorded by the proof dependency. Its docstring
  and full signature were read. The theorem's four-step docstring carries the
  complete node proof, including the coordinate naturality and transport by
  an inverse linear equivalence.

Edge cases checked mathematically against the source and signature:

- P = 0: use a zero tensor; every test tensor x is zero.
- M = 0 or f = 0: every tensor is a kernel element, and the product includes
  every representative/kernel pair, so the same construction applies.
- f = id: its tensor kernel is zero, so the zero element suffices.
- The zero ring is allowed; no nontriviality or characteristic condition occurs.
- Nonflat finitely presented modules, e.g. Z/nZ over Z, are allowed for P and Q;
  every step uses product comparison and naturality, never left exactness.
- Empty presentation ranks m = 0 or n = 0 are valid matrix codes. Products are
  unrestricted set-indexed products. Even an empty product would be allowed
  by the imported finite-presentation comparison; no nonempty hypothesis is added.
- R, P and M have independent universes. Q has an independent arbitrary universe.
  The representative isomorphism transports to larger or smaller presentations
  of Q; no equality of universes is imposed.

Searches performed (in addition to reading the node's existing searches):

- msearch.py leanfinder: "A finitely presented module mapping to a Mittag Leffler
  module has one tensor kernel witness inducing all kernels for finitely presented
  test modules". Eight results included `TensorProduct.map_ker`,
  `LinearMap.tensorKerEquiv` and flatness criteria. None asserts this universal
  element; tensorKerEquiv additionally assumes flatness.
- msearch.py leansearch: "A finitely presented source mapping to a Mittag Leffler
  module has a universal tensor kernel element for all finitely presented test
  modules". Eight hits were tensor-kernel equivalences or presentation tensor
  constructions; no universal witness theorem. The equivalences impose flatness.
- msearch.py loogle: `Module.FinitePresentation, TensorProduct`. Five results
  concern scalar extension, finite-presentation tensor products and local-ring
  freeness; none is this witness theorem.
- msearch.py grep: `Mittag|universal.*kernel|kernel.*witness`. Ten hits concern
  inverse-system Mittag-Leffler, unrelated kernels, or trigonometric functions;
  no tensor-product universal witness theorem.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for universal tensor/kernel
  witnesses, this node id, and `IsMittagLeffler`: the existing module Mittag-Leffler
  definitions and Hom-systems theorem were found, but no statement of this lemma.
  The Hom-systems theorem's conclusion concerns stabilization of Hom images,
  rather than this witness. Its explicit universe instantiation also confirms
  the order of IsMittagLeffler's four universe parameters.
- rg in both source trees and `dag/lean_names_upstream.json` for
  `exists_universal_tensor_kernel|universalTensorKernel|universal_tensor_kernel`:
  no match. No declaration is duplicated.

No statement dispute or dependency-interface fault was found.

## Second reading by Q15

Self-check of the node and delivered signature: the existential T and z occur
before every Q and x, the kernel equation uses rTensor on f, and the evaluation
uses lTensor on q, so both tensor factors have the required orientation.
All of R, P, M, f, the finite-presentation hypothesis on P, the tensor ML
hypothesis on M, the finite-presentation hypothesis on Q and the kernel premise
on x are present. T is only required to be an R-module with a set-sized carrier;
no flatness or finite-presentation condition on it is introduced. The proof
plan uses the recorded declarations and transports every Q through a finite
matrix presentation. This check found no mismatch requiring a node correction.
This is a worker self-check, not a claim of an independent second agent reading;
the dispatch brief assigns independent review to the maintainer and prohibits
starting other agents.

Validation: the prescribed scompile.py compiled the sandbox probe and the actual
library module successfully, with no compiler diagnostics. The first deliver2.py
--no-push run passed server preflight and per-file compilation (dry-run commit
4a133f8c6ff). All Lean source lines are at most 100 characters.
