## Worker report

The new module `Sheaf.RingTheory.SplitCoidealFaithfullyFlat` states
`RelativeHopf.splitCoidealFaithfullyFlat`, with its sole proof `sorry`.
No definitions, extra nodes, dependency repairs, or statement corrections are needed.
The existing node is changed only in `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field k is `(k : Type u) [Field k]`.
- A is a unital commutative k-algebra: `(A : Type v) [CommRing A] [Algebra k A]`.
- B is a unital commutative k-algebra with algebra-valued comultiplication and counit:
  `(B : Type w) [CommRing B] [Bialgebra k B]`. The full Mathlib definition was read:
  Bialgebra extends Algebra and Coalgebra; Coalgebra supplies coassociativity and both
  counit laws, and the Bialgebra fields assert that comultiplication and counit preserve
  one and multiplication. Thus these are precisely the node's algebra maps and identities.
- The algebra-valued antipode is `(S : B →ₐ[k] B)`. `hSleft` and `hSright` say
  `mu (S tensor 1) Delta = eta epsilon` and `mu (1 tensor S) Delta = eta epsilon`,
  respectively, as equalities of k-linear maps. There is no extra Hopf assumption on A.
- The specified k-algebra map i is encoded by `[Algebra A B] [IsScalarTower k A B]`.
  Its underlying map is `algebraMap A B`, and its k-algebra homomorphism is
  `IsScalarTower.toAlgHom k A B`. This is a change of representation of the input map,
  not an additional hypothesis: every k-algebra map i induces exactly this A-algebra
  structure on B, its k-algebra commutation gives the scalar tower, and conversely the
  scalar tower gives precisely that commutation. All later occurrences use this same map.
- `hi : Function.Injective (algebraMap A B)` is the required injectivity.
- `hcoideal` quantifies over every `a : A` and puts `Coalgebra.comul (algebraMap A B a)`
  in the linear range of `TensorProduct.map (IsScalarTower.toAlgHom k A B).toLinearMap
  (LinearMap.id : B →ₗ[k] B)`. This map is i tensor 1_B on A tensor_k B; using its linear
  range expresses the node's image condition verbatim. No Hopf structure on A is used.
- `hsplit : ∃ r : B →ₗ[A] A, ∀ a : A, r (algebraMap A B a) = a` is exactly the
  existential A-linear retraction. The A-module structure of B comes from the same
  A-algebra structure encoding i. The identity is pointwise r composed with i = id_A.
- `Module.FaithfullyFlat A B` is the requested conclusion. The recorded dependency's
  `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact` identifies this with preservation
  and reflection of exactness, so no conclusion is omitted.
- No finite-dimensionality, finite generation, characteristic condition, or Hopf
  structure on A occurs. The three type universes u, v, w are independent.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: the recorded Mathlib
  `Algebra.TensorProduct.instCommRing`, `instAlgebra`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, `productMap`, `productMap_apply_tmul`, and `ext` from
  `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`. The statement's tensor and
  range are the same underlying Mathlib tensor; the existing `TensorProduct.map`
  is i tensor id. These definitions and signatures were opened in the source.
- `def-weil-pbc-faithfully-flat-ring-map`: the recorded `Module.FaithfullyFlat`,
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, and its exactness equivalence.
  The output is module faithful flatness, so the ring-map wrapper is unnecessary.

The full five-step natural-language proof from the node is rendered in the theorem's
source docstring, with its named dependencies. Imports for stated proof dependencies:
`Sheaf.RingTheory.RelativeHopfModuleKernels`,
`Sheaf.RingTheory.CoidealCanonicalTensorIsomorphism`,
`Sheaf.RingTheory.CoidealCoinvariantProjection`, `Mathlib.RingTheory.RingHom.Flat`,
and `Mathlib.LinearAlgebra.TensorProduct.RightExactness`.
The module-tensor proof dependency is Mathlib's TensorProduct already imported transitively.
`lem-sfb-relative-hopf-counit-criterion` has no Lean record or mathlib_match in the read
snapshot, so there is no module to import for that proof-only dependency; it is named
in the proof docstring. It is not needed to type this statement. No import cycle is added.

Edge cases checked before writing:

- A = B and i = id with r = id is included; the conclusion is self faithful flatness.
- A = k and the unit inclusion is included; the counit gives the usual splitting.
- Neither infinite-dimensional B nor an infinitely generated A is excluded.
- A = 0 cannot inject unitaly into a nonzero B. B = 0 is already impossible for a
  Bialgebra over a field: its counit is unital to k. No nontriviality assumption was added.
- All characteristics are allowed. No index-set or test-module universe restriction is added.
- The two antipode identities use the correct tensor factor, and the coideal image uses
  i in the first factor (right coideal, not the opposite convention).

Searches for existing statements (all through prescribed msearch.py or read-only rg):

- leanfinder: "A commutative Hopf algebra is faithfully flat over a right coideal
  subalgebra admitting a module retraction": eight hits, including
  `Module.FaithfullyFlat.self`, tensor descent lemmas, `RingHom.FaithfullyFlat`, and a
  PicardGroup submodule lemma. None deduces flatness from a coideal splitting.
- loogle: "Bialgebra, Module.FaithfullyFlat": zero hits.
- grep, RingTheory: "[Cc]oideal|Hopf.*[Ff]lat|[Ff]lat.*Hopf": thirteen hits,
  all quotient-coideal/Hopf-ideal structure material, no split-coideal flatness theorem.
- leansearch: "A split right coideal subalgebra of a commutative Hopf algebra is
  faithfully flat": eight hits giving faithful-flatness definitions, self-flatness,
  descent, and the algebra-map equivalence; none is the assertion here.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  "coideal|[Cc]oideal|splitCoideal|split_coideal": the existing RelativeHopf data,
  kernels, canonical tensor isomorphism and projection modules were found and read;
  none states the present theorem. Upstream hits concern Hopf ideals and etale Hopf algebras.
- grep for "lem-sfb-split-coideal-faithfully-flat" in `lean/WeilConjectures`: no hits.

Source checked online: https://arxiv.org/html/2301.05480v2, Theorem 1.1 and the
conditional-expectation convention immediately before section 2. The local PDF remains
WANTED as in the inherited node; the HTML supplies the theorem and its proof. In the
commutative specialization, A-linearity implies A-bilinearity since
E(a h a') = aa' E(h) = a E(h) a'. No statement fault or dispute was found.

Validation: scompile.py compiled the sandbox and library module cleanly (only the
expected sorry is present). The delivery dry run and final delivery are recorded below.

## Second reading by Q88

A separate in-thread rereading compared the node JSON to the generated Lean file,
with no additional agent (the dispatcher explicitly forbids starting other agents).
This is a self-review, not a claim of independent review; the maintainer's independent
review remains pending. The field, two commutative algebras, both coalgebra identities
via Bialgebra, algebra-valued antipode and its two explicit identities, injective map,
first-factor tensor-image condition, existential linear retraction, and faithful-flat
module conclusion all match as itemized above. Encoding i by a compatible algebra
structure was checked in both directions; it adds no restriction. The retraction
uses the same structure as the conclusion. There are no local notations, hidden
implicit variables, noncanonical maps, data chosen from existence, or additional
finiteness hypotheses. No mismatch required a change on this rereading.

Dry run: `deliver2.py Q88 lem-sfb-split-coideal-faithfully-flat --no-push` returned
`OK (dry run)` at commit `d4a8ac61825`: preflight passed and the module compiled.
