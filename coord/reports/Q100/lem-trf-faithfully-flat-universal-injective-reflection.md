## Worker report

The module `Sheaf.RingTheory.FaithfullyFlatUniversalInjectiveReflection` states
`LinearMap.universally_injective_iff_baseChange_of_faithfullyFlat` with `sorry`.
No definition or additional node is introduced, and the original node changes only in `lean`.

Hypothesis and clause correspondence:

- Commutative rings R and S: `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`.
- The ring homomorphism R → S: `[Algebra R S]`, with underlying map `algebraMap R S`.
  This encodes any unital commutative-ring homomorphism through its `toAlgebra` structure.
- Faithful flatness of that map: `[Module.FaithfullyFlat R S]`, exactly the recorded
  module formulation of `def-weil-pbc-faithfully-flat-ring-map`.
  `RingHom.faithfullyFlat_algebraMap_iff` confirms the ring-map equivalence.
- Arbitrary R-modules P and Q and their R-linear map u: `{P : Type w} {Q : Type x}`,
  their `AddCommGroup` and `Module R` instances, and `(f : P →ₗ[R] Q)`.
- The canonical S-linear scalar extension: `f.baseChange S`, which has type
  `S ⊗[R] P →ₗ[S] S ⊗[R] Q`. Its defining formula is
  `LinearMap.baseChange_tmul`: `s ⊗ p ↦ s ⊗ f p`. The S-action is on the first factor.
- Universal injectivity over R: the left side quantifies over every R-module L and
  requires `Function.Injective (f.lTensor L)`, the canonical map `1_L ⊗ f`.
- Universal injectivity over S: the right side quantifies over every S-module T and
  requires `Function.Injective ((f.baseChange S).lTensor T)`.
- The node's “if and only if” is the displayed `↔`.

Universes u, v, w, x, t are all explicitly declared. Both test quantifiers range over
`Type (max u v w x t)`, an arbitrary common upper bound, rather than an independent
possibly too-small universe. This admits the restricted S-module in the forward argument
and `S ⊗[R] L` in the reverse argument in the same test universe. Ring and module universes
are otherwise independent. No finiteness, freeness, flatness of P/Q, or injectivity of f
is assumed. There is no auxiliary or hollow hypothesis.

Dependency declarations read and used:

- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat`, in
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`; the full class and exactness interface
  were inspected. The ring-map definition and algebraMap equivalence in
  `Mathlib.RingTheory.RingHom.FaithfullyFlat` were also read to verify the encoding.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.tmul`,
  `TensorProduct.lift`, `TensorProduct.ext'`, and `LinearMap.lTensor` / `rTensor`, in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, and `.Map`.
  `LinearMap.baseChange` in `.Tower` supplies the more linear S-scalar extension.
- Proof dependency `lem-trf-faithfully-flat-ltensor-injective-reflection` is the exact
  Mathlib leaf `Module.FaithfullyFlat.lTensor_injective_iff_injective` in `.Basic` above.
- Proof dependencies `lem-trf-scalar-tensor-cancel-base-change` and
  `lem-trf-scalar-tensor-distrib-base-change` are the exact Mathlib leaves
  `TensorProduct.AlgebraTensorModule.cancelBaseChange` and `.distribBaseChange`, in
  `Mathlib.LinearAlgebra.TensorProduct.Tower`. Their signatures and pure-tensor formulas
  were read. Both modules are already public imports for the statement dependencies;
  no additional proof-only imports are necessary.

Source checked: local `literature/stacks-project/algebra.tex`, the full lemma and proof
of `lemma-faithfully-flat-universally-injective` (Tag 05CK, around line 20255) and
`lemma-ffdescent-ML` (Tag 05A5, around line 22342). The latter explicitly uses faithful
flatness to reflect universal injectivity. The theorem docstring records every step of
both implications, with the exact cancellation, distributivity, and reflection interfaces.
There is no source discrepancy or statement dispute, and no repair note exists for this item.

Edge cases checked mathematically: R and S may be zero rings; under faithful flatness,
S = 0 forces R = 0, in which case all modules are zero and both tests hold. P and Q may
be zero modules. For P = 0 both sides hold. For Q = 0 the tests force P = 0, preserved
and reflected by faithful flatness. Identity scalar extension S = R gives the same
condition on both sides under the tensor unit equivalences. Identity maps are universally
injective, and a zero map is universally injective precisely when its source is zero.
No nontriviality instance or restriction on characteristics is present.

Searches for existing declarations (2026-10-18):

- `msearch.py ... leansearch "For a faithfully flat algebra S over R, a linear map is
  universally injective if and only if its scalar extension to S is universally injective"`:
  returned `RingHom.FaithfullyFlat`, faithful flat tensor products, flat preservation,
  `Module.FaithfullyFlat.lTensor_injective_iff_injective`, and a scheme-theoretic statement;
  no exact universal equivalence for arbitrary linear maps.
- `msearch.py ... leanfinder "faithfully flat scalar extension reflects universal injectivity
  of a linear map after tensoring with every module"`: eight hits, including the ordinary
  injectivity reflection theorem and flatness criteria, no exact universal equivalence.
- `msearch.py ... loogle "LinearMap.baseChange, Module.FaithfullyFlat.lTensor_injective_iff_injective"`:
  no hits.
- `msearch.py ... grep "UniversallyInjective|universally.injective|universally_injective"
  RingTheory`: no hits.
- `rg` in the upstream `WeilConjectures` and project `lean/Sheaf` for universal-injectivity
  names: scheme-theoretic universal injectivity and related module criteria/localization
  statements, no faithfully flat base-change equivalence. The module finite-test,
  localization/stalk criterion, and Mittag-Leffler descent statements were inspected.
- Direct `rg` in Mathlib, upstream, project sources, and `dag/lean_names_upstream.json`
  for the proposed declaration name and universal-injective/baseChange/faithfullyFlat
  combinations: no existing matching declaration.
- `grep -rn` for the exact node id in upstream `WeilConjectures`: no hits.

Validation: the prescribed `scompile.py` wrapper compiles the delivery module; the delivery
preflight/dry run and final push are recorded by the prescribed `deliver2.py` wrapper.

## Second reading by Q100

Author's explicit self-check under the dispatcher brief (no other agents may be started):
reopened the original node and the delivered signature and matched each clause above.
The two sides are universal injectivity of the original R-linear map and its canonical
S-linear scalar extension; the direction is equivalence, the first-factor S-action is
Mathlib's existing action, and the test universes dominate both ring universes. All binders
are explicit with auto-implicit disabled. No mismatch, correction, new node, or dependency
repair was needed. This is an author check; the maintainer supplies the independent review.
