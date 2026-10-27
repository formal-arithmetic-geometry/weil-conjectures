## Worker report

The module `Sheaf.RingTheory.FiniteColengthCompletionComparison` states
`AdicCompletion.FiniteColength.comparison`. Its only postponed proof is this theorem,
with the complete seven-step DAG proof in its docstring. Five transparent abbreviations
specialize existing Mathlib constructions to this inclusion: the original module quotient,
the ring presentation of the algebra completion, the completed inclusion, the completed
projection, and its module cokernel. Their data are fully supplied by Mathlib; none uses
choice or a postponed proof. No new DAG notion or dependency repair is needed.
The item's natural-language statement and dependency lists are unchanged.

Hypothesis-by-hypothesis correspondence:

- `A : Type u`, `[CommRing A]`, `[IsNoetherianRing A]`, `[IsLocalRing A]` give the
  commutative Noetherian local base. Its distinguished ideal is
  `IsLocalRing.maximalIdeal A`; Mathlib's local-ring predicate includes nontriviality,
  as required for a unique proper maximal ideal.
- `C : Type v`, `[CommRing C]`, `[Algebra A C]` encode the commutative target and
  specified ring homomorphism `f = algebraMap A C`. This is arbitrary algebra data,
  not a restriction to a preferred homomorphism. `hf` says that f is injective and
  `[Module.Finite A C]` says C is finite as an A-module.
- `Quotient A C` is literally `C ⧸ LinearMap.range (Algebra.linearMap A C)`, the
  module quotient M = C/f(A). No ideal quotient or quotient ring is imposed on M.
- `r : ℕ`, `s : CompositionSeries (Submodule A (Quotient A C))`, `hs₀`, `hsr`,
  `hlen` specify a filtration from zero to M of exactly length r. CompositionSeries
  uses successive covers in the submodule lattice: Mathlib's
  `covBy_iff_quot_is_simple` identifies these with nonzero simple successive quotients.
  Since the conclusion does not mention s, quantifying over its supplied witness is
  equivalent to the node's existence of a filtration. There is no r > 0 assumption.

Clause-by-clause correspondence, in conclusion order:

1. The first equality of submodules is exactly m^r M = 0; the next says m^n M = 0
   for every n >= r. Ideals act on the top submodule, so this is annihilation of M,
   not a condition just on its chosen generators.
2. The family `ε n hn` identifies the nth quotient with M for n >= r. Its value on
   every quotient representative is that representative. The next equation says
   these identifications take every actual `AdicCompletion.transitionMap` to the
   identity of M. This states constancy of the tower under canonical identifications,
   without pretending that distinct quotient types are definitionally identical.
3. `Function.Bijective (AdicCompletion.of ... M)` states that the actual A-linear
   completion map iota_M is an isomorphism; the map is already linear in Mathlib.
4. `Function.Injective inclusion`, `Function.Exact inclusion projection`, and
   `Function.Surjective projection` are the three clauses of the displayed short
   exact sequence. The two maps are exactly `AdicCompletion.map` applied to f and
   to the quotient projection, with scalars restricted from Ahat to A.
5. `α` is an A-linear equivalence from M to the module cokernel of the completed
   inclusion. Its formula on every c is precisely [c] -> [iota_C(c)]. `β` is the
   A-linear quotient isomorphism to Mhat; its formula is [z] -> qhat(z).
   The equality of linear maps `β.toLinearMap.comp α.toLinearMap = of ... M`
   is the claimed equality of the composite with iota_M. All quotients here are
   Mathlib submodule quotients.
6. Mathlib's `AdicCompletion m C` is a module completion; the ring instance on
   completions instead expects an ideal of C. `AlgebraCompletion A C m` is
   `AdicCompletion (m.map (algebraMap A C)) C`. Since (mC)^n = m^n C, these are
   two presentations of exactly the displayed completion, not two distinct notions.
   The linear equivalence `e` is pinned down by every coordinate: if z's nth
   coordinate is represented by c, the nth coordinate of e(z) is represented by c.
   Every coordinate has a representative, so this determines e uniquely. The algebra
   map `fhat` is specified on every input as e of the completed module inclusion.
   Consequently it is the induced map fhat in the node, not an arbitrary map or an
   extra assumption. Neither e nor fhat is assumed: both are in the conclusion.
7. `T` is explicitly an `AlgEquiv` over Ahat. Its target algebra structure is
   `fhat.toRingHom.toAlgebra`, so the structural map really is fhat. The equation
   on every pure tensor is exactly a tensor c -> fhat(a) * iota_C(c), and the next
   equation records the structural inclusion a -> a tensor 1.
8. `U` is an `AlgEquiv` over Ahat on the reversed tensor product, with Mathlib's
   `Algebra.TensorProduct.rightAlgebra`. Its equation on every tensor identifies
   it with T composed with `Algebra.TensorProduct.comm`; the final equation gives
   U(1 tensor a) = fhat(a). Thus both factor orders and their structural inclusions
   are retained. No unspecified map or stronger algebra hypothesis replaces them.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs` (full abbreviation and docstring read).
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs` (finite generation of the top submodule).
- `def-weil-pbc-adic-completion`: `AdicCompletion`, `AdicCompletion.of`,
  `AdicCompletion.eval`, `AdicCompletion.transitionMap`,
  `Mathlib.RingTheory.AdicCompletion.Basic`; its algebra structures and `evalₐ`
  in `Mathlib.RingTheory.AdicCompletion.Algebra`.
  `AdicCompletion.map` is read in `Mathlib.RingTheory.AdicCompletion.Functoriality`.
- `def-weil-module-base-change`: `TensorProduct`, `TensorProduct.mk`, and
  `LinearMap.baseChange` in `Mathlib.LinearAlgebra.TensorProduct.Tower`.
  The node uses the tensor objects, with the ring structure and tensor flip read
  in `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`.
- Proof leaves `lem-weil-pbc-completion-exact-finite-modules` and
  `lem-weil-pbc-completion-finite-module-tensor` have no lean records, and are
  Mathlib matches. Their full statements/docstrings were read:
  `AdicCompletion.map_injective`, `.map_exact`, `.map_surjective` in `.Exactness`,
  and `.ofTensorProductEquivOfFiniteNoetherian`, `.ofTensorProduct_tmul`,
  `.ofTensorProduct_naturality` in `.AsTensorProduct`. The latter module is a
  plain proof import; the modules supplying statement data are public imports.
  The same-universe finite-module proof APIs can be applied after resizing a finite
  module; this theorem keeps independent u and v and adds no universe restriction.

Sources read directly: Stacks varieties.tex, the statement and complete proof of
lemma-prepare-delta-invariant (Tag 0C1R), especially the finite-length quotient and
part (9), and lemma-normalization-same-after-completion (Tag 0C3V), especially the
finite-algebra tensor-completion paragraph. The module's proof follows the accepted
DAG's elementary expansion and its two existing Mathlib completion inputs.

Edge cases checked before and after writing:

- r = 0 forces zero = M; every quotient in the tail, including n = 0, is zero.
  The completion and both module cokernels are zero; the statement remains valid.
- C = A with f the identity gives M = 0, and the tensor comparison reduces to the
  usual Ahat tensor A identification. No nonzero cokernel is assumed.
- For a field base, m = 0; all positive completion coordinates stabilize at once.
  A nonzero finite-dimensional quotient can have arbitrary positive length r.
- For the cusp inclusion localized at its singular point, the quotient has finite
  length and the completed quotient retains that same length. No normality,
  reducedness, dimension-one, or locality of C is added.
- Characteristic is unrestricted. The local base is nonzero, and C is nonzero by
  injectivity, while the zero quotient is explicitly allowed. All index sets are
  the natural numbers and all algebra/module types have explicitly bound universes.

Search log (the prescribed msearch wrapper, plus direct source searches):

- LeanFinder: "An injective finite algebra over a Noetherian local ring with finite
  length quotient has canonically isomorphic completed cokernel and algebra tensor
  completion". Eight hits, including `ofTensorProductEquivOfFiniteNoetherian`, its
  bijectivity/formula/naturality lemmas, and `tensor_map_id_left_injective_of_injective`.
  None states the finite-length, constant-tail, canonical-cokernel and algebra clauses
  together. They are used as existing constructions/proof leaves.
- Loogle: "AdicCompletion.ofTensorProduct, CompositionSeries, AdicCompletion.map".
  Zero hits for this combined query. The individual declarations were subsequently
  located and read directly from their Mathlib files.
- LeanSearch: "A finite length module over a local ring is annihilated by a power
  of the maximal ideal and its canonical completion map is an isomorphism".
  Eight hits: `IsAdicComplete`, `IsFiniteLength`, `AdicCompletion.of_bijective`,
  `AdicCompletion`, `of_surjective`, `module`, `of_bijective_iff`, and
  `IsAdicComplete.of_lift`. None is this theorem.
- msearch grep, RingTheory: `(finite.length|colength|CompositionSeries).*complet|`
  `complet.*(finite.length|colength|CompositionSeries)` returned zero hits.
- Direct rg in Mathlib, WeilConjectures, Sheaf, and `dag/lean_names_upstream.json`
  for `FiniteColength|finiteColength|finite_colength` returned no declarations.
  The conceptual searches `CompositionSeries.*Adic|Adic.*CompositionSeries` and
  finite-colength variants in WeilConjectures and Sheaf also returned no hits.
  The required grep for the item's id in WeilConjectures returned no hits.
- Wider searches for completion algebra comparisons found
  `Sheaf.RingTheory.CompletionFiniteQuotientData` and
  `Sheaf.RingTheory.AdicBaseTensorLocalComparison`; both were read. The former is
  specific to a monic local quotient, and the latter concerns localized tensor
  algebras at primes; neither gives this finite-colength result or a generic
  canonical module/ring completion identification usable in this signature.

No statement fault, disputed claim, correction, new node, or dependency repair.
Compilation is exclusively through scompile.py; expected sorry warnings are permitted.

## Second reading by Q07

No separate worker was started, as required by the dispatcher brief; the maintainer
provides the independent review. I reread the node alongside the final signature.
The finite filtration starts at bottom and ends at top (CompositionSeries alone
would omit both conditions), the exponent is its exact length including zero,
and the tower condition uses actual quotient equivalences. Both completed maps
are induced by the original maps. Alpha and beta are determined on every quotient
representative and their composite is the completion map. The coordinate condition
on e preserves the original completion object across Mathlib's two presentations.
Both tensor equivalences have the specified completed-base structures and formulas,
including the reversed order. The only compile repair was marking the two completed
linear-map abbreviations noncomputable; this did not change their data or types.
An initial universally true representative formula for transitions was replaced
before delivery by the full family of tail equivalences and its transition equation.
