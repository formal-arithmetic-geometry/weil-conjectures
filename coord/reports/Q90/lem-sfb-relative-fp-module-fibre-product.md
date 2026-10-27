## Worker report

The module `Sheaf.RingTheory.RelativeFinitePresentationFibreProduct` states
`Module.finitePresentation_relative_fibreProduct`. Its only theorem has proof
`sorry`; no new definition or postponed helper theorem is introduced.

I read the current item, all eight accepted proof steps, the statements and records
of its three statement dependencies, the recorded Mathlib declarations and their
source docstrings, and Stacks `more-algebra.tex`, Situation 08KH and Tag 08KP,
including the paragraph beginning “Assume B′ → D′ is flat”. The accepted split
is preserved. The earlier worker's stage-1 refusal is superseded by the explicit
stage handoff in the current `coord/brief-stage2.md` §0: this stage-2 node has no
Lean record. No repair note or return entry for this item was present.

Hypothesis and clause correspondence:

- The commutative rings are `A`, `A'`, and `B`, with separately bound universes
  `uA`, `uA'`, and `uB` and their `CommRing` instances. The maps `B → A` and
  `A' → A` are `f` and `g`; surjectivity is exactly `hg : Function.Surjective g`.
- The pullback `R` is the existing Mathlib subring `f.pullback g`, defined by
  equality of the images of the two coordinates, with inherited coordinatewise
  operations. The projection maps are `f.pullbackFst g` and
  `f.pullbackSnd g`. The three algebra structures on the component rings and
  the equations `hB`, `hA'`, `hA` fix their restriction maps to precisely those
  projections and their composite to `A`. They are presentations of the node's
  specified canonical actions, not extra conditions on any ring map. Every
  ring homomorphism supplies the requisite algebra structure via `toAlgebra`.
- The notation `I = ker g` is not used in the conclusion or any assumption;
  it introduces no independent object. In particular no hypothesis on that
  ideal is introduced in Lean.
- The ambient commutative algebra is `S : Type uS`, `[CommRing S]`,
  `[Algebra (f.pullback g) S]`. Its sole flatness condition is
  `[Module.Flat (f.pullback g) S]`. There is no algebra finite-presentation
  condition.
- The three component algebras are literally
  `S ⊗[f.pullback g] B`, `S ⊗[f.pullback g] A'`, and
  `S ⊗[f.pullback g] A`. These use the recorded tensor-product definition.
  Equations `hSB`, `hSA'` specify the canonical maps `b ↦ 1 ⊗ b` and
  `a' ↦ 1 ⊗ a'`. Equations `hBA`, `hA'A` specify the maps on pure tensors
  `s ⊗ b ↦ s ⊗ f b`, `s ⊗ a' ↦ s ⊗ g a'`. Since pure tensors generate,
  these equations uniquely determine the maps. The two `IsScalarTower`
  instances with bottom ring `S` express their compatibility with the
  existing left `S`-action. These canonical structures exist for every ring
  datum in the node; no added existence or finiteness assumption is hidden.
- `N : Type uN` and `M' : Type uM` have additive commutative group and component
  module instances. Their `B`, `A'`, and `S` module instances and scalar towers
  express restriction along the canonical maps just specified. Tower
  compatibility forces these actions to be the restrictions: apply
  `smul_assoc` to the scalar acting on `1` in the intermediate algebra.
- The two finite-presentation hypotheses are exactly
  `[Module.FinitePresentation (S ⊗[f.pullback g] B) N]` and
  `[Module.FinitePresentation (S ⊗[f.pullback g] A') M']`.
  Relative flatness is exactly `[Module.Flat B N]` and `[Module.Flat A' M']`,
  not flatness over the larger component algebras.
- The overlap is written in extension-of-scalars order as
  `(S ⊗[R] A) ⊗[S ⊗[R] B] N` and
  `(S ⊗[R] A) ⊗[S ⊗[R] A'] M'`. These are canonically the node's
  `N ⊗[B] A` and `M' ⊗[A'] A`: the first identification sends
  `(s ⊗ a) ⊗ n` to `(s • n) ⊗ a` and has inverse
  `n ⊗ a ↦ (1 ⊗ a) ⊗ n`; use the identical formulas with `A'`, `M'`
  on the other side. Balancing follows from the canonical algebra-map
  equations, and both composites are the identity on pure tensors.
  They respect the `S ⊗[R] A` action. Thus `φ`, the linear equivalence
  over `S ⊗[R] A` between these two tensors, is exactly the node's
  specified isomorphism transported by canonical tensor identifications.
  It is arbitrary among such isomorphisms, not replaced by an unspecified
  map or by a stronger compatibility assumption.
- The canonical maps into the overlap are `TensorProduct.mk ... 1`, namely
  `n ↦ 1 ⊗ n` and `m' ↦ 1 ⊗ m'`. The first is followed by `φ`.
  `LinearMap.restrictScalars S` views these as `S`-linear maps; composing
  with `LinearMap.fst S N M'` and `LinearMap.snd S N M'` gives the two maps
  from the product. Their difference has kernel exactly the pairs
  `(n,m')` with equal overlap images. Its inherited submodule action is
  the coordinatewise `S`-action, so it is precisely `P` under the above
  canonical identification of the overlap. There is no extra vanishing
  or equality hypothesis in the conclusion.
- The conclusion `Module.FinitePresentation S (LinearMap.ker ...)` asserts
  exactly finite presentation of that patched module over `S`.
- There is no `Nontrivial`, Noetherian, nilpotence, or finite-generation
  hypothesis on the rings, the kernel ideal, or the ambient algebra.
  Each ring/module has an explicitly declared universe. `autoImplicit`
  is disabled; no independent small universe for test objects occurs.

Dependency declarations used:

- `def-weil-pbc-module-tensor-product`: Mathlib's `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, the canonical map
  `TensorProduct.mk`, and the tower/cancellation interfaces in
  `Mathlib.LinearAlgebra.TensorProduct.Tower`. The statement uses precisely
  these existing tensor products, not a new quotient construction.
- `def-sc-finitely-presented-module`: `Module.FinitePresentation` from
  `Mathlib.Algebra.Module.FinitePresentation`. Its finite generating set
  and finite relation kernel are equivalent to the displayed finite free
  presentation in the node.
- `def-weil-pbc-flat-ring-map`: `Module.Flat` and `RingHom.Flat`, publicly
  available from `Mathlib.RingTheory.RingHom.Flat`. The former is the
  module notion in this statement; the latter's recorded definition
  explicitly uses that same module notion for a ring homomorphism.
- Existing structural interfaces: `RingHom.pullback`, `pullbackFst`,
  `pullbackSnd` in `Mathlib.RingTheory.LocalRing.Pullback`;
  `LinearMap.ker`, `fst`, `snd`, and `restrictScalars`; the commutative
  tensor algebra in `Mathlib.RingTheory.TensorProduct.Basic`.

The proof-dependency Mathlib modules are imported with plain `import`:
right exactness (`lTensor_exact`, `rTensor_exact`), tensor over a quotient
(`TensorProduct.quotTensorEquivQuotSMul`; cancellation is already publicly
imported), and flat quotient tensor injectivity
(`LinearMap.lTensor_injective_of_exact_of_flat`). The finite-presentation
kernel theorem `Module.FinitePresentation.fg_ker` is already imported by the
finite-presentation statement dependency. I read these full signatures.
The three patching proof prerequisites
`lem-sfb-flat-module-fibre-product-patching`,
`lem-sfb-finite-module-fibre-product-patching`, and
`lem-sfb-patched-module-base-change` have neither a Lean record nor a
Mathlib match in the read repository. They are proof dependencies, not
notions missing from this statement; no unpublished module is imported.
All eight proof steps, with their node citations, are in the theorem docstring.

Edge cases checked before finalizing:

- If `g` is an isomorphism, the pullback reduces to `B` and the patched
  module reduces to `N`; the overlap and kernel formulas still apply.
- If `A` is the zero ring, the pullback is `B × A'`, the overlap tensor is
  zero, and the patched module is the product of the component modules.
- If the ambient algebra `S` is zero, both component modules and their
  fibre product are zero. All canonical algebra and tower data exist.
- Zero component modules are permitted. The isomorphism requires only
  their overlap extensions to agree; no nonzero condition was inserted.
- A trivial kernel ideal, a non-finitely generated kernel ideal, and
  rings with no Noetherian assumption are all admitted. The hypotheses
  depend only on surjectivity and the stated relative flatness and finite
  presentation conditions.

Searches performed using the prescribed `msearch.py` wrapper:

- LeanFinder query: “A fiber product of modules over a surjective ring
  pullback is finitely presented over a flat ambient algebra when the
  two modules are finitely presented and relatively flat”. Eight hits:
  `Module.FinitePresentation.trans`, `FinitePresentation.of_isBaseChange`,
  `instFinitePresentationTensorProduct`, and other base-change/factorization
  results; none states the patching result.
- Loogle query: `Module.FinitePresentation, TensorProduct`. Five hits,
  including `instFinitePresentationTensorProduct` and
  `Module.FinitePresentation.isBaseChange_map`; none states this result.
- Grep query: `pullback|fibre.product|fiber.product|Milnor`, subdirectory
  `RingTheory`. Thirteen hits. The ring pullback already exists as
  `RingHom.pullback`; the flatness hits concern preservation of finite
  limits, not relative finite presentation of a patched module.
- LeanSearch query: “Finite presentation of relatively flat modules
  patched over a fiber product of rings with a flat ambient algebra”.
  Eight hits, including flat descent, module finite presentation from
  algebra finite presentation, tensor extension, and finite projective
  criteria; none is this patching statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for patching names,
  fibre/fiber products, relative finite presentation, `08KP`, the Stacks
  lemma label, and the proposed declaration name, plus the required
  node-id search in `lean/WeilConjectures`, found no existing declaration
  stating this node. `dag/lean_names_upstream.json` contained no match
  for the proposed name or source tag. Mathlib source searches found
  the existing pullback, tensor, and module interfaces used above.

There is no statement correction, disputed statement, new node, dependency
record repair, or change to the accepted split. The only node field changed
is `lean`.

## Second reading by Q90

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
