## Worker report

Item: `lem-sfb-finite-hopf-dual-pairing`, group Q34, stage 2.
Module: `Sheaf.RingTheory.HopfAlgebra.FiniteDualPairing`.
The unchanged node is realized jointly by the fifteen declarations listed in `lean.declarations`.
The main declaration is `HopfAlgebra.finiteDual_pairing_criterion`.

The module constructs the dual coproduct by transposing multiplication and applying the
inverse of `TensorProduct.dualDistribEquiv`, and defines the counit by evaluation at one.
The dual antipode is actual precomposition with the original antipode. Their laws are
separate named theorem statements; the Coalgebra, Bialgebra and HopfAlgebra instances
refer to those proofs and contain fully specified data. The convolution ring and its
commutativity come from Mathlib, not a second multiplication definition.

Clause-by-clause correspondence:

- The commutative base ring is `(R : Type u) [CommRing R]`.
- The associative unital (possibly noncommutative) algebra B is `(B : Type v) [Ring B]
  [HopfAlgebra R B]`. Mathlib's HopfAlgebra extends Bialgebra (Algebra and Coalgebra),
  requiring both the coproduct and counit to preserve multiplication and the unit,
  coassociativity, both counit identities, and both antipode identities. The full
  signatures in HopfAlgebra/Basic, Bialgebra/Basic and Coalgebra/Basic were read.
- Finite freeness is `[Module.Free R B] [Module.Finite R B]`, and cocommutativity is
  `[Coalgebra.IsCocomm R B]`. Module.Free is exactly the dependency's recorded notion.
  Mathlib's finite chosen basis construction handles a subsingleton base ring too.
- Tensor products use the dependency's `TensorProduct`, over R (over T after extension).
- The dual is `WithConv (Module.Dual R B)`. This is Mathlib's existing convolution
  synonym, identified with Hom_R(B,R) by `WithConv.linearEquiv`; the underlying
  additive module and scalar action are unchanged. `finiteDualCoalgebraData`,
  `finiteDualCoalgebra`, `finiteDualBialgebra`, `finiteDualAntipode` and
  `finiteDualHopfAlgebra` supply the specified operations and Hopf structure.
- The multiplication formula `(fg)(b)=(f tensor g)(Delta_B b)` is conjunct 1 of
  `finiteDual_formulas`, using `LinearMap.mul'` after `TensorProduct.map`.
  Conjunct 2 states `1 b = Coalgebra.counit b`.
- The coproduct formula is conjunct 3 of `finiteDual_formulas`: map away the WithConv
  wrappers, evaluate through `TensorProduct.dualDistrib` at `b tensor b'`, obtaining
  `f (b*b')`. This determines the coproduct by the recorded tensor-duality equivalence.
- The counit `f(1)` and antipode `f composed with S_B` are conjuncts 4 and 5.
  `finiteDual_bialgebra_axioms` records the seven coalgebra/bialgebra laws, and
  `finiteDual_antipode_axioms` records both antipode laws for these actual operations.
- Every commutative base algebra is `(T : Type z) [CommRing T] [Algebra R T]`, with no
  flatness condition. `finiteDualBaseChange R B T` is the concrete evaluation map,
  built from `Module.Dual.baseChange` and `LinearMap.liftBaseChange`.
  `finiteDual_baseChange` supplies a `BialgEquiv` with exactly that underlying map,
  explicitly preserving antipodes. Thus it is a Hopf isomorphism. Its last conjunct
  states the requested formula `t*t'*algebraMap R T (f b)` on both pure tensors.
- The extra generation assumption is `P : Set B` and `Algebra.adjoin R P = top`.
  The primitive assumptions are exactly both conjuncts of `hprim`: the coproduct is
  `b tensor 1 + 1 tensor b`, and the counit is zero, for every b in P.
- The second Hopf algebra is `(C : Type w) [CommRing C] [HopfAlgebra R C]`, with no
  finiteness, freeness, flatness, or cocommutativity hypothesis on C.
- Its convolution dual is the existing `WithConv (Module.Dual R C)`, hence each
  `r : B →ₐ[R] WithConv (Module.Dual R C)` is exactly a unital convolution algebra map.
  `finitePairingTranspose r.toLinearMap` is constructed with `LinearMap.flip` and
  the WithConv linear equivalences. Its value at c,b is definitionally r(b)(c).
- The first conjunct of `finiteDual_pairing_criterion` says this fixed linear map
  underlies a bialgebra homomorphism preserving antipodes if and only if the displayed
  derivation identity holds for all b in P and all c,c'. This is exactly the Hopf
  homomorphism criterion, with all coefficients and multiplication orders retained.
- Its second conjunct states `exists unique r` for every bialgebra map t with this
  transpose. A bialgebra map between Hopf algebras automatically respects antipodes,
  by the inverse-uniqueness argument in node proof step 9; Mathlib has BialgHom rather
  than a separate HopfAlgHom. Thus this quantifier is exactly over Hopf maps.
  Equality of linear maps fixes every pairing value and expresses the unique converse.
- `finiteDual_pairing_natural` gives both naturality squares, on all evaluations:
  precompose in B by a Hopf map beta, or in C by a Hopf map gamma. Equality on all
  evaluations is equality of the transposes; the unique inverse is therefore natural too.
- `finiteDual_pairing_baseChange` states that the scalar-extended pairing defines
  an algebra map rT, gives equality of the two ways to transpose and extend scalars,
  and states the extended pairing's value `u*v*algebraMap R T (r b c)`.
  These are equalities of the actual maps, using the same dual comparison as above.
  They give scalar compatibility of the correspondence and its formulas. No
  isomorphism involving the dual of infinite C is assumed or asserted.
- `finiteDual_baseChange_comp` states the full equality for successive scalar
  extensions, using Mathlib's `AlgebraTensorModule.cancelBaseChange` on tensor domains
  and its dual map on dual codomains. This records the final composition clause of
  node proof step 11 without choosing any comparison isomorphisms.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`.
  Read the class and documentation, including `Module.free_iff_set`; finite chosen
  basis behavior was checked in FreeModule/Finite/Basic.
- `def-weil-pbc-module-tensor-product`: `Mathlib.LinearAlgebra.TensorProduct.Defs`,
  `TensorProduct`; Basic's `TensorProduct.lift`, `lift.tmul`, `ext'`, and Map's
  `LinearMap.rTensor`, `rTensor_tmul` were read. All tensor maps use these operations.
- Proof dependency `lem-sfb-convolution-linear-map-algebra`: the recorded
  `Mathlib.RingTheory.Coalgebra.Convolution` declarations `LinearMap.convRing`,
  `convAlgebra`, `convMul_apply`, `convOne_apply`, `convAlgebraMap_apply` were read.
  The module imports that file publicly because its convolution algebra occurs in
  the statement itself; `convCommRing` supplies the required commutativity.
- Proof dependency `lem-sfb-finite-free-tensor-dual`: the recorded
  `Mathlib.LinearAlgebra.Contraction`, `TensorProduct.dualDistribEquiv`, and
  Dual/Lemmas's `TensorProduct.dualDistrib_apply` were read. The equivalence is
  used directly as data of the dual coproduct, so its import is public as well.

All other imports provide structures and operations actually used: Hopf tensor products,
bialgebra morphisms/equivalences, dual base change, finite/free scalar extension, and
`Algebra.adjoin`. The old Sheaf CompactObject example is withdrawn; the node's current
record points to `WeilConjectures.CategoryTheory.CompactObject`, whose header and
statement were read as the current example.

Source checked locally: Milne's PDF printed pp.65--66 (Definition 3.3 and discussion 3.4)
and pp.222--223 (Propositions 11.35--11.36), with pdftotext. As the node already says,
the arbitrary-base-ring primitive criterion is the agent-supplied extension of this
construction; the report does not attribute that general theorem to Milne.

Edge cases checked before and during drafting:

- No Nontrivial assumption on R, B, C or T. Zero rings and zero scalar extensions
  remain included. An empty basis is allowed; Hopf counitality itself forces a
  zero underlying algebra over a nonzero ring to be impossible, without extra assumptions.
- P may be empty: B=R with its standard Hopf structure is covered; the generator
  condition is vacuous and the transposed scalar map is Hopf, as required.
- In characteristic two (indeed every characteristic), x=2x implies x=0 by additive
  subtraction. No division by two is used or imposed.
- Noncommutative B is permitted. Only C and the convolution dual of cocommutative B
  are commutative. No invertibility of the antipode is assumed.
- C may be infinite or nonflat; all its dual occurrences are convolution or actual
  functional extension, never a finite-dual equivalence.
- T may be nonflat (e.g. an arbitrary quotient of R). The finite-free dual comparison
  uses a finite basis, so the statement includes this case.
- R, B, C, T and the naturality arguments have explicitly declared, independent
  universes. No unbound implicit variables, no extra size equation, no local notation,
  no chosen arbitrary maps, and no definition with postponed data occur.

Searches for an existing statement (all via msearch.py unless indicated):

- LeanFinder: "Finite free cocommutative Hopf algebra dual is commutative Hopf algebra
  with primitive generator transpose pairing criterion" returned 8 constructors and
  antipode-identity hits, including `CommSemiring.toHopfAlgebra`, `HopfAlgebra.ofAlgHom`,
  and antipode sums. None constructs this dual or states the pairing criterion.
- Loogle: "HopfAlgebra, Dual" returned zero hits (Dual was not a recognized standalone
  identifier). This was supplemented by the successful semantic and source searches.
- LeanSearch: "Linear dual finite free Hopf algebra primitive generator Hopf pairing"
  returned 8 hits on dual pairings, freeness and finite-dimensional pairings, including
  `Module.dual_free`; none was the Hopf-dual/pairing theorem.
- Mathlib grep: `dual.*Hopf|Hopf.*dual|bialgebra.*pairing` returned zero hits.
- Project rg: `HopfAlgebra|hopfDual|Hopf.*[Pp]airing|finiteHopf` over both
  `lean/WeilConjectures` and `lean/Sheaf` found Hopf infrastructure and related modules.
  `FiniteDualHopfModule` was read: it supplies a field-valued action/coaction, not this
  dual Hopf structure. `Paper/DualBaseChange` is about six-functor sheaf duality.
- `grep -rn lem-sfb-finite-hopf-dual-pairing lean/WeilConjectures` found no upstream
  declaration. The upstream name index search for finite Hopf duals/pairings likewise
  found no candidate. Exact searches of all fifteen new declaration names in Mathlib,
  WeilConjectures and Sheaf found no collisions.

No new nodes, dependency repairs, statement correction or disputed statements.
The only node field changed is `lean`. Every helper is part of the very dual operations,
canonical comparison or transpose whose statement this node already owns.

The eight postponed named statements are `finiteDual_bialgebra_axioms`,
`finiteDual_antipode_axioms`, `finiteDual_formulas`, `finiteDual_baseChange`,
`finiteDual_baseChange_comp`, `finiteDual_pairing_criterion`,
`finiteDual_pairing_natural` and `finiteDual_pairing_baseChange` in namespace
`HopfAlgebra`. Each has exactly `by sorry`, a source, the node identifier, and the
relevant complete natural-language proof steps in its docstring. Nothing is proved.
All seven definitions/instances have real data; the instances' proof fields reference
only the separately named axiom theorems.

Validation: scompile.py compiled the final module in both sandbox and library module
modes against the published live build, with no errors or unexpected warnings.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
