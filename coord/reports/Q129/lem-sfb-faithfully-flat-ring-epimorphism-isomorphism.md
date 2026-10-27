## Worker report

The module `Sheaf.RingTheory.FaithfullyFlatRingEpimorphism` states
`Algebra.bijective_algebraMap_of_faithfullyFlat_of_epi`, with proof `sorry`.
It is the full faithfully-flat ring-epimorphism lemma of Stacks Tag 04VU,
`literature/stacks-project/algebra.tex`, lemma-faithfully-flat-epimorphism.
I read that lemma, its proof, and the preceding lemma-epimorphism. No definition,
dependency repair, new node, or statement correction is needed. The node copy changes
only `lean`. There is no STATEMENT-DISPUTED issue.

Hypotheses and conclusions, clause by clause:

- The commutative rings with identity are `(R : Type u) (S : Type v)` with
  `[CommRing R] [CommRing S]`. The universes are independent and explicitly bound.
- The unital homomorphism f is `algebraMap R S`, supplied by `[Algebra R S]`,
  following the project's faithfully-flat ring-map convention (STATE, FAITHFULLY
  FLAT RING MAPS). This encodes every ring homomorphism: an arbitrary `f : R →+* S`
  supplies the algebra structure `f.toAlgebra`, whose algebra map is f. It neither
  fixes a special map nor adds an injectivity assumption.
- Faithful flatness is precisely `[Module.FaithfullyFlat R S]`, the declaration
  recorded by `def-weil-pbc-faithfully-flat-ring-map`. This is equivalent to the
  node's exactness preservation and reflection by
  `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`. I read its class declaration,
  docstring, and this equivalence in `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`.
  I also read `RingHom.FaithfullyFlat` and `faithfullyFlat_algebraMap_iff` in
  `Mathlib.RingTheory.RingHom.FaithfullyFlat` to check the map/algebra encoding.
- The epimorphism hypothesis is the explicit cancellation property `hepi`:
  for a commutative ring B and unital maps `a b : S →+* B`, equality of
  `a.comp (algebraMap R S)` and `b.comp (algebraMap R S)` implies `a = b`.
  B lives in `Type (max u v)`. This is a sufficient universe for the tensor-square
  test, hence is equivalent to unrestricted ring epimorphy. Indeed, cancellation
  for the two maps to S tensor_R S makes those inclusions equal. Applying the
  tensor-product universal property then gives cancellation into any commutative
  ring of any universe. Thus this encoding does not impose a size restriction on
  the mathematics or introduce a vacuous test universe. No independent lower
  test-ring universe is used. No new predicate is defined.
- Bijectivity of f is `Function.Bijective (algebraMap R S)`.
- The clause "and hence an isomorphism of rings" is explicit as
  `∃ e : R ≃+* S, e.toRingHom = algebraMap R S`. The equality specifies that the
  original map is the isomorphism. This is equivalent to bijectivity, rather than
  an additional restriction or a claim that the rings are merely abstractly
  isomorphic. The two conclusions are joined by `∧`.
- There is no finite-generation, finite-presentation, nontriviality, domain, or
  field binder. The docstring explicitly records the absence of finiteness.

Dependency declarations and imports:

- Statement dependency `def-weil-pbc-faithfully-flat-ring-map`:
  `Module.FaithfullyFlat`, publicly imported from
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`. The other public imports provide
  the algebra map and ring-equivalence types in the signature:
  `Mathlib.Algebra.Algebra.Basic` and `Mathlib.Algebra.Ring.Equiv`.
- Proof dependency `lem-weil-pbc-algebra-tensor-pushout-universal-property` is a
  Mathlib leaf, using `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`,
  `includeLeft`, `includeRight`, `ext` in `Mathlib.RingTheory.TensorProduct.Basic`,
  and `productMap`, `productMap_apply_tmul`, `productMap_left`, `productMap_right`
  in `Mathlib.RingTheory.TensorProduct.Maps`. I read these declarations and their
  relevant docstrings. Plain import `Mathlib.RingTheory.TensorProduct.Maps`
  supplies the recorded interfaces, including Basic, for the future proof.
- Proof dependency `def-weil-pbc-module-tensor-product` is a Mathlib leaf:
  `TensorProduct` in `Mathlib.LinearAlgebra.TensorProduct.Defs`, and
  `TensorProduct.lift`, `lift.tmul`, `ext'` in
  `Mathlib.LinearAlgebra.TensorProduct.Basic`, read in source. The latter is
  imported plainly for this dependency; it includes the former.
- The proof docstring follows all three DAG steps: epimorphy identifies the two
  tensor inclusions, multiplication is their inverse, and exactness reflection
  descends bijectivity of the tensor map. It also explains the final inverse
  homomorphism. All postponed proof content belongs to this one named DAG theorem.

Edge cases checked mathematically before writing:

- The identity of any commutative ring, including the zero ring, satisfies the
  hypotheses and both conclusions. No `Nontrivial` hypothesis excludes it.
- If S is zero, faithful flatness forces R zero by reflection of tensor
  exactness; the conclusion is correct. A nonzero ring mapping to the zero ring
  is epic but fails faithful flatness.
- The localization Z to Q is a ring epimorphism and flat, but is not faithfully
  flat. This shows the faithful part is essential and is retained.
- The diagonal k to k × k is faithfully flat for a nonzero field k, but the two
  projections disagree while agreeing after composition. It fails `hepi`.
- Independent source and target universes are allowed; the maximum test universe
  contains a lifted tensor square and so detects the required epimorphy.

Searches for reuse (2026-10-24):

- `msearch.py ... leanfinder` with "A faithfully flat epimorphism of commutative
  rings is bijective and an isomorphism": eight hits, headed by
  `RingHom.FaithfullyFlat.codescendsAlong_bijective`, with
  `Module.FaithfullyFlat.bijective_of_tensorProduct` also returned. They are
  descent ingredients requiring a separate base-changed bijectivity argument,
  not this statement. I read the latter's full signature in Descent.lean.
- `msearch.py ... loogle` with `RingHom.FaithfullyFlat, Function.Bijective`:
  two hits, `of_bijective` (the converse) and `codescendsAlong_bijective`.
- `msearch.py ... leansearch` with "A faithfully flat epimorphism of commutative
  rings is an isomorphism": eight hits, including the scheme isomorphism
  criterion, faithful-flat injectivity, and the definitions. No exact match.
- `msearch.py ... grep` for
  `faithfully.*[Ee]pi|[Ee]pi.*faithfully|bijective_of.*[Ee]pi` in RingTheory:
  zero hits.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for faithfully-flat/epi
  phrases found explanatory references in FrobeniusFixedPointsEquiv,
  FlatMonomorphismLocalStructure, and CharZeroCommutativeUnipotentVectorGroup;
  none states this theorem. The item-id search in `lean/WeilConjectures` had
  zero hits. The candidate declaration/module-name search in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` also
  had zero hits.
- Read `Mathlib.Algebra.Algebra.Epi` and
  `Mathlib.Algebra.Category.Ring.Epi`: `Algebra.IsEpi` characterizes the tensor
  multiplication map, and `CommRingCat.epi_iff_epi` relates it to categorical
  cancellation. Their bijectivity/surjectivity theorem requires `Module.Finite`,
  which this node does not assume. The signature keeps the node's cancellation
  formula directly and introduces no private definition.

Validation: `scompile.py Q129 lem-sfb-faithfully-flat-ring-epimorphism-isomorphism`
compiled the delivered file on the server successfully in module mode, both as
the sandbox module and under its library module name (1.1 s and 1.0 s).
No error or non-sorry warning was reported. `set_option autoImplicit false`
enforces explicit binding. Every theorem proof is `sorry`; nothing is proved.

## Second reading by Q129

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
