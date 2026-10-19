## Worker report

The module `Sheaf.RingTheory.UniquePrimeLocalization` states
`IsLocalization.uniquePrimeLocalization`, without proving it. Its four helper declarations
construct the canonical ring map and expose the canonical scalar structures on the two
module expressions. They have real data and reuse Mathlib constructions; they introduce
no independent mathematical notion, extra DAG node, or postponed helper theorem.
The item JSON changes only in `lean`.

Source read: Stacks Project `algebra.tex`, Tag 00EA,
`lemma-unique-prime-over-localize-below`, in particular case (1)+(2)(a) and its proof;
and Tag 00DK, `lemma-tensor-localization`, including its fraction formula and proof.
Tag 00EA gives equality of the two localizations under going up and uniqueness;
finiteness supplies integrality and hence going up, exactly as the node's proof says.
The module consequence is the tensor-localization formula followed by this change of
denominators. No source correction or statement dispute is needed.

Hypotheses and clauses, with their Lean encodings:

- The commutative rings are `{A : Type u}` and `{B : Type v}` with `[CommRing A]`
  and `[CommRing B]`. `[Algebra A B]` encodes precisely the named ring map phi,
  as `algebraMap A B`; commutative ring homomorphisms and these algebra structures
  carry the same data. There is no injectivity or domain assumption.
- Finiteness of B as an A-module is `[Module.Finite A B]`. No finiteness is imposed
  on the module M.
- The two prime ideals are `(p : Ideal A) [p.IsPrime]` and `(q : Ideal B) [q.IsPrime]`.
  Their contraction equation is `hpq : Ideal.comap (algebraMap A B) q = p`.
  The existence part of the unique-prime hypothesis is this specified q, while
  `huniq` quantifies over every prime ideal q' contracting to p and concludes q' = q.
- The submonoid S = A minus p is `p.primeCompl`. The denominators for S inverse B
  are `Submonoid.map (algebraMap A B) p.primeCompl`; the ring is its `Localization`.
  The target is `Localization.AtPrime q`.
- `uniquePrimeLocalizationMap p q hpq` is a B-algebra homomorphism constructed by
  `IsLocalization.liftAlgHom`, using `Algebra.ofId B (Localization.AtPrime q)`.
  The image of every S-denominator is a unit since its contraction is outside p.
  Thus it is exactly b/s maps to b/phi(s), not an arbitrary ring map.
  `Function.Bijective` of this specified algebra homomorphism states that it is
  an isomorphism, equivalently the existence of its algebra inverse.
- Every B-module is quantified by `M : Type w`, `[AddCommGroup M]`, `[Module B M]`.
  `[Module A M] [IsScalarTower A B M]` specify restriction along phi, rather than
  add a condition on the B-module: `Module.compHom M (algebraMap A B)` always
  supplies this action, and tower compatibility forces a acting as phi(a).
  No condition of finite generation, flatness, nonzero module, or faithful action
  occurs. Ring and module universes u, v, w are independent and explicitly bound.
- The exact source `M tensor_A A_p` is `M ⊗[A] Localization.AtPrime p`; its order
  is retained. `uniquePrimeTensorModule` equips it with the usual A_p action by
  transporting the ordinary left action across `TensorProduct.comm` using
  `AddEquiv.module`. Its additive group and underlying tensor product do not change.
- The exact target `M_q` is `LocalizedModule.AtPrime q M`. Its A_p action is
  `uniquePrimeLocalizedModule`: Mathlib's `LocalizedModule.moduleOfIsLocalization`
  gives its B_q action and `Module.compHom` restricts this along the actual map
  `Localization.localRingHom p q (algebraMap A B) hpq.symm`.
- `UniquePrimeModuleEquiv p q hpq M` is merely an abbreviation for `LinearEquiv`
  over A_p, with these two actual module structures supplied explicitly. The
  existential family `e` supplies one such isomorphism for every B-module.
- The first clause for e says exactly that `m tensor (a/s)` maps to
  `LocalizedModule.mk (algebraMap A B a • m)` with denominator phi(s).
  The denominator is explicitly typed as `q.primeCompl`; its proof uses hpq.
  This formula characterizes the induced canonical map; no choice of an unrelated
  equivalence can satisfy the formula.
- The last clause quantifies over arbitrary M, N, `f : M →ₗ[B] N`, and every tensor x.
  Its equation compares `e N ((f.restrictScalars A).rTensor A_p x)` with
  `LocalizedModule.map q.primeCompl f (e M x)`. This is the full naturality square
  for B-linear maps, not only a statement about generators or endomorphisms.

Statement dependencies read and reused:

- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic` (definition and docstring read).
  The additional recorded clauses `Ideal.ResidueField` and `Ideal.Fiber` were also
  inspected in the respective residue-field files; they do not occur in this item.
- `def-weil-pbc-module-localization`: `LocalizedModule`, `LocalizedModule.mk`, and
  `LocalizedModule.mkLinearMap` in `Mathlib.Algebra.Module.LocalizedModule.Basic`.
  `LocalizedModule.AtPrime` comes from its `AtPrime` module;
  `LocalizedModule.map` comes from `Mathlib.RingTheory.Localization.Module`.
  The existing dependency record is usable and does not need alteration.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, its canonical `tmul`, and
  `TensorProduct.comm` and tensor-map APIs exported by `Basic`.
- `def-weil-finitely-generated-module`: `Module.Finite` in
  `Mathlib.RingTheory.Finiteness.Defs`, the class asserting finite generation of
  the top submodule. This is finite module generation, not finiteness of a set.

The recorded proof inputs were also inspected. Their modules are imported without
`public`: `Algebra.IsIntegral.of_finite` in
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`;
`Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime` in
`Mathlib.RingTheory.Ideal.GoingUp`; `Ideal.exists_le_maximal` in
`Mathlib.RingTheory.Ideal.Maximal`; `IsLocalization.prime_localRing_residueField_iso`
in `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`; and
`IsLocalizedModule.rTensor`, `IsLocalizedModule.map_lTensor` in
`Mathlib.RingTheory.Localization.BaseChange`. The theorem docstring gives all five
steps of the node's proof, naming these nodes, including the module inverse and
its fraction-relation check. The only delivered theorem proof is `sorry`.

Edge cases checked: the zero module and arbitrary infinite modules are included;
no module nontriviality or finiteness instance is requested. Zero rings have no
prime ideals, which makes the corresponding prime-hypothesis cases vacuous rather
than silently excluded by a new ring hypothesis. The identity map B = A gives the
usual module localization. Noninjective finite maps, including nilpotent quotients,
are allowed. No step assumes localizations injective or rings reduced. A product
with two primes over p correctly fails the uniqueness assumption. Any prime,
including the zero prime in a domain, is allowed. All denominators are in the
specified prime complements, so a zero denominator is never introduced. Every
universe and variable is explicitly bound.

Searches actually run (no exact existing declaration for the entire statement):

- `msearch.py`, leanfinder:
  `finite algebra unique prime over a prime localization ring isomorphism and module tensor localization`.
  Eight hits, including `IsDedekindDomain.primesOverEquivPrimesOver`,
  `IsLocalization.AtPrime.liesOver_map_of_liesOver`,
  `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`, and
  `Algebra.QuasiFiniteAt.baseChange`. These do not assert the full unique-prime
  finite-algebra theorem with its natural module form.
- `msearch.py`, loogle: `IsLocalization.map, LocalizedModule.map`.
  Successful search with zero hits for the combined query. The individual APIs
  were then located and their full signatures and docstrings read in source.
- `msearch.py`, grep: `unique.*prime.*localiz|localiz.*unique.*prime`, subdirectory
  `RingTheory`. One hit, a comment about minimal-prime localization in
  `Ideal/MinimalPrime/Localization.lean`; this is not the statement here.
- `msearch.py`, leansearch:
  `finite algebra with unique prime above p localization equals localization at that prime and tensor module localization`.
  Eight hits, including `IsLocalization.tensorProduct_isLocalizedModule`,
  `LocalizedModule.AtPrime`, the iterated-localization comparison, and the
  canonical algebra structure on prime localizations. These supply constructions
  and related lemmas, not an exact match for the item.
- `rg` in the upstream `WeilConjectures` tree and in the project's `lean/Sheaf`
  for `uniquePrimeLocalization|unique.*prime.*localiz|lem-trf-unique-prime-localization`:
  no existing declaration for this item; only prose references in other modules.
  The chosen declaration names were also searched in Mathlib, the upstream tree,
  the project tree and `dag/lean_names_upstream.json`, with no collisions.
- Direct Mathlib searches and reads found `IsLocalization.liftAlgHom`,
  `Localization.localRingHom`, `LocalizedModule.moduleOfIsLocalization`,
  `AddEquiv.module`, and the tensor symmetry API. These are reused; no scalar
  restriction, localization, tensor product, or module-map notion is redefined.

Validation: the complete delivered module is checked through the prescribed
`scompile.py` wrapper with the standard file timeout. The final delivery dry run
and push are run after all compiler and preflight findings have been repaired.

## Second reading by Q136

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
