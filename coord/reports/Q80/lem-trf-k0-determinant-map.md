## Worker report

The module `Sheaf.RingTheory.K0DeterminantMap` states
`Module.FiniteProjectiveK0.exists_determinantMap`, with `sorry` as its sole proof.
No definition, helper theorem, or new node is introduced. No statement correction is needed.

The source was read in `literature/stacks-project/more-algebra.tex`: the K₀ recall
immediately before `lemma-det` (Tag 0AFX), the lemma and its proof, and
`lemma-invertible` (Tag 0B8I) with the following Picard-group description.
The theorem specializes precisely the node's rank-one and ring clauses, rather than
adding a formula for arbitrary constant ranks that this node does not state.

Hypothesis and clause correspondence:

- A commutative ring S is `(S : Type u) [CommRing S]`; no nonzero or domain assumption.
- The specified presented K₀ is `Module.FiniteProjectiveK0 S`, and its module class
  is the recorded `Module.FiniteProjectiveK0.mk S Q`. The actual quotient construction
  in `Sheaf.RingTheory.FiniteProjectiveK0` is imported, not recreated.
- The Picard group is `CommRing.Pic S` from `Mathlib.RingTheory.PicardGroup`.
  Its definition is the small type of isomorphism classes of tensor-invertible modules.
  This is the same group as the node's finite projective prime-local rank-one modules:
  Tag 0B8I identifies invertibility with finite locally free rank one, and finite
  projectivity identifies finite locally free modules with finite projective modules.
  Mathlib provides finite and projective instances for invertible modules, localization
  preserves invertibility, and over a local ring such modules are free and hence
  isomorphic to the ring (`Module.Invertible.free_iff_linearEquiv`). Conversely the
  local evaluation map is an isomorphism for prime-local rank-one finite projectives,
  so its global evaluation map is an isomorphism, the defining `Module.Invertible`.
  The group law is tensor product, by `CommRing.Pic.mk_tensor`; the identity class is
  represented by S, by `CommRing.Pic.mk_self`. No extra choice of Picard group is made.
- Existence of the group homomorphism is
  `∃ det : Module.FiniteProjectiveK0 S →+ Additive (CommRing.Pic S)`.
  `Additive` simply writes the tensor group law additively; it imposes no extra data.
- For every Q, the binders are `(Q : Type v) [AddCommGroup Q] [Module S Q]`
  `[Module.Finite S Q] [Module.Projective S Q]`. Its universe v is arbitrary and independent
  of the ring universe u; finite generation allows the recorded K₀ construction to
  represent Q by a quotient in the ring universe. No invertibility assumption is added.
- Localization at every prime, free of rank one, is explicitly
  `∀ (p : Ideal S) [p.IsPrime], Nonempty (LocalizedModule p.primeCompl Q ≃ₗ[
  Localization p.primeCompl] Localization p.primeCompl)`.
  A linear equivalence with the localized ring says exactly free of rank one,
  avoiding the ambiguity of natural-number finrank without a freeness hypothesis.
- The equality `det([Q]) = [Q]` is expressed by
  `Nonempty (CommRing.Pic.AsModule (det (mk S Q)).toMul ≃ₗ[S] Q)`.
  A Picard representative is isomorphic to Q exactly when the Picard element is Q's
  isomorphism class: this follows directly from the quotient definition, and is reflected
  in `CommRing.Pic.mk_eq_iff`, `CommRing.Pic.ext_iff`, and `CommRing.Pic.mk.linearEquiv`.
  This formulation allows Q's class to be specified without requiring a separately proved
  `Module.Invertible S Q` instance in the statement. It does not replace the canonical
  class by an arbitrary map or weaken the equality to nonemptiness of a module.
- The last clause is `det (mk S S) = Additive.ofMul (1 : CommRing.Pic S)`.
  The identity here is the tensor unit represented by S, exactly as in the node.

Dependency declarations read and used:

- `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`: finite generation.
- `Mathlib.Algebra.Module.Projective`, `Module.Projective`: projectivity.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`: localization.
- `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`: the freeness notion;
  rank-one freeness is rendered by its equivalent linear-isomorphism form.
- `Sheaf.RingTheory.FiniteProjectiveK0`, `Module.FiniteProjectiveK0` and
  `Module.FiniteProjectiveK0.mk`: the exact prescribed K₀ construction and classes.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct`: the tensor law underlying Pic.

Proof dependencies are imported without `public`: the recorded
`Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence` (read its declaration signatures
and proof docstrings, especially `Module.determinantModule_finite_projective` and
`Module.existsUnique_determinantExactSequence`), `Mathlib.LinearAlgebra.ExteriorPower.Basis`
(the first-exterior-power specialization), and `Mathlib.RingTheory.Localization.BaseChange`
(tensor localization). The abelian-group presentation dependency is already publicly
imported by `Sheaf.RingTheory.FiniteProjectiveK0`.
The theorem docstring carries all four proof steps, including the Picard-group comparison,
zero-chart case, isomorphism invariance, direct-sum relations, and ring normalization.

Edge cases checked: the zero ring is included (no primes and all modules subsingleton;
Pic and K₀ trivial); Q = S has its canonical localized rank-one equivalences and yields
the explicit normalization. Over a field, K₀ is ℤ and Pic is trivial; for k × k, ranks can
vary between components but rank-one Q has rank one at each prime. A nontrivial invertible
ideal over a Dedekind domain is allowed, so the statement does not force all Q free.
The zero module over a nonzero ring fails the rank-one premise. No characteristic,
connectedness, or integral-domain restriction was introduced. Arbitrarily large module
universes are admitted. The final theorem is a statement only, with no proofs supplied.

Searches made using the prescribed `msearch.py` wrapper:

- LeanFinder: `determinant homomorphism from K0 to Picard group` returned
  `Submodule.unitsToPic`, `CommRing.relPic`, `CommRing.Pic.mk`, Pic group instances,
  `CommRing.Pic.mapRingHom`, and `CommRing.Pic.AsModule`; none has K₀ as its source.
- Loogle: `CommRing.Pic, Module.Finite, finite projective` returned no matches
  (unknown identifier `finite`). The exact candidate Pic declarations were then read
  in source, including their complete signatures and docstrings.
- Grep: `K_0|Grothendieck|determinant|Picard` in Mathlib `RingTheory` returned the Picard
  group and ordinary determinant material, with no K₀ determinant homomorphism.
- LeanSearch: `determinant homomorphism from the Grothendieck group of finite projective
  modules to the Picard group` returned `Matrix.detMonoidHom`, `Matrix.GeneralLinearGroup.det`,
  `LinearMap.det`, `LinearEquiv.det`, and ordinary determinant basis lemmas; no match.
- Direct rg in upstream `WeilConjectures`, side `lean/Sheaf`, Mathlib, and
  `dag/lean_names_upstream.json` for `FiniteProjectiveK0`, determinant/Picard names,
  `FiniteProjectiveK0.*(det|Pic)|exists_determinant.*[Kk]0|exists_determinantMap`, plus
  the item id in upstream: no existing statement or name collision. Side K₀ and
  `K0ClassTrivialInvertible` are respectively the dependency and a downstream consumer,
  not this theorem. Mathlib's Picard definition is reused without a private copy.

Validation: `scompile.py Q80 lem-trf-k0-determinant-map` compiled the final file cleanly
as sandbox and library module (2.7 s and 2.3 s). `set_option autoImplicit false` checks
explicit binding of every universe and variable. No warnings or errors.
No STATEMENT-DISPUTED flag or dependency fault remains.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
