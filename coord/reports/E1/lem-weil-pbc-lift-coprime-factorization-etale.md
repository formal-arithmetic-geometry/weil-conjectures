## Worker report

The module `Sheaf.RingTheory.EtaleLiftCoprimeFactorization` states
`Polynomial.exists_etale_lift_coprime_factorization`, with the sole proof `sorry`.
It states exactly the arbitrary-ideal lifting result of Stacks Tag 07M1.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- A commutative ring A: `{A : Type u} [CommRing A]`.
- An arbitrary ideal I: `(I : Ideal A)`.
- A monic polynomial f: `(f : A[X]) (hf : f.Monic)`.
- Given factors over A/I: `(g₀ h₀ : (A ⧸ I)[X])`.
- Their product is the reduction of f:
  `hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀`.
- The first factor has invertible leading coefficient:
  `hleading : IsUnit g₀.leadingCoeff`.
- The factors generate the unit ideal: `hcoprime : IsCoprime g₀ h₀`.
  Mathlib's predicate expresses the existence of a Bezout identity in the polynomial ring.
- There exists a commutative extension ring and ring map:
  `∃ (B : Type u) (_ : CommRing B) (φ : A →+* B)`.
- Spec B → Spec A is étale:
  `AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))`.
- IA' is the extended ideal `I.map φ`. The induced map, rather than an arbitrary
  quotient isomorphism, is bound as
  `α := Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map`.
  `Function.Bijective α` says this ring homomorphism is an isomorphism.
- The lifted polynomials: `∃ g h : B[X]`.
- Their product is f mapped to B: `f.map φ = g * h`.
- Their reductions are the given factors transported along the induced map:
  `g.map (Ideal.Quotient.mk (I.map φ)) = g₀.map α` and
  `h.map (Ideal.Quotient.mk (I.map φ)) = h₀.map α`.

Dependency used: `def-weil-etale-morphism` is realized by
`AlgebraicGeometry.Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
Its complete signature and affine-local docstring were read in the pinned Mathlib source;
it is the node's scheme-morphism notion. The other imports supply existing Mathlib
polynomial monicity, coprimality, and induced ideal quotient maps. In particular
`Ideal.quotientMap` was read in `Mathlib.RingTheory.Ideal.Quotient.Operations`.

Edge cases checked: no Nontrivial assumption on A or its quotient, no properness
assumption on I, and no degree restriction. For I = top the quotient is the zero ring,
where the hypotheses still make sense (0 = 1 and 0 is a unit); the conclusion asks for
an extension with the same zero quotient. The zero ring A and its polynomials are
included. Constant monic f = 1 and unit constant factors are included. The conclusion
adds neither monicity nor coprimality of the lifted factors, as neither is a clause
of this node. The extension carrier uses the same universe as A: the source's
construction uses localization and a finitely presented universal factorization ring,
which have carriers in Type u, as does Mathlib's residue-field lifting theorem.
All variables and the universe are explicitly bound.

Searches made with `/home/ubuntu/weil-launcher/msearch.py`:

- leanfinder: "Lift a coprime factorization of a monic polynomial modulo an ideal to
  an etale ring extension inducing an isomorphism modulo that ideal". Eight results,
  including `Polynomial.instEtaleUniversalCoprimeFactorizationRing` and square-zero
  lifting for standard étale pairs. None states arbitrary-ideal quotient-trivial lifting.
- loogle: `Algebra.Etale, IsCoprime, Polynomial.map`. One result:
  `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`.
  Read its full signature and docstring: it assumes a prime, factors over its residue
  field, and supplies an extension prime and residue-field isomorphism. It is not
  the arbitrary ideal quotient statement and cannot serve as an existing declaration.
- leansearch: "coprime polynomial factorization modulo ideal lifts etale extension
  quotient isomorphism". Service unavailable: Internal Server Error.
- grep: `07M1|lift.*factorization|exists_etale.*factor` in Mathlib/RingTheory.
  Only the universal factorization map lifting correspondence was found.
- rg in the source WeilConjectures tree for the node id, `lift_factorization`, and
  `exists_etale.*factor`: only unrelated smooth-morphism slicing results.
- rg in `lean/Sheaf` for coprime lifting and Tag 07M1: the existing
  `FactorizationLocallyNilpotent.lean` is a different result, requiring a locally
  nilpotent ideal and producing a unique factorization without an extension.
- rg for the chosen declaration name and coprime lifting in the source, the project
  Lean modules, and `dag/lean_names_upstream.json`: no declaration-name collision.

The local literature checkout is absent. Read the complete statement and proof from
https://stacks.math.columbia.edu/tag/07M1 instead; both agree with the node. The docstring
contains all four DAG proof steps and their cited nodes, including the normalization,
the zero quotient case, composition, and undoing the unit twist.

Validation: server `scompile.py E1 lem-weil-pbc-lift-coprime-factorization-etale`
compiled the module in 1.7 seconds, exit code 0, with no warnings or errors.
The independent second reading is left for the dispatched second reader.

## Second reading by E1

I read the node statement, its Stacks source (More on Algebra, Tag 07M1), the dependency
`def-weil-etale-morphism`, and the worker module independently. The correspondence is:

- `A` and `[CommRing A]` render the commutative base ring; `I : Ideal A` renders the
  arbitrary ideal; `f : A[X]` and `hf : f.Monic` render the monic polynomial.
- `g₀ h₀ : (A ⧸ I)[X]` render the factor polynomials over the quotient. `hfactor` is
  the equation that the image of `f` under `Ideal.Quotient.mk I` is `g₀ * h₀`.
- `hleading : IsUnit g₀.leadingCoeff` is exactly the invertible-leading-coefficient
  hypothesis, and `hcoprime : IsCoprime g₀ h₀` is exactly generation of the unit ideal.
- `∃ B [CommRing B] φ` renders the étale extension and ring map. The following
  `AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom φ))` is the dependency's
  scheme-morphism notion of étale.
- The `let α := Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map` binds the induced
  quotient map `A ⧸ I → B ⧸ I.map φ`; `Function.Bijective α` says it is an isomorphism.
- `∃ g h : B[X]` and `f.map φ = g * h` render the lifted factorization, while the two
  subsequent `Polynomial.map` equations render that both reductions are the α-images of
  the given factors. Quantifier and conjunction order agrees with the node.

No mismatch was found, so no source or Lean change was necessary. The quotient map is
induced by `φ` and the extended ideal, rather than an unrelated isomorphism. The same
universe `Type u` for `B` is permitted by the constructive étale factorization used in the
source and does not exclude the zero ring, zero ideal, or arbitrary quotient cases.

Edge cases checked: `I = ⊤` and the zero quotient, the zero base ring, constant monic
`f = 1`, unit constant factors, and empty/zero polynomial support. No nontriviality,
properness, degree, characteristic, or finiteness assumptions are added; the conclusion
also does not add monicity or coprimality of the lifted factors.

Searches were rechecked with `msearch.py` (LeanFinder, Loogle, and LeanSearch), `rg` in
Mathlib, `WeilConjectures`, and `lean/Sheaf`, and the upstream-name index. The only close
Mathlib result is the residue-field theorem
`Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`, which has a
prime-residue-field hypothesis and is not this arbitrary-ideal lifting statement. No
existing declaration matches this node.
