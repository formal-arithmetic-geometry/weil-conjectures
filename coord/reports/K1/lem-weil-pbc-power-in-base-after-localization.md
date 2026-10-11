## Worker report

The module states the finite purely inseparable power calculation after localization. It binds a Noetherian integral domain `A'`, fraction field `K'`, finite domain algebra `E` with fraction field `L`, and finite purely inseparable field extension data. The conclusion supplies a nonzero localization element `s`, defines `A'' = Localization.Away s` and `E'' = E ⊗[A'] A''`, and uses the canonical right tensor inclusion `ι : A'' → E''`.

The characteristic hypothesis is `CharZero K' ∨ ∃ p, Nat.Prime p ∧ ∃ _h : CharP K' p, True`. The characteristic-zero clause is `Function.Surjective ι`, expressing that every localized algebra element comes from the base. The positive-characteristic clause states that for every prime characteristic `p` and every `x : E''`, some `x^(p^n)` equals `ι a` for an `a : A''`.

Dependencies used are Mathlib's `Module.Finite`, `IsPurelyInseparable`, `IsFractionRing`, localization, and tensor-product declarations. The finite/integral morphism dependency's recorded `AlgebraicGeometry.IsFinite` is not needed as a ring-level constructor; the statement uses Mathlib's ring-level `Module.Finite` directly.

Edge cases checked: `s` is explicitly nonzero; `n = 0` is allowed; characteristic zero and positive characteristic are separated; no nonemptiness or positivity restriction is imposed on `E''` elements.

Searches: `rg` over project and source for purely inseparable, localization, and finite-algebra declarations (no exact project statement); Mathlib search of `IsPurelyInseparable`, `IsFractionRing`, `Localization.Away`, and tensor products (used canonical declarations); `msearch.py` searches recorded by the node found no exact localization theorem.

## Earlier second reading (a previous round; superseded)

Read the node and module together. Every node hypothesis is represented by an explicit Lean binder or typeclass: Noetherian integral `A'`, fields `K'` and `L`, domain finite algebra `E`, fraction-ring instances, finite purely inseparable extension, and the characteristic split. The conclusion's nonzero `s`, localization definitions, characteristic-zero surjectivity, and positive-characteristic power-in-image clause match the corresponding clauses. The canonical tensor inclusion is used because `algebraMap A'' E''` is not available automatically for this tensor product.

## Second reading by K1

I independently opened the item, all three statement dependency nodes, their
Mathlib declarations, and the delivered module. No new nodes or dependency
modules accompany this delivery. The node's mathematical statement is unchanged.

Source reading: the literature is not installed in this machine's read-only
clone. I read the server's `literature/stacks-project/algebra.tex`, lines
10600–10785, over ssh. Tag 0BR5 is the universal-homeomorphisms SECTION
`section-universal-homeomorphism`, not a lemma called
`algebra-lemma-purely-inseparable`. Lemma 0BR8 (`lemma-powers`) consumes the
power-in-image calculation; it does not itself state this denominator-clearing
lemma. The source imposes no standing field, Noetherian, normality, or
characteristic assumptions beyond the individual statements. The delivered
lemma is the elementary finite-algebra spreading input described in the node's
proof/source records. I corrected the module's source citations accordingly;
the node's pre-existing stale source.place text was not changed.

Object, hypothesis, and conclusion checklist (each verdict is MATCH after repair):

- Base A': `(A' : Type u) [CommRing A'] [IsDomain A']
  [IsNoetherianRing A']`, exactly a Noetherian integral domain; no normality.
- Fraction field K': `(K' : Type v) [Field K'] [Algebra A' K']
  [IsFractionRing A' K']`. The last declaration is Mathlib's localization at
  `nonZeroDivisors A'`, not an unrelated field containing A'.
- Finite A'-algebra E: `(E : Type w) [CommRing E] [IsDomain E]
  [Algebra A' E] [Module.Finite A' E]`. The finite-morphism dependency explicitly
  defines affine-local finiteness as finite generation as a module.
  I opened `AlgebraicGeometry.IsFinite` in `Mathlib.AlgebraicGeometry.Morphisms.Finite`:
  its `finite_app` is `RingHom.Finite`, whose definition in
  `Mathlib.RingTheory.Finiteness.Defs` is precisely `Module.Finite` with the
  given ring hom's algebra structure. The present ring-level statement therefore
  directly uses that existing notion, rather than inventing a scheme predicate
  or duplicating the dependency. No replacement dependency module is necessary.
- Fraction field L of E: `(L : Type z) [Field L] [Algebra E L]
  [IsFractionRing E L]`, using the same canonical fraction-ring declaration.
- The induced extension L/K': `[Algebra K' L]`, Mathlib's `Algebra` as recorded
  by `def-pc-field-extension`. The implicit commutative diagram is now explicit:
  `[Algebra A' L] [IsScalarTower A' E L] [IsScalarTower A' K' L]` says the two
  composites from A' to L agree. These compatibility binders express the
  extension of the given structure map; they add no mathematical restriction
  to the node's intended fraction-field extension.
- Finite purely inseparable extension: `[Module.Finite K' L]
  [IsPurelyInseparable K' L]`, exactly the two declarations recorded by
  `def-weil-pbc-finite-purely-inseparable-extension`. I opened
  `IsPurelyInseparable` and `isPurelyInseparable_iff_pow_mem` (Stacks 09HE)
  in `Mathlib.FieldTheory.PurelyInseparable.Basic`; with exponential
  characteristic 1 it says the extension is trivial, and with characteristic p
  it says every element has a p-power in the base.
- One localization for both cases: `∃ s : A', s ≠ 0 ∧ ...`. This witness precedes
  both characteristic clauses, as in the node. `Localization.Away s` is A'[1/s]
  and `E ⊗[A'] Localization.Away s` is precisely the specified E''.
- Canonical base inclusion: `Algebra.TensorProduct.includeRight
  (R := A') (A := E) (B := Localization.Away s)`, whose source definition sends
  a to `1 ⊗ₜ a`; no arbitrary map is introduced.
- Characteristic zero: `CharZero K' → Function.Surjective (...)`. The canonical
  inclusion is injective under the compatible domain/fraction-field hypotheses
  (E[1/s] embeds in L and A'[1/s] embeds in K'). Thus surjectivity expresses
  equality of these subrings, E'' = A'', rather than equality of unrelated
  carrier types. No extra conclusion is required to express the node's equality.
- Positive characteristic: `∀ p : ℕ, Nat.Prime p → CharP K' p →
  ∀ x : E ⊗[A'] Localization.Away s, ∃ n : ℕ, ∃ a : Localization.Away s,
  includeRight a = x ^ (p ^ n)`. Field characteristics p > 0 are prime;
  `n : ℕ` includes zero. The existential a expresses membership in the image.
  The quantifier order is s, characteristic p, element x, exponent n, preimage a;
  no uniform exponent was imposed although the proof produces one.

Mismatches found and repaired:

1. H3: the old algebra structures A' → E → L and A' → K' → L were unrelated.
   Without compatibility, inseparability refers to an arbitrary embedding of K',
   whereas localization uses the given A'-algebra E. Added the common A'-algebra
   structure on L and both scalar-tower instances, as listed above.
2. H3: E and L shared a universe parameter. Replaced L's universe by an
   independent z; fraction-field presentations in different universes are covered.
3. H3/H5 hypothesis audit: the explicit `hchar` characteristic disjunction was
   not a node hypothesis and is automatic for a field. Removed it entirely;
   the two characteristic implications remain in the conclusion.
4. H9: removed all three statement `let` binders, expanding the localization,
   tensor product and canonical inclusion so that later proof work can unfold
   them. These are existing Mathlib notions, not new definitions.
5. H8/H9: corrected both source docstrings, supplied the copyright/license
   header, and expanded the proof docstring to all four concrete node steps,
   including common exponent, nonzero denominator product, injectivity,
   Frobenius on module-linear combinations, and fraction-field preservation.
   Wrapped the source citation to stay within 100 columns. The sole proof is
   still `sorry`; no mathematical assertion was proved or weakened.
6. Updated `lean.statement` to the signature verbatim. The Worker report and
   earlier second reading above describe the superseded draft where they differ.

Edge cases: domain/field assumptions already exclude zero rings, exactly as
in the node; x = 0 is included. An empty finite generating set would force E
zero and so cannot occur, but the empty denominator product is 1 and introduces
no extra nonemptiness premise. n = 0 is permitted (p^0 = 1). Characteristic zero
and every positive field characteristic are covered without hchar; p = 0 and
composite p cannot satisfy the prime-characteristic premises. No scheme or
index set occurs in this ring statement, so empty schemes and empty indexing
categories impose no restriction. u, v, w, z are all explicitly declared and
independent, and no variable is left to auto-implicit inference.

Independent searches, with queries different from the original worker's:

- LeanFinder via `msearch.py`: "localizing a finite algebra with purely
  inseparable fraction field makes powers lie in the base". Eight hits,
  including `IsPurelyInseparable.pow_mem`, `elemExponent_def`, and
  `isPurelyInseparable_iff_pow_mem`; these concern fields or exponents, not
  existence of a nonzero localization denominator for a finite domain algebra.
- Loogle via `msearch.py`: `IsPurelyInseparable, TensorProduct`. Four hits.
  I opened `IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar`
  and `exists_pow_mem_range_tensorProduct`: they require tensoring over a FIELD
  k and an already purely inseparable k-algebra K. Here tensoring is over the
  DOMAIN A', and E need not be a purely inseparable A'-algebra before clearing
  denominators. These are useful proof tools, not an exact existing statement.
  The other two hits are spectrum homeomorphism conclusions, also different.
- Grep: searched `localiz|Away|IsFractionRing` in Mathlib's and the source's
  purely-inseparable directories (no localization theorem); searched
  `purelyInseparable|purely_inseparable|IsPurelyInseparable` in both
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and repository `lean/Sheaf`
  and opened relevant hits/signatures. Found field tensor-power tools, field
  splitting/descent statements and universal-homeomorphism statements; none
  supplies this denominator-clearing existence conclusion. Also searched the
  proposed declaration name in Mathlib, source, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no collision.
- The inherited node also records the LeanSearch request (service unavailable).
  No exact existing statement was found; this module remains necessary.

Validation: compiled the repaired module through `scompile.py` on the project
server; the initial source-citation long-line warning was corrected before the
final clean compile and delivery preflight. No new definition, hollow data,
private notion, proof, or unbound universe was introduced.
