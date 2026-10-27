## Worker report

The module `Sheaf.FieldTheory.GeneratedFieldScalarCharacterOrder` states
`AlgEquiv.generated_field_scalar_character_order`, with `sorry` as its entire proof.
It introduces no definitions. The node is unchanged except for its `lean` record.
No statement fault or disputed claim was found.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field extension E/F is `(F : Type u) [Field F] (E : Type v) [Field E]
  [Algebra F E]`. Its embedding is `algebraMap F E`, injective for fields.
  The field universes are independent.
- The nonnegative integer r is `(r : ℕ)`; the list of nonzero generators is
  `(b : Fin r → Eˣ)`. In a field every nonzero element is a unit, so this includes
  exactly the permitted generators.
- The smallest subfield containing the base image and all generators is exactly
  `IntermediateField.adjoin F (Set.range (fun j : Fin r ↦ (b j : E)))`.
  Its equality to `⊤` is `hgen`. The definition of `adjoin` is literally the
  subfield closure of the union of the base image and the generator range.
- U, its identity, multiplication and inverse closure, with inherited operations,
  are bundled as `(U : Subgroup Fˣ)`. This introduces no additional condition:
  `Subgroup` is a subset containing one and closed under multiplication/inverses.
  `[Finite U]` expresses precisely the finiteness assumption, without choosing
  an enumeration.
- G is `E ≃ₐ[F] E`, algebra automorphisms fixing the base image. Mathlib's
  `AlgEquiv.aut` group multiplies by composition; `mul_apply` reads
  `(σ * τ) x = σ (τ x)`.
- `hscalar` quantifies over every automorphism σ and index j and asserts an
  `a : U` with `σ (b j : E) = algebraMap F E ((a : Fˣ) : F) * (b j : E)`.
  The nested coercions read a scalar in U as a base-field element.
- `∃ χ : (E ≃ₐ[F] E) →* (Fin r → U)` supplies the group homomorphism into
  the tuple group with coordinatewise multiplication. The first conjunct is
  exactly its required coordinate formula.
- The next conjunct quantifies over every group homomorphism ψ satisfying that
  coordinate formula and concludes `ψ = χ`. Thus uniqueness is uniqueness for
  the formula alone, not uniqueness merely among injective homomorphisms.
- `Function.Injective χ` is the injectivity conclusion for that same χ.
- `Finite (E ≃ₐ[F] E)` is the finiteness conclusion, not an assumption.
- `Nat.card (E ≃ₐ[F] E) ∣ Nat.card U ^ r` is the integer-cardinality conclusion.
  Both types are finite under the hypothesis/conclusion, so `Nat.card` is their
  ordinary nonnegative integer cardinality.
- There is no algebraicity, normality, separability, finite-dimensionality or
  characteristic hypothesis. The finite family may be empty.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, read in
  `Mathlib.Algebra.Field.Defs`, including its full inherited signature/docstring.
- `def-pc-field-extension`: `Algebra`, read in
  `Mathlib.Algebra.Algebra.Defs`; the supplied definition-node record explicitly
  identifies a field extension with `[Field F] [Field E] [Algebra F E]`.
  These declarations are publicly available through the statement imports.
- The already-stated proof dependency `lem-sfb-injective-hom-finite-group-order`
  is a Mathlib leaf with two declarations: `Subgroup.card_dvd_of_injective`
  (`Mathlib.GroupTheory.Coset.Card`) and `Finite.of_injective`
  (`Mathlib.Data.Fintype.EquivFin`). Both full signatures were read, and these
  modules are imported as proof-only imports. The theorem docstring gives all
  three DAG proof steps, including cancellation, the equalizer subfield and
  the finite-product count before applying those two declarations.
- Existing Mathlib notions used directly: `AlgEquiv` and its automorphism group
  (`Mathlib.Algebra.Algebra.Equiv`), `Subgroup`
  (`Mathlib.Algebra.Group.Subgroup.Defs`), `IntermediateField.adjoin`
  (`Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`), and `Nat.card`
  (`Mathlib.SetTheory.Cardinal.NatCard`). No private substitute is defined.

Edge cases checked before writing:

- r = 0: `Fin 0` has no elements, the range is empty, and `hgen` says that the
  base image equals the whole field. The character target is the singleton
  empty-tuple group. The stated injection therefore forces G trivial, and the
  divisor bound is divisibility of 1. Neither r > 0 nor a chosen index is needed.
- U can be the identity subgroup. Then its tuple group is trivial, so the scalar
  hypothesis and generation imply every automorphism is the identity. An empty
  U is correctly excluded by its required identity element.
- Redundant or repeated generators and generators already in the base are
  admitted. Units ensure cancellation even in positive characteristic.
- Infinite or transcendental E/F is allowed; finiteness of the automorphism
  group follows from the scalar hypothesis rather than from an added field
  finiteness assumption.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “Automorphisms of a field generated by finitely
  many nonzero elements acting by scalars in a finite subgroup of base field
  units admit a unique injective character into the product, with automorphism
  order dividing the product cardinality”. Eight hits: cyclotomic
  `IsPrimitiveRoot.autToPow_injective`, `AlgEquiv.card_le`, Hilbert 90,
  polynomial Galois action injectivity, finite-field cyclicity and cardinalities.
  None states the general finite-family scalar theorem.
- `msearch.py ... loogle "AlgEquiv, MonoidHom, Function.Injective"`: five hits,
  including scalar restriction, fraction-field transport, normal compositum
  restriction and the cyclotomic character. None is the requested theorem.
- `msearch.py ... leansearch`: “Field automorphisms acting by scalars on finitely
  many field generators give a unique injective homomorphism into a finite
  product of scalar subgroups”. Eight hits: fixed-point automorphism bijections,
  finite Galois adjunction, subfield transport and finite-dimensional automorphism
  finiteness. None matches the scalar hypothesis and complete conclusions.
- `msearch.py ... grep
  "scalarCharacter|scalar_character|autEquivRootsOfUnity|adjoin_algHom_ext"
  FieldTheory`: seven hits, in KummerExtension and IntermediateField/Adjoin/Defs.
  Read `autEquivRootsOfUnity` and `adjoin_algHom_ext` / `algHom_ext_of_eq_adjoin`.
  The former concerns one splitting-field radical with stronger assumptions;
  the latter supplies only generator extensionality.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `scalarCharacter|scalar_character|generated.field|scalar.character` found no
  exact statement. `MultiradicalGaloisDegree.lean` was read: it assumes roots of
  binomials in an algebraic closure and states a more specialized Galois-degree
  result, so it does not replace this arbitrary-extension statement.
- `grep -rn 'lem-sfb-generated-field-scalar-character-order'
  lean/WeilConjectures` found no attachment. Exact-name `rg` in Mathlib,
  `dag/lean_names_upstream.json`, WeilConjectures and Sheaf found no clash for
  `generated_field_scalar_character_order`.

Source checked: `literature/stacks-project/fields.tex`, section-Kummer opening
paragraph (lines 3215 onward): the scalar ratio gives an injective group
homomorphism, followed by the subgroup-order divisibility argument. The DAG
explicitly extracts its finite-family generalization and excludes the separate
Galois-degree theorem. No correction of the node is needed.

Validation: `scompile.py Q154 lem-sfb-generated-field-scalar-character-order`
compiled this delivered file in both sandbox and library module forms on the
server, without errors or unexpected warnings. No local or global build was run.

## Second reading by Q154

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
