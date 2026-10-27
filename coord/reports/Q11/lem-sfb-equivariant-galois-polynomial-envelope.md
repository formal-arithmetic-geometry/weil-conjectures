## Worker report

The module `Sheaf.FieldTheory.EquivariantGaloisPolynomialEnvelope` states
`exists_equivariant_galois_polynomial_envelope`, with its sole proof `sorry`.
No definition, dependency module, statement correction, or new node is needed.
Only the item's `lean` field changes.

Sources read: the item's full statement and eight proof steps; Stacks Fields
`lemma-galois-over-fixed-field` (09I3), `lemma-lift-maps` (0BME), including their
proofs; the current blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
part (3). The named local de Jong PDF is absent in this read clone; the original
PDF at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf was opened instead.
The field-envelope statement here is the accepted agent elaboration recorded in
this node, not a claim that de Jong prints this exact polynomial formulation.

Hypothesis and clause correspondence:

- Field K: `(K : Type u) [Field K]`.
- Finite group H: `(H : Type t) [Group H] [Finite H]`.
- The field-automorphism action A is `[MulSemiringAction H K]`; `h • x` is A_h(x).
  Such an action of a group acts by ring equivalences, hence field automorphisms.
  There is no `FaithfulSMul` hypothesis. No data of A are lost by the action encoding.
- F is written throughout as `FixedPoints.subfield H K`, whose carrier definition
  is precisely the elements fixed by every h. Taking the image H_0 of the action
  gives the same subfield; H_0 itself is auxiliary notation, not additional data.
- Finite, possibly empty polynomial index set: `(I : Type w) [Finite I]` with no
  `Nonempty I`. The independent index universe does not restrict this finite family.
- Polynomials, monicity, specified degrees and positive degrees: `f`, `d`, `hmonic`,
  `hdegree` and `hpositive` respectively. `natDegree` has the usual degree because
  a monic polynomial over a field is nonzero.
- Nonempty finite component sets: `B`, `[∀ i, Finite (B i)]`, `[∀ i, Nonempty (B i)]`.
- Finite separable component field extensions: `E`, their `Field` and `Algebra K`
  instances, `hfinite : ∀ i b, FiniteDimensional K (E i b)` and `hseparable`.
- Given K-algebra product decompositions: `quotientEquiv`. The quotient is by the
  principal ideal `Ideal.span {f i}`, and the dependent function algebra is the
  product of the fields E i b, with its pointwise operations.
- The extension M and tower F ⊆ K ⊆ M: the existential `Field M`, `Algebra K M`,
  `Algebra F M` and `IsScalarTower F K M` binders. In a field these algebra maps
  are embeddings. M is in `Type (max u v)`, allowing both the original field and
  all component fields at their original, independent universes.
- Both finite Galois assertions are the four explicit conjuncts
  `FiniteDimensional F M`, `IsGalois F M`, `FiniteDimensional K M`, `IsGalois K M`.
  Mathlib's `IsGalois` is normal and separable algebraic, as the node requires.
- The embeddings are `∀ i b, Nonempty (E i b →ₐ[K] M)`. Ring homomorphisms out
  of fields are injective, so these are K-embeddings, all for the same algebraMap.
- Complete linear factorizations: `beta : (i : I) → Fin (d i) → M` and the equality
  `(f i).map (algebraMap K M) = ∏ nu, (X - C (beta i nu))`.
  Exactly d i factors occur, with repetitions permitted.
- J is a `Subgroup (H × (M ≃ₐ[F] M))` with carrier characterized by the membership
  biconditional, exactly `sigma (algebraMap K M x) = algebraMap K M (h • x)`.
  A subgroup uses the product's componentwise group operations. `Finite J` gives
  finiteness; it is not asserted by an arbitrary unrelated group structure.
- `rho : J →* H`, the pointwise first-coordinate equality, and
  `Function.Surjective rho` give precisely the specified surjective projection.
- `action : J →* (M ≃ₐ[F] M)` and its second-coordinate equality give the action
  by automorphisms from the second projection. Its next conjunct states the
  restriction to K is the original action through rho.
- N is the actual `rho.ker`. The equivalence `e : rho.ker ≃* (M ≃ₐ[K] M)` and its
  evaluation equality require e to be the very second projection `(1,sigma) ↦ sigma`,
  not an unspecified abstract group isomorphism.
- The last biconditional states M^N = the image of K point by point, using the
  second-coordinate action and `Set.range (algebraMap K M)`. All preceding algebra
  embeddings commute with this same map, as required by the final sentence.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, signature and docstring.
- `def-pc-field-extension`: `Algebra`, Mathlib.Algebra.Algebra.Defs, signature and
  docstring; `algebraMap` supplies each specified embedding.
- `def-pc-field-tower`: Sheaf.FieldTheory.FieldTower, `FieldExtension.degree` and
  its docstring. The module explicitly records `Module.Finite`/`FiniteDimensional`
  for the finite-extension clause; the conclusion uses that existing predicate.
- `def-weil-polynomial-ring`: `Polynomial`, Mathlib.Algebra.Polynomial.Basic,
  its signature and docstring; polynomial `map`, `Monic`, `natDegree`, `X`, `C`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  Mathlib.FieldTheory.Separable, lines 539–570, including the algebraicity instance.
- Proof ingredients: `IsGalois.of_fixed_field`, `IsGalois.tower_top_of_isGalois`,
  `IsGalois.mem_range_algebraMap_iff_fixed`, `IsGalois.card_aut_eq_finrank`
  (Mathlib.FieldTheory.Galois.Basic); `FixedPoints.finrank_eq_card` and
  `AlgEquiv.fintype` (Mathlib.FieldTheory.Fixed); `Algebra.IsSeparable.trans`
  (Mathlib.FieldTheory.SeparableDegree); `AlgEquiv.liftNormal` and
  `AlgEquiv.liftNormal_commutes` (Mathlib.FieldTheory.Normal.Basic);
  `Polynomial.Splits.of_dvd` (Mathlib.Algebra.Polynomial.Splits);
  `finite_galois_receiving_separable_extensions`
  (WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions).
  The published receiving theorem's full source/docstring was read, and its
  module is imported privately. All eight proof steps are in the theorem docstring.

Edge cases checked mathematically: I empty still requires M to contain K; the
receiving-family construction must always include K. The conclusion retains all
J/rho/kernel clauses in this case. A trivial or nonfaithful action is allowed;
for a trivial action F = K and J = H × Aut_K(M). A faithful action with no
polynomials permits M = K. No characteristic restriction is imposed, including
when the characteristic divides |H|. B_i is required nonempty exactly as in the
node. Degree one is allowed. No distinctness of beta is demanded. Fields may
have independent universes; the finite component index and group universes do
not constrain M's universe. Zero or constant polynomials are excluded exactly
by monicity and positive specified degree, not by an extra hypothesis.

Searches actually run:

- msearch.py leanfinder: `finite group action on a field finite Galois extension
  splitting polynomials compatible automorphism pairs surject to the original group`.
  Eight results, including `FixedPoints.toAlgAut_surjective`,
  `Polynomial.Gal.restrict_surjective`, and `IsGaloisGroup.mulEquivAlgEquiv`.
  These are ingredients or different statements, not this combined envelope.
- msearch.py loogle: `IsGalois.of_fixed_field, FixedPoints.subfield, AlgEquiv.liftNormal`:
  zero hits for this combined query.
- msearch.py grep in Mathlib FieldTheory:
  `polynomial.envelope|compatible.*[Gg]alois|semilinear.*envelope`: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item ID, polynomialEnvelope,
  galoisPolynomialEnvelope, compatible Galois and semilinear envelope names:
  no matching envelope declaration; only unrelated occurrences of “compatible”.
- rg of the new full name, envelope patterns and item ID in dag/lean_names_upstream.json,
  lean/WeilConjectures and lean/Sheaf: no hit. No existing duplicate was found.

Validation: scompile.py compiled both the sandbox and final module against the
published live library. The initial Fintype B hypothesis produced an unused-Fintype
warning; it was replaced by Finite B without changing the mathematics. The next
compile passed cleanly (2.8 s sandbox, 4.7 s final module). `autoImplicit` is false;
all five universes and every variable are explicitly bound. No statement dispute.

## Second reading by Q11

Author's separate reread of the actual node and final module (not an independent
agent review; the dispatcher expressly prohibits starting other agents).
I checked the complete hypothesis/conclusion correspondence above against the
file. In particular the membership biconditional defines exactly all compatible
pairs, rho and action are constrained to their actual coordinates, the kernel
is rho.ker rather than an arbitrary subgroup, and its equivalence is constrained
on every element of M to be the second projection. This removes the possibility
of replacing the canonical map by an unrelated isomorphism. The F-algebra
structure is tied to K by IsScalarTower. The terminal range is the same algebraMap
used by all K-algebra embeddings and the polynomial coefficient map. The only
change found necessary was the Fintype-to-Finite warning repair. No source or
node statement change, dependency repair, or missing notion was found.
