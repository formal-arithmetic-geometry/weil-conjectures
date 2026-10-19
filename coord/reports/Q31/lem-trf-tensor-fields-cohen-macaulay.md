## Worker report

The module `Sheaf.RingTheory.TensorFieldsCohenMacaulay` states
`Algebra.TensorProduct.isNoetherianRing_and_local_depth_eq_dimension_of_fg`, with
one `sorry` proof and no new definitions. The source is Stacks Project, Algebra,
Tag 045M, `lemma-tensor-fields-CM`, read at
`literature/stacks-project/algebra.tex:47266–47286`. The item statement is unchanged.
There are no new nodes, dependency repairs, statement disputes or source faults.

Clause-by-clause correspondence:

- A field k: `{k : Type u} [Field k]`.
- Field extensions K/k and L/k: `{K : Type v} {L : Type w} [Field K] [Field L]`
  and `[Algebra k K] [Algebra k L]`. The algebra maps are the specified field
  embeddings, automatically injective because the source is a field.
- At least one extension finitely generated AS A FIELD:
  `hfg : (⊤ : IntermediateField k K).FG ∨ (⊤ : IntermediateField k L).FG`.
  `IntermediateField.FG` is the existence of a finite set whose intermediate-field
  adjoin equals the given field, exactly the smallest-subfield condition in the node.
  This permits transcendental extensions; it does not mean finite type as an algebra.
- The commutative ring T = K tensor_k L is `TensorProduct k K L`, with Mathlib's
  commutative algebra tensor ring structure. Its multiplication is the specified
  multiplication by `Algebra.TensorProduct.tmul_mul_tmul`; no extra equation needs
  to be assumed or concluded about this already defined ring.
- T Noetherian: `IsNoetherianRing (TensorProduct k K L)` is the first conjunct.
- Every prime ideal q: `∀ (q : Ideal (TensorProduct k K L)) [q.IsPrime], ...`.
- Its localization T_q: `Localization.AtPrime q`.
- T_q Noetherian local: the two explicit conjuncts
  `IsNoetherianRing (Localization.AtPrime q)` and `IsLocalRing (Localization.AtPrime q)`.
- Its depth equals its dimension:
  `(IsLocalRing.depth (R := Localization.AtPrime q) (Localization.AtPrime q) :
  WithBot ℕ∞) = ringKrullDim (Localization.AtPrime q)`.
  This is the recorded depth of the ring as a module over itself. The coercion puts
  depth in the dimension's `WithBot ℕ∞`; prime localizations are nonzero, so the
  dimension-bottom case never arises here. No finite natural depth is chosen.
- No algebraicity, separability or perfectness: none of these is a hypothesis.
  The only hypothesis beyond the field and algebra structures is `hfg`.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-field-extension`: `Algebra`, Mathlib.Algebra.Algebra.Defs, with the
  `[Field k]`, `[Field K]`, `[Field L]` specializations of its recorded interface.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  Mathlib.LinearAlgebra.TensorProduct.Defs, imported through
  Mathlib.RingTheory.TensorProduct.Basic; the latter supplies multiplication and
  `Algebra.TensorProduct.tmul_mul_tmul`.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  Mathlib.RingTheory.Noetherian.Defs.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  Mathlib.RingTheory.Localization.AtPrime.Basic.
- `def-weil-pbc-depth`: `IsLocalRing.depth` and `Ideal.depth`,
  Sheaf.RingTheory.Depth. The finite-module instance is the canonical self-module
  instance and adds no hypothesis.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  Mathlib.RingTheory.KrullDimension.Basic.

The complete docstring follows all nine proof steps of the node and names their
inputs. All recorded proof-dependency modules are imported without `public`, except
those already publicly imported for the statement. In particular the polynomial
Cohen–Macaulay, flat-module localization, flat local depth formula and support-depth
bound modules are imported; no new dependency interface is required.

Edge cases checked against the mathematical statement and Lean binders:

- k = K = L: the empty generating set is permitted; T is k, with depth and dimension 0.
- Only L/k finitely generated: the right side of `hfg` permits this with no hypothesis
  on K/k; the proof uses the tensor swap.
- K = k(t): finite generation uses intermediate-field adjoin, so this essential
  transcendental case is included. The finite transcendence-basis size may be zero.
- Positive-characteristic inseparability, e.g. K = L = k(a^(1/p)): the tensor may be
  nonreduced. There is no domain, reducedness, separability or perfectness assumption;
  an Artinian prime localization still has depth and dimension 0.
- Arbitrary relative sizes: `u`, `v`, `w` are independent and explicitly bound.
- Fields exclude the zero ring by definition; localization is taken only at primes,
  so its canonical nonzero local-ring structure applies. No prime is singled out.

Searches made with the prescribed msearch.py wrapper (machine log: searches.jsonl):

- grep: `CohenMacaulay|cohen.macaulay|tensor.*[Ff]ield.*[Nn]oetherian`. 0 hits. No hits. Digest 4f53cda18c2baa0c.
- loogle: `TensorProduct, IsNoetherianRing`. 8 hits. tensorProduct_reesAlgebra_isNoetherian_of_fg, AdicCompletion.ofTensorProductEquivOfFiniteNoetherian, AdicCompletion.coe_ofTensorProductEquivOfFiniteNoetherian, AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian, AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of, AdicCompletion.tensor_map_id_left_injective_of_injective, AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply, AdicCompletion.tensor_map_id_left_eq_map. Digest 6f250254ebc40252.
- leanfinder: `The tensor product of two extensions of a field is Noetherian Cohen Macaulay if one extension is finitely generated as a field`. 8 hits. Algebra.EssFiniteType.baseChange, Algebra.IsAlgebraic.tensorProduct, Algebra.TensorProduct.isField_of_isAlgebraic, IntermediateField.LinearDisjoint.isDomain', Algebra.FiniteType.baseChange, Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced, Algebra.IsGeometricallyReduced.isReduced_algebraicClosure_tensorProduct, IntermediateField.LinearDisjoint.exists_field_of_isDomain. Digest 04bc798a4140c7dc.
- leansearch: `A tensor product of fields is Cohen Macaulay when one extension is finitely generated`. 8 hits. instFinitePresentationTensorProduct, Algebra.TensorProduct.isField_of_isAlgebraic, IntermediateField.LinearDisjoint.isField_of_forall, Algebra.TensorProduct.isAlgebraic_of_isField, IntermediateField.LinearDisjoint.isField_of_isAlgebraic, RingHom.Finite.tensorProductMap, Algebra.FormallySmooth.instTensorProduct, FGModuleCat.tensorObj_obj. Digest 5d32ae3bfec1e46a.

None of the semantic hits gives local depth or Cohen–Macaulayness: they concern
linear disjointness, fields or domains, algebraicity, finite presentation and base
change. Loogle's hits concern the Rees algebra and adic completion. The grep has
no Cohen–Macaulay declaration. These are not exact matches.

Direct rg searches of `lean/Sheaf`, the read-only upstream `WeilConjectures`,
Mathlib, and `dag/lean_names_upstream.json` for the proposed declaration,
`tensor.*[Ff]ield.*[Cc]ohen`, `[Cc]ohen.*[Tt]ensor`, and related names found no
existing statement. The item's id occurs in the project's RelativeAssassinBaseChange
proof docstring only. The required upstream `grep -rn` for this item id found none.
The existing PolynomialAlgebraCohenMacaulay module gives a different theorem about
polynomial rings and is imported as the recorded proof input, not duplicated.

Validation: scompile.py compiled the sandbox and library module separately, each
in 2.0 seconds, with no errors or warnings. `set_option autoImplicit false` prevents
implicit variables, and all three universes are declared explicitly.

## Second reading by Q31

No second reading by a worker: the dispatched brief requires direct delivery;
the maintainer's independent review is the review. No sub-agents were started.
