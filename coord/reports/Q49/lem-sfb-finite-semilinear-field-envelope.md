## Worker report

The module `Sheaf.FieldTheory.FiniteSemilinearFieldEnvelope` states
`exists_finiteSemilinearFieldEnvelope`, with its entire proof postponed by `sorry`.
The accompanying structure `FiniteSemilinearFieldEnvelope` packages exactly the
witnesses and clauses of this node. It introduces no independent mathematical
notion and contains no postponed data or auxiliary theorem. No statement correction,
new DAG node, or dependency repair is required.

Hypothesis and clause correspondence:

- Fields K and L: `(K : Type u) (L : Type v) [Field K] [Field L]`.
- The specified inclusion K ⊆ L: `[Algebra K L]`; between fields its algebra map
  is injective. Finiteness is `[FiniteDimensional K L]`, the Mathlib abbreviation
  for the recorded `Module.Finite K L`.
- The finite group H: `(H : Type w) [Group H] [Finite H]`, with its universe
  independent of both field universes.
- The given homomorphism: `A : H →* (K ≃+* K)`. There is no injectivity or
  faithfulness hypothesis.
- The fixed field F is `base : Subfield K`, constrained by `mem_base` to have
  exactly the elements fixed by every `A h`. This specifies the existing Mathlib
  subfield notion by its membership condition, not a replacement field notion.
- The tower F ⊆ K ⊆ L ⊆ M: `carrier`, `field`, `overL`, `overK`, `towerK`,
  `overBase`, and `towerBase`. Here `carrier : Type (max u v)` allows all input
  field sizes and supports a finite normal closure; these are existential output
  data, not added input hypotheses. `towerK` and `towerBase` impose the required
  agreement of embeddings. The F-algebra structure on L is induced through K,
  so the two displayed towers also give compatibility through L.
- M/F finite and normal: `finiteBase`, `normalBase`, using Mathlib
  `FiniteDimensional` and `Normal` (algebraic and every minpoly splits).
- The precise group J with componentwise law: `pairs : Subgroup
  (H × (carrier ≃ₐ[base] carrier))`. Its `mem_pairs` is the biconditional
  `p ∈ pairs ↔ ∀ k, p.2 (algebraMap K carrier k) =
  algebraMap K carrier (A p.1 k)`. Thus every compatible pair is present and
  no extra pair is present. The subgroup group law is the inherited product law.
- Projection ρ: `rho : pairs →* H`, with `rho_apply` prescribing the first
  coordinate exactly. `finitePairs` and `surjective_rho` state its two properties.
- The J-action: `action : MulSemiringAction pairs carrier`, with `action_apply`
  prescribing evaluation of the second coordinate. This is the field-automorphism
  action; because J is a group, every action map is invertible. `action_on_base`
  explicitly renders compatibility with A on K.
- N is literally `rho.ker`. `kernelEquiv : (carrier ≃ₐ[K] carrier) ≃* rho.ker`
  states the group isomorphism. `kernelEquiv_apply` specifies its first coordinate
  as 1 and its second coordinate's underlying ring automorphism as precisely sigma.
  This states the same `(1, sigma)` formula without requiring a local instance for
  restriction of scalars inside a structure field. `kernelEquiv_action` explicitly
  gives action compatibility.
- M^N is `fixed : IntermediateField K carrier`. `mem_fixed` prescribes exactly
  invariance under every element of `rho.ker`, for the specified evaluation action.
  Being an intermediate field also records K ⊆ M^N. `finiteFixed` and
  `purelyInseparableFixed` state the finite purely inseparable conclusion.
- K/F finite Galois: `finiteK` and `galoisK`. Mathlib `IsGalois` is exactly
  normal and separable algebraic, with finiteness stated separately.
- M/K finite normal: `finiteOverK` and `normalOverK`.
- If L/K is separable: each final field has antecedent `Algebra.IsSeparable K L`.
  `galoisBase_of_separable` and `galoisOverK_of_separable` render the two Galois
  conclusions, using the same carrier and structure data already supplied.
  `fixed_eq_bot_of_separable` renders M^N = K as equality with the bottom
  K-intermediate field, i.e. the image of K in M.
- Existence of all of these witnesses is `Nonempty (FiniteSemilinearFieldEnvelope
  K L H A)`. This is existence of fully specified structures; it is not a choice
  of data from a sorry-backed existence theorem.

Dependency interfaces read and used:

- `Field`, Mathlib.Algebra.Field.Defs (`def-weil-field`).
- `Algebra` and `algebraMap`, Mathlib.Algebra.Algebra.Defs
  (`def-pc-field-extension`).
- Sheaf.FieldTheory.FieldTower is publicly imported for `def-pc-field-tower`.
  Its module documentation explicitly assigns finiteness to `Module.Finite`
  rather than requiring the numeric `FieldExtension.degree` in every statement.
  This module uses that recorded finiteness notion through `FiniteDimensional`.
- `Algebra.IsSeparable`, Mathlib.FieldTheory.Separable, records separable
  algebraicity including algebraicity of every element.
- `IsPurelyInseparable` and `Module.Finite`,
  Mathlib.FieldTheory.PurelyInseparable.Basic, are the recorded inseparability and
  finite-extension predicates, including characteristic zero.

All ten proof dependencies were read. Their available module interfaces are
imported privately as the stage-3 plan: `IsGalois.of_fixed_field`,
`FixedPoints` finiteness; `IntermediateField.normalClosure`, `normalClosure.normal`,
`normalClosure.is_finiteDimensional`, `normalClosure.algebra`;
`card_algHom_le_finrank`/`Finite.algHom`;
`AlgEquiv.restrictNormalHom_surjective`; `Normal.tower_top_of_normal`;
`Normal.fixedField_purelyInseparable` from
WeilConjectures.FieldTheory.NormalExtensionFixedFieldPurelyInseparable;
`Algebra.IsSeparable.trans`; `finite_galois_receiving_separable_extensions` from
WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions;
`Algebra.isSeparable_tower_top_of_isSeparable`; and
`IsGalois.mem_range_algebraMap_iff_fixed`. Their mathematical steps are all
included in the theorem docstring. The source combination was checked directly
in fields.tex at the cited normal-closure, lift-maps, fixed-field and normal-case
lemmas; no change to that mathematical combination was needed.

Edge cases checked mathematically: H trivial; H nontrivial acting trivially
(then F = K and J retains the entire H factor); K = L; characteristic zero
(the finite purely inseparable fixed extension is trivial); positive characteristic
with inseparable L/K (no separability is imposed on the general witness); separable
L/K including the identity extension; and arbitrary relative sizes of u, v and w.
No field cardinality or group cardinality lower bound is added. The action is
never silently replaced by its faithful image in the output group.

Searches made with the prescribed msearch tool:

- leanfinder: `finite normal field envelope retaining a semilinear finite group`.
  Eight hits including `FixedPoints.normal`, `AlgEquiv.fintype`, and
  `normalClosure.is_finiteDimensional`; these are ingredients, not the full result.
- loogle: `AlgEquiv, Normal, fixedField` gave no hits because the unqualified
  `fixedField` identifier was not recognized. Follow-up
  `AlgEquiv.restrictScalars` returned the restriction-of-scalars interface and
  its related lemmas; these do not give the envelope.
- leansearch: `Finite normal extension and finite group of compatible pairs
  extending automorphisms of a field`. Eight hits including `Normal`, `IsGalois`
  and `IntermediateField.normal_iff_forall_map_eq'`; no full envelope result.
- grep in Mathlib FieldTheory: `semilinear|compatible.*pair|fixedField` returned
  the standard fixed-field API and semilinear Frobenius maps, no envelope.
- rg of project WeilConjectures and Sheaf for finite/semilinear/normal-envelope
  combinations, and their FieldTheory modules for semilinear declarations:
  related invariant-parameter and normal-subfield material, no matching result.
- rg of `dag/lean_names_upstream.json`, WeilConjectures and Sheaf for
  `SemilinearFieldEnvelope|finite_semilinear_field_envelope`: no match.
- Search of the node id in WeilConjectures: no existing declaration.

Validation: scompile.py compiled both sandbox and actual library module forms
successfully with no errors or warnings. The initial restriction-of-scalars
instance failure was repaired using the equivalent underlying-ring-equivalence
formula described above. No `#check` diagnostics or local instances remain.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
