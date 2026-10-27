## Worker report

Module: `Sheaf.RingTheory.CommonFiniteTraitExtension`.
Declaration: `IsDiscreteValuationRing.exists_common_finite_trait_extension`.
This delivery states the node with one `sorry`; it defines no new notion and proves nothing.
The node is unchanged except for `lean`. No statement correction or dispute is needed.

Source read: ILO, Travaux de Gabber, Expose IV §4.2.3, printed page 58,
the paragraph beginning “De tels idéaux p étant en nombre fini”. It chooses a single finite
base change dominating the finitely many Epp base changes. Also read the current blueprint
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.md`.
The node expands the algebra behind this finite common base change.

Clause-by-clause translation:

- The complete DVR W0 is `(W0 : Type u) [CommRing W0] [IsDomain W0]
  [IsDiscreteValuationRing W0] [IsAdicComplete (IsLocalRing.maximalIdeal W0) W0]`.
  DVR includes a nonzero maximal ideal; fields and the zero ring are not admitted.
- Its fraction field is `(K0 : Type v) [Field K0] [Algebra W0 K0]
  [IsFractionRing W0 K0]`. Its residue field k0 is the actual quotient
  `IsLocalRing.ResidueField W0`, without a second independent field parameter.
- The finite set is `(I : Type t) [Finite I]`, with no nonemptiness assumption.
- The family is `Wi : I → Type w`, with pointwise commutative ring, domain, DVR,
  and maximal-ideal adic completeness instances.
- The specified W0 maps are `[∀ i, Algebra W0 (Wi i)]`. Their injectivity is `hinj`;
  their locality is `[∀ i, IsLocalHom (algebraMap W0 (Wi i))]`.
  Locality means reflection of units; for local rings this is exactly equality of
  the inverse image of the target maximal ideal with the source maximal ideal
  (`IsLocalRing.local_hom_TFAE`, clauses 0 and 4).
- The fraction fields `Ki : I → Type x` have `[Field (Ki i)]`,
  `[Algebra (Wi i) (Ki i)]` and `[IsFractionRing (Wi i) (Ki i)]`.
  `[Algebra K0 (Ki i)]` and `[Module.Finite K0 (Ki i)]` express their finite
  extensions over K0. The equality `hK` says that these extensions agree on W0
  with the given maps W0 → Wi → Ki. It expresses the meaning of the induced
  fraction-field extension, rather than imposing an additional mathematical condition.
- The conclusion existentially quantifies a commutative domain W, its DVR and
  W0-algebra structures and locality of `algebraMap W0 W`. It asserts completeness,
  injectivity, and `Module.Finite W0 W`.
- For every i the existential `f : Wi i →ₐ[W0] W` is a map over the specified W0
  structure, and `Function.Injective f ∧ IsLocalHom f.toRingHom` supplies the
  embedding and locality. No compatibility with a separately chosen common field
  is added to the conclusion.
- `RingHom.Finite (IsLocalRing.ResidueField.map (algebraMap W0 W))` states finite
  dimension along the canonical residue map. This map is injective because it is
  a unital map of fields. This uses the specified map, rather than a freely chosen
  algebra structure on the residue fields.
- `PerfectField (IsLocalRing.ResidueField W0) → PerfectField (IsLocalRing.ResidueField W)`
  is precisely the conditional perfectness clause. `PerfectField` agrees with the
  node's characteristic-zero-or-surjective-Frobenius formulation: use
  `PerfectField.ofCharZero`, `PerfectRing.ofSurjective` with `PerfectRing.toPerfectField`,
  and in the converse direction `PerfectField.toPerfectRing`.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, class signature and docstring.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete`,
  `Mathlib.RingTheory.AdicCompletion.Basic`, the Hausdorff and precomplete conditions.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`, finite generation of the top submodule.
  `RingHom.Finite` in the same module specializes this to a specified map.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`, `Mathlib.AlgebraicGeometry.ResidueField`.
  These are literally `IsLocalRing.ResidueField` of the stalk and its induced map.
  Since the node explicitly takes W/m_W for a local ring, it uses that same
  underlying quotient construction and `IsLocalRing.ResidueField.map` directly,
  from `Mathlib.RingTheory.LocalRing.ResidueField.Basic`. No substitute is defined.
- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- Fraction fields use Mathlib's `IsFractionRing` from
  `Mathlib.RingTheory.Localization.FractionRing`.

Available proof-plan imports are retained as ordinary, non-public imports:
`WeilConjectures.FieldTheory.CommonExtensionFields` (`Field.exists_common_extension`),
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`
(`IntermediateField.adjoin_rank_le_of_isAlgebraic_right`), and
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (`integralClosure`).
`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` and
`Algebra.IsAlgebraic.perfectField` are already supplied by the public imports.
`lem-per-complete-dvr-finite-normalization` currently has no usable Lean record,
so there is no recorded module to import for that proof dependency; it is not
needed to type this statement. All six statement dependencies have usable interfaces.

Edge cases checked:

- I empty: W = W0, identity structure map; the family conclusion is vacuous and
  the residue extension is the identity finite extension.
- Singleton family, including the identity extension: no nontrivial-extension
  condition has been added.
- Positive characteristic and purely inseparable fraction-field extensions are
  allowed: no separability or characteristic instance appears.
- Imperfect k0 is allowed: perfectness is only an implication in the conclusion.
- Mixed characteristic is allowed as well as equal characteristic.
- The ring, fraction fields, and index type have independent explicitly bound
  universes. W may be taken in the base ring universe u: a finite algebra over
  W0 has a model of that size. No bound on the sizes of the supplied Ki is imposed.

Searches made (2026-10-24):

- `msearch.py ... leansearch "common finite extension of finitely many complete discrete valuation rings"`:
  eight hits (DVR characterizations, valued local compactness, valuation extension);
  no common finite trait extension statement.
- `msearch.py ... leanfinder "common finite extension dominating finitely many complete discrete valuation rings over one complete DVR"`:
  eight hits on local compactness, Dedekind DVRs and adic completions;
  no matching theorem.
- `msearch.py ... loogle "IsDiscreteValuationRing, IsAdicComplete, RingHom.Finite"`:
  zero hits.
- `msearch.py ... grep "exists_common_finite_trait|common.*trait|common.*valuation" RingTheory`:
  zero hits in Mathlib.
- `rg -n` with that pattern in `lean/WeilConjectures` and `lean/Sheaf`:
  unrelated common overrings, stable reduction and valuation constructions;
  no common finite complete trait theorem. `grep -rn` for the exact node id in
  `lean/WeilConjectures` returned no matches.
- The node's `lean_removed` records the deleted former module and name; the current
  source searches confirm that this name is available and no declaration survives.
- No repair note for this item exists under `coord/repair-notes`.

All binders and universe variables are explicit; `autoImplicit` is disabled.
Initial server compilation passed for both the sandbox and library module (41.2 s and
52.7 s). Removed the redundant RingHom.Finite module import: RingHom.Finite is
already defined in the required Finiteness.Defs import. The delivery dry run
recompiles the final module and runs the maintainer preflight.

## Second reading by Q57

No second reading by a worker: the dispatcher's instructions prohibit starting
other agents. The maintainer's independent review is the second reading.

Final verification: `deliver2.py Q57 lem-per-epp-common-finite-trait-extension --no-push`
returned OK: commit `1c1aebaa169` passes the maintainer preflight and both server
compile checks. The node diff changes only `lean`; its signature is verbatim
from the module. The only postponed proof is the named main theorem.
