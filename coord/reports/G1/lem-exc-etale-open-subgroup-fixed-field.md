## Worker report

`Sheaf.FieldTheory.OpenSubgroupFixedField` states
`openSubgroup_fixedField_finite_separable` with a `sorry` proof. Source:
Stacks [Tag 03QR](https://stacks.math.columbia.edu/tag/03QR), proof of
Lemma 58.2.2; [Tag 03SF](https://stacks.math.columbia.edu/tag/03SF)
gives the finite G-set context. The specified local Stacks `.tex` checkout is
absent on this machine; I read these source places online.

The field `K` and its extension `Ks` are `(K : Type u) (Ks : Type v)
[Field K] [Field Ks] [Algebra K Ks]`. Its separable closure is
`[IsSepClosure K Ks]`, imported from the recorded dependency module
`WeilConjectures.Mathlib.FieldTheory.IsSepClosed`, whose
`IsSepClosure.exists_intermediateField_mem` records that it is the union
of finite separable subextensions. Mathlib's `IsSepClosure` class gives
the separably closed and separable algebraic data. The Galois group is
`Gal(Ks/K)` with the Krull topology supplied by Mathlib.

For every open subgroup: `∀ H : Subgroup Gal(Ks/K), IsOpen (H : Set Gal(Ks/K)) →`.
The fixed field is `IntermediateField.fixedField H`. Its finite extension
property is `FiniteDimensional K (IntermediateField.fixedField H)`; separability
is `Algebra.IsSeparable K (IntermediateField.fixedField H)`; the inverse
correspondence is `(IntermediateField.fixedField H).fixingSubgroup = H`.
The cosets are `Gal(Ks/K) ⧸ H`; their finiteness, discreteness, and continuous
left action are respectively `Finite`, `DiscreteTopology`, and `ContinuousSMul`
on that type. Mathlib supplies its quotient topology and left group action.

For the converse, `X : Type w` has `[TopologicalSpace X]`, `[DiscreteTopology X]`,
`[Finite X]`, `[MulAction Gal(Ks/K) X]`, `[ContinuousSMul Gal(Ks/K) X]`, and
`[MulAction.IsPretransitive Gal(Ks/K) X]`. The chosen point is `(x : X)`.
Its subgroup is `MulAction.stabilizer Gal(Ks/K) x`; the conclusion gives
its `IsOpen` carrier and both `FiniteDimensional` and `Algebra.IsSeparable`
for its `IntermediateField.fixedField`.

Dependency declarations used: `Algebra` for field extensions (Mathlib,
`Mathlib.Algebra.Algebra.Defs`); `IsSepClosure` and the recorded
`IsSepClosure.exists_intermediateField_mem` (the latter in
`WeilConjectures.Mathlib.FieldTheory.IsSepClosed`); and
`Algebra.IsSeparable` (Mathlib, `Mathlib.FieldTheory.Separable`). For proof
planning I also read `InfiniteGalois.fixingSubgroup_fixedField`,
`InfiniteGalois.isOpen_iff_finite`, `Subgroup.quotient_finite_of_isOpen`,
`QuotientGroup.discreteTopology`, and `QuotientGroup.instContinuousSMul`.

Edge cases: arbitrary field characteristic and arbitrary universes `u`, `v`,
`w`; the trivial absolute Galois group and `H = ⊤` give a one-point coset
space; `H = ⊥` is permitted when open; the converse has a point `x`, so it
does not improperly assert one for an empty transitive G-set. A singleton
G-set is allowed.

Searches: `msearch leanfinder` with "open subgroup of absolute Galois group
fixed field finite separable extension and finite discrete coset action"
found `InfiniteGalois.isOpen_iff_finite` but no packaged two-way statement.
`msearch loogle` with `InfiniteGalois.isOpen_iff_finite,
InfiniteGalois.fixingSubgroup_fixedField,
Subgroup.quotient_finite_of_isOpen` returned no hits. `msearch grep` for
`fixedField|fixingSubgroup|isOpen_iff_finite|quotient_finite_of_isOpen`
in `Mathlib/FieldTheory` found component Galois results. `rg` in
`WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found
no matching declaration or recorded upstream name. The node-id search in
`WeilConjectures` returned no hit. The theorem compiled remotely with no
errors or warnings.

## Second reading by G1

I compared the node's statement and both proof steps with the module, its
recorded dependencies, and the source places. The item-by-item reading is:

- Field extension `K`: `(K : Type u) [Field K]`; extension `Ks/K`:
  `(Ks : Type v) [Field Ks] [Algebra K Ks]`. These are the Mathlib rendering
  recorded by `def-pc-field-extension`; there is no characteristic restriction.
- Separable closure `K^sep`: `[IsSepClosure K Ks]`. This is Mathlib's notion
  cited by `def-pd-separable-closure`; the recorded
  `IsSepClosure.exists_intermediateField_mem` states its finite separable
  subextension property. No extra finiteness or normality assumption occurs.
- Krull Galois group `G`: `Gal(Ks/K)`, with its Mathlib Krull topology from
  `Mathlib.FieldTheory.Galois.Infinite`; the same group occurs throughout.
- Every open subgroup `H`: `∀ H : Subgroup Gal(Ks/K),
  IsOpen (H : Set Gal(Ks/K)) →`. No normality assumption is present.
- Fixed field `L`: `IntermediateField.fixedField H`; finite separable over
  `K`: `FiniteDimensional K ... ∧ Algebra.IsSeparable K ...`. The latter is
  exactly the Mathlib notion in `def-weil-pbc-separable-algebraic-extension`.
- Inverse correspondence `H = Gal(Ks/L)`:
  `(IntermediateField.fixedField H).fixingSubgroup = H`; equality direction
  is immaterial and the subgroup is the same `H`.
- Transitive coset `G/H`: `Gal(Ks/K) ⧸ H`, with `Finite ... ∧
  DiscreteTopology ... ∧ ContinuousSMul Gal(Ks/K) ...`. Mathlib supplies
  the left quotient action and quotient topology. No normality is needed.
- Converse G-set: `∀ (X : Type w) [TopologicalSpace X]
  [DiscreteTopology X] [Finite X] [MulAction Gal(Ks/K) X]
  [ContinuousSMul Gal(Ks/K) X]
  [MulAction.IsPretransitive Gal(Ks/K) X] (x : X), ...` gives precisely a
  finite transitive discrete continuous G-set with a chosen point.
- Converse conclusions: `IsOpen (MulAction.stabilizer ... x : Set ...)`,
  then `FiniteDimensional K (IntermediateField.fixedField ...)` and
  `Algebra.IsSeparable K (IntermediateField.fixedField ...)`, using the
  same stabilizer in both fixed-field clauses.

Edge cases: `u v w` are unrestricted universes; `K` has arbitrary
characteristic. `H = ⊤` gives the one-point quotient, and `H = ⊥` remains
allowed whenever it is open. The empty G-set is not excluded as a type:
the converse asks for a point `x`, so its assertion is vacuous there, as
the node requires. The one-point G-set is included. There is no index,
scheme, or degree parameter in this node.

Independent searches: `msearch leanfinder` for "absolute Galois group open
point stabilizer fixed field finite separable transitive finite continuous
set" found `InfiniteGalois.isOpen_iff_finite` and related components, not
the complete statement. `msearch loogle` for
`InfiniteGalois.isOpen_iff_finite` found that component. `msearch grep` for
`stabilizer|fixedField|quotient_finite_of_isOpen`, plus `rg` in Mathlib's
`FieldTheory`, the source `WeilConjectures`, and repository `lean/Sheaf`,
found no exact packaged statement or duplicate declaration.

Source check: Stacks Tag 03QR explicitly takes an arbitrary field and its
separable closure, uses open point stabilizers, and obtains finite separable
fixed fields. Tag 0BML gives the open-subgroup/finite-subextension
correspondence. Tag 03SF, also cited by the node, concerns Galois covers of
connected schemes rather than this field-case assertion; the node's
mathematical statement remains correct. No signature mismatch was found.
The first reader's preflight corrections to the blueprint id and recorded
signature were already present; this reading changed only this report.
