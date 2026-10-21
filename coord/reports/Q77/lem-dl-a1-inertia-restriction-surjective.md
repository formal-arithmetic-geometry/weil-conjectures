## Worker report

The module `Sheaf.FieldTheory.InertiaRestrictionSurjective` states
`Ideal.inertia_map_restrictNormalHom`, with its only proof `sorry`.
The source is Stacks Tag 0BSX, `lemma-one-orbit-geometric-galois-compare`,
in `literature/stacks-project/more-algebra.tex:32869` (read through its proof).
No definition, new node, dependency repair, or statement correction is needed.
Only the item's `lean` record is changed.

Hypotheses and clauses, compared with the node:

- A normal domain A: `(A : Type u) [CommRing A] [IsDomain A]
  [IsIntegrallyClosed A]`. These are the recorded inline normal-domain encoding
  of `def-weil-pbc-normal-ring`.
- K = Frac(A): `(K : Type v) [Field K] [Algebra A K]
  [IsFractionRing A K]`, allowing any model of the fraction field.
- K ⊆ L ⊆ M: the field and `Algebra` binders on K, L, M, together with
  `[IsScalarTower K L M]`. The A-algebras and the scalar towers
  `A K L`, `A K M`, and `A L M` express that all occurrences of A use this same
  inclusion. These express compatible inclusions, not extra mathematical restrictions.
- L/K and M/K Galois: `[IsGalois K L] [IsGalois K M]`. Read
  Mathlib's `IsGalois` class: its fields are `Algebra.IsSeparable` and `Normal`.
  Separability includes algebraicity (the recorded dependency encoding), and
  normality says that the minimal polynomials split. No finite-dimensional,
  finiteness, Noetherian, DVR, maximal-ideal, or residue-separability assumption occurs.
- B and C are exactly `integralClosure A L` and `integralClosure A M`, using
  the recorded `integralClosure` declaration, not replacement rings or arbitrary maps.
- The chosen prime is `(r : Ideal (integralClosure A M)) [r.IsPrime]`.
- q = r ∩ B is written directly as
  `r.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom`.
  `AlgHom.mapIntegralClosure` is Mathlib's actual restriction of the inclusion
  L → M to integral elements, with the same underlying element map.
- The actions on B and C are Mathlib's `MulSemiringAction` on integral closures,
  induced by the evaluation action of `L ≃ₐ[K] L` and `M ≃ₐ[K] M`.
- I_r and I_q are the existing `.inertia` subgroups. The underlying definition
  `AddSubgroup.inertia` means `∀ x, σ • x - x ∈ r`, exactly identity on C/r.
  `Ideal.inertia_le_stabilizer` shows this already includes stabilization of r.
  Since r is prime, identity on C/r is equivalent to identity on Frac(C/r):
  one direction restricts along the injective inclusion, and the other fixes
  every numerator and nonzero denominator. The same applies to the contracted
  prime. Thus this is the node's inertia, including the explicit residue-field clause.
- Restriction is exactly `AlgEquiv.restrictNormalHom L`, the canonical group
  homomorphism, with its full signature and commutation property read in
  `Mathlib.FieldTheory.Normal.Defs`.
- The conclusion is subgroup-image equality
  `(r.inertia (M ≃ₐ[K] M)).map (AlgEquiv.restrictNormalHom L) = q.inertia (L ≃ₐ[K] L)`.
  Left-to-right inclusion states that restriction lands in lower inertia;
  right-to-left inclusion states every lower inertia element has an upper
  inertia preimage. Together they are precisely the assertion that restriction
  induces a surjective group homomorphism. No unrelated surjective map is chosen.

Dependency declarations read and used:

- `def-weil-pbc-normal-ring`: `IsIntegrallyClosed`, `IsDomain`, in
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` and its imports;
  only the normal-domain clause is relevant here, not the general normal-ring clause.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`, used through `IsGalois` in
  `Mathlib.FieldTheory.Galois.Basic`.
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`.
- Additional existing constructions: `AlgHom.mapIntegralClosure`,
  `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`;
  `AlgEquiv.restrictNormalHom`, `Mathlib.FieldTheory.Normal.Defs`;
  `AddSubgroup.inertia`, `Mathlib.Algebra.Group.Subgroup.Basic`;
  `Ideal.inertia_le_stabilizer`, `Mathlib.RingTheory.Ideal.Pointwise`.
  Public imports expose these dependency interfaces transitively.

The stated proof dependencies are imported: `Mathlib.RingTheory.Localization.Integral`
for `integralClosure.isFractionRing_of_algebraic` (proof-only import),
`Mathlib.FieldTheory.Normal.Basic` for `AlgEquiv.restrictNormalHom_surjective`,
and `Mathlib.FieldTheory.Galois.Basic` for `IsGalois.tower_top_of_isGalois`.
The residue-lifting proof node `lem-dl-a1-galois-prime-residue-lifting`
has no recorded declaration or mathlib match in the read repository; no module
for this proof-only dependency can be imported yet. Its full lifting argument is
referenced in the six-step docstring. It is not needed to type the statement.

Edge cases checked before writing: r may be the zero prime or a nonmaximal prime;
no quotient-field action needs an extraneous chosen maximal ideal. For A a field
and r zero, inertia is trivial, so the conclusion is equality of trivial subgroups.
L = K, M = L, and all identity extensions are allowed. Infinite Galois extensions
are included. Residue extensions may be inseparable: fixing their whole quotient
fraction field has the intended meaning regardless of separability. All four
universes are explicitly independent; every binder is explicit, with autoImplicit off.
There are no empty-domain cases because A is a domain and K, L, M are fields.

Searches made with the prescribed wrapper:

- `leanfinder`: "Restriction from inertia of an integral closure prime in an
  infinite Galois extension to inertia in a Galois subextension is surjective".
  Eight hits: prime conjugacy and finite residue/stabilizer surjectivity,
  `IsFractionRing.stabilizerHom_surjective`,
  `Ideal.Quotient.stabilizerHom_surjective_of_profinite`, and inertia-degree
  formulas; no exact inertia restriction theorem.
- `loogle`: `Ideal.inertia, AlgEquiv.restrictNormalHom`: zero hits.
- `grep`: `inertia.*(surject|restrict)|surject.*inertia|exists_mem_inertia`:
  three unrelated hits in `Mathlib/RingTheory/Polynomial/Morse.lean`.
- `leansearch`: "Restriction maps inertia groups of primes of integral closures
  surjectively in a tower of infinite Galois field extensions". Eight hits,
  including `AlgEquiv.restrictNormalHom` and finite restriction results; none
  asserts surjectivity between these inertia subgroups.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for inertia/restriction,
  and the item id in `lean/WeilConjectures`: no exact statement. Read
  `WeilConjectures.Mathlib.RingTheory.Invariant.Profinite` in full through
  `Ideal.exists_mem_inertia_eqOn`: it assumes a maximal ideal, so cannot attach
  to this arbitrary-prime node. `Sheaf.FieldTheory.FiniteTameCharacterTower`
  has a private finite-DVR normalization comparison: its extra DVR, finite-degree,
  and maximal-ideal hypotheses exclude the general statement here.
  Searched `dag/lean_names_upstream.json` and all three Lean roots for the new
  declaration name: no conflict.

Validation: scompile.py compiled the sandbox and library module separately on the
server, cleanly (1.4 s and 1.6 s), with no errors or warnings.
No statement dispute or node fault was found.

## Second reading by Q77

This is the worker's final self-reading; the dispatcher brief assigns the independent
reading to the maintainer and prohibits starting other agents. Reopened the node and
compared its clauses to the signature above: normal domain, fraction field, compatible
field tower, both possibly infinite Galois hypotheses, actual integral closures,
arbitrary chosen prime, canonical contraction, exact inertia, and canonical restriction
are all represented. Checked that subgroup-image equality supplies both well-definedness
and surjectivity and that quotient identity is equivalent to fraction-field identity.
No mismatch or correction was found. Independent review remains with the maintainer.
