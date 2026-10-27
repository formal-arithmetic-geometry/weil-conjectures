## Worker report

The module `Sheaf.RingTheory.EquivariantMarkedCylinderAlgebraization` states
`RingTheory.exists_equivariant_marked_cylinder_algebraization`. Its sole proof is
`sorry`; there are no definitions, extra axioms, new nodes, dependency repairs or
statement corrections. Only the assigned node's `lean` field changes. The earlier
module was removed during pruning; I read the earlier Q59 report and reconstructed
and compiled the statement against the current library, rather than binding a removed
name as an existing declaration.

Sources read: the node and its fourteen proof steps; all nine statement-dependency
records and the recorded definitions and docstrings in Mathlib or the project; ILO,
Expose V, 1.1.1--1.2.4, 2.1.1--2.2.8, and 3.1.1--3.2.4, printed pp.63--68, from the
local PDF; the current blueprint's sk-p-dl-a1-perverse section under
`literature/blueprint/latest/`. The original node is a supporting algebraization
lemma, not the blueprint unit's own statement. No mathematical fault was found.

In the following correspondence only, R denotes `MvPowerSeries (Fin (n + 1)) V`,
and D denotes `MvPowerSeries (Fin n) Λ`. The signature has no local notation or
let binders.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| V a field or complete DVR | `[CommRing V] [IsDomain V] [IsLocalRing V]`, maximal-ideal `IsAdicComplete`, and the alternatives in `hkind` |
| r >= 1 | `n : ℕ` and the variable set `Fin (n + 1)` |
| B complete Noetherian normal local domain | `[CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]` and maximal-ideal `IsAdicComplete` |
| Coefficient subring V in B | Composite of `MvPowerSeries.C` with `algebraMap R B`; it is injective by `hinj` and injectivity of constants |
| Coefficient inclusion induces residue-field isomorphism | `hres`: a ring equivalence of V/m_V with B/m_B whose quotient-map square equals that coefficient composite |
| Injective module-finite local formal presentation | `[Algebra R B] [Module.Finite R B] [IsLocalHom (algebraMap R B)]` and `hinj` |
| Finite group with order invertible in V | `(H : Type v) [Group H] [Finite H]` and `horder : IsUnit (Nat.card H : V)` |
| Local automorphisms of V and B | Two `MulSemiringAction` instances; group action maps are ring automorphisms, and automorphisms of a local ring preserve its unique maximal ideal |
| Compatible map and variables fixed | `hequiv`: intertwines the B action with coefficientwise `MvPowerSeries.map (MulSemiringAction.toRingHom H V h)`; the latter fixes every formal variable |
| H trivial in field case | `Subsingleton H` in the field alternative of `hkind` |
| Λ exactly V^H | `(Λ : Subring V)` and `hΛ : Λ = FixedPoints.subring V H` |
| Λ field or complete DVR respectively | `[IsLocalRing Λ]`, maximal-ideal `IsAdicComplete`, and `IsField Λ` or `IsDiscreteValuationRing Λ` in the matching alternative of `hkind` |
| Existence of denominator f | The theorem quantifies `(f : R)` with its two required properties; this is equivalent to the existential hypothesis in the node |
| f nonzero modulo m_V | `hred`, coefficientwise reduction by `Ideal.Quotient.mk (IsLocalRing.maximalIdeal V)` is nonzero |
| Finite map etale after inverting f | `hetale`: `RingHom.Etale` for the canonical `IsLocalization.Away.map` from `Localization.Away f` to the localization of B away from its image |
| A_0 exactly B^H | `(A₀ : Subring B)` and `hA₀ : A₀ = FixedPoints.subring B H` |
| Any finite family of marking ideals | `(s : ℕ) (I : Fin s → Ideal A₀)` |
| Equivariant change of formal coordinates fixing V | Existential `c : R ≃ₐ[V] R`, together with its commutation equation for each coefficient action; its images of the standard variables are the new coordinates |
| D = Λ[[u_1,...,u_{r-1}]] | The ring D above, included by `MvPowerSeries.map Λ.subtype`, then `MvPowerSeries.rename Fin.castSucc`, then c |
| D is the complete coefficient ring | D is a finite-variable power-series ring over the complete field or DVR Λ, so it is complete local; no extra completeness assumption on D is imposed |
| The structural map D to A_0 is that inclusion | Existential `d`, with `A₀.subtype.comp d` equal to the full composite just described followed by `algebraMap R B`; equality specifies all formal series, not only variables |
| Finite-type D[T]-algebra C | `∃ (C : Type u) (_ : CommRing C) (a : Polynomial D →+* C) (hft : a.FiniteType)` |
| Maximal ideal n of C | `p : PrimeSpectrum C` and `p.asIdeal.IsMaximal` |
| n lies over (m_D,T) | `p.asIdeal.comap a = Ideal.comap Polynomial.constantCoeff (IsLocalRing.maximalIdeal D)`; the ideal on the right is exactly (m_D,T) |
| D[T] to C quasi-finite | `Algebra.IsQuasiFiniteAtPrime (Polynomial D) C q` for every `q`, using precisely `a.toAlgebra` and `hft`; for finite-type maps this is equivalent to finite fibre spectra and finite residue extensions |
| C/n finite over D/m_D | Existential `k : (D ⧸ m_D) →+* (C ⧸ p.asIdeal)` with `k.Finite`, and its quotient-map square tied to `a.comp Polynomial.C`; surjectivity of the quotient map makes k canonical |
| Ideals J_1,...,J_s in C | `J : Fin s → Ideal C` |
| Isomorphism of completed C_n with A_0 | `e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) (Localization.AtPrime p.asIdeal) ≃+* A₀` |
| The isomorphism is D-linear | For every `x : D`, applying e to the canonical image of `a (Polynomial.C x)` in the completion gives `d x`; a ring equivalence with this equation is precisely a D-algebra equivalence |
| The same isomorphism carries extended J_i onto I_i | The final `Ideal.map` equality for every `i : Fin s`, along C to C_n to its completion to A₀ |
| Empty family, zero and unit markings allowed | No positivity assumption on s and no propriety or nonzero condition on I or J |

The coefficient subring and both actions are the given ones: no extra coefficient map,
faithfulness, characteristic restriction, arbitrary completion map, or arbitrary replacement
for the coordinate inclusion is introduced. A ring automorphism of the local formal ring
preserves powers of its maximal ideal and is therefore continuous in its formal topology.
The common ring universe u covers any V and B after universe enlargement; H has the
independent universe v. A finite-type model can be taken in u by its finite presentation.
There is no quantification over test rings in a smaller unrelated universe.

Dependency declarations used (module and name):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `IsAdicComplete`,
  `AdicCompletion`, its ring and algebra structure and the canonical `algebraMap`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`, `.Rename`, `.Inverse`: `MvPowerSeries`,
  `MvPowerSeries.C`, `.map`, `.rename`, its algebra and local-ring structures.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
  This Mathlib dependency has no `lean` record and needs no repair.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`; `RingHom.Finite` packages
  the same notion for the displayed residue-field map.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, with the
  permitted ring-map encoding `RingHom.Etale` used for the localized ring map.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`; residues
  at maximal ideals use their canonical quotient fields.
- `WeilConjectures.RingTheory.QuasiFiniteAtPrime`: `Algebra.IsQuasiFiniteAtPrime`,
  read from its actual source, using the canonical fibre point and its open singleton.

Auxiliary notions are existing library definitions:
`FixedPoints.subring` in `Mathlib.Algebra.Algebra.Subalgebra.Operations`,
`IsIntegrallyClosed` in `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
and `IsLocalization.Away.map` in `Mathlib.RingTheory.Localization.Away.Basic`.
All statement modules are public imports. All currently recorded proof modules are
private imports, including the recently restored `TraceOneInvariantFiniteness`.
Unstated proof dependencies remain in the DAG and are spelled out in the fourteen-step
proof docstring; they are not missing notions needed to type this statement.

Edge cases checked against the node and source before writing:

- r=1 is n=0. D has no formal variables and is canonically Λ; the empty-domain
  `rename Fin.castSucc` still gives the coefficient inclusion.
- s=0 is `Fin 0`. The model and equivalence still exist, with the ideal equation vacuous.
- I=0 and I=A₀ have no excluded hypotheses and retain their full ideal structures,
  rather than just equality of radicals or supports.
- A trivial group is allowed, required in the field case. Nonfaithful DVR actions are
  allowed. The group has positive cardinality because it is a group, with no separate
  cardinality assumption.
- The field and DVR cases remain separate in `hkind`; no perfectness, mixed
  characteristic or algebraic closedness assumption is added.
- All residue maps and the local completion use the specified structural maps and ideals.

Searches made before writing (no surviving exact declaration found):

- `msearch.py ... leanfinder "A complete normal local invariant ring with finitely many
  marked ideals is the completion of a quasi-finite algebra over a polynomial cylinder"`:
  eight hits on quasi-finiteness, henselian completion and formal smoothness; none states
  marked equivariant algebraization.
- `msearch.py ... loogle "MvPowerSeries.map, MulSemiringAction.fixedSubring,
  AdicCompletion, Algebra.IsQuasiFiniteAtPrime"`: zero hits, unknown identifier
  `MulSemiringAction.fixedSubring`; source search found the correct existing
  `FixedPoints.subring` instead.
- `msearch.py ... grep "equivariant.*algebraization|marked.*cylinder|fixedSubring"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "finite group invariant normal complete local ring
  algebraization ideals over power series polynomial ring"`: eight hits, local-ring
  power-series and Weierstrass results, no marked algebraization theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for cylinder/algebraization names:
  related formal-glueing results, no exact theorem. The literal node-id grep in
  `lean/WeilConjectures` has no hits. The exact declaration and module names are absent
  from the current Lean sources and `dag/lean_names_upstream.json`.
- `tools/lean_names_upstream.py show <item>`: no matching declaration.
- `tools/blueprint_refs.py search cylinder`: zero matching blueprint nodes.
- Direct Mathlib source search located the actual fixed subring, coefficient action,
  renaming, localized map and completion interfaces, so no new definition is needed.

Validation: `scompile.py Q58 lem-per-equivariant-marked-cylinder-algebraization <file>`
compiled the delivered module cleanly in both sandbox and library positions (2.4 s each).
The required dry run and final delivery repeat the preflight and single-file checks.

## Second reading by Q58

This is the author's second clause audit, not an independent agent review; the dispatcher
forbids starting other agents and assigns independent review to the maintainer. I reopened
the node, the ILO source passages and the final Lean file. The table above covers each
hypothesis and conclusion of the node. In particular I rechecked the quotient-map square
in `hres`, the coefficientwise H action in `hequiv`, both alternatives in `hkind`, the
full ring-map equation for `d`, the ideal (m_D,T), the exact algebra instance in the
quasi-finite clause, and the square specifying the finite residue extension. Finally e
is linear for d and the identical e transports all the J_i. No mismatch was found;
no hypothesis, marking or edge case was added or removed. The compiled first draft
already had these equations, so no signature correction was necessary. No statement
change or disputed statement is claimed.
