## Worker report

The module `Sheaf.LinearAlgebra.CofactorLocalDescent` states
`Module.existsUnique_cofactor_local_descent`, with its proof `sorry`.
The node's natural-language statement and all its dependency fields are unchanged.
The remaining declarations are explicit types, predicates, and the concrete local
wedge expression belonging to this statement, not independently postponed lemmas.
There are no definition bodies containing sorry, private definitions, local notation,
local instances, auto-implicit variables, or proof attempts.

Source read: Stacks `duality.tex`, label `lemma-determinant`, Tag 0E9Y,
including its displayed formula and omitted well-definedness check. This node is the
rank-difference-one construction, without any injectivity assumption. Its seven-step
DAG proof is included in the main theorem's docstring. The exterior retract, scalar
comparison, basis-change, cover gluing and arbitrary-localization arguments are all
retained; no change to the blueprint unit is needed.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A commutative ring | `{A : Type u} [CommRing A]` |
| c nonnegative | `c : ℕ` |
| Arbitrary finite projective P and Q | Independent `P : Type v`, `Q : Type w`, additive groups, A-module instances, and `[Module.Finite A P] [Module.Projective A P]` and the analogous Q instances |
| Ranks c and c+1 at every prime | `hP : ∀ p : PrimeSpectrum A, Module.rankAtStalk P p = c` and `hQ` with `c + 1` |
| Any A-linear u, without injectivity | `u : P →ₗ[A] Q`; no additional condition on u |
| C = Q/u(P) | The actual quotient `Q ⧸ LinearMap.range u`, with `(LinearMap.range u).mkQ` its quotient map |
| J and D_u | The existing `⋀[A]^c P`; `CofactorTarget` is only an explicit abbreviation for `Dual A (⋀[A]^c P) ⊗[A] (⋀[A]^(c+1) Q)` |
| Finite common standard cover of the specified ranks | `∃ n f, Ideal.span (Set.range f) = ⊤ ∧ ∀ i, Nonempty (Basis (Fin c) ...) ∧ Nonempty (Basis (Fin (c+1)) ...)` |
| The cover's localized modules | `Localization.Away (f i) ⊗[A] P` and Q, canonically identified with `LocalizedModule.Away (f i) P` and Q by Mathlib's `LocalizedModule.equivTensorProduct` |
| J finite projective | `Module.Finite A (⋀[A]^c P) ∧ Module.Projective A (⋀[A]^c P)` |
| Every localization B = S⁻¹A | `e : ∀ S : Submonoid A, CofactorScalarComparison (Localization S) u c`; the canonical ring represents every localization via its unique A-algebra isomorphism, so there is no restriction on the localization |
| Exterior comparisons | `source`, `target` are B-linear equivalences normalized by `source_wedge`, `target_wedge` on all pure wedges and scalars |
| Dual comparison and its specified evaluation | `dual` with `dual_eval`: evaluation on `source (b' ⊗ x)` is `b * b' * algebraMap A B (l x)` |
| Tensor comparison for D_u | `line` with `line_tensor`, sending `b ⊗ (l ⊗ x)` to `dual (b ⊗ l) ⊗ target (1 ⊗ x)` |
| C_B identified with B tensor C | `cokernel` and `cokernel_class`, whose value is the class of `b ⊗ v` in the actual cokernel of `u.baseChange B` |
| Agreement under successive localizations | `CofactorComparisonsCoherent`: for every inclusion S ≤ T, the exterior squares commute on all localized wedges, the dual square commutes with evaluation, and the line square preserves the tensor factors. Transitions use `IsLocalization.map` and `TensorProduct.map`; the normalization on spanning tensors also fixes their identity and composition identifications. Every successive localization is such a transition after canonical localization identifications. |
| A unique global map w_u | `∃! w : (Q ⧸ LinearMap.range u) →ₗ[A] CofactorTarget A P Q c, ...` |
| Formula on any free localization of P | `IsLocalCofactor` quantifies over every S, every `Basis (Fin c) (Localization S) (Localization S ⊗[A] P)`, and every localized vector v. No freeness assumption on localized Q is imposed in this formula. |
| w on the localization is scalar extension | The formula uses exactly `w.baseChange (Localization S)`, composed with the normalized cokernel and line comparisons |
| The displayed dual basis wedge | `exteriorPower.pairingDual ... (exteriorPower.ιMulti ... p.coord)`, the determinant of the coordinates on the top exterior power, taking value 1 on the ordered basis wedge |
| The wedge of u(p_1),...,u(p_c),v | `exteriorPower.ιMulti ... (Fin.snoc (fun i ↦ u (p i)) v)` in `cofactorBasisValue` |
| Independence of basis and lift | The same w satisfies `IsLocalCofactor` for *every* basis and vector. Two lifts of a quotient class have identical left sides, and two bases have the same left side. |
| Every finite standard free cover | `CofactorCoverDescent` quantifies over every n, f with unit-ideal span and every pair of bases of P and Q of the specified ranks |
| The values on v/1 match on overlaps | First conjunct of `CofactorCoverDescent`, using `LocalizedModule.equivTensorProduct` and exactly the `IsLocalizedModule.lift` restriction maps used by the recorded `coverModuleExact` |
| They localize from a unique d in D_u | Second conjunct, `∃! d, ∀ i, (e ...).line (1 ⊗ d) = cofactorBasisValue ... (1 ⊗ v)` |
| This is w_u, independently of the cover | `IsLocalCofactor` applied to each chart identifies d with `w (mkQ v)`; global uniqueness and quantification over every cover make the characterization independent of the cover |
| c=0 | `∀ hc : c = 0, Subsingleton P ∧ ∀ v, (hc ▸ w) (mkQ v) = (exteriorPower.zeroEquiv ...).toLinearMap ⊗ (exteriorPower.oneEquiv ...).symm v`; this removes the dual of the degree-zero exterior power and gives the canonical degree-one identification |
| Zero ring included | No `Nontrivial A`, no prime-existence, and no nonempty-cover assumption; n=0 is allowed |

Dependency declarations read and used:

- `Mathlib.Algebra.Module.Projective`: `Module.Projective`, the canonical free
  surjection splitting, equivalent to the node's projectivity notion. Finiteness
  is separately asserted with Mathlib's `Module.Finite`.
- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `ExteriorAlgebra`,
  `ExteriorAlgebra.ι`, `exteriorPower`; exterior powers are the actual homogeneous
  submodules of the exterior algebra, with no replacement notion.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`,
  `LocalizedModule.mkLinearMap`, `LocalizedModule.Away`, `IsLocalizedModule.lift`.
- `WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover`:
  `Module.exists_standardFreeCover_of_finite_projective`.
- `WeilConjectures.RingTheory.CoverModuleExact`: `RingTheory.coverModuleExact`
  and `RingTheory.localizationAway_map_units_of_dvd`; the report and predicate
  use the latter's full divisor/unit signature and the former's canonical overlap
  maps, rather than a private module-restriction definition.
- `Mathlib.RingTheory.Spectrum.Prime.FreeLocus`: `Module.rankAtStalk` is finrank
  of the prime-localized module; `Module.isLocallyConstant_rankAtStalk` is the
  recorded proof dependency for constancy and stalk ranks.
- `Mathlib.LinearAlgebra.ExteriorPower.Basis`: `Module.Basis.exteriorPower`,
  `exteriorPower.ιMultiDual` and the pure-wedge basis/evaluation results;
  `exteriorPower.zeroEquiv` and `exteriorPower.oneEquiv` from ExteriorPower.Basic.
- `Mathlib.LinearAlgebra.TensorProduct.Basis` and `.Tower`:
  `Module.Basis.baseChange`, `TensorProduct.AlgebraTensorModule.cancelBaseChange`
  (the free-base-change-tower node's Mathlib matches), and `LinearMap.baseChange`.
- `Mathlib.RingTheory.Localization.BaseChange`: `LocalizedModule.equivTensorProduct`,
  `IsLocalizedModule.isBaseChange`, and the tensor localization comparisons
  recorded for `lem-weil-pbc-localization-tensor-product`.
- `Mathlib.Algebra.Module.LocalizedModule.Exact`: `LocalizedModule.map_exact`,
  the recorded exact-localization match.
- `WeilConjectures.LinearAlgebra.GenericExteriorPowerLocalization`:
  `exteriorPower.isLocalizedModule_of_pure_wedge`, the available pure-wedge
  localization proof interface.

The proof dependency `lem-trf-projective-exterior-scalar-comparisons` has neither
Lean record nor Mathlib match in the current DAG. It is only a proof dependency:
no statement object is taken from it, and there is no module to import. The scalar
comparison assertions required by this item's own statement are explicitly stated
in this theorem, including their defining formulas and tower compatibility.
No missing statement notion or unusable recorded dependency required a new node.

Duplicate searches (all performed for this delivery):

- `msearch.py`, leanfinder, query `Canonical cofactor map cokernel finite projective modules exterior powers localization gluing`:
  eight hits, including `Module.Finite.exists_comp_eq_id_of_projective`,
  `exteriorPower.presentation.isPresentationCore`, and general projective/localization
  lemmas; none states the cofactor localization and descent theorem.
- `msearch.py`, loogle, query `exteriorPower.baseChange, exteriorPower, LinearMap.dualMap`:
  zero hits, unknown identifier `exteriorPower.baseChange`.
- `msearch.py`, grep, query `cofactor|exterior.*[Bb]ase[Cc]hange` in LinearAlgebra:
  four unrelated Vandermonde/adjugate hits; no match.
- `msearch.py`, leansearch, query `Local cofactor map finite projective module exterior powers cokernel`:
  eight hits on `ModuleCat.cokernelIsColimit`, exterior-power functors/presentations,
  and ordinary cokernel data, not this statement.
- `rg` for `cofactor|Cofactor` in `lean/Sheaf` and `lean/WeilConjectures`:
  read `Sheaf.LinearAlgebra.TwoTermCofactorNaturality` in full through
  `existsUnique_twoTermCofactorPresentation`. It is a different statement: a
  two-term determinant presentation, contraction normalization and derived naturality.
  It does not state the present node's finite cover, exterior projectivity,
  localization comparisons, successive localization, or matching-family assertion.
  Its `TwoTermComplex.cofactorLine` is a codomain abbreviation for bundled two-term
  complexes; this module uses the same tensor/exterior/dual types directly for
  arbitrary modules P, Q, without importing the downstream naturality theorem.
- `rg -n 'lem-sfb-cofactor-local-descent' lean/WeilConjectures`: no match.
- `rg` for all proposed declaration names in Mathlib, `lean/Sheaf`, and
  `lean/WeilConjectures`: no existing names. Exterior-power and tensor source files
  were searched for base change, dual comparison, and quotient comparison APIs.

Edge checks before writing and after elaboration:

- c=0: Fin.snoc of the empty family is the one-vector wedge; the coordinate
  determinant is the empty determinant 1. The theorem explicitly states P=0
  as `Subsingleton P` and the canonical degree-one identification.
- A=0 and empty cover: unit-ideal span permits n=0 precisely when 0=1;
  additive module structures then force every element to be zero. Bases of any
  prescribed finite cardinal exist over the zero ring, so the statement never
  invokes invariant-basis-number or prime existence there.
- u=0 with c>0: every positive image wedge vanishes and the cofactor map is zero.
- Noninjective maps over a nonreduced ring, e.g. A=k[epsilon]/epsilon²,
  c=1, u(a)=(epsilon*a,0): wedge annihilation still kills u(P); no injectivity
  has been silently imposed.
- Rescaling/changing the ordered basis multiplies the numerator wedge and its
  dual by inverse units, with no division by factorials and no restriction on
  characteristic. The chosen `pairingDual` uses determinants, not a factorial
  normalization.
- S containing zero: Localization S and all its modules vanish, so comparison,
  basis formula, and tower coherence remain valid.
- Independent universes for A, P, Q: the theorem retains u, v, w independently.
  Canonical localization rings have universe u and scalar-extended modules the
  required maximum universe; representing localizations canonically excludes
  no algebra and adds no universe equality assumption.

Validation: `scompile.py N9 lem-sfb-cofactor-local-descent` compiled the complete
module in both sandbox and library module contexts, with no diagnostics other than
any expected sorry notice. `autoImplicit` and `relaxedAutoImplicit` are both false.
No statement disputes or node faults were found.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
