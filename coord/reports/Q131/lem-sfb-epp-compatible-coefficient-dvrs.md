## Worker report

The module `Sheaf.RingTheory.EppCompatibleCoefficientDVRs` states
`IsDiscreteValuationRing.exists_epp_compatible_coefficient_dvrs`, with `sorry` as its
only proof. It introduces no definitions, additional nodes, or dependency repairs.
The item's node changes only in `lean`. Its statement, accepted split, and dependency
lists are preserved.

Source read: `literature/stacks-project/more-algebra.tex`, Tag 09F9,
`theorem-epp`, especially the two final coefficient-ring preparation paragraphs
(local lines 35617–35657). These first choose the lower Cohen ring or k[[t]], then
the upper coefficient DVR, lift the compatible square, and conclude upper finiteness.
The module docstring carries all seven steps of the node's proof and names their inputs.

Hypotheses and clauses, matched against the node:

- The prime is `(p : ℕ) (hp : p.Prime)`.
- The two complete DVRs are `A : Type u`, `B : Type v`, each with `CommRing`,
  `IsDomain`, `IsDiscreteValuationRing`, and
  `IsAdicComplete (IsLocalRing.maximalIdeal ...) ...`. Completeness includes separatedness.
- The given injective local map is `(f : A →+* B) [IsLocalHom f]`
  and `(hf : Function.Injective f)`. The standard local-hom notion is equivalent to
  pulling the upper maximal ideal back to the lower maximal ideal for local rings.
- `K`, `M`, `k`, and `l` are rendered by `FractionRing A`, `FractionRing B`,
  `IsLocalRing.ResidueField A`, and `IsLocalRing.ResidueField B`; thus they are the actual
  fraction fields and residue quotients, rather than unrelated fields.
- The given residue inclusion is `IsLocalRing.ResidueField.map f`. Its range is the
  occurrence of k inside l in `hcore`. The right hand side of `hcore` is exactly
  `⋂ n : ℕ, Set.range (fun x : IsLocalRing.ResidueField B ↦ x ^ (p ^ n))`.
- Algebraic closedness is `[IsAlgClosed (IsLocalRing.ResidueField A)]`, and characteristic
  p is `[CharP (IsLocalRing.ResidueField A) p]`. Mathlib's IsAlgClosed docstring and
  `exists_root`/`of_exists_root` identify this with the node's nonconstant-polynomial
  root condition.
- The fixed uniformizer is `π : A` with
  `hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}`. In a DVR this also excludes π = 0.
- The conclusion existentially provides `A₀ : Type u`, `D : Type v`, their ring/domain/DVR
  structures and maximal-ideal completeness, and maps `a : A₀ →+* A`,
  `h : A₀ →+* D`, `b : D →+* B`. Each has its own `IsLocalHom` and injectivity witness.
- The commutative square is `b.comp h = f.comp a`.
- The lower residue identification is the equivalence `eA`, with
  `IsLocalRing.ResidueField.map a = eA.toRingHom`. This says exactly that A₀ has residue
  k compatibly with the map to A.
- The upper identification is the equivalence `eD`, with
  `IsLocalRing.ResidueField.map b = eD.toRingHom`. This says exactly that D has residue
  l compatibly with the map to B.
- The specified residue map of A₀ to D is expressed by
  `eD.toRingHom.comp (IsLocalRing.ResidueField.map h) =
  (IsLocalRing.ResidueField.map f).comp eA.toRingHom`.
- Index one is `Ideal.map h (IsLocalRing.maximalIdeal A₀) = IsLocalRing.maximalIdeal D`.
- The finite D-module conclusion is `@Module.Finite D B _ _ b.toAlgebra.toModule`.
  The scalar structure comes from the chosen inclusion b, not an arbitrary action.
- The final finite-dimensional conclusion is `FiniteDimensional` for `FractionRing B`
  over `FractionRing D`, with module structure induced by the canonical
  `IsFractionRing.map ... hb`. It is the extension of precisely b.
- If K has characteristic p, `CharP (FractionRing A) p` implies the existence of
  `e : PowerSeries (IsLocalRing.ResidueField A) ≃+* A₀`. Under this identification,
  `a (e PowerSeries.X) = π` and `Function.Bijective a` give the prescribed parameter
  and isomorphism to A. The equality for `PowerSeries.C c` says that this power-series
  identification has the specified residue identification, so its constants are k.
  Ring equivalence is the typed rendering of choosing A₀ = k[[t]].
- If K has characteristic zero, `CharZero (FractionRing A)` implies
  `IsCohenRing p A₀ ∧ IsCohenRing p D`. Together with eA and eD this says that these
  are Cohen rings for k and l. The common witnesses satisfy whichever characteristic
  case applies; no characteristic assumption was imposed on the original fraction field.
- There is no finite-generation, algebraicity, separability, or transcendence-degree
  hypothesis on l/k. The source's separability argument belongs only to the proof.

Statement dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, lines 55–60; uniformizers use
  its `irreducible_iff_uniformizer`, lines 91–94. This node is a Mathlib leaf and has
  no Lean record to repair.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete`,
  `Mathlib.RingTheory.AdicCompletion.Basic`, lines 44–56, including its Hausdorff
  and precomplete parents. It is imported publicly by the Cohen-ring module.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, lines 90–105,
  and `RingHom.toAlgebra`, lines 190–197. The theorem uses the canonical fraction
  rings and induced algebra/module structure for the specified ring homomorphism.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  `Mathlib.RingTheory.MvPowerSeries.Basic`, lines 84–87, and its one-variable
  abbreviation `PowerSeries`, `Mathlib.RingTheory.PowerSeries.Basic`, lines 58–61,
  with `C` and `X`, lines 147–159. The dependency record explicitly permits PowerSeries.
- `def-weil-pbc-cohen-ring`: `IsCohenRing`,
  `WeilConjectures.RingTheory.CohenRing`, lines 23–30. It combines primality, domain,
  DVR, maximal ideal generated by p, and p-adic completeness exactly as the node says.

The module imports all stated proof inputs, using their recorded upstream modules:
`CohenRingsExist`, `CohenRingLiftToCompleteLocal`, `PowerSeriesFieldCohenRegularComplete`,
`WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.TFAE`, `PowerSeriesAdicEvaluation`,
`FieldCohenPowerSeriesFormallySmooth`, `FormallySmoothAdicLiftIntoComplete`,
`Mathlib.FieldTheory.SeparablyGenerated`, `WeilConjectures.FieldTheory.SeparableExtension`,
and `FiniteOverCompleteRing`. The proof input `lem-sfb-dvr-index-one-adic-formal-smoothness`
has no Lean record or Mathlib match in the read base, so there is no module to import;
it is named explicitly in proof step 4. It is not needed to type the statement.

Edge cases checked mathematically before writing:

- For the identity of k[[t]] with k algebraically closed of characteristic p, take
  A₀ = D = k[[t]], identity maps, and the parameter coordinate; the conclusions reduce
  to rank-one module and fraction-field finiteness.
- For A = k[[t]], B = l[[s]], t mapping to s^e with any e ≥ 1, the coefficient
  square permits D = l[[t]]. It requires index one only for A₀ to D, so it does not
  incorrectly require the given map or D to B to be unramified. B has finite rank e over D.
- In mixed characteristic A itself may be ramified: only A₀ and D must be Cohen rings,
  and the statement does not require p to generate the maximal ideal of A or B.
- Infinite residue extensions are admitted, for example rational function fields in
  arbitrarily many variables over k whose perfect core is k. No module-finiteness
  constraint is placed on l over k.
- The n = 0 term of the perfect-core intersection is all of l and imposes no extra
  restriction. Characteristic 2 is included. Zero rings and fields are excluded exactly
  by the DVR/domain requirements; the chosen parameter cannot be zero.
- Universes u and v are independent. The coefficient DVRs live in the universes of
  their respective original rings, so no equality between these universes is assumed.

Searches run on 2026-10-24, before writing:

- `msearch.py ... leanfinder` with query "An injective local map of complete discrete
  valuation rings admits compatible coefficient DVRs with index one and finite upper
  extension": eight hits, including valuation-extension injectivity, completed-Dedekind
  DVRs, Witt-vector DVRs, and local valuation factorizations; none states this square.
- `msearch.py ... loogle` with `IsDiscreteValuationRing, IsAdicComplete`: zero hits.
- `msearch.py ... leansearch` with "Compatible coefficient discrete valuation rings for
  an injective local map of complete discrete valuation rings": eight hits on valuation
  subring inclusions and DVR constructors; no compatible coefficient square.
- `msearch.py ... grep` with `CohenRing|coefficient.*valuation|valuation.*coefficient`
  in `RingTheory`: eleven hits, on Laurent-series coefficients, valuation minpolys,
  and polynomial subrings; no compatible coefficient square.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `coefficient.*[Dd][Vv][Rr]|compatible.*[Cc]oefficient|epp-compatible-coefficient-dvrs`
  found unrelated sheaf coefficient comparisons and local coordinates, no item match.
- Exact-name `rg` over both Lean roots and `dag/lean_names_upstream.json` for
  `exists_epp_compatible_coefficient_dvrs|EppCompatibleCoefficientDVRs` found no collision.
- The repair-notes directory and Q131 returns contained no entry for this item.

Validation: `scompile.py Q131 lem-sfb-epp-compatible-coefficient-dvrs` compiled the delivered
file on the live server as both sandbox and library module, with no errors or unexpected
warnings (7.8 s and 2.1 s). `set_option autoImplicit false` enforces explicit binding of all
variables; both universes are declared. The maximum Lean line length is at most 100.
No node fault or disputed statement was found.

## Second reading by Q131

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
