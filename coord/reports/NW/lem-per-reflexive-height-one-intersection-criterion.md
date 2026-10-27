## Worker report

The module `Sheaf.RingTheory.ReflexiveHeightOneIntersection` states
`Module.isReflexive_iff_isTorsionFree_and_heightOne_intersection`, with its proof
postponed by `sorry`. It is Stacks Project, More on Algebra, Tag 0AVB,
`lemma-reflexive-over-normal`, equivalence (1) and (3). I read the statement and
proof in `literature/stacks-project/more-algebra.tex`, lines 5578–5634, and the
seven proof steps in the current DAG node. The theorem's docstring contains all
seven steps, including the explicit dual-evaluation argument and empty intersection.

The earlier BLOCKED ending concerned an unchanged stage-1 split. The present
assignment is stage 2: the live node is split and reviewed, has no Lean record,
and appears in the stage-2 queue. There is no repair note for this item.
Only the item's `lean` field is changed. No statement correction, extra definition,
or dependency module is needed.

### Clause-by-clause correspondence

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A commutative ring | `(A : Type u) [CommRing A]` |
| A domain | `[IsDomain A]`; in particular the zero ring is excluded exactly as in the node |
| Noetherian | `[IsNoetherianRing A]` |
| Normal domain | `[IsDomain A] [IsIntegrallyClosed A]`, the normal-domain encoding recorded by the dependency |
| Fraction field K | The canonical `FractionRing A = Localization (nonZeroDivisors A)`; no extra field assumption is added |
| An A-module M | `(M : Type v) [AddCommGroup M] [Module A M]`; `u` and `v` are independent explicit universes |
| Finite generation of M | `[Module.Finite A M]` |
| M_K = K tensor_A M | Both ranges have type `Submodule A (FractionRing A ⊗[A] M)`; the target is inferred from `LocalizedModule.equivTensorProduct` |
| Torsion freeness, nonzero a annihilating m forces m = 0 | `Module.IsTorsionFree A M`; I read its definition and its domain interpretation in `Mathlib.Algebra.Module.Torsion.Free` |
| Reflexivity of the specified evaluation map | `Module.IsReflexive A M`; its defining field is bijectivity of `Module.Dual.eval A M`, evaluation `m` at a functional being that functional applied to `m` |
| H(A): nonzero primes with no intermediate prime | `p : PrimeSpectrum A` and `p.asIdeal.height = 1`; over a domain this is precisely the chain definition of height one |
| M_p = localization at A minus p | `LocalizedModule p.asIdeal.primeCompl M`, the domain of `LocalizedModule.liftOfLE` in the right-hand range |
| Image of M in M_K | The left-hand `LinearMap.range`, using `LocalizedModule.mkLinearMap (nonZeroDivisors A) M`, followed by `LocalizedModule.equivTensorProduct` restricted to A-scalars |
| Image of each M_p in M_K | The right-hand `LinearMap.range`, using `LocalizedModule.liftOfLE p.asIdeal.primeCompl (nonZeroDivisors A) p.asIdeal.primeCompl_le_nonZeroDivisors`, followed by that same tensor equivalence |
| M is reflexive iff torsion free and equal to the intersection | The outer `↔`, the conjunction `∧`, and the equality of the left-hand range with `⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1), ...` |
| Empty intersection is all of M_K | Empty indexed infima in the complete lattice of submodules are `⊤` |

The generic equivalence sends `m/s` to `(1/s) ⊗ m`, as seen in
`LocalizedModule.equivTensorProduct_symm_apply_tmul`. The prime-to-generic map sends
`m/s` to the same fraction, by `IsLocalizedModule.liftOfLE_mk'`. The denominator
inclusion is the existing theorem `Ideal.primeCompl_le_nonZeroDivisors`.
Thus these are the canonical images, rather than independently chosen maps.
Taking the canonical fraction field simply fixes a model for the fraction field
named in the node; the tensor product is the node's actual ambient object.
Under the torsion-free conjunct, all the localization maps in question are
injective by the module fraction zero criterion, exactly justifying the node's
identification language. No injectivity hypothesis is added.

### Recorded statement dependencies used

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (all ideals finitely generated).
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, together with `IsDomain`, as its record prescribes for a
  normal domain. No extra all-prime normality assumption is introduced.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite` (the top submodule is finitely generated).
- `def-weil-pbc-module-localization`:
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`,
  `LocalizedModule.mkLinearMap` and `LocalizedModule.liftOfLE`.
  `Mathlib.RingTheory.Localization.BaseChange` provides the existing
  `LocalizedModule.equivTensorProduct`.

I read these dependency nodes and the definitions and docstrings of their
recorded declarations. The statement additionally uses Mathlib's `PrimeSpectrum`,
`Ideal.height`, `LinearMap.range`, `LinearMap.comp`, and `LinearMap.restrictScalars`.
No new version of any notion is declared.

The ordinary (non-public) imports retain every stated proof dependency's module:
`WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight`,
`WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes`,
`Mathlib.RingTheory.Noetherian.Basic`,
`Sheaf.LinearAlgebra.Dual.TorsionFreeBidualInjective`,
`Mathlib.RingTheory.Flat.Localization`,
`Mathlib.Algebra.Module.FinitePresentation`,
`Mathlib.LinearAlgebra.Dimension.Free`,
`Mathlib.RingTheory.Localization.Submodule`,
`Mathlib.RingTheory.Localization.LocalizationLocalization`,
`Mathlib.RingTheory.Localization.AtPrime.Basic`,
`WeilConjectures.AlgebraicGeometry.Regular`,
`Mathlib.RingTheory.DiscreteValuationRing.Basic`, and
`Mathlib.LinearAlgebra.FreeModule.PID`.
The remaining proof-dependency modules are already public imports because the
statement itself uses them (`LocalizedModule.Basic`, `Localization.BaseChange`,
`IntegralClosure.IntegrallyClosed`, `Ideal.Height`).
The unstated-proof criterion itself has no duplicate declaration in these imports.

### Edge cases checked before writing

- If A is a field, all its primes have height zero. The right-hand infimum is
  the full generic fibre, and finite-dimensional modules are reflexive with
  their image equal to that fibre. This checks the empty-height-one case.
- If M = 0, evaluation is bijective, torsion freeness holds and every image is
  the zero submodule. The generic fibre is itself zero, including for an empty
  intersection.
- For A = Z and M = Z/2, both sides are false because the torsion-free
  conjunct fails and evaluation is not bijective. The image equality alone
  could lose torsion; retaining the conjunction is essential.
- For the ideal (x,y) in k[x,y], height-one localizations have intersection A
  in the generic fibre but the module image is the proper ideal (x,y).
  Its bidual is A, so neither side holds; the equality is a substantive clause.
- Finite free modules, including rank zero, satisfy both sides. No basis,
  positive-rank, dimension-one, or nonempty-spectrum hypothesis is added.
- `u` and `v` are independently bound and there are no auto-bound variables.

### Searches for existing declarations

All remote searches used the prescribed `msearch.py NW` item wrapper.

1. `leanfinder`: “A finite module over a normal Noetherian domain is reflexive
   if and only if it is torsion free and equals the intersection of its
   localizations at height one primes”. Eight hits: Dedekind-domain and
   flat/torsion-free results, semilocal finite-generation, and DVR TFAE;
   none states the arbitrary-dimension normal-domain intersection criterion.
2. `loogle`: `Module.IsReflexive, IsIntegrallyClosed`. Zero hits.
3. `grep`: `IsReflexive|reflexive|HeightOneSpectrum`, subdirectory `RingTheory`.
   Twenty-five displayed hits concern Picard-group reflexivity and Dedekind
   height-one spectra, valuations and ideals, not this criterion.
4. `leansearch`: “A finite module over a normal Noetherian domain is reflexive
   if and only if it is torsion free and is the intersection of its height one
   localizations”. Eight hits give `Module.IsReflexive`, its torsion-free
   consequence, finite free/projective reflexivity, and PID results;
   no exact theorem.
5. `rg` on both project trees for
   `reflexive.*(inter|local)|IsReflexive|lem-per-reflexive-height-one-intersection-criterion`:
   only flat base change, finite products and quotient-duality reflexivity,
   and unrelated colimit text. No existing criterion or tagged module.
6. The upstream-name index has no reflexivity/intersection declaration.
   Direct Mathlib source reads found the exact standard definitions and maps
   used above: `Dual/Defs.lean`, `LocalizedModule/Basic.lean`,
   `Localization/BaseChange.lean`, `Ideal/Operations.lean`, and `Ideal/Height.lean`.

### Validation

The prescribed `scompile.py` compiled the module both as a sandbox module and
at its final library module name against the published live build. Both checks
passed with no errors and no warnings (2.2 s and 2.0 s in the clean run).
The sole postponed theorem is the recorded main declaration; no definition or
additional theorem is introduced. The report will be delivered with the normal
server preflight and compile checks. Independent mathematical review is the
maintainer's review, as required by this dispatched brief.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
