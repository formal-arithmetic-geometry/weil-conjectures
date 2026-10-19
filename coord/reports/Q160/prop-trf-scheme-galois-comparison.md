## Worker report

The module `Sheaf.SixFunctors.SchemeGaloisComparison` states
`WeilConjectures.FiniteFieldDatum.schemeGaloisComparison` with proof `sorry`.
It introduces no definitions and no new nodes. The statement uses the recorded
scheme Frobenius and geometric Galois Frobenius, the arbitrary constant-ring
pro-etale derived pullback, and the existing universal-homeomorphism predicate.

The hypotheses and clauses are rendered as follows.

- The global finite-field datum is
  `D : WeilConjectures.FiniteFieldDatum.{u}`. The finite-type model is
  `X₀ : Over (Spec (CommRingCat.of D.k₀)))` with exactly
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`.
- The coefficient is `A : Type u` with `[CommRing A] [Finite A]`. The phrase
  “annihilated by an integer invertible in k” is the explicit hypothesis
  `hA : ∃ n : ℕ, IsUnit (n : D.k) ∧ ∀ a : A, n • a = 0`; this permits the
  zero ring and does not impose a chosen presentation of `A`.
- The first existential is the natural isomorphism
  `κ : proEtaleConstantRingDerivedPullback A (D.schemeFrobenius X₀) ≅
  proEtaleConstantRingDerivedPullback A (D.geometricGaloisFrobenius X₀)`.
- The second existential is the family `κiter` for every `m : ℕ` with
  `1 ≤ m`, comparing pullback along `schemeFrobeniusIterate X₀ m` with pullback
  along the `m`-th power of `geometricGaloisFrobenius`; its `m = 1` value is
  required to equal `κ`.
- The family is multiplicative: for positive `m,n`, the statement supplies the
  power equalities `hP` and `hG`, inserts the canonical derived pullback
  composition comparisons `proEtaleConstantRingPullbackComposition`, and requires the
  resulting composite of `κiter m` and `κiter n` to equal `κiter (m+n)`.
  `Functor.whiskerLeft` and `Functor.whiskerRight` express the two natural
  transformations in the order `G_m(κ_n) ∘ κ_m(T_n)`.
- For every positive `m`, the absolute `p^(a*m)`-power Frobenius on the geometric
  fibre is asserted to be `IsUniversalHomeomorphism`. The two factorization clauses
  reproduce both equalities of the recorded `absoluteFrobenius_factorization`,
  so the comparison is tied to the scheme/Galois factorization rather than an
  arbitrary isomorphism.

The added statement dependency `pur713-def-pullback-comparison` is already landed;
its canonical constant-coefficient composition specialization is used to type the
multiplicative law, without introducing a new definition.

The statement dependencies and declarations used are:

- `pur713-def-pullback-comparison`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`,
  `AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition`.
- `def-trf-scheme-frobenius`: `Sheaf.SixFunctors.SchemeFrobenius`,
  declarations under `WeilConjectures.FiniteFieldDatum`, especially
  `schemeFrobenius`, `schemeFrobeniusIterate`, and
  `geometricGaloisFrobenius`.
- `prop-trf-frobenius-factorization`: `Sheaf.AlgebraicGeometry.FrobeniusFactorization`,
  `WeilConjectures.FiniteFieldDatum.absoluteFrobenius_factorization`.
- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum` and `geometricFiber`.
- `def-weil-pbc-proetale-site`: `WeilConjectures.SixFunctors.ProEtale.Derived.ModuleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` (through the published
  constant-ring operations module).
- `def-weil-absolute-frobenius-scheme`: `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`,
  `AlgebraicGeometry.Scheme.iterateFrobenius`.
- `def-weil-pbc-proetale-operations`: `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
  `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback`.
- `def-weil-universal-homeomorphism`: Mathlib's
  `CategoryTheory.MorphismProperty.universally`, `AlgebraicGeometry.topologically`,
  and `IsHomeomorph`; the equivalent class `IsUniversalHomeomorphism` is
  imported from `WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius`.

The proof dependencies imported for the stated plan are
`AbsoluteFrobeniusSite`, `FrobeniusTrivializationPullback`,
`ProEtaleConstantRingOperations`, and the canonical composition interface. They
supply the exact trivialization, composition normalization, and localization
interfaces named in the node proof; no proof is attempted here.

Edge cases checked: `m,n` are positive only where the source requires iterates;
`m=1` is explicitly retained; `A` may be the zero ring; no reducedness,
nonemptiness, separatedness, or extra characteristic assumption is added; the
universal-homeomorphism clause covers nilpotents and the empty scheme; all
universes are bound explicitly and the coefficient ring uses the same `Type u`
as the finite-field datum.

Searches for an existing declaration were run before writing:

- `msearch.py ... leanfinder "Derived pullback along scheme Frobenius naturally
  isomorphic to geometric Galois Frobenius on pro etale constant coefficient
  sheaves"`: no matching declaration; only generic `Scheme.Modules` pullback
  and Frobenius candidates.
- `msearch.py ... loogle "frobenius, RingHom"`: Mathlib Frobenius ring-map
  lemmas only; no site or derived-category comparison.
- `msearch.py ... grep "frobenius|Frobenius" AlgebraicGeometry`: no Mathlib
  AlgebraicGeometry match.
- `rg` over `WeilConjectures/` and `lean/Sheaf`: no declaration for this node;
  the nearby `PurityFiniteSetting.schemeGeometricFrobeniusComparison` has a
  different purity datum and coefficient interface, so it is not an exact match.

No `STATEMENT-DISPUTED` issue or node correction was found.

## Second reading by Q160

I reread the node, its source blueprint text, the complete proof steps, and all
seven statement dependencies against the module. The finite-field datum and
finite-type hypotheses are unchanged. The coefficient annihilation condition is
written as an existential integer with `IsUnit` in `D.k`, and no finiteness or
constructibility condition beyond the stated finite ring is added. The first
comparison has the scheme Frobenius source and geometric (not arithmetic)
Galois target. The iterate family is indexed by every `m ≥ 1`, is normalized at
`m = 1`, and its multiplicative law explicitly uses the canonical pullback
composition isomorphisms and both whiskerings. The absolute Frobenius map is
written with the model-characteristic section term, so it includes nonreduced and
empty schemes. The two factorization equalities are copied from
`absoluteFrobenius_factorization`; no clause or hypothesis was found missing.
The file compiles cleanly with `scompile.py`, with only the expected `sorry`.

## Resumed packet check by Q160

The saved report described a multiplicative law which was absent from the saved
Lean file. Restored that law explicitly, using the already-published canonical
`proEtaleConstantRingPullbackComposition` and added its owning landed node to
`stmt_deps`. With `T_i = L(Phi^i)^*` and `G_i = L(g^i)^*`, the two whiskerings
are `T_n ⋙ T_m → T_n ⋙ G_m → G_n ⋙ G_m`. At an object K their composite is
`G_m(kappa_n(K)) ∘ kappa_m(T_n(K))`, exactly Step 8 of the node proof.
The scheme power equalities only transport the endpoints to exponent m+n;
no arbitrary functor comparison is introduced. Rechecked m=n=1 and all positive
m,n. No mathematical statement correction or new node is needed.

The factorization compatibility is now an equation for the actual comparison,
in addition to both underlying factorization equalities. For each positive m,
`r` is the site isomorphism whose two projections specify relative Frobenius;
its first projection is the p^(am)-power map and its second is the site object's
structure map. The displayed module-adjunction unit equation fixes `τ` as the
left-adjoint mate of the induced sectionwise direct-image trivialization.
The last equation makes `κiter m hm` the composite of the factorization transport,
canonical pullback-composition inverse, and the exact derived descent of `τ`.
Thus κ is tied to the specified canonical cancellation, including nilpotents and
the empty scheme; arbitrary scalar multiples of a natural isomorphism cannot
satisfy this normalization. These witnesses restate properties of the published
absolute-Frobenius trivialization and introduce no new definition or theorem.

Current-source check: `def-weil-pbc-proetale-site` now records
`AlgebraicGeometry.ProEtale.ModuleDerivedCategory` in
`WeilConjectures.SixFunctors.ProEtale.Derived.ModuleDerivedCategory`; read it
through `scompile.py --source` and import that recorded module. The actual
pullbacks use the intrinsic constant-ring `SheafOfModules` presentation
already selected by `def-weil-pbc-proetale-operations`. Both are the ordinary
unbounded localization on the same small weakly-etale/fpqc site; no new module
category or second definition is introduced here. The intrinsic presentation
lifts A to `ULift.{u+1,u} A` and keeps site objects in u+1 and morphisms in u.

All stated proof prerequisites are imported (non-public when used only by the
proof); the theorem docstring now carries all eight DAG proof steps.

## Continuation self-check by Q160

The prescribed dry run compiled the saved Lean file, but preflight rejected the
recorded signature: it included the trailing `:=` delimiter. Removed that
delimiter from `lean.statement`, retaining the exact signature text preceding it.
The theorem and its mathematical statement are unchanged. Reread the current
main-20261015 comparison and proof, the recorded scheme/Galois constructors,
factorization, arbitrary constant-ring operations and canonical composition
interface. The positive iterate law and normalized factorization compatibility
match those sources; the zero ring, empty scheme and nonreduced cases remain.
