## Worker report

The module `Sheaf.Paper.OpenCompactSupportFiniteTor` states node
`sk-lem-sf-open-ctf` in four coefficient clauses. All four theorem proofs are `sorry`.
The three public value wrappers call the existing compact-support value definitions
verbatim, supplying the quasi-compactness instance inferred from the locally Noetherian
target. They neither choose new objects nor replace the canonical construction.
There are no new DAG nodes, dependency-record repairs, or statement corrections.

Hypotheses and clauses, matched against the node:

- The standing field is `D : FiniteFieldDatum.{u}`. Its `D.k` is the prescribed
  algebraic closure of the finite field of cardinality `D.q = D.p ^ D.a`.
  `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` impose the coefficient prime condition.
- `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]` are the finite extension of Q_l.
  `Padic.coefficientExtensionRing l E n` is exactly the specified quotient of the
  valuation ring by the chosen uniformizer power; `hn : 1 ≤ n` includes every positive
  exponent. Natural index `n` at the integral stage denotes exponent `n+1`.
- `U Y : Scheme.{u}` with their `Over (Spec (.of D.k))` structures, and the
  `LocallyOfFiniteType` and `QuasiCompact` instances on each structure morphism,
  state precisely that both schemes are finite type over D.k.
- `j : U ⟶ Y`, `[IsOpenImmersion j]`, and `[j.IsOver (Spec (.of D.k))]` give the
  open immersion over k. `c : Compactification j` supplies an arbitrary specified
  compactification. No density or separatedness of either scheme is imposed.
- `a b : ℤ` and `hab : a ≤ b` state the ordered interval. The section explicitly
  includes the geometric instances and `hab`, including in the finite clause,
  where the ambient compact-support functor alone does not reference those instances.
- The finite input `K : finiteTorConstructibleCategory l E n hn U` is membership in
  Dctf(U,A_{E,n}). `hcoh : proEtaleCohomologicalSupport K.obj ⊆ Set.Icc a b` is
  actual cohomological concentration, and `hTor : HasProEtaleTorAmplitude ... a b`
  is the arbitrary-module Tor test in exactly the same interval. The conclusion
  states all three corresponding properties of the actual
  `sfIntrinsicCompactSupport c A` value. The finite instance is the recorded
  `Padic.finite_coefficientExtensionRing`; it is not an added coefficient assumption.
- The integral input is an object of `sfIntegralConstructibleCategory`, together
  with `hK : finiteTorConstructibleIntegral ... K.obj` for Dctf membership.
  `sfIntegralStandardClass ... true b` and `... false a` assert vanishing above b
  and below a in the actual completed-coefficient module derived category.
  `hTor : ∀ n : ℕ, HasProEtaleTorAmplitude ... ((scalarReductionDerivedExtension ... n).obj
  K.obj) a b` is one unchanged interval at every positive finite reduction.
  The conclusion gives finite-Tor constructibility, both actual cohomological
  bounds, and that same universal reduction-Tor condition for the recorded integral
  compact-support value. It does not identify a cohomology bound with the bound
  of the reductions.
- The rational input is any `K : sfRationalConstructibleCategory l E U`.
  The hypotheses and conclusion use `sfRationalStandardClass ... true b` and
  `... false a`; these allow separate integral witnesses up to rational isomorphism.
  The output wrapper calls `sfRationalCompactSupportValue` on `K.obj`, exactly
  the raw rationalization's integral representative. Its type is already Dbc(Y,E),
  hence Dctf(Y,E) by definition. There is no numerical Tor predicate at this stage.
- `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`, and
  `[IsAlgClosure (Padic l) Ω]` give the fixed algebraically closed coefficient field.
  The common-stage input is any `generalAlgebraicallyClosedConstructibleCategory`
  object. The output is the recorded `sfQbarCompactSupportValue` at `K.stage`,
  on `K.obj.obj`. `sfCommonStageStandardClass ... true b` and `... false a`
  give exactly the two common-stage bounds, separately allowing witnesses at
  other finite stages and common-stage isomorphisms. Its output type gives Dbc,
  hence Dctf, and again no numerical Tor interval is imposed.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`,
  `finiteTorConstructibleCategory`, `finiteTorConstructibleIntegral`, and the
  field-category equality expressed by `finiteTorFieldCoefficientCategory`.
- `Sheaf.Paper.SfConstructibleHeart`: `WeilConjectures.sfIntegralStandardClass`,
  `sfRationalStandardClass`, `sfCommonStageStandardClass`. Their full definitions
  were checked: actual integral homology vanishing and separate isomorphism closures
  at rational and common stages.
- `sk-def-sf-operations` has no lean record and has a closed upstream audit.
  Its six named upstream definitions were read in full, including the inherited
  binders. They provide the small-etale operation realization, not this node's
  pro-etale coefficient stages. The actual relevant pro-etale operations are reused
  through the dependency node's own cited constructions, without restating the
  operations node: `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport` in
  `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`, and
  `WeilConjectures.sfIntegralCompactSupportValue`, `sfRationalCompactSupportValue`,
  `sfQbarCompactSupportValue` reexported by the recorded
  `Sheaf.Paper.QcqsCompactSupportRealization`.
- Other reused notions: `AlgebraicGeometry.Scheme.proEtaleCohomologicalSupport`,
  `HasProEtaleTorAmplitude`, `WeilConjectures.scalarReductionDerivedExtension`,
  `WeilConjectures.PurCompactSupport.coefficientPrimeUnit`,
  `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, and Mathlib's
  quasi-compactness instance for an open immersion into a locally Noetherian scheme.

Edge cases checked before drafting: U empty (all extensions are zero), j identity,
K zero, n=1, a=b, negative a and b, and nonseparated finite-type schemes.
The arbitrary c includes the trivial compactification with proper part identity;
compactifications need not be dense. The general universe u can be enlarged for the
scheme and finite coefficient datum; the common algebraic closure has independent v.
No equality between the small-site object universe u+1 and morphism universe u is imposed.
The rational and common-stage bounds do not demand one representative for both inequalities.

Searches:

- `msearch.py leanfinder`: "Extension by zero preserves constructible complexes and every
  cohomological interval and finite Tor amplitude on the pro etale site at finite integral
  rational and algebraically closed coefficients". Eight hits about shape extension,
  derived-category bounds, or existence of bounded representatives; none states the node.
- `msearch.py loogle`: `Constructible, TorAmplitude, lowerShriek` returned zero with
  unknown identifier Constructible. A second valid quoted search `"Sheaf", "Tor"`
  returned twelve presheaf/Yoneda and Kan-extension declarations, no match.
- `msearch.py grep`: `extensionByZero|constructibleTorAmplitudeIn_rightDerivedLowerShriek|
  finiteTorConstructible` returned zero Mathlib hits.
- `rg` and node-id search in upstream WeilConjectures found
  `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedLowerShriek`,
  in `SixFunctors/Etale/Derived/Stability/OpenImmersion.lean`. Its full signature and
  docstring restrict to small-etale finite coefficient module sheaves. It cannot
  replace the pro-etale integral, raw rational and common-stage clauses.
- `rg` in `lean/Sheaf/Paper` found `OpenExtensionFiniteTor`, which states finite
  termwise extension by zero and independent finite intervals. Its full source was
  read and it is used as a proof dependency, rather than copied as the four-stage
  compact-support assertion. The other matches define the existing coefficient
  categories, compact-support values and standard classes; none states all four clauses.

Initial compile of all recorded proof imports exposed a library duplicate through
`Sheaf.Paper.CompactificationCoherence` / `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomology`:
legacy `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek` duplicates
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification` from the
FiniteCoefficient module. The obsolete proof-only import is omitted; the statement
uses the existing intrinsic compact-support definition and its intended coherence
argument remains explicit in the docstring. No shared or upstream file was changed.

## Second reading by N1

Author's second pass, not an independent review: reread the node and all four signatures.
Checked the finite full-subcategory projection, the actual integral homology bounds,
uniform quantification over all positive reductions, and separate rational/common-stage
witnesses. Corrected the section-variable inclusion so that the finite statement also
retains every base-field, finite-type and open-immersion hypothesis, and all four retain
a ≤ b. The wrappers contain actual calls to the existing definitions and no sorry data.
Independent mathematical review is supplied by the maintainer's delivery review.

Validation: scompile.py compiled the complete module, with all retained proof imports and
explicit geometric section binders, cleanly in both sandbox and library module forms.
Only the four intended named theorem proofs use sorry. The node differs from the base
only in lean; every source line is at most 100 characters.
