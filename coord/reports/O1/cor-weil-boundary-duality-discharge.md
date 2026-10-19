## Worker report

The module `Sheaf.SixFunctors.BoundaryDualityDischarge` states
`AlgebraicGeometry.ProEtale.boundary_duality_input`.  Its conclusion is the recorded
`AlgebraicGeometry.ProEtale.BoundaryDualityInput` predicate, which contains both clauses of
the node: preservation of finite-Tor constructibility under the duality operations and the
canonical evaluation-defined boundary exchange (including its evaluation/double-dual
compatibility).

The node's hypotheses are rendered as follows.  The global finite-field datum is
`D : WeilConjectures.FiniteFieldDatum.{u}`; its `D.k` is the fixed algebraic closure of the
finite field.  The coefficient prime is `l : ℕ` with `[Fact l.Prime]` and `hl : l ≠ D.p`.
The finite extension is `E : Type u` with `[Field E] [Algebra (Padic l) E]`
and `[FiniteDimensional (Padic l) E]`.  The finite stage is `n : ℕ`; the dependency's
canonical convention uses the positive level `n + 1` inside
`BoundaryDualityInput`.  The separated finite-type scheme is given by
`Y : Scheme.{u}`, its structure morphism
`aY : Y ⟶ Spec (CommRingCat.of D.k)`, and the instance hypotheses
`[IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]`.  The conclusion
`BoundaryDualityInput D l hl E n Y aY` is exactly the boundary-duality input for every
locally closed piece and every closed immersion between those pieces; its `Assertions.exchange_isIso`
field is the isomorphism assertion for the evaluation-defined map `β_L`.

The statement dependency used is the existing declaration
`AlgebraicGeometry.ProEtale.BoundaryDualityInput` in module
`Sheaf.SixFunctors.BoundaryDualityInput`.  Its signature was read in full.  In particular,
its `Data` witness fixes the site comparison, exceptional inverse image, duality, evaluation,
tensor-exceptional comparison, and the canonical exchange map rather than introducing an
arbitrary map.

Edge cases checked before writing the statement include `n = 0` (the dependency's `n + 1`
coefficient level is still positive), `Y = Spec k`, the identity closed immersion, the empty
locally closed piece, and the zero derived object.  The `BoundaryDualityInput` definition
covers these cases without adding hypotheses; in particular the theorem does not identify
ordinary pullback with exceptional pullback.

Searches for an existing declaration were made with:

- `msearch.py ... leanfinder "finite-stage boundary duality input holds for every separated finite-type scheme canonical evaluation-defined boundary map is an isomorphism"`: eight unrelated affine-transition-limit hits; no boundary-duality declaration.
- `msearch.py ... loogle "BoundaryDualityInput, nonempty_iso_leftDerivedUpperStar_verdierDual"`: zero hits (`BoundaryDualityInput` is not a Mathlib identifier).
- `msearch.py ... grep "BoundaryDualityInput|boundary[_A-Za-z]*duality|leftDerivedUpperStar_verdierDual" Mathlib`: no Mathlib hits.
- `rg` in `WeilConjectures/`: found `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_verdierDual`, but its statement is only an existence of an etale isomorphism for one closed immersion and does not state the `BoundaryDualityInput` predicate or its canonical pro-etale data.
- `rg` in `lean/Sheaf`: found only the dependency module `Sheaf.SixFunctors.BoundaryDualityInput`; no discharge theorem.

No new definition node or dependency repair was needed.  No `STATEMENT-DISPUTED` flag applies.

## Second reading by N1

I reread the node, the complete dependency declaration, and the generated signature.  Every
node hypothesis appears in the Lean binders, and the conclusion is exactly the dependency's
finite-stage `BoundaryDualityInput` predicate.  The positive-stage convention is explicit in
the dependency definition (`n + 1`), so no stage is omitted.  The dependent predicate's
canonical `exchange_isIso` clause renders the stated evaluation-defined `β_L` assertion.
No mismatch was found.

## Proof-plan imports

The theorem docstring carries the node's fourteen proof steps verbatim, with line wrapping.
The module imports the compatible recorded Lean modules of the proof dependencies, without
`public`, plus the Mathlib geometry modules used by its Mathlib leaves. The following proof prerequisites
have no recorded Lean declaration on the supplied base, so no import can yet be added:
- `lem-weil-boundary-alpha-normalization`.
- `lem-weil-finite-duality-site-comparison`.
- `lem-weil-boundary-proetale-q-compatibility`.

The master and main-20261015 blueprint statements and proofs were compared; they agree for
this corollary. The maintenance note is resolved stage 1 (the fourteen-step proof split),
and imposes no outstanding stage-2 interface repair.

Import compatibility findings for the maintainer: adding every recorded proof import failed on
two retired/duplicate upstream interfaces. I retained the side required by the actual statement
and omitted the incompatible proof-only imports:

- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula` imports `Sheaf.Paper.ExchangeProjection`,
  then the old `LowerShriek.OpenImmersion.BaseChange`; its overlay compile fails because
  `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv` is already declared by the finite-coefficient
  `UpperLowerStar.Iso` module. This proof-only import is omitted.
- `Sheaf.Paper.BoundaryDualizingComposition`, `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`,
  `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`,
  `Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass`,
  `Sheaf.Paper.BoundaryProEtaleProjectionComparison`, and
  `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate` each transitively import the
  finite-coefficient `Derived.Comparison`. Together with the statement dependency they fail
  because `AlgebraicGeometry.ProEtale.derivedComparisonAdjunctionPlus` is already declared by
  `WeilConjectures.SixFunctors.ProEtale.Derived.Comparison`. Those proof-only imports are omitted;
  the owning recorded statement dependency is retained unchanged.

After resolving these duplicate imports, both sandbox and library-form compiles pass cleanly.
The full proof plan still names all of these dependencies for stage 3. No live source or
dependency node was edited.

Additional required search: `msearch.py ... leansearch "Canonical evaluation boundary exchange
for finite coefficient Verdier duality under a closed immersion is an isomorphism"` returned eight
closed/open immersion and complex-truncation results, none about Verdier boundary exchange.
The exact new declaration name has no hit in Mathlib, upstream, or the existing side library.
The upstream blueprint-id search found the existence-only etale theorem already discussed.
