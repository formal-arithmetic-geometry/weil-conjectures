## Worker report

The module `Sheaf.TraceFormula.FrobeniusProperPowerExchange` states the reviewed
node without changing its statement or its stage-1 split. The previous worker's
reported live-wins refusal concerned re-splitting; this is exclusively its stage-2
statement. There are no new nodes or dependency repairs.

Every declaration is in `WeilConjectures.FrobeniusProperPower`. All helper data
are actual constructions; only `geometry` and `pasting` have proof `sorry`.
Both have the corresponding part of this node's full natural-language proof in
their docstrings. The helpers merely name this node's maps and the two paths in
its equations; they introduce no replacement site, coefficient category, or
independent comparison isomorphism.

Hypotheses and clauses:

- The global datum is `D : FiniteFieldDatum.{u}`. Its fields explicitly include
  prime p, positive a, q = p^a, cardinality q for k0, and a fixed algebraic closure k.
- `W₀ : Over (Spec (.of D.k₀))` and `[IsProper W₀.hom]` render the model and
  proper structure morphism. `LocallyOfFiniteType` and `QuasiCompact`, hence finite
  type, follow from this properness instance. No separate stronger hypothesis is
  added. `D.geometricFiber W₀` is the recorded pullback over the base embedding;
  `.left` is W and `.hom` is the projection p to the actual scheme Spec k.
- `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p`, `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`, `n : ℕ`, and `_hn : 1 ≤ n`
  are exactly the coefficient assumptions. The ring throughout the theorem is
  `Padic.coefficientExtensionRing l E n`, the existing quotient by the nth power
  of the fixed uniformizer in the existing valuation ring. No arbitrary coefficient
  sheaf identification is an input.
- `middle D W₀ r` is the rth endomorphism power of the recorded
  `D.geometricGaloisFrobenius W₀`, namely id × Spec(gamma).
  `base D r` is the rth endomorphism power of the existing
  `(frobeniusPointIso D).hom`, exactly Spec(gamma) with gamma inverse q-power.
  Mathlib's `End` multiplication reverses category composition, which is accounted
  for by `pow_succ` in `powerStep`.
- `geometry r hr` asserts `IsPullback (middle r) p p (base r)` and `IsIso` of
  both horizontal arrows for every positive r. The commutativity is the inherited
  `IsPullback.toCommSq`. `square r hr` is the recorded `ChosenCartesianSquare`:
  its isomorphism is `IsPullback.isoPullback` and its two projection equations
  specify its hom as precisely `(b^r,p)`, by pullback uniqueness. Its inverse is
  described explicitly in the proof docstring. The definition never chooses an
  arbitrary isomorphism of schemes.
- `B`, `Q`, `L`, and `R` are the actual ordinary constant-ring derived pullbacks
  and ordinary right-derived direct image, on the existing small pro-etale sites.
  `R` uses `proEtaleRingDerivedDirectImage` with the same constant-section scalar
  action and coefficient comparison as `L`; `proEtaleRingDerivedAdjunction` is
  their specified adjunction. No boundedness, constructibility, completion,
  etale-origin restriction, or k-linearity is assumed.
- `powerStep` uses the existing `proEtaleConstantRingPullbackComposition` in its
  iterated-to-composite direction, the inverse of the node's composite-to-iterated
  comparison. Its only further maps are equality transports for `pow_one` and
  `pow_succ`. `t` and `d` are its base and middle specializations. Lean writes
  Q_m followed by Q_1 as `Q m ⋙ Q 1`, corresponding to the node's Q_1 Q_m.
- `theta` is exactly `c_(p,h^r)^(-1)`, commutativity transport, then `c_(b^r,p)`.
  The compositors are the published general comparison specialized to the actual
  constant-section identifications; their normalization is preserved, rather
  than replaced by arbitrary isomorphisms. The square's chosen identification
  supplies exactly its specified commuting equality.
- `exchange` is `mateEquiv` of that `theta` using the specified derived adjunction
  at both vertical sides. Thus its component inserts the unit, applies theta under
  R, then contracts the counit. This is the ambient definition's recipe, also the
  finite direct-image Frobenius recipe in the recorded exchange dependency.
- `squareLeft` names theta_(m+1) L(t_m), and `squareRight` names
  (d_m L)(B_1 theta_m)(theta_1 Q_m). Explicit functor associators merely identify
  the parentheses. The first conjunct of `pasting` is their equality.
- `mateLeft` names u_(m+1)(t_m R), and `mateRight` names
  R(d_m)(u_1 B_m) Q_1(u_m). Their equality is the second conjunct.
  These are natural transformations on the full ambient derived categories.
  Evaluating their equality at any K gives exactly the displayed component
  equation, including all K and every ambient derived morphism. This includes
  the statement's naturality clause without a separate assumption on K.
- `m : ℕ` and `hm : 1 ≤ m` retain the exact positive-iterate range. All remaining
  positivity proofs are the elementary proofs that 1 and m+1 are positive.

Dependency interfaces read and used (including public reexports):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `FiniteFieldDatum.geometricFiber`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the reexported
  `Padic.coefficientExtensionRing` and `Padic.finite_coefficientExtensionRing`.
- `Sheaf.SixFunctors.SchemeFrobenius`:
  `FiniteFieldDatum.geometricGaloisFrobenius` and `geometricGaloisDerivedPullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback` and
  `proEtaleConstantRingComparison`; its public operations/adjunction interface
  supplies `proEtaleRingDerivedDirectImage` and `proEtaleRingDerivedAdjunction`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `WeilConjectures.integralTowerGeneralPullbackComposition` reexports the full
  `proEtaleCanonicalPullbackComposition`; its public constant specialization is
  `proEtaleConstantRingPullbackComposition`. The latter explicitly retains the
  canonical general comparison and the composite constant-coefficient transport.
- `Sheaf.Paper.CondensedAmbientExchange` publicly retains the general ring-sheaf
  `proEtaleAmbientRingedExchange` and its normalized pullback comparison.
  This item is in that ordinary ring-sheaf presentation, not its additional
  condensed-module-object specialization. `theta` and `exchange` specialize
  that exact compositor and mate recipe to the Frobenius power square.
- `Sheaf.Paper.FrobeniusGeometricExchange` reexports
  `FrobeniusExchange.finiteDirect`, `frobeniusDirectFinite`, and
  `finiteTensorExchange`, whose finite direct recipe is the same ambient mate.
  The higher-stage `frobeniusCommonStage` is not used to replace finite coefficients.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`.
- The additional already-landed statement dependency
  `def-weil-frobenius-point-transport`, module
  `Sheaf.SixFunctors.FrobeniusPointTransport`, supplies the existing
  `WeilConjectures.frobeniusPointIso`. This avoids defining Spec(gamma) again.
- Every recorded proof-dependency module is imported privately, including the
  canonical constant-coefficient composition and factorized pullback pasting,
  the Frobenius-square geometry, and the Mathlib/upstream mate pasting/whiskering
  interfaces. The proof docstring names their exact uses in the five node steps.

Source and edge checks: read the full local Stacks
`sites-cohomology.tex`, `remark-compose-base-change-horizontal` (0E47), including
its explicit order h' pullback, inner exchange, outer exchange, g' pullback then
composite comparison. This agrees with Q_1(u_m), then u_1 at B_m K, then R(d_m).
Checked m=1, n=1, the empty W, p the identity, and K=0. Powers are scheme
endomorphisms with scheme inverses, so semilinear/non-k-linear horizontal arrows
remain allowed. The theorem excludes m=0, n=0, and r=0 exactly where the node
requires positivity. Equal site/field/coefficient size parameter u is the existing
library convention: the sheaf coefficient rings live in CommRingCat.{u+1} by
ULift, and the small site has object size u+1 and morphism size u. No site
universe equality or extra smallness hypothesis is introduced.

Searches for an existing exact statement:

- `msearch.py leanfinder`: "Proper direct image exchange for powers of geometric
  Frobenius composes with canonical derived pullback comparisons" returned eight
  hits concerning scheme/module pullback compositors, including
  `Scheme.Modules.conjugateEquiv_pullbackComp_inv`, not this Frobenius power law.
- `msearch.py leansearch`: "Proper base change exchange for iterates of Frobenius
  using adjunction mates" returned eight hits including
  `CategoryTheory.frobeniusMorphism_mate` (monoidal closed categories) and
  `LinearMap.baseChange_pow`; none says this statement.
- `msearch.py loogle`: the guessed combination `CategoryTheory.mateEquiv,
  AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition` had zero hits
  (project name unknown to Loogle); querying `CategoryTheory.mateEquiv_vcomp`
  returned the general mate-pasting lemma, used as a proof dependency.
- `msearch.py grep`: `frobenius.*power.*exchange|mateEquiv_vcomp` under
  Mathlib/CategoryTheory found the general mate-pasting lemmas, not this statement.
- `rg` over Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for
  `FrobeniusProperPower|frobenius_proper_power|frobenius.*power.*exchange`, and
  broader power/exchange names found no exact declaration. The existing
  compact-support transport-composition theorem is a different consumer and
  includes point transport and open extension. The exact node-id grep in
  `lean/WeilConjectures` found no declaration.

No statement fault or STATEMENT-DISPUTED issue was found. No stage-1 field is
changed. The node copy changes only `lean` and adds the landed point-isomorphism
owner to `stmt_deps` as authorized by brief-stage2 section 5.

## Second reading by NJ

No independent worker reading is claimed. This worker was instructed not to start
other agents; since 2026-10-17 workers deliver directly for the maintainer's
independent review. The worker rechecked every clause against the final file.
