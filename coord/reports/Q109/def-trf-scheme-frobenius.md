## Worker report

The module `Sheaf/SixFunctors/SchemeFrobenius.lean` states the complete
`def-trf-scheme-frobenius` notion.  `schemeFrobenius` is the scalar extension
`D.relativeFrobenius X₀`; thus its affine formula is `a ⊗ b ↦ a^q ⊗ b`.
`schemeFrobeniusIterate` is the monoid power in `End`, and the arithmetic and
geometric Galois maps are respectively the inverse and hom of
`D.geometricFrobenius X₀`.  `schemeFrobenius_isFinite_isRadicial` states the
finite and radicial clauses with `sorry`; its proof docstring identifies the
already recorded dependency theorem.  The three derived
pullback definitions use `Scheme.proEtaleConstantRingDerivedPullback` on the
corresponding iterated morphisms, so they are the canonical constant-coefficient
pullbacks on the small pro-etale site.

The global datum and finite-type hypotheses are rendered by
`D : FiniteFieldDatum`, `X₀ : Over (Spec (CommRingCat.of D.k₀))`, and the
instances `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`.  The base change
is exactly `D.geometricFiber X₀`; no separatedness or reducedness is added.
The q-power map clause is `D.relativeFrobenius X₀`; the finiteness and
radiciality clause is the conjunction
`IsFinite (D.schemeFrobenius X₀) ∧ UniversallyInjective (D.schemeFrobenius X₀)`.
The iterate clause is `let Φ : End ... := D.schemeFrobenius X₀; Φ ^ m`.
The arithmetic/geometric Galois clauses are the corresponding `Aut` inverse
and hom.  Pullback clauses are the displayed functors in the module, with
arbitrary `A : Type u` and `[CommRing A]` and `m : ℕ`.

Dependencies used: `WeilConjectures.FiniteFieldDatum` and
`geometricFiber` from `Sheaf.Paper.FiniteFieldFiber`;
`geometricFrobenius` from `Sheaf.AlgebraicGeometry.FrobeniusDetailed`;
`relativeFrobenius` from `Sheaf.AlgebraicGeometry.RelativeFrobeniusGeometricFiber`;
`relativeFrobenius_isFinite_isRadicial` from
`Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial`; and
`Scheme.proEtaleConstantRingDerivedPullback` from
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`. The coefficient-stage
operations are the recorded `finiteDerivedPullback`,
`constructibleIntegralPullback`, `rationalDerivedPullback`, and
`commonStageDerivedPullback` of `Sheaf.Paper.DerivedPullbackTensorHom`. The small
site category is the recorded `Scheme.proEtaleDerivedCategory` of
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` (site objects in u+1, morphisms
in u, module values in u+1). Finite type uses Mathlib
`LocallyOfFiniteType` and `QuasiCompact`; finiteness uses `IsFinite`; radiciality
uses `UniversallyInjective`, whose `tfae_universallyInjective` is Tag 01S4.

Edge cases checked: `m = 0` gives the identity endomorphism by `pow_zero`;
`m = 1` gives the original Frobenius by `pow_one`; the empty model is allowed
(the geometric fibre and its unique endomorphism remain well typed); and no
reducedness or separatedness assumption is present.  The finiteness/radiciality
statement is inherited uniformly, including the zero and empty schemes.

Searches made:

- `msearch.py ... leanfinder "scheme and Galois Frobenius ..."`: only generic
  field Frobenius hits, no scheme construction.
- `msearch.py ... loogle "Scheme Frobenius, geometric Frobenius, derived pullback"`:
  no hits (the query identifier `Scheme` was unknown).
- `msearch.py ... grep "schemeFrobenius|geometricGaloisFrobenius|arithmeticGaloisFrobenius" AlgebraicGeometry`:
  no hits in the searched Mathlib directory.
- `rg` over `WeilConjectures` and project `lean/Sheaf`: upstream has a distinct
  `Scheme.Hom.geometricGaloisFrobenius` for the canonical `AlgebraicClosure`
  construction, while this node fixes an arbitrary closure in `FiniteFieldDatum`
  and requires the scalar-extended relative Frobenius and derived pullbacks;
  therefore no exact existing declaration matches this item.

Current-source self-check, 2026-10-17: the saved packet was compiled and the
required first dry run found the signature record included `noncomputable` and
`:=` although the preflight reader excludes them, declaration docstrings lacked
the exact blueprint marker, and the property theorem had a proof. Those three
faults are repaired. The missing independent second reading is intentionally
left for the separately dispatched reader. No second-reading section is authored
by this worker.

I compared the retained node and every current statement dependency, including
its recorded source declarations, with the current blueprint at
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-prop-sf-rf-shriek-preservation/def-trf-scheme-frobenius.md` (order 2415).
The saved node differs from the shared repository only in `lean`; there is no
statement correction. The extracted child
`lem-trf-scheme-frobenius-finite-radicial` has already landed and has its own
usable module, so no duplicate child packet is required.

The current coefficient dependency specifies more than the constant-ring
specialization in the saved packet. The repaired module therefore also supplies
both scheme and geometric Galois pullbacks at each of its four stages:

- `schemeFrobeniusFiniteDerivedPullback` and
  `geometricGaloisFiniteDerivedPullback` call `finiteDerivedPullback l E n`.
  Here `l` is prime, `hl : l ≠ D.p`, and `E` is a finite extension of `ℚ_[l]`.
  The parameter `n : ℕ` denotes positive level `n+1`, exactly as the recorded
  dependency; the coefficient ring is `finiteCoefficientRing l E (n+1)`.
- The corresponding `IntegralDerivedPullback` definitions call
  `constructibleIntegralPullback l E` on the derived-complete integral
  constructible category. This uses the completed coefficient sheaf and the
  recorded derived inverse-limit construction, rather than a constant ring
  substituted for completed coefficients.
- The corresponding `RationalDerivedPullback` definitions call
  `rationalDerivedPullback l E`, preserving integral objects and extending
  morphisms by the recorded rational scalar formula.
- The corresponding `CommonStageDerivedPullback` definitions call
  `commonStageDerivedPullback l Ω`, for an arbitrary algebraic closure
  `Ω : Type v` of `ℚ_[l]`. These preserve coefficient stages and use the
  specified conjugated representative maps in the pair-category quotient.

In all four cases the map is exactly `D.schemeFrobeniusIterate X₀ m`, or
`((D.geometricFrobenius X₀) ^ m).hom`, respectively. Thus the displayed functors
are pullbacks along the prescribed m-fold maps, with no new choice of operation.
`schemeFrobeniusCoefficientInvertible` constructs the required residue-field
instances from `hl`, using `model_characteristic`, the canonical evaluation
map to each residue field, `CharP.charP_iff_prime_eq_zero`, and Mathlib's
`invertibleOfCoprime` with `Nat.coprime_primes`. Its data are the explicit Bezout
inverse; it introduces no extra invertibility hypothesis or postponed theorem.
It is marked `instance_reducible` as required for class-valued definitions.
Every helper is included in `lean.declarations` and has a source docstring.

Additional edge checks: m=0 also gives the identity for the Galois powers;
m=1 gives the designated map. Positive finite levels are n+1 even at n=0.
The global datum supplies a≥1 and q=p^a, so there is no q=0 case. Characteristic
is evaluated only at actual points, hence the coefficient-instance construction
also applies to the empty fibre. Nonreduced models and nonseparated models are
allowed. No restriction is imposed on the closure Ω's independent universe v.
The affine descriptions and k-linearity are those of
`relativeFrobenius_affine` and `relativeFrobenius_projections`; the Galois affine
formula and semilinearity are those of `galoisMap_affine` and
`galoisMap_projections` in the recorded dependency, not a new construction.

The only postponed theorem is
`WeilConjectures.FiniteFieldDatum.schemeFrobenius_isFinite_isRadicial`, matching
the item's finite/radicial clause and the existing child statement. Its complete
proof is to unfold the alias and apply
`relativeFrobenius_isFinite_isRadicial`. Definitions contain real data and no
`sorry`. No disputed statement, new node, or dependency repair is needed.

## Second reading by Q109

I did not author the module. I read the sandbox node and module together, the
current blueprint `main-20261015/sec-six-functors-basics/`
`sk-prop-sf-rf-shriek-preservation/def-trf-scheme-frobenius.md` (order 2415),
and each of the nine statement-dependency records and its relevant source
signature. The node's statement is unchanged from the shared base: only its
`lean` field differs. There is no statement correction and no new node or
dependency module in this delivery. No repair note exists for this item. The
coefficient dependency's repair note is resolved; its current module supplies
the four coefficient stages rather than the withdrawn pullback-only binding.

The independent object/hypothesis/conclusion checklist is as follows. Names in
the right column are in `WeilConjectures.FiniteFieldDatum`, unless qualified.

| Node object, hypothesis, or clause | Lean rendering and verdict |
| --- | --- |
| Prime p, positive a, q=p^a, finite field k0 with q elements, fixed algebraic closure k and inclusion | `D : FiniteFieldDatum.{u}`; I opened the structure in `Sheaf.Paper.FiniteFieldFiber`: `prime`, `exponent_pos`, `cardinality_eq`, `card_base`, and the field/algebra/closure instances supply exactly these data. Pass. |
| Finite-type k0-scheme X0 | `X₀ : Over (Spec (CommRingCat.of D.k₀))`, `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`. These are precisely the two recorded Mathlib conditions defining finite type; no separatedness, reducedness, smoothness or extra finiteness is assumed. Pass. |
| Geometric fibre X=X0 times k over k0 | `(D.geometricFiber X₀).left`. I opened `geometricFiber`: it is the existing `Over.pullback` along `Spec.map (algebraMap D.k₀ D.k)`, not the upstream fibre at a different chosen closure. Pass. |
| Arithmetic field Frobenius sigma(z)=z^q and geometric gamma=sigma inverse | The dependency's `geometricFrobenius` specializes `galoisMap` to `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`. I opened this field declaration: it is the inverse of `frobeniusAlgEquivOfAlgebraic`; the latter's apply formula is power `Fintype.card D.k₀`, which equals q by `card_base`. No independent field automorphism is chosen. Pass. |
| g_gamma=id times Spec(gamma) | `geometricGaloisFrobenius` is `(D.geometricFrobenius X₀).hom`. The dependency constructs its hom with `galoisMap`, its inverse with gamma inverse, and supplies `galoisMap_projections` and `galoisMap_affine`. In particular this is semilinear over k, with affine formula a tensor b to a tensor gamma(b); it is not silently required to be a k-morphism. Pass. |
| Model q-power map Phi0, linear over k0 | `schemeFrobenius` uses `D.relativeFrobenius X₀`. I opened that definition: its model map is `X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a`, bundled over k0 using the named `model_frobenius_over` theorem. Thus the exponent is p^a=q. Pass. |
| Phi=Phi0 times id_k, a k-morphism, affine formula a tensor b to a^q tensor b | `schemeFrobenius` is an alias of the recorded `relativeFrobenius`, whose data are the image of that model map under `Over.pullback.map`. The dependency's `relativeFrobenius_projections` includes preservation of the k-structure map; `relativeFrobenius_affine` specifies the tensor map with identity on k. These clauses are inherited by definitional unfolding; no arbitrary endomorphism is substituted. Pass. |
| Phi finite and radicial | `schemeFrobenius_isFinite_isRadicial` states exactly `IsFinite (D.schemeFrobenius X₀) ∧ UniversallyInjective (D.schemeFrobenius X₀)`. I opened the child `relativeFrobenius_isFinite_isRadicial`, with identical hypotheses. Mathlib's `tfae_universallyInjective`, Tag 01S4, identifies the second conjunct with the node's residue-field radiciality. Pass. |
| m any nonnegative integer, Phi^m its m-fold iterate | `schemeFrobeniusIterate ... (m : ℕ)` takes the power in `End`. There is no positivity assumption on m. Pass. |
| Arithmetic scheme automorphism g_sigma=id times Spec(sigma) | `arithmeticGaloisFrobenius` is `(D.geometricFrobenius X₀).inv`; the actual inverse in that dependency is `galoisMap` at gamma inverse. Thus the correct coefficient map is used, with no reversal of arithmetic and geometric conventions. Pass. |
| L(Phi^m)* and L(g_gamma^m)* on the small pro-etale site | The constant-ring aliases call `Scheme.proEtaleConstantRingDerivedPullback A` on the designated powers. I opened this operation and `Scheme.proEtaleDerivedCategory`: these use the intrinsic constant-ring `SheafOfModules` localization, not an etale site or a different fixed-scalar category. Pass. |
| Finite coefficient convention for every positive level | `schemeFrobeniusFiniteDerivedPullback` and `geometricGaloisFiniteDerivedPullback` call the recorded `finiteDerivedPullback l E n`; its actual ring is `finiteCoefficientRing l E (n+1)`. `l` is prime, `hl : l ≠ D.p`, and E is any finite extension of the l-adic field. These are exactly the global coefficient assumptions. Pass. |
| Completed integral and rational coefficient conventions | The `IntegralDerivedPullback` aliases call `constructibleIntegralPullback`; the `RationalDerivedPullback` aliases call `rationalDerivedPullback`. I read their types and definitions: the former restricts the canonical completed integral construction, and the latter has the uniquely prescribed integral object and linear morphism action. No constant sheaf is substituted for the completed integral coefficient sheaf. Pass. |
| Algebraically closed coefficient convention | Both `CommonStageDerivedPullback` aliases call `commonStageDerivedPullback l Ω` on the required powers. I read its `existsUnique` specification: stages are retained and representatives act by the rational pullback conjugated with the specified scalar comparisons. Ω has independent universe v. Pass. |
| No extra invertibility hypothesis on X | `schemeFrobeniusCoefficientInvertible` constructs the required pointwise instances from `hl`, characteristic p and `invertibleOfCoprime`. The evaluation of `model_characteristic` in each residue field supplies characteristic p; distinct prime numbers are coprime. These are existing theorem applications and explicit Bezout data, not a new assumed proposition or a choice from an undetermined existence claim. Pass. |

For the geometric clauses I checked Stacks `varieties.tex`, the definitions and
proofs around `lemma-relative-frobenius` (0CCB),
`lemma-relative-frobenius-finite` (0CCD), and
`remark-n-fold-relative-frobenius` (0CCG). The source assumes characteristic p
and local finite type for finiteness, with no separatedness or reducedness.
The a-fold map over k0 identifies its final twist with X0 since the q-power
map of k0 is identity, and scalar extension preserves finite and radicial.
This agrees with the blueprint and the child theorem used here.

Edge cases: m=0 is the identity scheme map by the monoid power convention;
the associated pullback is the canonical identity pullback up to its usual
functorial isomorphism, not an asserted literal equality of chosen functors.
m=1 is the original map. At finite parameter n=0 the coefficient level is 1,
so every allowed positive level is present and the level-zero quotient is not
accidentally used. Empty schemes and zero affine coordinate rings are allowed;
pointwise invertibility over an empty fibre has no points to supply and the
characteristic statement explicitly covers the zero ring. Nonreduced and
nonseparated finite-type models are allowed. All prime characteristics occur,
including 2; the datum has a>=1 so q cannot be 0 or 1. There is no index family
to require nonemptiness. The arbitrary universe u is inherited from the datum
and scheme interfaces. The small site has objects in u+1 and arrows in u,
module values in u+1, with the recorded ULift of coefficients; no equality of
those universes is imposed. The common coefficient closure uses independent v.

Independent searches on 2026-10-17, using different phrases from the worker:

- LeanFinder through `msearch.py`: `base change of q power map from finite
  field scheme with pullback on proetale cohomology`; 8 hits, including
  `PerfectionMap.map` and general etale/base-change infrastructure, no match.
- Loogle through `msearch.py`: `FiniteField.frobeniusAlgEquivOfAlgebraic`;
  7 hits for the field automorphism and its power/apply lemmas, not the
  combined scheme/coefficient-stage construction.
- LeanSearch through `msearch.py`: `scalar extended Frobenius endomorphism
  and proetale derived inverse image`; 8 ring, linear, Witt-vector and
  purely inseparable Frobenius hits, no scheme-level match.
- `rg` for `frobenius|Frobenius` in Mathlib's AlgebraicGeometry directory
  found no matching scheme declaration. I separately read the actual
  Mathlib `IsFinite`, `LocallyOfFiniteType`, `QuasiCompact`, and
  `UniversallyInjective` definitions used above.
- `rg` for `geometricGaloisFrobenius|relativeFrobenius|schemeFrobenius|galoisMap`
  over all upstream `WeilConjectures` and project `lean/Sheaf`, and inspection
  of upstream `AlgebraicGeometry/GeometricFrobenius.lean` and
  `SixFunctors/ProEtale/TraceFormula/Frobenius.lean`: the former's
  `Scheme.Hom.geometricGaloisFrobenius` uses the specifically constructed
  `AlgebraicClosure k0` fibre. The latter's `ProEtale.relativeFrobenius` is
  a lift into the Frobenius twist of a morphism X to Y, not the scalar
  extension of a model's q-power map on the chosen closure. Neither states
  this complete node. The usable project constructions are precisely the
  dependency declarations reused here; their data are not reconstructed.

No mathematical mismatch was found, so I retained the Lean and node record
unchanged and appended only this independent review. The extra arithmetic
constant-ring pullback is a canonical specialization along the already
introduced arithmetic map, not an additional assertion. Every definition has
real data; the only postponed theorem is the named finite/radicial assertion,
with the direct unfold-and-apply proof plan and source/blueprint docstring.
All declarations have source/blueprint docstrings, all delivered Lean lines
are at most 100 characters, and `autoImplicit false` plus explicit `universe u v`
leaves no unbound variable. There are no new nodes, dependency repairs or
statement-change citer verdicts to audit.

Validation: `scompile.py Q109 def-trf-scheme-frobenius` on the delivered
`SchemeFrobenius.lean` compiled both sandbox and library-path versions cleanly
(3.7 and 4.2 seconds), with no errors or warnings. The module is the only Lean
file in this delivery. The node's primary `lean.statement` records its exact
signature; server preflight and delivery validation are recorded below.

The required `deliver2.py Q109 def-trf-scheme-frobenius --no-push` completed
with exit code 0: `OK (dry run): commit 2cd225c73f passes the preflight and
compiles; nothing pushed`. The staged packet contained exactly this report,
the item's node, and its single module. Final delivery uses the same reviewed
Lean and node; only this validation note was appended after the dry run.
