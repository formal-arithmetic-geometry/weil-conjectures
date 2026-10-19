## Worker report

Repair of returned immutable head `0d074ea32f99`. The saved packet was inspected first and
its prescribed initial dry run passed (`6609e7460c`), but the required mathematical self-check
confirmed that it still contained the returned arbitrary-map defect. The old trace formulas
were retained, while their inputs were replaced as described below. The node copy is based on
the current shared DAG, retaining the current five-step proof and all non-Lean fields.

`Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` states the source scalar-trace equality, with
one postponed theorem, `WeilConjectures.PurAdicScalarTrace.scalar_trace_coherence`. It uses the
canonical ambient completed proper/open presentation. `sfQcqsCompactSupportRealization`
identifies this presentation, naturally and with the recorded reduction projections, with
`sfCompactSupportFiniteIntegralFunctor`; the integral categories are full subcategories, so
an equality of these ambient arrows is precisely the equality in the source's integral
constructible categories. This is not a replacement of the source category by generic data.

Hypothesis and clause correspondence:

- Global finite-field datum: `D : FiniteFieldDatum.{u}`; coefficient prime and characteristic
  restriction: `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`.
- Finite extensions: `E F : Type u` with `Field`, `Algebra (Padic l)`, `FiniteDimensional`, and
  `ι : E →ₐ[Padic l] F`. A field algebra hom is injective, so this is the specified inclusion.
  The bottom field is fixed to `ULift.{u} (Padic l)`, with `baseInclusion` the algebra map
  composed with `ULift.algEquiv`. The lift is the actual Q_l, not a further finite extension;
  it permits arbitrary scheme universe u. The direct and composite maps from it agree by
  the algebra-hom scalar equation. No independent iota_02 or tower-equality assumption remains.
- Separated finite-type k-schemes: `Xbase`, `Ybase` are their `Over (Spec (.of D.k))`
  structures; `Xft`, `Xqc`, `Xs`, `Yft`, `Yqc`, `Ys` express locally finite type,
  quasi-compactness and separatedness of the two structure maps. All are retained by
  `include`, rather than silently dropped by Lean's section-variable generalization.
- Morphism: `f : X ⟶ Y`, `fbase : f.IsOver (Spec (.of D.k))`, `fs : IsSeparated f`,
  `fft : LocallyOfFiniteType f`, `fqc : QuasiCompact f`; dimension and smoothness are
  `d : ℕ` and `fsm : SmoothOfRelativeDimension d f`. Their binders are retained too.
  A compactification `c : Compactification f` presents the canonical compact-support
  construction for an arbitrary compactification, as allowed by its recorded independence.
- The coefficient rings are `completedIntegralCoefficientSheafUnrestricted` and their
  commutative versions. These are the actual inverse limits of the finite coefficient
  sheaves. Coefficient inclusions are the residue-normalized `completedCoefficientMap`.
- `P_L` is `PurCompactSupport.image (PurCompactSupport.completed l L) c`, the published
  completed proper direct image after open extension, with the canonical coefficient
  pullback identifications. Its identification with the recorded integral functor is
  the proof dependency `sfQcqsCompactSupportRealization` explained above.
- `C_{F/E,W}` is `completedDerivedScalarExtension l E F ι W`, the published ordinary
  left-derived change of rings along the actual completed sheaf map. Its universal
  representative counit is `completedScalarCounit`. The recorded finite-free comparison
  `completedScalarComparison` identifies this with `integralScalarExtensionOfUniverses`
  on complete inputs. It is not a generic functor field.
- `unit l L W` places `SheafOfModules.unit` of the actual completed coefficient ring in
  degree zero. `twistedUnit` applies `(integralSheafTwist l L W d).mapDerivedCategory`
  and then the derived shift `[2*d]`. `overTwistedUnit` constructs the required inverse
  of l in every residue field from `hl` using `coefficientPrimeUnit` and the actual
  structure map. Invertibility is therefore not a further hypothesis.
- The three `CoefficientComparison` arguments give presentations of the named canonical
  comparisons, not additional arbitrary maps. Their `compact.hom` is required to equal
  `(PurCompactSupport.comparison (PurCompactSupport.completedChange ...) c).app T_L`.
  Both compact-support functors and both scalar functors are fixed in this equality.
  The source already calls this canonical map an isomorphism on these twisted units.
- The coefficient-unit identification is `UnitMultiplication`. Its `chain` is normalized
  at every pro-etale object and every pure tensor in degree zero by the precise formula
  `b tensor x ↦ b * completedCoefficientMap(x)`. The complexes have no other nonzero
  terms. Its derived `iso.hom` is required to be exactly `completedScalarCounit` followed
  by `DerivedCategory.Q.map chain.hom`. Thus these choices determine the canonical unit
  multiplication on every arrow, rather than merely asserting some Nonempty isomorphism.
  No coherence equation, trace equation, or extra mathematical restriction is assumed.
- `theta_L` and `a_{F/E,1_E}` are both constructed by `twistComparison`. It applies the
  canonical ordinary beta to `intrinsicIntegralCoefficientTwist D l hl E W 0`, then
  applies the target exact twist functor to the normalized unit multiplication, then
  shifts by `[2*d]`, using the canonical scalar shift comparison. They are not fields.
- `t₀` has exactly source `P_Q_l(T_Q_l)` and target `unit_Q_l,Y`. It is arbitrary: no
  nonzero, integration-normalization or compatibility hypothesis is imposed.
- `trace` is the explicit composite `P_L.map theta.inv ≫ c.inv ≫ C_Y.map t₀ ≫ unit.hom`.
  It supplies both t_E and t_F from that same base trace.
- The conclusion is `aFE.compact.hom ≫ P_F.map (twistComparison ...).hom ≫ trace_F =
  C_FE,Y.map trace_E ≫ aFE.unitY.iso.hom`. Lean composes left to right. This is exactly
  the displayed source identity with the suppressed target coefficient-unit map restored.

Dependency interfaces actually used are the `PurCompactSupport.completed`, `completedChange`,
`image`, `comparison`, `coefficientPrimeUnit` and canonical scalar-shift interface of
`Sheaf.Paper.IntegralCompactSupportCoefficientComparison`; the completed coefficient rings,
`completedCoefficientMap`, ordinary scalar complex, universal counit, derived extension and
ordinary-to-completed comparison of `Sheaf.Paper.FiniteFreeCompletedScalarComparison`;
`integralSheafTwist` and the literal signed-zero unit from the coefficient-twist modules;
`intrinsicIntegralCoefficientTwist` from `Sheaf.Paper.IntrinsicCoefficientTwists`;
`Scheme.Hom.residueFieldAlgebraMap` from `WeilConjectures.ZetaSeries`;
`integral_twist_derived_scalar` through the named projections in the dependency repair;
and the normalized recorded compact-support realization. Those publicly import the original
coefficient extension, completed integral coefficient, derived-change-of-rings, and purity
convention interfaces. The old ten standalone imports were removed; the public
construction imports, the required Mathlib ULift field instance and existing
`WeilConjectures.ZetaSeries` residue-field map imports, and the compact-support realization
proof import remain.

Edge cases: d=0 is permitted and uses the canonical shift by zero; the formulas also cover the
empty scheme and zero base trace. The equal-field and identity-inclusion cases use the same
normalized tensor maps, not an extra nonidentity assumption. The universal lift of Q_l avoids
restricting the scheme universe. Ramified extensions use the same completed coefficient map
and finite-free scalar comparison; no unramified or properness hypothesis was introduced.
The returned sign counterexample is excluded by the explicit multiplication formula and
universal counit equation, and altering compact comparison violates its defining equation.

Searches: fresh `msearch.py leanfinder "Derived compact support trace scalar extension
coherence"` returned test-function scalar maps and `LinearMap.trace_baseChange`, not a
six-functor trace statement. `msearch.py loogle "CategoryTheory.Functor.commShiftIso"`
reported no match (identifier unavailable to the remote index); the actual shift declaration
was read in local Mathlib `CategoryTheory/Shift/CommShift.lean`. `msearch.py grep
"extend.*[Uu]nit|[Uu]nit.*extend" CategoryTheory` found five unrelated bicategory/limit hits.
Project/upstream `rg` for the item id and scalar_trace_coherence found no existing declaration.
The saved and current node searches were retained and read. Additional local searches for
coefficient-unit and beta interfaces found the existing characterized theorem, the published
scalar complex/counit, the actual compact-support mate and realization, and Mathlib's ULift
field/module instances. None states the required trace equality.

No source statement correction is needed. The arbitrary-data and arbitrary-E0 defects were
in the returned Lean, not in the mathematical node. All definitions have actual data; the
only new sorry is the requested theorem statement.

## Dependency modules

`lem-weil-integral-twist-derived-scalar`: added
`Sheaf.Paper.IntegralTwistDerivedScalarCanonical`. The old module is publicly imported
unchanged, preserving its full theorem and all representative/completion characterizations.
The old existential interface had no named beta to use in theta and a. The new definitions
`integralTwistOrdinaryBeta` and `integralTwistCompletedBeta` project its first and second
witnesses. The former is determined on every good K-flat representative by the theorem's
pure-tensor and universal-counit equations. The latter is determined by conjugation with
its specified completion comparison. This is a section 1(B) named-interface repair, not
a second construction or an isomorphism chosen from an uncharacterized existence theorem.
No further postponed theorem is added. Only this dependency's lean record is changed.

## Second reading by N9

This is the dispatcher's requested worker self-check, not an independent-agent review.
I re-read the source node, its five proof steps, the two delivered files and the return.

H3: the old record let every P, C, T, U, theta, c, a and unit map vary independently of
all geometric and coefficient inputs. In the repair P and C are literal published functors,
U is the completed ring unit, T is its actual derived twist and shift, and theta/a are
composites of the dependency's fully characterized beta, coefficient multiplication and
canonical shift. The only presentation fields remaining for c and unit maps carry equations
fixing them to their actual mate and local multiplication/counit constructions. Replacing
v by -v fails the pure-tensor formula, including in the identity-field case. The base
coefficient is now literally a size lift of Q_l, rather than an arbitrary finite extension.

I checked the datum and prime inequality against D/l/hl; the extension clause against the
Field/Algebra/FiniteDimensional binders and injective algebra hom; both scheme clauses
against their three structure-map properties; the k-morphism clause against fbase and its
three morphism properties; and smooth pure dimension against d/fsm. Named section
hypotheses are explicitly included to prevent accidental omission. Residue invertibility
is constructed from hl rather than assumed. The chosen compactification presents the same
canonical functor for every compactification.

I checked T_0/T_E/T_F by unfolding unit, overTwistedUnit and twistedUnit: the coefficient
ring sheaf is the completed sheaf, the degree is zero before the specified twist and the
shift is positive 2d. The theta/a composite has source C(T_E) and target T_F, in the order
scalar/shift comparison, shifted beta, shifted target twist of the unit multiplication.
The beta projections still use the full theorem's K-flat characterization. I checked both
trace definitions have source P_L(T_L) and target unit_L,Y, with exactly the four factors
of node proof Step 1. The final equality starts at C_FE,Y(P_E(T_E)) and ends at unit_F,Y;
its rightmost target identification is explicitly the normalized unit multiplication.
No trace normalization or nonzero condition has entered any helper or theorem binder.

H4/H9: the free fields and old unused direct imports were removed. The repaired statement
now directly names the actual completed scalar, exact integral twist and canonical
compact-support comparison declarations, and names beta through the dependency module.
The compact-support-realization import is a proof dependency identifying the ambient
construction with the recorded integral functor, as the theorem docstring explains.
H11: this reading records each hypothesis, each object/map and each composite, rather
than the previous three generic sentences. The d=0, identity extension and zero trace
cases remain within the signature. The mathematical node text is unchanged.

## Validation

The saved packet's initial dry run passed, but was not treated as mathematical approval.
The named-beta dependency module compiled cleanly through scompile.py. An intervening
server overlay publication briefly failed in the upstream split module
`IntegralCompactSupportCoefficientData` (missing IsIso instances); source inspection
through `scompile.py --source` and retry resolved it after the server source was repaired.
The subsequent file compile reached the repaired trace module and reported only the
missing existing residue-map import, which was added. Final scompile.py run succeeded for both delivered files, each in its own sandbox and
library form: canonical beta 13.9/14.6 seconds, trace coherence 33.6/33.7 seconds. Neither
delivered file emitted a warning. The wrapper also printed two inherited line-width
warnings in the maintainer-owned `IntegralCompactSupportCoefficientData`; that file is
not part of this delivery and was not edited. The first repaired dry run found a metadata-only issue: the declaration-list extractor
read the docstring phrase "structure obtained" as a declaration. That spurious name was
removed from lean.declarations; no Lean signature or definition changed.
