## Worker report

`Sheaf/SixFunctors/IntegralDualizing.lean` states `WeilConjectures.prop_coef_integral_dualizing`. This repair retains the delivered integral statement and replaces the faulty finite-transition interface identified in the return. The node’s natural-language statement and proof are unchanged. The returned-delivery repair and second reading below describe the canonical maps in full.

Hypotheses, individually: `D : FiniteFieldDatum.{u}` supplies the fixed finite field, its algebraic closure, and characteristic; `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` supplies the other prime. `E : Type u`, `Field E`, `Algebra (Padic l) E`, and `FiniteDimensional (Padic l) E` supply exactly the finite coefficient extension. Its integers, chosen uniformizer, and quotients are the dependency's `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionRing`; no new coefficient ring is constructed. `X : Scheme.{u}` and `X.Over (Spec (.of D.k))` supply the scheme and its structure morphism. `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on that morphism express separated finite type. `d : ℕ` supplies nonnegativity and `hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)` is the dimension bound. There is no smoothness, properness, nonemptiness, extra Tor hypothesis on K, or ambient exceptional-adjoint assumption.

Clauses, individually:

- Ordinary completed coefficients: all integral objects lie in `DerivedCategory (scalarReductionSource l E X)`, the published category of ordinary sheaves of modules over `completedIntegralCoefficientSheafUnrestricted`. The small pro-etale site retains object universe `u+1` and morphism universe `u`.
- The finite dualizing objects are `integralDualizingFiniteTerm`: the recorded `ProEtale.sfFiniteExceptional` at the structure map, applied to the actual regular finite coefficient module in degree zero. The theorem identifies `T.M n` with this object for every n. Natural index n means the positive quotient exponent n+1; zero exponent is not introduced.
- `T : NormalizedDVRTower l E X D hl` retains actual finite coefficient restrictions, all comparable-pair semilinear maps, their identity and composition equations, the derived object of strict towers, the evaluation isomorphisms, and the equations identifying the evaluated transitions with those finite maps. Its normalization is the derived scalar-extension universal property; it is not an uncategorified family.
- `Nonempty (ω.obj ≅ (integralDualizingLimit l E X).obj T.tower)` identifies omega with total right derived inverse limit of that strict tower. `integralDualizingLimit` extracts the functor together with its right-derived universal property from `ringedStrictTowerHomotopyLimitOfUniverses`, rather than choosing an object from an unconstrained existence statement.
- `IntegralDualizingLimitPresentation ... T ω.obj` retains a Roos triangle with projection p and connecting map delta on the actual derived evaluations. Its reduction comparison is `normalizedDVRCounitComparison`, the adjoint of each limit projection under the normalized integral tensor/restriction adjunction. Every such map is invertible. The displayed equation for all m,n,h identifies T's finite transitions with the canonical quotient-induced reduction transitions; equal indices and arbitrary composites are included. Thus the isomorphisms in the first display are the canonical counit reductions, not arbitrary isomorphisms between unrelated objects.
- `ω : sfIntegralConstructibleCategory l E X` supplies both derived completeness and membership in `D^b_c(X,R)`: its property is precisely `sfIntegralConstructible`, namely canonical augmented reduction completeness and constructible finite reductions with one common bounded cohomological interval.
- `HasProEtaleTorAmplitude ... (-(2 * (d : ℤ))) 0` on every intrinsic finite reduction gives exactly the uniform interval [-2d,0]. This replaces the saved weaker existential finite-Tor condition and avoids the saved fixed-scalar universe mismatch.
- `integralDualizingGlobalHom l E X ω.obj` is the functor K ↦ RΓ(X,RHom(K,omega)). Its internal Hom is literally the recorded `derivedInternalHomOfUniverses`. The sections functor is evaluation at the final object with the scalar action supplied by `integralConstantToCompletionOfUniverses`; it is then right derived using the published K-injective infrastructure. Its target is the derived category of modules over R, retaining the R action rather than merely underlying abelian groups.
- `integralDualizingCompactSections` is K ↦ Γ(s,Ra_!K), including its action on morphisms. It uses `exists_compactSupportReductionTower` with its natural evaluation comparisons and specified quotient/compact-support transitions, followed by the same total right derived inverse-limit construction and point sections. On the algebraically closed coefficient point, sections are exact, so the displayed derived sections implement the coefficient-point Gamma of the node. A mere choice of Roos vertices separately for each K would not give a functor; this is why the saved value-only helper was replaced by the published coherent functor interface. A compactification is supplied by `hasCompactification_of_finiteType_over_field`, with the same compactification at every level.
- `Nonempty (integralDualizingGlobalHom ... ≅ (integralDualizingCompactSections ...).op ⋙ coefficientDerivedDual ...)` is a natural isomorphism of functors to D(R). It is the full derived mapping-complex assertion, natural for every morphism of constructible K. `coefficientDerivedDual` is exactly RHom_R(-,R[0]). The harmless coefficient carrier `ULift.{u+1,u} R` puts the ordinary module category in the section universe; the constant scalar map, regular coefficient unit, and module action are unchanged under its ring equivalence with R.
- The last clause records the degree-zero Hom bijection explicitly. Its right target is the actual regular completed coefficient sheaf at s in degree zero, and its left input is the same compact-support functor used to define C. It quantifies over every constructible integral K and asserts only the right-adjoint value at this coefficient unit.

Dependency declarations used: `FiniteFieldDatum` (`Sheaf.Paper.FiniteFieldFiber`); the coefficient-extension constructions and positive-level finiteness (`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`); `topologicalKrullDim` (Mathlib and its recorded upstream extension); `completedIntegralCoefficientSheafUnrestricted`, its commutative presentation, and `integralConstantToCompletionOfUniverses` (`Sheaf.Paper.CompletedIntegralCoefficients`, `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`); `sfFiniteExceptional` (`Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`); `NormalizedDVRTower` and its exact restrictions and evaluations (`Sheaf.Paper.NormalizedDVRTower`); `normalizedDVRCounitComparison` and `normalizedDVRReductionTransition` (`Sheaf.Paper.NormalizedDVREffectivity`); `sfIntegralConstructible` (`Sheaf.Paper.SfIntegralConstructible`), which uses the recorded derived-completeness and intrinsic finite-constructibility predicates; `HasProEtaleTorAmplitude` (`Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`, reexported by the recorded `Sheaf.Paper.FiniteTorAmplitude`); `ringedStrictTowerHomotopyLimitOfUniverses`; `derivedInternalHomOfUniverses`; and the recorded compact-support and coefficient-point constructions. The new dependency `lem-coef-finite-dualizing` is added to stmt_deps and supplies the finite-term and counit-adjoint transition interface. Two existing landed dependencies are also used: `lem-weil-compact-support-reduction-tower-functor` (`Sheaf.Paper.CompactSupportReductionTower`, `exists_compactSupportReductionTower`) gives the map action missing from a value-only presentation, and `def-sf-coefficient-duality` (`Sheaf.Paper.CoefficientDuality`, `coefficientDerivedDual`) gives the ordinary R-module derived Hom on the right. The dependency record is copied with a lean-only repair; no independent new notion node is needed. Published dependency interfaces used by the statements are imported; the proof plan and DAG retain the remaining proof dependencies. The compact-support comparison uses a smaller published module because the broad recorded import has the duplicate-declaration conflict described below.

Edge cases checked: the empty scheme has dimension minus infinity and satisfies the bound; d=0 gives [0,0]; n=0 denotes the first positive coefficient quotient; all positive levels, all equal-index maps, and all longer quotient maps are present. Zero objects remain allowed. Every constructible K is quantified without an extra Tor condition. Coefficients are never replaced by continuous or condensed modules. The coefficient carrier lift changes only size presentation, not the ring or scheme site. Every variable and universe is declared explicitly. A named specialization of `integralCoefficientRingSheafify` specifies both equal input universes, resolving Lean's otherwise ambiguous maximum in the sheafification instance; it reuses the published instance unchanged. Definitions have actual data; every postponed helper is a named theorem with a source and proof plan.

Searches retained from the saved packet: msearch leanfinder, query “integral dualizing object derived inverse limit finite exceptional inverse image”, returned eight unrelated condensed/profinite declarations, none stating this proposition. msearch loogle, query `finiteExceptionalInverseImage,NormalizedDVRTower,sfIntegralConstructible`, returned no hit and reported its first identifier unknown; this was not treated as proof of absence. msearch grep, query `dualizing|dualizingComplex|finiteExceptionalInverseImage` in the specified SixFunctors directory, returned no matching proposition. The repair also ran msearch grep for `integralDualizing|prop_coef_integral_dualizing` (zero hits), and direct rg over Mathlib, upstream WeilConjectures, and published lean/Sheaf for all new helper prefixes and the theorem name (zero hits). Source inspection found and reused the existing coherent compact-support tower, total derived inverse limit, intrinsic finite exceptional inverse image, actual Tor-interval predicate, and coefficient derived dual; none was privately redefined.

The statement is not disputed and no natural-language correction is made. The repair note on this node is a resolved stage-1 re-splitting instruction; its natural statement and current proof route are retained.
## Returned-delivery repair

The initial required dry run of the saved packet passed at temporary commit 755cc6825a.
The source self-check nevertheless reproduced every mathematical defect in the return of
immutable head e851d143b5d2: `integralDualizingExceptionalTransition_existsUnique` asserted
only `∃! τ, τ = 0`, and the definition selected that zero map. Its docstring did not
match its type. The former second reading had failed to inspect that definition. The
replacement deletes both the trivial theorem and its choice-based transition definition.
The current shared main still has no Lean record for either delivered node, so the
packet retains main's natural statements and proof plans and repairs only the Lean data.

The finite dependency now contains an ordinary-etale construction before transport.
`finiteDualizingEtaleAdjunction` is the actual `rightDerivedUpperShriekAdjunction` for
one fixed compactification. `finiteDualizingEtaleCounit` evaluates its counit at the
regular coefficient complex. `finiteDualizingEtaleComparison` is the adjunction
transpose of the inverse proper/open compact-support coefficient comparison, followed
by derived scalar extension of that counit and the normalized scalar-unit identification.
All three arrows are actual published constructions, not existentially selected maps.
The compact-support arrow is `Etale.ExceptionalCoefficients.compactSupportMap`: its
proper factor is the counit mate `scalarMate` and its open factor is the normalized
`openIso`. These are the same canonical arrows defining the comparison in
lem-fix-compact-support-coefficient-change. The broader recorded module also imports
an obsolete pro-etale interface that causes a duplicate `upperStarIsoLowerStarInv` in
the current server overlay; the smaller canonical-map module avoids that import.

`finiteDualizingCoefficientComparisons`, the dependency's primary statement, asserts
invertibility of that compact-support comparison and of the defined u, the explicit
counit identity, the identity-quotient equation under the canonical scalar-unit
comparison, and the quotient cocycle under `pbcFixedScalarExtensionComp`. It also
asserts invertibility of the intrinsic comparison and the intrinsic identity and
cocycle equations. Its source-based proof docstring gives the construction, finite-Tor
domain check, affine-local verification, counit pasting, and site transport.

`finiteDualizingEtaleTransition` is exactly the scalar-adjunction adjunct of the
counit-defined etale u. `finiteDualizingOrigin` uses the published comparison-site
unit (`boundaryDualizingComparisonIso`), the canonical intrinsic realization
unit/counit, and the regular-module comparison uniquely normalized by 1 mapping to 1.
`finiteDualizingRealizationRestriction` pastes the existing comparison/scalar square
with the intrinsic scalar square uniquely normalized on scalar-unit sections.
`integralDualizingExceptionalTransition` is the conjugate of the etale transition
through these specified isomorphisms. Thus its definition contains no free choice of
a transition or of a dualizing identification. All auxiliary choices are from unique
section normalizations or from derived scalar-adjunction universal properties.
`integralDualizingFiniteComparison` is its intrinsic scalar adjunct. The item's square
now writes the adjunct of this u explicitly using `Adjunction.homEquiv`, with right
adjoint the actual `normalizedDVRRes`. The uniform Tor bound, Roos presentation,
natural mapping-complex isomorphism, and H^0 clause retain their saved statements.

Additional source inspection: opened the complete current blueprint statement and
proof at main-20261015/sec-smooth-purity/sk-lem-sp-tower/lem-coef-finite-dualizing;
read the full signatures and defining bodies of the exceptional adjunction, etale
scalar extension, proper/open coefficient comparison, scalar-unit and composition
comparisons, site-unit dualizing comparison, intrinsic coefficient realization,
and normalizedDVRRes with its unit and composition comparisons. An additional msearch
grep for `finiteDualizingEtaleComparison|finiteDualizingCoefficientComparisons|integralDualizingExceptionalTransition`
returned zero hits. Existing general scalar, adjunction, and site constructions are
reused; the new declarations only specialize or state this dependency's own maps.

## Dependency modules

`lem-coef-finite-dualizing`: the returned record was unusable because its theorem
asserted only uniqueness of zero, omitting every clause of the dependency. The
replacement `Sheaf.SixFunctors.FiniteDualizing` states the full coefficient-change
claim, constructs its actual counit-defined map, and provides its normalized finite
pro-etale transport for the consumer. Only this dependency's `lean` record changes.

Finite dependency clause audit: the same `D,l,hl,E,X` and finite-type/separated binders
supply all its hypotheses; `m,n : ℕ` and `h : n ≤ m` encode the source's
`1 ≤ m+1 ≤ n+1` after relabeling the larger level as m. `finiteDualizingCoeff` and
`finiteDualizingQuotientBase` use the exact O_E quotient, with the fixed ULift only
for coefficient size. `finiteDualizingEtaleSupport`, `finiteDualizingEtaleExceptional`,
and `finiteDualizingEtaleTerm` give F_A, its right adjoint, and omega_A at A_s.
`finiteDualizingEtaleComparison` gives the specified counit-defined u. The first
conjunct of `finiteDualizingCoefficientComparisons` states both required
invertibilities and the actual counit equation; the second gives u_A,A under the
canonical scalar-unit identification; the third gives u_A,C under the canonical
associator. The last three conjuncts give the transported intrinsic isomorphism
and its semilinear unit and cocycle. The definitions `finiteDualizingOrigin` and
`finiteDualizingRealizationRestriction` specify exactly which site comparison
carries the etale map to the intrinsic pro-etale map.

The intrinsic restriction normalization is stated over general finite rings, with
`finiteDualizingIntrinsicRingMap` simply applying constant sheafification to the
scalar map. `finiteDualizingRestriction_eq` identifies specialization at the actual
quotient with the recorded tower restriction; its proof plan checks consecutive
maps and induction on their distance. Heterogeneous equality in the normalization
records equality of the very same underlying section with its changed scalar action.
It adds no ring or site hypothesis. This general interface avoids repeated kernel
expansion of Padic quotient presentations. The two named universe-specific instances
reuse `integralCoefficientRingSheafify.{u,u}` and `essentiallySmallSelf` verbatim.
The main module also imports the newly landed proof dependency
`Sheaf.Paper.CoefTowerCoaugmentation`.

## Second reading by Q48

I reopened the complete finite-dualizing node, its replacement Lean file, the integral
node, and the consumer square. In particular I expanded the transition all the way to
its defining arrows, rather than relying on its name or docstring. The former
`∃! τ, τ = 0` theorem is gone. The new etale u is the actual Hom-equivalence image of
inverse compact-support comparison, scalar extension of the actual exceptional
counit, and the regular-unit comparison. The main finite theorem asserts that this
compact-support arrow is invertible, so the imported total inverse has its actual
inverse value on every use here. The theorem also asserts u is invertible and gives
the counit, unit and cocycle equations. The two unique-normalization helper theorems
specify actual section values, respectively 1 and every generating section x; their
choices therefore determine canonical identifications, not arbitrary automorphisms.
The generic scalar restriction specializes to the exact recorded quotient restriction.
The pro-etale transition is the etale scalar adjunct transported through these same
identifications. The consumer's right-hand arrow explicitly takes `homEquiv` of
`integralDualizingFiniteComparison` with right adjoint `normalizedDVRRes`.

I matched the finite datum and characteristic exclusion, finite coefficient extension,
separated finite-type structure morphism, and nonnegative dimension bound with the
binders listed in the worker report. I matched the finite terms and their transition
square, actual strict-tower Rlim, canonical reduction comparisons, constructibility
and completeness, interval [-2d,0], natural derived Hom isomorphism, and degree-zero
Hom clause with the corresponding integral conjunctions. Equal indices now have the
stated identity comparison; no equation forces that identity to be zero. A longer
quotient is covered by the explicit cocycle. Natural n=0 means positive exponent 1;
empty X allows the zero regular module; d=0 gives exactly [0,0]. No extra Tor hypothesis
on K or ambient pro-etale adjunction has been added. All sizes retain the original
site object universe u+1 and morphism universe u. Every binder and universe is explicit,
every definition contains actual data, and the postponed claims are named theorems
with source and proof docstrings in this dependency's Lean declaration list.

## Proof-import compatibility

The required proof-import audit added the recorded modules individually. The wrapper
confirmed the same retired-interface duplicate when those modules transitively import
`ProEtale.UpperLowerStar.Iso`. The following incompatible broad proof modules are
omitted; their dependency ids and source proof steps remain in the unchanged DAG.
The concrete canonical maps needed to state this delivery come from the smaller
published interfaces documented above. All remaining recorded proof modules are imported.

- `Sheaf.SixFunctors.CompactCoefficientComposition → Sheaf.Paper.EtaleCompactSupportCoefficientChange → Sheaf.Paper.CompactSupportCoefficientChange → Sheaf.Paper.ExchangeProjection → WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekProjection → WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjection → WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal → WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal.Comparison → WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal → WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso`

The expanded proof-import check also exposed the retired ordinary pro-etale
`Derived.OpenImmersionLowerShriek` duplicate against `FiniteCoefficient.Derived.OpenLowerShriek`.
The wrapper reported this concrete duplicate (rather than a source error in the repaired maps).
The following broad proof imports were omitted to keep the finite-coefficient interface:

- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace → Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions → WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek`

Additional repair searches: msearch LeanFinder for “Canonical coefficient change
isomorphism for finite exceptional dualizing complexes defined as the adjunct of
compact support coefficient comparison followed by the counit, compatible with
cocycle and unit” returned eight unrelated general adjunction/condensed/complex
declarations, none the finite-dualizing statement. Loogle for
`Adjunction.homEquiv,Functor.mapDerivedCategorySquareIso` returned zero hits with
“unknown identifier Adjunction.homEquiv”; this is a search qualification limitation,
not evidence that the APIs are absent (their full source signatures were read and used).
The fully qualified retry `CategoryTheory.Adjunction.homEquiv,CategoryTheory.Functor.mapDerivedCategorySquareIso` also returned zero hits, reporting the latter side-library helper unknown to the Mathlib search index.

The expanded proof imports made repeated kernel expansion of the specialized
derived restriction exceed the limit in one library pass. The specialization now
uses `finiteDualizingIntrinsicRestriction_existsUnique`: its defining property is
HEq with the explicitly derived generic scalar comparison. This fixes the entire
isomorphism, including every component, under `finiteDualizingRestriction_eq`; it
is stronger than a mere existence or Nonempty choice and permits no automorphism.
The proof plan specifies exact localization of eqToIso, so the same construction
is retained while its repeated quotient expansion is avoided. The second reading
also checked this derived normalization and its use in the transition.

## Validation of the repaired packet

The final two-file scompile.py run completed with exit 0 and no warnings or errors.
The finite module took 40.5 s in the private overlay, 34.4 s preliminary, 38.5 s
in its sandbox check, and 37.9 s as the library module. The integral module took
12.5 s in its sandbox check and 11.8 s as the library module. Each retained the
60-second limit, nice 19 and two threads. The preceding server confirmation also
accepted both files. The local timeout and each incompatible proof-import path
are recorded above along with their repairs.

## Retained-packet self-check, 2026-10-17 UTC

The retry retained the completed repair rather than restoring the returned zero-map
interface. I read both complete delivered modules and the return, and checked the
current main-20261015 blueprint statements for both nodes. Against the current shared
node copies, the finite dependency differs only in `lean`; the integral node differs
only in `lean` and the three explicitly reported added statement dependencies. Both
primary recorded signatures occur verbatim in their files; all 53 declarations are
recorded, and neither file has a line over 100 characters.

I opened `ExceptionalCoefficientComparison.compactSupportMap`, its `comparisonInverse`
and `unitIso`, the actual etale `rightDerivedUpperShriekAdjunction`,
`sfFiniteExceptional`, `boundaryDualizingComparisonIso`, `sfIntrinsicRealizationUnit`,
`normalizedDVRRes`, and the scalar unit, composition and comparison-restriction maps.
The inverse helper has a zero fallback outside its isomorphism domain, but the finite
theorem explicitly asserts invertibility of this very compact-support comparison at
every dualizing term, so no use here selects that fallback. The etale `u` transposes
that inverse followed by the actual counit and regular-unit identification. The
intrinsic transition transports its scalar adjunct through the specified site-unit
and section-normalized coefficient comparisons. The integral square applies the
Hom-equivalence of derived extension adjoint to the actual `normalizedDVRRes` to
`integralDualizingFiniteComparison`. This closes H5/H13 and the zero-transition H3
fault without replacing the canonical map by an arbitrary isomorphism. The finite
unit and cocycle conjuncts cover equal levels and all longer quotients. Empty X,
positive exponent n+1, d=0, the full Tor interval, and the natural derived-Hom and
H^0 clauses were checked again against the integral node. This is the worker's
self-check; the maintainer remains the independent reviewer.


## Duplicate-theorem repair, 2026-10-17 UTC

The required initial dry run of the retained packet passed at commit ae15b6a63c.
I then repaired the independent review of returned head a70a30e779c8: removed
`WeilConjectures.integralCoefficientPrime_isUnit` and its declaration-list entry,
imported `Sheaf.Paper.DirectImagesConstructible`, and used its existing theorem
`WeilConjectures.finiteFieldDatumPrimeUnit D l hl` in
`integralDualizingCompactTower`. No replacement theorem or alias is introduced.

I opened the existing theorem's complete docstring and signature. Both it and the
removed theorem bind exactly `(D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
(hl : l ≠ D.p)` and conclude `IsUnit (l : D.k)`. Neither has earlier section
variables, extra hypotheses, or a different namespace interpretation. In particular,
the supplied unit is still in D.k, not in the finite base field or coefficient ring.
Direct rg searches of the published Sheaf library and upstream WeilConjectures
sources found the existing statement in DirectImagesConstructible and no upstream
alternative. The integral module has no remaining reference to the removed name.

Against current main, the dependency node still changes only in `lean`, and the
integral node still changes only in `lean` and its previously documented additions
to `stmt_deps`. Both primary signatures and all natural-language statements are
retained. The integral construction still uses the same compactification and the
same coherent compact-support tower; proof irrelevance identifies the supplied
unit evidence. The finite dependency module is unchanged. The hypothesis/clause
and edge-case audit in the retained worker report and second reading still applies.
This repair leaves 52 recorded declarations across the two modules.


Repair validation: the explicit two-file scompile.py invocation completed with
exit 0 and no errors or warnings. The finite module's library check took 32.2 s;
the integral module with DirectImagesConstructible imported took 12.3 s. Both
remain within the required 60 s limit. The source self-check confirmed verbatim
primary signatures, permitted node-field differences, all 52 declaration records,
explicit autoImplicit false, and no lines over 100 characters. The duplicate
repair changes no primary signature, hypothesis, conclusion, or canonical map.
