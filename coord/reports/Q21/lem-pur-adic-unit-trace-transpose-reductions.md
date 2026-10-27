## Worker report

The module states the unit-trace construction with its actual exceptional adjunction,
ordinary coefficient extension, inverse completed projection and prescribed finite
smooth-purity reductions. No uniqueness of reconstructed integral lifts is asserted.

The finite-field datum and coefficient datum bind the characteristic, coefficient
prime, inequality and fixed algebraic closure. Intermediate fields with finite-dimensional
instances are precisely the permitted finite coefficient fields; bottom is the base
field. Schemes carry their k-structures and separated finite-type hypotheses.
SmoothOfRelativeDimension d f supplies smoothness and pure relative dimension, including
d = 0. Every exponent is n+1, so all positive exponents occur.

The objects coefficientUnit, tateUnit and sourceFunctor give respectively the completed
regular module in degree zero, its shifted Tate line, and completed pullback followed
by the recorded exact twist and shift. operation uses the specified RingSystem
adjunction on the recorded compactification. targetReduction uses its counit-normalized
coefficient comparison, the counit-normalized finite realization, and the canonical derived-reduction presentation.
HasPrescribedReductions compares the resulting actual arrow with purAdicFiniteArrow
using purAdicSourceReduction. HEq only accommodates the separately presented canonical
finite exceptional target; it does not identify arbitrary choices.

unitTrace is P(g0) followed by the specified adjunction counit. scalarTrace uses the
published PurAdicScalarTrace.trace, including canonical twistComparison, multiplication
normalization of coefficient units, and the inverse support comparison. Construction.formula
is exactly j followed by adicTranspose of adicTraceMap. The latter is the inverse
actual completed projection followed by t tensor identity and the coefficient unitor.
The j normalization is imposed on every K-flat representative by the explicit termwise
line tensor, shift and Koszul symmetry. Its data is not chosen from a bare existence.
Construction.gamma is a natural transformation; sourceLinear, supportLinear and
exceptionalLinear retain the coefficient actions. reductions covers every positive
uniformizer exponent, invertible applies to these very components. traceReductions
gives the normalized finite trace at every exponent. cofinalTrace retains the explicit
finite universal trace equation, including the finite-free coefficient map and its
root normalization. Further derived quotient reduction covers noncofinal exponents
without a flatness restriction.

The theorem first supplies at least one base-field g0 with its prescribed unit
reductions. Its universal clause then allows every such g0 and constructs the family
for every finite field F. It does not assert that two such integral g0 coincide.

Dependencies used: PurityFiniteSetting (FiniteFieldDatum/CoefficientDatum);
CoefficientExtensionFinite (valuation rings and quotients); SfIntegralConstructible
and FiniteTorAmplitudeSites (full uniform finite-Tor categories);
CoefficientTwistsDetailed/IntrinsicCoefficientTwistsUnrestricted (actual twisting line);
ConstructibleExceptionalAdjunctionCoefficients (RingSystem, operation, adjunction,
scalar realization and comparison.b; FiniteRightNormalization supplies the counit-normalized
finite realization);
IntegralCompactSupportCoefficientComparison (image, comparison, finiteReductionIso,
finiteImageIso); AdicPurityObjects/AdicPuritySourceReduction (purAdicFiniteArrow,
purAdicSourceReduction); PurAdicReconstruction (base unit existence);
AdicProjectionShiftCoherence (adicProjection, adicTraceMap, adicTranspose);
AdicScalarTraceCoherence (normalized coefficient comparison and trace);
CompletedUnitPullbackTower (Core, actual pullback unit and admissibility);
FiniteUniversalSmoothTrace (cofinal finite trace equation);
CoefficientRingedTensorHomModel (K-flat representative tensor comparison);
LineUnboundedDerivedTensor/TensorColimitsIndependentCoefficients (canonical total
collapse and site-tensor presentation).

Edge cases read before writing: zero coefficient complex; empty source or target;
relative dimension zero; identity geometry; base field itself; ramified extensions;
smallest exponent one; cofinal exponents er and arbitrary further quotient m.
No positive-dimensional, nonzero-object, nonempty-scheme or unramified hypothesis
is added. Further quotient need not be flat.

Searches: msearch.py leanfinder for integral smooth purity from unit trace projection
formula and adjoint transpose returned algebra trace declarations, not this statement.
msearch.py loogle CategoryTheory.Adjunction.homEquiv returned the abstract adjunction
interface. msearch.py grep smoothTrace|adicReconstruction|unitTrace returned no exact
match. rg in WeilConjectures and Sheaf for the item ID found no existing statement.
Project searches for adic trace/projection found the published scalar trace coherence
and projection-shift coherence modules, whose constructions are reused. Mathlib tensor,
single-functor, bifunctor-shift and natural-transformation sources were inspected.

Validation: scompile.py compiled each of the five modules separately in dependency
order, in both sandbox and library modes. There were no errors or unexpected
warnings; the theorem proof alone is postponed.

## New nodes

def-pur-unit-trace-reduction-data: Fix the finite-field and completed coefficient setting and the specified compact-support/exceptional adjunction. Define the completed coefficient unit, shifted Tate unit and completed pullback-twist-shift source. A finite right normalization is the finite right realization characterized by its smooth exceptional counit equation. Define target reduction by scalar realization, the exceptional coefficient mate, this normalized finite right realization and the actual reduction presentation. HasPrescribedReductions is equality at every positive exponent with the recorded finite smooth purity map under its prescribed source comparison. The pulled coefficient unit is identified with the Tate unit by its actual pullback comparison and tensor unitor.

def-pur-unit-trace-tensor-coordinates: For the completed Tate line and smooth pullback, define the shifted degree-zero line complex. Its canonical twist reassociation is degree-zero total-tensor collapse followed by the inverse second-slot shift comparison and Koszul symmetry. Define the ordered completed tensor functor and the restricted source functor. IsJNormalized specifies its localized formula on every K-flat representative using the recorded tensor models and ordinary-to-completed map. Normalize the coefficient-unit constraint by scalar multiplication, expressed by the total-complex left unitor on every K-flat representative.

def-pur-unit-trace-scalar-data: For a permitted base-unit isomorphism g0, define its trace as compact support of g0 followed by the specified exceptional counit. HasTraceReductions is the equality of every positive derived reduction with the normalized finite coefficient-valued smooth trace under the prescribed source comparison. Represent Q_l by the bottom intermediate field and its unique inclusion. Define the scalar-extended trace by the published ordinary derived scalar extension, inverse support comparison, canonical Tate twist/shift comparison and multiplication-normalized coefficient-unit comparison. CofinalFiniteTraceCompatibility is the finite universal trace equation at er, retaining the root and coefficient-map normalization.

def-pur-unit-trace-construction: Construction is the normalized data of the unit trace, completed projection and exceptional-adjunction assembly from a fixed base trace. It includes the canonical finite right realization, coefficient-unit constraint, twist/tensor comparison and inverse actual projection. It contains a natural transformation whose components equal the displayed adjoint transposes, their coefficient linearity including the Hom bijection, equality of all positive reductions with prescribed finite smooth purity, invertibility of every component, all normalized finite trace reductions and the finite scalar-trace equation at cofinal levels.

All four packages serve the explicit unit-trace assembly in the current blueprint Steps 2-3. Existing operations are reused; these define only their canonical composite maps, normalizations and resulting data. Existence is asserted only by the main theorem. Search results are recorded in each definition node.

LeanSearch was also run for the normalized assembly package: eight flatness/smooth-algebra
hits, none providing these canonical composite maps or the theorem. The successful query
and its results are recorded in every new node and in searches.jsonl.

def-pur-adic-projection-trace-data owns the existing adicProjection,
adicTraceTensor, adicTraceMap and adicTranspose in
Sheaf.Paper.AdicProjectionShiftCoherence. Its statement describes their actual
composite formulas and input witnesses, without asserting the module theorem.

def-pur-adic-scalar-trace-data owns the existing unit, unitComplex, twistedUnit,
residueInverse, overTwistedUnit, UnitMultiplication, CoefficientComparison,
twistComparison, trace and baseInclusion in
Sheaf.SecSmoothPurity.AdicScalarTraceCoherence. The pure-tensor multiplication,
K-flat counit and compact-support mate normalizations are retained.

def-pur-completed-unit-pullback-data owns the existing integral system/unit,
Admissible, Reduction, calculus and Core definitions in
Sheaf.Paper.CompletedUnitPullbackTower. Core's whole-system, finite-component,
Roos and unit formulas are described, with no existence theorem asserted.

def-pur-finite-trace-presentation-data owns the existing finite unit, Tate-line,
traceSourceIso, traceOnTwist, traceSupportModel, traceCompactComparison and
traceUnitExtensionIso constructions in Sheaf.Paper.FiniteUniversalSmoothTrace.
Its statement asserts no finite universal trace theorem.

Each new owner cites the current blueprint transport proof. The successful
LeanSearch query for completed projection, scalar unit trace and pullback data
returned eight abstract adjoint/scalar-module/analysis hits, not these geometric
interfaces; Loogle returned zero hits and Mathlib grep zero. DAG and project
searches found the published declarations and no existing definition owners
for these four interfaces. All searches are recorded in the new node records.

## Returned-delivery repair

The returned immutable head was fb7dfb40df87. The current main node has the same
mathematical statement and no Lean record; the returned five modules remain this
packet's modules. The delivery wrapper rebases the packet on current main.

H2: added existing:true definition owners def-pur-adic-projection-trace-data,
def-pur-adic-scalar-trace-data and def-pur-completed-unit-pullback-data, binding the
published definitions without copying or changing them. The item and all four
unit-trace definition nodes now cite these owners instead of
lem-pur-adic-projection-shift-coherence, lem-pur-adic-scalar-trace-coherence and
lem-pur-completed-unit-pullback-tower. The tensor presentation citation is now
def-pur-site-sheaf-tensor-presentation-data. The unused
lem-pur-line-unbounded-derived-tensor citation is removed everywhere, and its
module import is replaced by the exact generic BifunctorSingle import. No
LineUnbounded declaration is used, so its data owner is not a dependency either.

Advisory ownership: finiteImageIso and finiteReductionIso already have owner
def-pur-finite-compact-support-scalar-data; this packet now cites that node.
Added def-pur-finite-trace-presentation-data as the existing:true owner of
traceCompactComparison and the associated unit/Tate-line presentation maps.

Advisory on cofinalTrace: that field is the finite scalar-extension equation;
it is not asserted to contain t_E syntactically. The separately stated
traceReductions field is HasTraceReductions of scalarTrace(t0), at every n+1.
At n+1=er, it identifies (t_E)_{er} with the normalized finite B-trace. The base
HasTraceReductions identifies (t0)_r with the normalized finite A-trace.
CofinalFiniteTraceCompatibility states precisely the coefficient-extension
comparison between these finite traces, so the three equations give
(t_E)_{er}=((t0)_r tensor 1)c^{-1} with the stated Tate/unit presentations.
No cofinal index or arbitrary quotient case is omitted.

Advisory on HEq: both sides of each reduction predicate are actual morphisms
in the same fixed intrinsic finite-coefficient derived category. Their types use
separately defined coefficient-reduction and finite-purity presentations.
HEq asserts equality in this dependent family, not equality up to an arbitrary
isomorphism, nor equality after forgetting coefficients. It entails equality of
those arrow types; after transporting by that equality it is ordinary arrow
equality. The prescribed source and counit-normalized target composites are
written in full before this equality, so HEq cannot absorb an arbitrary endpoint
comparison or a sign change. No theorem is added merely to choose a transport.

H11: the prior self-check paragraph has been removed. The separate reader
/root/second_reading checked the item, all four construction modules and the new
existing:true owners clause by clause; its signed reading appears below.

## Second reading by Q21

Reviewer: the separate Q21 second-reading agent (`/root/second_reading`), 2026-10-24 UTC.
This is an independent reading of the statement and definitions, not the author's
self-check. I read the original item statement and eight-step proof, the current
blueprint transport proof, all five sandbox Lean modules, the four original
definition-node records, and the published declarations in
AdicProjectionShiftCoherence, AdicScalarTraceCoherence, CompletedUnitPullbackTower,
AdicPurityObjects, AdicPuritySourceReduction, PurAdicReconstruction,
FiniteUniversalSmoothTrace, and the finite presentation maps in
IntegralCompactSupportCoefficientComparison. I then read the four new existing
definition-owner records and the replacement dependency lists. I did not edit Lean,
run a compiler, or prove the postponed theorem.

Clause-by-clause comparison:

1. The fixed finite-field datum is `D : FiniteFieldDatum` and its coefficient datum is
   `C : D.CoefficientDatum`. The prime and its inequality with the characteristic are
   supplied by `C.l` and `C.different`. The coefficients are literal intermediate
   fields of `C.Qbar` with `FiniteDimensional (Padic C.l)`, so there is no added
   algebraically closed coefficient field or unrestricted infinite extension.
   `baseField := ⊥` is the base coefficient field inside this same closure, and
   `baseInclusion := IntermediateField.inclusion bot_le` is its canonical inclusion.

2. The scheme hypotheses give the stated structure maps to `Spec D.k`, finite type
   as locally finite type plus quasi-compact, and separatedness. `f.IsOver` says that
   `f` respects those structure maps. `SmoothOfRelativeDimension d f` supplies
   smoothness of pure relative dimension, and `d : ℕ` includes dimension zero.
   The explicit locally finite type and quasi-compact instances for `f` are the
   usual finite-type hypotheses on this same morphism; they impose no new
   mathematical restriction for a morphism between the given finite-type
   k-schemes. There is no nonempty or positive-dimensional hypothesis.

3. `coefficientUnit` reuses `integralConstantCoefficientObject`, the regular
   completed coefficient module in degree zero. `tateUnit` is the published
   integral twisting object followed by `[2d]`. `sourceFunctor` is exactly
   completed pullback, the actual integral twist, and that shift. Its restriction
   uses `finiteTorConstructibleIntegralCategory`, the full derived-complete
   constructible category with uniform finite-Tor bounds. No arbitrary substitute
   for the completed unit, Tate line, source functor or finite reduction is used.

4. `operation` uses the specified `RingSystem` adjunction on the recorded
   compactification. `FiniteRightNormalization.iso` identifies its finite right
   functor with the published finite exceptional functor, and `.counit` pins the
   identification by the actual smooth exceptional counit. These are existential
   conclusion data, not added assumptions. This prevents sign changes or an
   arbitrary realization of the right functor from changing what the prescribed
   reductions mean. `targetReduction` composes the actual derived quotient
   presentation, scalar realization, exceptional coefficient mate, this normalized
   finite right realization, and the target quotient presentation.

5. The outer existential provides `normal0`, a normalized `core0`, finite-Tor
   membership of `T0`, and at least one isomorphism `g0 : T0 ≅ G0 1`. Its reductions
   are imposed on `sourceUnitIso.hom ≫ g0.hom`, so the source is first identified
   with `H0 1` using the actual completed pullback unit, exact twist and tensor
   unitor. The following universal quantifier ranges over *every* `g0` with those
   reductions, rather than fixing a convenient lift. The conclusion never asserts
   uniqueness or equality of two integral lifts.

6. `unitTrace` first uses the left realization to enter the specified support
   functor, applies that functor to `g0`, and follows it by the adjunction counit.
   It therefore renders `epsilon_1 ∘ P(g0)` with the specified adjunction. The
   immediate `HasTraceReductions` conclusion identifies every positive quotient
   of this very trace with `coefficientValuedSmoothTrace` under the displayed
   compact-support and source comparisons. The exponent is `n+1` with unrestricted
   `n : ℕ`; no positive level is omitted.

7. For every finite coefficient field `F`, the theorem supplies
   `Nonempty (Construction ... F ... t0)`. The trace in that package is the defined
   `scalarTrace ... coefficients t0`. Expanding it and the published
   `PurAdicScalarTrace.trace` gives `P(theta.inv)`, inverse compact-support mate,
   ordinary derived scalar extension of `t0`, and the target unit multiplication,
   with the outside `twistedUnitIso` factors changing only the presentation of the
   same shifted Tate unit. `CoefficientComparison.normalization` fixes the support
   mate. Its `UnitMultiplication` data are fixed sectionwise by
   `b ⊗ x ↦ b iota(x)` and by the universal K-flat counit. The published
   `twistComparison` fixes the twist and shift comparison. Thus the package does
   not replace the stated canonical coefficient comparison by an arbitrary map.

8. `adicProjection` is the actual completed proper/open projection composite,
   retaining its completion units. `completionIso` and `projectionIso` assert
   invertibility of these particular maps. In `Construction.formula`,
   `adicTraceMap` is the inverse of this projection followed by ordinary
   `t_E ⊗ 1`, the actual completion comparison and left unitor. The term supplied
   as its trace is precisely `scalarTrace ... t0 ≫ unitIso.hom`. `unitNormalized`
   pins `unitIso` on every K-flat representative to the total-complex left unitor,
   eliminating arbitrary choices of coefficient-unit constraint.

9. The `j` field has exactly the ordered target `T_E` completed-tensor `L_E K`.
   `chainCoordinates` is degree-zero total-tensor collapse, inverse second-slot
   shift comparison, and Koszul symmetry. `chainJ` first uses the actual
   site-sheaf twist/tensor presentation. `jNormalized` identifies `j` on every
   K-flat representative with this chain construction, localization, the recorded
   tensor-model comparison, the resolution isomorphism, and the actual
   ordinary-to-completed comparison. In particular it specifies the intended
   reassociation and symmetry, including the even shift, rather than merely an
   isomorphism between the correct objects.

10. `adicTranspose` applies the specified exceptional `Adjunction.homEquiv` after
    the left realization. Consequently `Construction.formula` is exactly
    `j.hom.app K ≫ adicTranspose(adicTraceMap(...))`, i.e. the statement's
    `adj(u) ∘ j`. `gamma` itself is a natural transformation, not unrelated
    component choices. `sourceLinear`, `supportLinear`, `exceptionalLinear` and
    `adjunctionLinear` retain the actual coefficient actions; the components live
    in the coefficient module-derived categories throughout.

11. `Construction.reductions` applies `HasPrescribedReductions` to these very
    `gamma.app K` for every object of the full finite-Tor category and every
    positive exponent. The right side is `purAdicSourceReduction` followed by the
    actual `purAdicFiniteArrow.hom`, whose definition is the published finite
    `smoothPurityMap` on the actual derived quotient of K. This retains the
    prescribed finite purity normalization and coefficient action.
    `Construction.invertible` is `IsIso (gamma.app K)` for those same components;
    it is not an unrelated existence of isomorphic endpoints.

12. `Construction.traceReductions` fixes every positive quotient of the defined
    scalar-extended `t_E` as the normalized finite smooth trace. At `n+1=e*r`,
    `cofinalTrace` additionally supplies the finite universal trace equation with
    the coefficient map, root comparison, trace-twist comparison and normalized
    unit extension all retained. This field alone does not mention `t_E`; its
    relevance is its conjunction with `traceReductions` for `t_E` and the theorem's
    base `HasTraceReductions` for `t0`. Substitution of those two reduction
    equalities into the finite universal equation gives the stated cofinal
    identity `(t_E)_(er) = ((t0)_r ⊗ 1)c^-1` in the canonical presentations.
    The stronger explicit all-positive-level trace-reduction field covers the
    arbitrary further quotient assertion. No flatness of that further quotient
    is assumed.

13. The two reduction predicates use `HEq` between the displayed morphisms with
    their separately elaborated dependent Hom types. This is equality after
    equality transport of those types; it is not equality modulo an arbitrary
    isomorphism or a choice of comparison. The actual canonical comparison maps
    are already present in the two expressions. Thus `HEq` retains equality of
    these maps, rather than merely asserting equal ranks or isomorphic arrows.
    An explicit `eqToHom` presentation could improve readability, but I found no
    weaker reduction assertion here.

Edge cases: `d=0` removes the even shift without altering the construction;
`K=0` is allowed in the full subcategory and needs no nonzero condition; empty
schemes have the same regular-unit and ring-map formulas; `E=⊥` is included in the
universal coefficient quantifier; `m=1` is `n=0`; ramified extensions are handled by
`n+1=e*r` at cofinal levels and all `n+1` in `traceReductions`, including levels not
divisible by e. Neither the coefficient formula nor the arbitrary quotient clause
adds an unramifiedness or flatness assumption.

H2 ownership check: the new `existing:true` records own precisely the reused
definitions in the three published theorem modules, without copying a Lean
declaration or claiming their theorem conclusions. The projection owner lists
`adicProjection`, `adicTraceTensor`, `adicTraceMap`, and `adicTranspose`; the scalar
owner lists the unit/multiplication/comparison/twist/trace definitions; the pullback
owner lists the actual system, reduction and `Core` data. The finite-trace owner
similarly records the finite presentation maps, including `traceCompactComparison`.
The item and four assembly-definition records replace the three old theorem-owner
citations, replace the tensor-colimits citation by
`def-pur-site-sheaf-tensor-presentation-data`, and drop the unused line-derived-tensor
lemma. `finiteImageIso` and `finiteReductionIso` use the existing
`def-pur-finite-compact-support-scalar-data` owner. The Lean source now imports the
generic `BifunctorSingle` API in place of `LineUnboundedDerivedTensor`, and no
`LineUnbounded` declaration is used.

Verdict: the H2 owner repairs describe the actual reused definitions, and this
reading supplies the missing H11 independent clause-by-clause review. I found no
statement weakening, added mathematical hypothesis, hollow definition, arbitrary
canonical comparison, or integral-lift uniqueness assertion. The cofinal and HEq
points above are explanatory advisories, not newly found mathematical mismatches.
Compilation and delivery checks remain the author's separate responsibility.

Repair validation: all five modules compiled separately via scompile.py in dependency
order, sandbox and library modes, with no errors or unexpected warnings. No new
dependency path returns to any packet node. Current-main comparison changes only
lean and stmt_deps on the item; its statement and proof remain verbatim.
