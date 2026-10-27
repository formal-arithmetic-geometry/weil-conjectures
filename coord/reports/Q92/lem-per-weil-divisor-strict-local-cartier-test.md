## Worker report

Stage 2, Q92, item `lem-per-weil-divisor-strict-local-cartier-test`.

The item is stated in `Sheaf.AlgebraicGeometry.WeilDivisorStrictLocalCartierTest`.
There are four named theorems, each with proof `by sorry` and the relevant source-based
natural-language proof. There are no proved theorems or additional axioms. The original
statement and split are unchanged. The item gains the statement dependency
`def-per-cartier-fraction-cover`, whose separate module contains actual definitions only.
There is no dependency repair and no statement correction.

Clause-by-clause reading of the item:

1. **Scheme Y.** Each theorem binds `Y : Scheme.{u}`. This is the recorded
   `AlgebraicGeometry.Scheme`, including the empty scheme.
2. **Noetherian, with a finite Noetherian affine cover.** `[IsNoetherian Y]` is Mathlib's
   class extending `IsLocallyNoetherian Y` and `CompactSpace Y`. Its local Noetherian
   condition and quasi-compactness give exactly a finite Noetherian affine cover.
3. **Normality at every point.** `hnormal` is literally
   `∀ y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)`.
   This is the inline normal-domain interface recorded for `def-weil-pbc-normal-ring`.
   No global integrality or connectedness is assumed.
4. **Finite integer Weil divisor, distinct integral codimension-one closures.**
   `E : AlgebraicCycle Y ℤ` reuses Mathlib's locally finitely supported coefficient
   functions on the points of Y. A point represents its reduced irreducible closure;
   distinct points of a scheme have distinct irreducible closures. `hE` requires each
   nonzero coefficient to have `ringKrullDim (Y.presheaf.stalk z) = 1`. On a normal
   locally Noetherian scheme this is codimension one. Compactness makes the locally
   finite support finite, so this is exactly the finite sum in the node. No arbitrary
   family, enumeration or multiplicity of prime-divisor indices is introduced.
5. **Normalized valuation.** `CartierFractionCover.HasCoefficients` uses length orders
   `Ring.ord` on the numerator and denominator germs, subtracting them in ℤ.
   At the normal height-one stalk these are the normalized DVR orders. Strict-local
   fraction orders are the recorded `Ring.weilFractionOrder`, which uses the existing
   `Ring.weilOrder` and an actual `IsLocalization.sec` fraction presentation. There is
   no freely chosen valuation or normalization.
6. **Cartier divisors and effectivity.** `CartierFractionCover` gives actual open sets
   containing each indexed point and numerator/denominator sections. Both germs must
   be non-zero-divisors at every point of the chart. `overlap_unit` is the literal
   cross-multiplied equality expressing that the two fractions differ by a regular
   unit. Such cover data presents a Cartier divisor. The theorem only asserts
   existence of presentation data, so different presentations are not identified
   as different abstract Cartier divisors. `IsCartierWeilMultiple` is existence of
   this data with coefficients `a * E z`. `C.IsEffective` sets every denominator to
   one; the numerator is already a regular non-zero-divisor by the structure field.
7. **Geometric point and strict henselization R.** Bind `y`, a residue separable
   closure `K`, and a stalk algebra `H`, with exactly the residue-algebra and scalar
   tower instances of the recorded `StrictHenselizationPresentationIn`. The
   presentation `P` is the universal pointed-etale colimit and specified algebra
   identification, not just an arbitrary strictly henselian algebra. All residue
   separable closures and all presentations are tested. This is the strict local
   ring determined by a geometric point, independently of enlarging its separably
   closed residue field. `H` and `K` lie in `Type (max u v)`; the base stalk stays in
   `Type u`, so the test-algebra universe cannot be too small.
8. **R is a Noetherian normal local domain.**
   `strictLocalWeil_normal_finite` asserts
   `IsNoetherianRing H ∧ IsLocalRing H ∧ IsDomain H ∧ IsIntegrallyClosed H`, for every
   `P`, without assuming any of these four conclusions on H.
9. **E_R and its coefficients.** `localWeilCoefficient E y φ q` contracts the actual
   height-one prime `q` along the actual homomorphism `φ`, then uses
   `Y.fromSpecStalk y` to locate its generic point on Y, and evaluates E there.
   Thus a prime over a supported divisor has exactly its coefficient and every
   other prime has zero. A divisor not passing through y has no such contracted
   prime. `strictLocalWeil_normal_finite` also asserts finite support of this
   coefficient function on `Ring.WeilHeightOnePrime H`; consequently it is a
   genuine finite Weil divisor (it can be bundled by `Finsupp.ofSupportFinite`).
   This does not assume a finite prime fiber or injectivity of a free map.
10. **Etale pullback and further strict-local compatibility.**
    `exists_etaleWeilPullback_strictLocal_compatible` binds any `f : V ⟶ Y` with
    `[Etale f]` and produces an actual `F : AlgebraicCycle V ℤ` with every coefficient
    equal to `etaleWeilCoefficient f E`. That coefficient is `E (f z)` in height
    one and zero elsewhere. The second conjunct tests every strict henselization
    of every `z : V` and equates its F coefficient with the E coefficient pulled
    directly through `(algebraMap ... H).comp (f.stalkMap z).hom`. This spells out
    compatibility with further strict localization; no comparison morphism is
    chosen or assumed. The neighborhoods need not be quasi-compact, so the cycle
    is allowed locally finite support there, exactly as for usual Weil divisors.
11. **Fixed integer a>0.** The equivalence and effective theorem bind `(a : ℤ)` and
    `(ha : 0 < a)`. It is the same a on both sides; there is no existential or
    geometric-point-dependent multiple.
12. **Exact iff and principal equation in Frac(R)×.**
    `isCartierWeilMultiple_iff_strictLocal` is precisely
    `IsCartierWeilMultiple Y E a ↔ IsStrictLocallyPrincipalWeilMultiple.{u,v} Y E a`.
    The latter definition quantifies every presentation and gives an actual
    `c : (FractionRing H)ˣ` with `weilFractionOrder q c.val = a * localWeilCoefficient ... q`
    for every height-one q. It includes existential witnesses of the known
    Noetherian normal-domain properties to use that valuation API; these are
    conclusions, never conditional hypotheses making a test vacuous. Localness
    is separately asserted by theorem 1. Equality of every coefficient is exactly
    `div_R(c) = a E_R`, including coefficient zero away from the support.
13. **E effective and global effective Cartier divisor.**
    `effectiveWeilMultiple_strictLocal_equations` assumes `heffective : ∀ z, 0 ≤ E z`
    and the equivalent Cartier condition `hcartier`. Its first conjunct produces
    a fraction cover C with the same exact coefficients and `C.IsEffective`.
    Its overlap units glue the regular principal ideals to the effective Cartier
    divisor; no independent ideal, arbitrary divisor, or freeness assumption is
    substituted for this construction.
14. **The same support.** The first conjunct also asserts
    `C.support = {y | ∃ z, E z ≠ 0 ∧ y ∈ closure ({z} : Set Y)}`.
    This is precisely the union of the underlying supported integral divisors.
    The support of C tests whether the local equation is a unit, using the same
    presentation's own equation, not an independently chosen closed subset.
15. **Regular strict-local generators.** The second conjunct produces `r : H`
    with `r ≠ 0` and every `Ring.weilOrder q r` equal to the required coefficient.
    Its nonzero image in `FractionRing H` therefore gives the required unit c;
    the normal-domain fact needed for that image is theorem 1. This states exactly
    that the generators may be taken in R rather than merely its fraction field.
16. **Pointed etale single equation.** The last conjunct quantifies any geometric
    point `ybar : Spec (.of Ω) ⟶ Y`, `[Field Ω] [IsSepClosed Ω]`, and produces V, f,
    `[Etale f]`, a lift `vbar` with `vbar ≫ f = ybar`, and a single global regular
    section s. Every germ of s is a non-zero-divisor, and all its height-one orders
    are `a * E (f z)`. Thus s defines exactly the pullback of the same effective
    Cartier divisor. Equality with that Cartier divisor is characterized by the
    orders on a normal scheme (the zero-order-unit argument of Tag 0BE8), so no
    replacement supported only on the same set is being asserted.

Dependency interfaces used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` through
  `IsNoetherian`; the finite-cover convention was checked against both class bodies.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  with `IsDomain` exactly as the dependency's inline normal-domain record requires.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn`, including the full universe parameters,
  pointed-etale diagram, colimit cocone, and specified algebra identification.
- `Sheaf.RingTheory.WeilDivisorClassGroup`: `Ring.WeilHeightOnePrime`, `Ring.weilOrder`.
- `Sheaf.RingTheory.HeightOneFractionOrder`: `Ring.weilFractionOrder`.
- `Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic`: `AlgebraicGeometry.AlgebraicCycle`;
  `Mathlib.AlgebraicGeometry.Stalk`: `Scheme.fromSpecStalk`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.

All recorded proof-dependency modules available when writing were imported as ordinary
(non-public) imports: NormalEtaleComponentsClopen, FlatBaseChangeReflexive,
StrictHenselizationFaithfullyFlat, StrictHenselizationNoetherian,
EtaleColimitNormalLocalDomain, EtaleNormalRing, FiniteSeparableFibersOfEtaleColimit,
and StrictHenselizationTriples. The etale-morphism dependency is a public import since
the statements use it. Five proof-only nodes have no recorded Lean module in the
read snapshot: lem-per-divisorial-fractional-module-lattices,
lem-per-ind-etale-height-one-valuation, lem-trf-finite-presentation-stalk-basis-spread,
lem-weil-pbc-finite-projective-descends-flat-local, and
lem-weil-pbc-finite-type-algebra-noetherian. Their proof uses are documented in the
appropriate theorem docstrings. No missing statement prerequisite is deferred.

Edge cases checked before and after writing:

- Empty Y: the point-indexed cover is empty and every local condition is vacuous;
  the geometric-point clause has no inputs. Nothing assumes nonemptiness.
- E=0: choose equations 1, all prescribed valuations are zero, and the support is
  empty; the strict-local generator is 1.
- A disconnected normal scheme: equations and germs are defined on open sets and
  stalks without a global function field or global domain assumption.
- Negative coefficients are permitted in the main equivalence and represented by
  fraction equations. Only the effective theorem assumes nonnegative coefficients.
- Points outside the divisor and a field strict-local ring: all relevant
  coefficients vanish; the latter has no height-one primes and generator 1 works.
- a is fixed globally and positive; a=1 is included. The support conclusion does
  not rely on a zero or negative multiple.
- All characteristics are allowed; no excellence, regularity, separation,
  finite residue field or module-finiteness condition is added.
- Normality/Noetherianity of H are conclusions; K,H are in max u v. There is no
  smaller-universe test that might be empty and no forced equality of universes.

Searches performed:

- `msearch.py leanfinder`: “A Weil divisor on a Noetherian normal scheme is Cartier
  if and only if it is principal on every strict henselization”. Eight generic
  DVR/Dedekind/Weierstrass/localization hits; none is this theorem.
- `msearch.py loogle '"WeilDivisor"'`: 11 online cycle predicate/subgroup hits.
  The pinned project's `AlgebraicCycle/Basic.lean` has the cycle and pushforward
  API but not this newer online `IsWeilDivisor` predicate. Hence `hE` states its
  height-one support condition inline using the actual pinned declarations.
- `msearch.py grep 'WeilDivisor|CartierDivisor|strictHensel'`: zero hits.
- `msearch.py leansearch`: “Cartier divisors on normal schemes defined by local
  equations Weil divisor strict henselization”: eight normalization, henselian,
  and fractional-representation hits; no strict-local Cartier test.
- `msearch.py leansearch`: “Cartier divisor local fractional equations regular
  unit ratios open cover scheme”: eight open-cover/fractional-sheaf hits, no
  fraction-cover presentation with overlap-unit equations.
- `msearch.py loogle 'CartierFractionCover, CartierDivisor'`: zero hits,
  unknown identifier CartierFractionCover.
- `msearch.py grep 'CartierFractionCover|CartierDivisor|IsCartierWeilMultiple'`:
  zero Mathlib hits.
- Direct `rg` over Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and the upstream
  name index found no proposed declaration name and no exact strict-local test.
  The item-id search over WeilConjectures and Sheaf also had no hits. Concept
  searches found the existing affine height-one orders, which are reused.
- Concept searches of `dag/nodes` and direct reading found
  `def-sfb-integral-cartier-divisor` and `def-sfb-space-divisors`; their modules
  were read. The former requires global integrality, excluding this node's empty
  and disconnected cases. The latter is a Cartier divisor on an algebraic-space
  small etale model. Neither is fraction-cover presentation data on an arbitrary
  scheme; neither is copied or replaced here.
- `blueprint_refs.py search 'Weil divisor'`: zero blueprint matches;
  `blueprint_refs.py search 'Cartier fraction'`: zero blueprint matches.
  `blueprint_refs.py ancestor` confirms lem-per-artin-gabber-affine-curve.

The local Stacks texts for 0EBM, 0BE8, 025P and effective Cartier equations were
opened. The blueprint latest unit and ancestor proof were read. Source-tag checking
uses the local tags table; 02OX is the regular-meromorphic-section definition.

No STATEMENT-DISPUTED flag or source-statement correction is needed.

Validation: both delivered modules compile separately through the prescribed
`scompile.py`, including the sibling-module overlay, with no errors or unexpected
warnings. Expected sorry proofs remain in the four item theorems only.

## New nodes

`def-per-cartier-fraction-cover` defines the additional data needed to express the
node on arbitrary, possibly empty or disconnected schemes: an actual open cover
with regular numerator/denominator germs and overlap units, its normalized order
predicate, effective presentation and support, the Cartier-multiple predicate,
and the actual contracted etale/strict-local coefficients and principal condition.
Its sources are the node's own local Cartier definition, Stacks Divisors 02OX,
01WQ, 0BE3, 0BE8 and 0EBM, with the recorded pointed-etale presentation of 04GW.
It reuses the existing algebraic cycle and affine valuation definitions. The new
node records the raw LeanSearch, Loogle and grep search responses and the DAG and
project searches. This is presentation data, not a second abstract Cartier-divisor
quotient, not a private copy of IntegralCartierDivisor, and not an assumed canonical
pullback. All definition bodies are concrete and have no sorry dependency from
this delivery.

## Second reading by Q92

This is a separate rereading by the same dispatcher-started worker; the brief
forbids starting other agents. Independent review remains the maintainer's.
I reopened the node, both Lean files, the recorded dependency declarations and
source snippets and checked the numbered clause mapping above.

The important checks were the unchanged fixed a and exact normalized coefficients,
the empty/disconnected cases, actual pointed-etale presentation rather than merely
strict henselianity, the explicit contraction through the stalk map, effective
support as a union of closures, and the pointed lift and single non-zero-divisor
section. I revised the principal predicate to give the normal-domain/Noetherian
proofs existentially; thus the fraction-order API never hides a vacuous conditional
assumption. I also corrected a source-tag inherited from an unrelated presentation
example: 0B8Z concerns a line-bundle lemma and is not the source of the new cover
definition; the delivered docstrings cite 02OX and the node's explicit local
Cartier definition instead. No mathematical statement was changed.

Both files use `set_option autoImplicit false`; all universes and binders are
explicit. There are no local notations, local instances, private declarations,
`let` or `show ... from` statements, or lines exceeding 100 characters. The new
node's declarations all carry its blueprint tag, and all four postponed theorems
carry the item's tag and their natural-language proofs. JSON signatures are
extracted verbatim from the delivered modules. The original node differs only
in lean and its added new-definition statement dependency.

Dry-run repair: the current server schema also requires `import_flags` on the new
definition node. Added the empty list after the first preflight reported that sole
missing field; no Lean declaration or original-node field was changed.
