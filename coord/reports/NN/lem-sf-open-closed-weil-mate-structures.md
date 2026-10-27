## Worker report

Item: `lem-sf-open-closed-weil-mate-structures`, group NN, stage 2.
Module: `Sheaf.SixFunctors.OpenClosedWeilMateStructures`.
Declaration: `WeilConjectures.sf_openClosed_weil_mate_structures`.
This repairs the immutable returned head `82f63df1bb4a`. The saved packet was
first dry-run unchanged: commit `714961c3b6b` passed preflight and compilation.
The required semantic self-check confirmed the F1′ completion gap in the return;
the new completion clause repairs it. Earlier F1/F2 and ownership repairs below
are retained. This delivery contains only statements and real definitions;
the sole postponed theorem is the main declaration. Its docstring retains the
complete mathematical proof plan. The DAG statement and proof are unchanged.

### Repair of F1′: one integral mate through completion

The return found that the ordinary integral mate and reduction clauses were not
linked to the tower integral mates used by rationalization. Added
`sfCompletionOpenClosedWeilMateAssertions` as a main-theorem conjunct. It uses
`OpenClosedScalarMateLift` from the actual `constructibleIntegralPullback`
functors to `PurCompactSupport.pull (completed l E)` along the three full
inclusions of `sfIntegralConstructibleCategory`. The direction is tower to
ordinary; all comparisons are invertible. This is precisely an identification
of the ordinary maps with the tower integral maps, and links the existing
finite reductions through that integral mate to rational and common-stage mates.

The five comparisons for j, i, FX, FU and FZ are **not free isomorphisms**.
`sfCompletionPullbackComparisonPin` quantifies over the published
`IntegralCompletedComparison.Comparison`, whose data include finite generator
normalization, every derived-limit projection, naturality and the shift
normalization. For every complete pbc representative M of every constructible K,
and every identification e of its coefficient transport with K, it pins the
ordinary-to-integral component s.inverse by the literal equation

    ordinary(e) ; s.inverse
      = rho.inverse ; transport(strictUnit ; towerIso) ; gamma.inverse ; integral(e).

Here strictUnit is `pbcActualStrictCompletedPullUnit`, towerIso is the existing
`IntegralCompletedComparison.towerIso` fixed by its completion-unit equation,
and gamma is **that given normalized Comparison's** gamma. This retains the
reflector/strict-tower passage in their actual orientations. The assertion is
universal over all five Comparison records, never a bare existential gamma.
There is no added Comparison hypothesis in the main theorem.

The coefficient comparison rho is itself pinned: the ordinary module rho₀
preserves every actual `pbcActualModuleUnitSection` as the corresponding
`proEtaleRingModuleUnitSection`; its derived rho commutes with the published
`pbcActualPullComplexCounit`, exact restriction factorization and the termwise
rho₀ on every complex. These specify the canonical ordinary transport, so an
arbitrary rho cannot cancel a twist of s. An explicit coverage clause says
every integral constructible K has a complete pbc coefficient representative;
normalization therefore tests the whole category, including zero and torsion K.
These are assertions about canonical isomorphisms, not definitions choosing data
from an uncharacterized existence theorem.

`OpenClosedScalarMateLift` fixes the inverse open comparison as the inverse
mate of sj and fixes the forward closed comparison as the mate of si.inverse.
Its words give the b/d transport from `sfConstructibleIntegralFrobeniusSquare`
(built with `zlIntegralPullComp`) to the exact `zlAmbientFrobeniusSquare`
(built with `geometricPullComposition`). The same words identify both units,
both counits and the literal alpha/c composites. Thus they supply the specific
b/d transport missing from the returned head, as well as the completion passage
of proof step 6. The existential source adjoints are invariant under their
unique adjunction-compatible isomorphisms, as in the accepted rationalization
clause, so its separate existential adjoints represent the very same mate words.

Only two helpers are added to this item's module and lean.declarations; neither
is an independent new mathematical notion requiring a new DAG node. They use
`IntegralCompletedComparison` from the already cited
`def-pod-integral-completed-comparison-data`; the public import is now explicit.
The theorem docstring explains the new completion and b/d identification.
The node statement, proof and proof dependencies remain unchanged.

### Repair of F1: rationalization of the actual mate words

`sfRationalizationOpenClosedWeilMateAssertions` now occurs in the main theorem.
Its integral pullbacks are exactly `constructibleIntegralPullback` for j, i,
and the three geometric Frobenius maps. These are the integral functors used
by `rationalDerivedPullback_existsUnique`, rather than an unrelated ambient
pullback presentation. `sfConstructibleIntegralFrobeniusSquare` fixes b and d
using `zlIntegralPullComp` and `zlFrobenius_naturality`, the same fixed integral
compositors whose localizations define `fieldWeilPullSquare`.

The clause supplies integral open and closed adjunctions on those constructible
categories. Their left/right adjoints are determined up to their unique
adjunction-compatible isomorphisms; no data definition chooses from a mere
existence assertion. The integral alpha and c are fixed by `openClosedAlpha`
and `openClosedC`, and asserted to be isomorphisms. The three comparison
functors are literally `sfRationalConstructibleLocalization l E X/U/Z`.
The j, i, FX, FU, FZ localization comparisons are natural isomorphisms with
components HEq to identities under the recorded rational pullback object
identification. Thus no free automorphism can be absorbed in them.

`OpenClosedScalarMateLift` fixes the inverse open operation comparison as the
inverse mate of sj and fixes the forward closed operation comparison as the
right mate of si inverse. Its `OpenClosedScalarMateWords` conjunct then states
preservation of b, d, both adjunction units, both counits, alpha and c as
literal equations of arrows under these pinned comparisons. This implements
the return's first permitted repair: a rationalization clause on the same
integral functors that the rational stage localizes. It makes no assertion
that the two integral presentations are definitionally equal.

### Repair of F2: remove copied completion assertions

The return explicitly allowed dropping the copies. The earlier repair removed the copied
`sfCompletedMatePullbackAssertions`, `sfClosedMateStrictReconstruction` and
the old, unlinked `sfCompletionOpenClosedWeilMateAssertions` conjunct.
The F1′ clause now reuses the last name for the explicit mate transport above. In particular the statement no longer repeats Nonempty Comparison,
the completion-unit IsIso, an unrelated existential open Operations record,
or the direct-image reconstruction theorem.

The integral mate formulas still use the actual ordinary completed-ring
module adjunctions on the recorded derived-complete constructible inputs.
`sfCoefficientOpenClosedWeilMateAssertions` still preserves their actual
mate words, units and counits through every positive finite reduction and
coefficient inclusion. The new F1′ clause above links the actual completion comparison to these
ordinary maps; it does not restore the removed unlinked reconstruction copies. The mathematical node
and every original statement dependency are retained.

### Finite presentation advisory

Added `sfFinitePresentationOpenClosedWeilMateAssertions` at every positive
level. It applies `OpenClosedScalarMateLift` from the finite ringed presentation
to the finite intrinsic presentation along the identity functors. Its five
pullback comparisons are the published `sfFiniteRingPullIso`, obtained by
termwise derivation of `PurCompactSupport.finitePullbackIso`. The open and
closed operation comparisons are their fixed adjunction mates. The clause
therefore explicitly links both j_! and i_* and their units/counits, as well
as b, d, alpha and c, across the two finite presentations.

### Hypotheses

| Node hypothesis | Lean rendering |
| --- | --- |
| Global finite field and its closure | `D : FiniteFieldDatum.{u}`, `D.geometricFiber` |
| Prime ell different from the characteristic | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` |
| Finite E/Q_ell in its chosen algebraic closure | `E`, its Field/Algebra/FiniteDimensional instances, `Ω : Type v` with IsAlgClosure and `_ιE : E →ₐ[Padic l] Ω` |
| Valuation ring and uniformizer quotients | The published `Padic.coefficientExtensionIntegers`, uniformizer, and `coefficientExtensionRing l E (n+1)` |
| X0 separated finite type over k0 | `X₀ : Over (Spec (.of D.k₀))`, LocallyOfFiniteType, QuasiCompact and IsSeparated on its structure map |
| Complementary open and closed immersions | `j₀`, `i₀`, IsOpenImmersion, IsClosedImmersion, and `_hij : Set.range i₀.left.base = (Set.range j₀.left.base)ᶜ` |
| Inherited finite-type U0 and Z0 | LocallyOfFiniteType and QuasiCompact on their structure maps, inherited from their immersions into finite-type Noetherian X0 |
| Geometric fibre maps | `zlFiberMap D j₀/i₀` |
| Geometric Frobenius, including semilinearity | `(D.geometricFrobenius T₀).hom`; no k-linearity assumption |
| The specified bounded constructible categories | `intrinsicFiniteTorsionConstructible`, `sfIntegralConstructible`, `sfRationalConstructibleCategory`, and `generalAlgebraicallyClosedConstructibleCategory` |

All universes and binders are explicit; `autoImplicit` is disabled. The scheme
universe u and coefficient-closure universe v are independent. The small
pro-etale site's distinct object/morphism universes are preserved. Fibre open
immersion instances and prime invertibility are constructed from the stated
hypotheses, not assumed additionally.

### Clauses

1. `OpenClosedWeilMateAssertions` pins alpha.hom to inverse `mateEquiv` of b.hom
   and c.hom to `mateEquiv` of d.inv. Its next equations spell out the three
   factors of each component using the actual aj/ai unit and counit. Both
   transformations are natural isomorphisms; a is alpha.inv.
2. Its normalized open equation is FX(epsilon_K) = a_j*K followed by j_!(b_K)
   followed by epsilon_FXK. Its closed equation is FX(eta_K), followed by c_i*K
   and i_*(d_K), equal to eta_FXK. Lean uses left-to-right composition `≫`.
3. `RestrictedOpenClosedWeilMateAssertions` gives the same words and normalized
   equations on finite and integral constructible objects, and invertibility
   there, without adding integral or finite Weil-pair assertions.
4. `sfFiniteOpenClosedWeilMateAssertions` instantiates the finite operations
   by the exact intrinsic derived open/pullback and actual K-injective direct
   image, with the specified ordinary transported adjunctions and canonical
   composition square. The new finite-presentation clause connects this with
   the finite ringed operations used by coefficient reduction.
5. `sfIntegralOpenClosedWeilMateAssertions` uses the completed coefficient
   sheaf, `PurCompactSupport.openDerivedAdjunction`, the ordinary
   `proEtaleRingDerivedAdjunction`, and `zlAmbientFrobeniusSquare` on exactly
   the recorded derived-complete constructible domain.
6. `OpenClosedScalarMateWords` includes b/d transport, comparison invertibility
   on the indicated domain, all four adjunction maps, and the alpha/c words.
   `sfCoefficientOpenClosedWeilMateAssertions` supplies these for every integral
   quotient reduction, every quotient transition, and every finite completed
   coefficient extension. Finite-to-finite reduction uses the finite-Tor
   constructible domain; no preservation for arbitrary nonflat inputs is added.
7. The new rationalization clause is described under F1. Rational finite scalar
   extension additionally uses `sfRationalScalarOpenClosedWeilMateAssertions`,
   with the published `rationalPullbackScalarComparison` localized from the
   fixed integral coefficient comparison.
8. `sfCommonStageOpenClosedWeilMateAssertions` applies the same fixed-mate
   transport along each actual finite-stage inclusion into the pair category.
   The pullback and Frobenius comparisons have identity-pinned components
   under `commonStagePullbackObject`; they cannot absorb an unspecified twist.
9. The rational and common-stage `OpenClosedWeilMateAssertions` conjuncts use
   the actual field/common-stage adjunctions. For every K and every isomorphism
   theta : FX(K) ≅ K, they assert invertibility of the displayed theta_A and
   theta_C words and give exactly the two equivariant counit/unit squares.
   No triangle, connecting map, or triangulated category of Weil pairs is added.

### Dependency declarations and ownership

All original fourteen dependencies and the ten additions in the returned
packet remain. The missing landed definition owners
`def-sp-open-coefficient-adjunction-data`, `def-zl-weil-ind-sheaf-category`,
and `def-weil-pbc-bounded-constructible-tower` are now explicitly cited.
The first supplies the general open adjunctions, the second supplies
`zlFiberMap`, `zlFrobenius_naturality`, `zlIntegralPullComp`, `zlPull` and
`zlFrobeniusSquare`, and the third supplies `pbcDerivedExtend` and its scalar
adjunctions. The unneeded derived-limit/scalar-unit/calculus-coherence
references identified by the return disappear with the copied completion
conjuncts, so no artificial statement prerequisite was added for them.

| Module | Used declarations |
| --- | --- |
| `Sheaf.Paper.FiniteFieldFiber` | `FiniteFieldDatum`, geometric fibres |
| `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` | finite quotient rings and their finiteness |
| `Sheaf.AlgebraicGeometry.FrobeniusDetailed` | geometric Frobenius |
| `Sheaf.Paper.DerivedPullbackTensorHom` | `constructibleIntegralPullback`, `rationalDerivedPullback`, common-stage pullback and scalar comparisons |
| `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` | intrinsic finite constructibility |
| `Sheaf.Paper.FiniteTorAmplitudeSites` | the actual intrinsic finite-Tor predicates |
| `Sheaf.Paper.SfIntegralConstructible` | integral predicate and full category |
| `Sheaf.Paper.SfRationalizationKaroubi` | actual rational category and `sfRationalConstructibleLocalization` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | pair category and actual finite-stage inclusions |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | completed/finite coefficients, pull/push/open operations and adjunctions |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | fixed scalarPull, properComparison, openComparison, reduction, finiteQuotientChange, completedChange, finitePullbackIso |
| `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations` | intrinsic pullback and exact termwise derivation |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange` | intrinsic derived open operation and canonical pullback square |
| `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction` | `exceptionalOpenAdjunction` |
| `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` | `sfIntrinsicConstantModuleAdjunction` |
| `Sheaf.Paper.FieldWeilShriekShiftData` | actual field open/proper functors, adjunctions, and pullback square |
| `Sheaf.Paper.CommonStageWeilShriek` | actual common-stage open/proper functors and adjunctions |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | ambient completed Frobenius and its fixed square |
| `Sheaf.Paper.SfWeilSheafComplex` | rational/common-stage Frobenius, prime-invertibility instances |
| `Mathlib.CategoryTheory.Adjunction.Mates` | `mateEquiv`, `conjugateEquiv` |

The five new definition nodes below provide exact existing attachments for
previously theorem-owned or unowned plain constructions. No Lean construction
is copied. Original proof-dependency modules remain normal imports, including
the integral open reconstruction theorem. The retired PbcDescentFunctors
proof import remains replaced by the canonical upstream StageSystem.Functor.
An independent traversal of statement and proof dependencies including every
new node found no path back to the item. No new theorem dependency is added.

### Edge cases and searches

Checked U=X/Z empty, U empty/Z=X, empty X, zero K, the smallest positive quotient
(exponent n+1=1), repeated quotient levels, identity finite coefficient maps,
arbitrary Weil isomorphisms, and semilinear geometric Frobenius. The localization
comparisons are identity-pinned even when the integral input is torsion or zero;
no rational faithfulness assumption is imposed. Every fixed adjoint comparison
is characterized by its mate, so identity cases cannot absorb automorphisms.

Retained the saved searches for the item: LeanFinder on Frobenius open/closed
mates returned eight generic hits; Loogle on mateEquiv/conjugateEquiv returned
only generic infrastructure; Mathlib grep found the abstract mate equations;
project searches found no declaration of this four-stage assertion. Repeated
searches for the new ownership attachments are recorded verbatim by query and
result in each new node's mathlib_searches: LeanSearch and LeanFinder (eight
hits each, no exact match), Loogle (zero hits), Mathlib CategoryTheory grep
(zero hits), local rg across WeilConjectures and Sheaf, a full recorded-name
DAG scan, and blueprint_refs searches. The recorded declarations already
exist in Sheaf and are reused unchanged. These searches do not justify new
copies of their constructions.

No `STATEMENT-DISPUTED` issue or statement correction is needed. All compiles
and dry runs use only the prescribed wrappers. A compiler diagnostic in the
new square was repaired by making the inherited prime instances explicit and
using the published comparison's transparency setting. Validation of the
final packet is recorded after the dry run below.

## New nodes

`def-sp-finite-intrinsic-pullback` attaches the existing transported finite
intrinsic pullback and its exact derived functor in
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`. The general
arbitrary-ring operations node does not identify these finite transported
constructions. The attachment states the actual realization and compositor.

`def-sp-finite-intrinsic-open-square` attaches the existing derived open functor
and pullback-composition square in
`Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`. This owns the plain
constructions used here without citing the open-exchange theorem.

`def-sp-finite-intrinsic-open-adjunction` attaches the already defined
`AlgebraicGeometry.Scheme.exceptionalOpenAdjunction` in
`Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`; the old only owner
was the theorem node prop-exc-open-adjoint. The statement specifies the
transported and termwise-localized ordinary adjunction.

`def-sp-finite-intrinsic-direct-adjunction` attaches the existing
`sfIntrinsicConstantModuleAdjunction` and normalized realization comparisons
in `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`. Its constant-unit
section normalization fixes the comparison before right derivation.

`def-sp-coefficient-mate-comparisons` attaches the existing scalarPull,
properComparison, openComparison, reduction, finiteQuotientChange,
completedChange, finitePullbackIso and finiteOpenIso in
`Sheaf.Paper.IntegralCompactSupportCoefficientComparison`. These plain
constructions were only attached to a theorem node. Their definition node
specifies the actual scalar-adjunction mates and finite presentation
comparison, without claiming the comparison theorem.

All five are `existing: true`, have no new Lean module, cite their constituent
definitions, and use the item's blueprint source and ancestor. Searches
located no existing definition node for these specific presentation data;
the theorem nodes carrying some plain definitions are not substituted as
statement prerequisites. The maintainer supplies the independent second
reading as specified in the dispatch brief; no independent agent was started.

## Repair self-check and validation

Compared the packet with the current read clone: only lean and permitted
stmt_deps additions differ on the item; its original statement, proof and
proof dependencies are unchanged. All new nodes have exactly matching inline
citations and dependency lists. The main Lean signature matches lean.statement
verbatim, all nineteen auxiliary definitions are recorded, there are no
lines above 100 characters, and the only sorry is the main named theorem.

The earlier repaired module and existing-declaration probe both compiled through the
prescribed delivery wrapper with no unexpected warning. The earlier repaired
packet's preflight caught a missing inline citation for the abstract derived
category in the new open-adjunction node; that citation is fixed. Stored
existing signatures now begin with def/abbrev as the verifier expects. The
final dry run and push are performed with all these fixes present.

The F1′ self-check additionally read the actual Comparison structure and gamma
projection/shift normalizations, its strict-tower/reflector comparison, the
ordinary pullback representative counits, both module unit-section definitions,
and constructibleIntegralPullback's exact restriction. The blueprint's integral,
rational and Weil paragraphs were read together. The new normalization was
checked for identity morphisms, empty schemes, zero/torsion objects and arbitrary
coefficient representatives e: the equation conjugates by e rather than forcing
coefficient transport to be definitionally the identity. No additional scheme
or coefficient universe equality is imposed.

For F1′ the isolated completion-clause diagnostic compiled in 24.9 s (sandbox)
and 28.4 s (library check). Whole-file checks exposed expensive elaboration of
the previously delivered rational scalar comparison clause. Its five normalized
comparison isomorphisms are now bound with their explicit types and heterogeneous equalities
identifying them with the exact published rationalPullbackScalarComparison.
This is the same assertion: each new bound is uniquely fixed by equality with the published isomorphism,
and the mate words still use exactly those published maps. It avoids substituting
large choice terms repeatedly into the generic mate-transport predicate. No
normalization, coefficient case or functor has changed. The full delivered
module is checked as one file under the unchanged 60-second limit; scratch
profiles and diagnostics are not delivered.

Final F1′ compilation: the complete delivered module passed the prescribed
scompile.py server confirmation in 53.7 s, with no unexpected warning. The
sandbox compile also passed in 54.9 s; the wrapper's first local library check
hit the fixed limit, so the wrapper performed its normal current-server
confirmation successfully. No timeout limit or tool was changed. Final checks
confirm the verbatim main signature, all nineteen helpers recorded, exactly one
named theorem sorry, no diagnostic commands and no lines above 100 columns.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
