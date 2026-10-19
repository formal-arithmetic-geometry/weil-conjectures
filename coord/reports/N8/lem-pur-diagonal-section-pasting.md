## Worker report

The module `Sheaf.Paper.PurityDiagonalSectionPasting` states `WeilConjectures.PurityFiniteSetting.DiagonalPasting.diagonalSectionPasting`. Its conclusion `Statement` specializes `ModelStatement` to the prescribed coefficient ring and includes the diagonal pasting equation, compatibility with arbitrary compatible source and target opens, and the conditional equality with the ordered affine-space comparison on every compatible affine open chart triple. The node statement and proof are unchanged. All definition data are explicit existing constructions; only named theorem proofs are postponed. The upstream TensorStructure implementation note forbids forcing the concrete ModuleCat tensor instance to compare with the generic derivedTensor instance: the public tensor and tensorComparison helpers therefore use the existing derivedTensor bifunctor and its functorial maps explicitly, preserving the exact derived tensor while avoiding the documented kernel timeout.

Hypotheses and clauses:

- `P : PurityFiniteSetting.{u}` is exactly the recorded global algebraic-closure field, distinct coefficient prime, finite coefficient extension, and level at least one. The ring is the existing `P.Coefficient`, with its standard coefficient-universe lift. `comparedExponent` supplies the implied prime-to-characteristic annihilator; there is no new invertibility hypothesis.
- `X Y Z : Scheme.{u}`, `f : X ⟶ Y`, `g : Y ⟶ Z`, and the map `aZ` to the recorded field specify the schemes over k; the maps from Y and X are `g ≫ aZ` and `f ≫ g ≫ aZ`. `LocallyOfFiniteType` and `QuasiCompact` give finite type. Together with finite type of f,g this implies finite type of all three schemes. No absolute separatedness is imposed on X,Y,Z.
- `IsSeparated f/g` and `SmoothOfRelativeDimension d f`, `SmoothOfRelativeDimension e g`, with `d e : ℕ`, are exactly separated smooth morphisms of pure relative dimensions d,e. Auxiliary compactifications are supplied by Nagata over the resulting Noetherian bases, and auxiliary dimensions by base change and composition. The explicit Noetherian and morphism-property instances in the universally quantified open restrictions are consequences of the compatible open squares; they restrict no open subschemes allowed in the node.
- `D Λ P X` at Λ = P.Coefficient is the finite etale presentation. `SameProEtaleMap` compares the actual images of the displayed arrows under `(ProEtale.comparisonUpperStar ... X).mapDerivedCategory`. Thus asserted equalities are on the original small pro-etale site, whose object and morphism universes remain u+1 and u. This is the same canonical comparison-coordinate convention as the recorded cohomological-smoothness dependency. `comparedSectionPresentation` explicitly identifies the actual pro-etale derived section pullback with this presentation; `finiteComparedDualizing` is the normalized exceptional image of the coefficient unit.
- `finiteExceptionalComposition Λ` (specialized to `P.Coefficient`) is `conjugateIsoEquiv` of the explicit compact-support compositor under `rightDerivedUpperShriekAdjunction` and the actual `Adjunction.comp`. It is not an arbitrarily selected natural isomorphism. `sigma` uses the specified `Etale.dualizingComplexTensorMap`, whose source already has omega first, followed by the inverse component of this conjugate. Thus it includes exactly the symmetry required by the node's ordering of theta.
- `diagonalSection` is `Etale.sectionInvariant` of the first self-product projection and its diagonal. Its actual pro-etale presentation is the repaired section-invariant interface. `alpha` uses `finiteDiagonalRestriction Λ`, the coefficient-variable interface of `diagonalComparedRestriction`, with the inverse of the specified smooth dualizing base-change mate, followed by the section pullback compositor and normalized identity pullback.
- `a`, `s`, `i`, and `j` are actual `pullback.lift`/`pullback.map` constructions. `geometry` states the two genuine Cartesian squares, a followed by b equals the first projection of W, t followed by a equals s, and the two diagonal identities. In particular neither an arbitrary compatible open square nor the chart square (F,G) is assumed Cartesian.
- `gammaF` pulls inverse beta for (a,s) along the f diagonal and composes pullbacks. `gammaG` pulls beta for (p_g,f) along the graph section after the explicit pullback reassociations. `kappa` tensors precisely these input comparisons, uses inverse monoidal pullback, pulls back `sigma_(a,b)`, then transports along a followed by b equals p_gf. No endpoint-only comparison replaces these maps.
- `Equation` is exactly alpha_gf after kappa equals sigma_f,g after alpha_f tensor Lf*alpha_g, compared as actual pro-etale arrows by `SameProEtaleMap`.
- For arbitrary compatible open immersions `u'`, `v`, `w`, `openFactor` first factors a restriction through the target-open Cartesian base change. `openDualizing` uses that beta and the normalized etale comparison for the residual source-open factor. `openPair` restricts both factors of the self-product; `openSection` uses the preceding normalized comparison on their first projections and the diagonal factorization. `tensorRestriction` is precisely monoidal pullback followed by the pullback compositor for the commuting square. `OpenEquation` records commuting squares for all three alpha maps, sigma, kappa, gammaF and gammaG. For the last two it uses the actual openMiddle/openPair maps and the normalized exceptional restriction of omega_a and omega_b. This includes target-only, source-only, simultaneous, identity and empty open restrictions.
- `A r B`, `pr`, and `zero` use the existing affine space with coordinate set `ULift (Fin r)`, its projection, and its zero section. `q d e B` forgets the first d coordinates by `Fin.natAdd`; `first` projects to them by `Fin.castAdd`. `affineGeometry` is the genuine Cartesian square and its zero-section/projection identities. `zeroInvariant` is D_r with no orientation or twist. `nu` is inverse beta on the first factor, the composed-pullback identification on the second, inverse monoidal pullback, and pullback of the specified sigma_(q,P_e), followed by equality of the total projection. The construction applies in particular to every separated finite-type k-scheme B in the node.
- `differenceFirst`, `differenceSecond`, and `differenceTotal` have literal coordinate differences in the second factors; the total vector concatenates the x block before the y block using `Fin.addCases`. `chartGeometry` records etaleness, finite type, separatedness, projection equations, and zero-section equations. `etaleRestriction` is selected from the already recorded UNIQUE counit-normalized etale ambient locality comparison; its definition uses that precise normalizing property, not a mere existence of an isomorphism. `etaleSection` pulls this comparison along the specified section. In `ChartEquation` the first identification is the differenceFirst section comparison, the second is gammaG followed by the differenceSecond section comparison, and the output is the differenceTotal section comparison. Its equality is exactly kappa followed by the output comparison equals the two input comparisons followed by nu. `Statement` quantifies this on every compatible affine open triple, with no chart existence or orientation assumption.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting` and `WeilConjectures.AlgebraicGeometry.InvertibleExponent`: the fixed setting and `HasInvertibleExponent`; the main module states `WeilConjectures.PurityFiniteSetting.comparedExponent` directly.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`: `AlgebraicGeometry.ProEtale.finiteComparedDualizing`, `IsCohomologicallySmoothFiniteCompared`, and the exact finite quotient instance; the published specified tensor and beta maps come from `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps`.
- `Sheaf.Paper.PuritySectionInvariantCompared`: `comparedSectionInvariant`, `comparedSectionPresentation`, `comparedSectionInvariant_invertible`.
- `Sheaf.Paper.PurityDiagonalBaseChangeCompared`: `finiteDiagonalRestriction`, `diagonalComparedRestriction`, `diagonalComparedProEtale`, `comparedDiagonalBaseChange`.
- `Sheaf.Paper.PurityFiniteExceptionalComposition`: `WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition`, the relocated adjunction conjugate of the landed canonical `Etale.unboundedEtaleLowerShriekCompIso`; its normalization is checked against `pur9-def-upper-shriek-composition`.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `ProEtale.sfFiniteExceptionalAt`; `Sheaf.Paper.DerivedPullbackTensorHom`: the finite derived operations in intrinsic coefficient coordinates, with the recorded equivalence to the fixed-coefficient presentation.
- Mathlib: `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `Etale`, `pullback`, `pullback.lift`, `pullback.map`, `IsPullback`, `Adjunction.comp`, `conjugateIsoEquiv`; upstream `SmoothOfRelativeDimension`, affine space and its projection, zero section, reindex and homOfVector.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`: `existsUnique_etaleAmbientAdjointLocalityIso`, the dependency newly added to stmt_deps. It already has a landed Lean record; it uniquely fixes the etale exceptional comparison by its sum-extension and compact-support counit transpose.
- Derived pullback composition, monoidal pullback, smooth duality, and etale local normal form are imported for the formulas and the recorded proof plan. The canonical site, unit, tensor, and compact-support comparisons are those of the existing finite-coefficient framework.

Edge cases checked: empty schemes and empty opens; d=0, e=0, and d=e=0 (the same Fin/ULift/addCases definitions apply to empty blocks); identity restrictions and etale dimension-zero maps retain their normalized unit; n=1 is included, n=0 excluded exactly by the conventions; no excluded characteristic equals ell; no absolute separatedness of X,Y,Z; arbitrary compatible source opens do not force Cartesian squares; the coordinate proof factors through R and never uses the false assertion that the (F,G) square is Cartesian. Every chosen object is either an existing real construction or is uniquely specified by the locality theorem.

Searches: LeanFinder query `pasting diagonal section invariant dualizing complex smooth composition coordinate comparison` returned eight unrelated coordinate/manifold results. Loogle query `CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction.comp` returned generic conjugation results, not the item. Mathlib grep `diagonal.*(pasting|section)|section.*pasting` in CategoryTheory returned no match. LeanSearch query `smooth dualizing complexes diagonal section comparison compatible with composition` returned eight results including pullback.diagonal_comp and smooth composition, none the stated pasting theorem. Searches of `WeilConjectures`, `lean/Sheaf`, DAG titles and statement text found the existing individual ingredients and no declaration of the whole node. Source checks found the exact canonical unbounded compact-support compositor, normalized etale locality, pullback composition, and affine coordinate constructors, all reused here rather than recreated.

## Second reading by N8

This is the author’s self-reading, as required by the dispatcher brief; no independent
review is claimed. I opened the current shared module and node, the maintained
snapshot, the source thm-pur-composition-coherence proof Step 1, and the Q94 return
for 4c5d513513. The retained maintenance snapshot is older than the current shared
packet. I compared their signatures and constructions and adopted the current
shared source, which imports the published PurityFiniteExceptionalComposition.
No dependency module or new node is delivered in this retry. The item node changes
only lean; its mathematical statement, proof and dependency lists are unchanged.

The finite field, positive coefficient level, coefficient ring P.Coefficient, dimensions
d,e in Nat, separated finite-type smooth f,g, and finite-type base map aZ are all
retained. Statement supplies the source-implied exponent rather than adding a hypothesis.
D and SameProEtaleMap preserve the etale-origin presentation and actual pro-etale
map equality. Alpha is the specified inverse-beta diagonal restriction. Sigma is the
published omega-first tensor mate followed by inverse adjunction-conjugate composition.
Kappa uses the literal pullback maps a,s,i,j, both specified gamma maps, inverse
monoidal pullback, and pullback of sigma, with equality transport for ba=p_gf.

Equation is the stated alpha/kappa/sigma equality. OpenEquation retains seven
substantive equalities for compatible source/target opens, using target base change
and normalized source etale locality rather than assuming a Cartesian open square.
ChartEquation retains the explicit ordered coordinate differences and equality with
nu. The coordinate blocks use Fin.castAdd, Fin.natAdd and Fin.addCases. The etale
comparison is selected from the unique counit-normalized locality statement. All
twelve proof steps remain in the theorem docstring. No arbitrary comparison map or
True predicate replaces any asserted clause. All definitions have real data, all
theorems retain sorry proofs, and autoImplicit is false. Empty schemes/opens, identity
restrictions, d=0, e=0 and both zero remain included; n=0 is excluded by the stated
finite-stage conventions. The site/coefficients retain the u/u+1 size convention.

The generic helper experiment still timed out and is absent from the delivered module
and declaration list. The delivered declarations are identical to the newer shared
PurityDiagonalSectionPasting source; the only source changes credit N8 and
explain the explicit arguments at kappa. No mathematical refactor is claimed. The current
source explicitly fixes the scheme arguments and tensor factors at the expensive
kappa composition. The fresh full compile passed: sandbox name 49.0 seconds,
delivered library name 47.6 seconds, no diagnostics, default 60-second limit.
The earlier historical snapshot and generic variant timed out; their failures do not
certify the newer packet. Only the passing invocation certifies this packet.


## Fresh searches by N8

LeanFinder: `Pasting of diagonal section invariant comparison for composable smooth
morphisms and affine coordinate compatibility` returned eight affine-space and
affine-limit results (including AffineSpace.reindex_over_assoc and comp_homOfVector),
none the pasting theorem. Loogle: `CategoryTheory.Limits.pullback.diagonal,
CategoryTheory.conjugateIsoEquiv` returned zero hits. Mathlib grep through msearch:
`diagonal.*(pasting|section)|section.*pasting` in CategoryTheory returned zero hits.
Source rg for diagonalSectionPasting, diagonal/pasting and section/pasting found
no upstream theorem; shared Sheaf source contains this item’s own current module
and individual compositor ingredients. Upstream rg for the item id returned no
match. These searches were executed by N8 on 2026-10-18; the preceding search
paragraph is the retained author’s historical search record.

## Current validation

The prescribed scompile.py invocation on the single current module exited zero:
the published compositor overlay took 7.4 seconds; the sandbox-name check took
49.0 seconds; the delivered library-name check took 47.6 seconds. No errors or
warnings were printed. The previous five supporting modules are already published
and are not edited or redelivered. The declaration list and exact multiline main
signature were checked against the current module; lines fit within 100 characters.
There are no new nodes or dependency modules, and no statement correction.

The first dry run compiled successfully but preflight refused an unchanged module:
“the module is part of the delivery”. I added the implementation comment at kappa
and credited N8, then reran the prescribed dry run. No gate was patched or bypassed.

## Retained-packet repair validation, 2026-10-18

The required first fresh dry run of the retained packet passed: deliver2.py
--no-push reported commit 0bbfca2de8 passes preflight and compiles. Both the
sandbox-name and delivered library-name checks completed under the unchanged
60-second per-file limit. This is fresh evidence for the retained source, not a
claim inferred from the earlier report or maintenance snapshot. No compiler or
launcher tool was modified.

I reread the item, its source proof Step 1, the Q94 return for 4c5d513513, the
retained module, and the canonical dependency interfaces. The saved packet already
contains the explicit scheme and tensor-factor arguments at kappa and the generic
derivedTensor presentation. The fresh passing dry run confirms that this retained
repair addresses the returned sandbox compilation timeout. Following the repair
brief's instruction for a passing saved packet, I retained its Lean source.

The self-check again matched the fixed finite field and positive finite coefficient
level, separated finite-type smooth f and g with dimensions d and e, finite-type
base, and all three conclusions. Alpha is the inverse-beta diagonal chain; sigma
is the specified tensor mate followed by the inverse conjugate compositor; kappa
uses gammaF, gammaG, inverse monoidal pullback and the pullback of sigma_(a,b).
OpenEquation has the seven actual comparison equalities. ChartEquation uses the
ordered coordinate differences and nu, with normalized etale localization selected
from a unique characterization. Empty opens and schemes, identity restrictions,
and either zero-dimensional block remain included. All twelve proof steps remain;
all postponed proofs are named theorems, and definition data are explicit. The
verbatim signature, declaration record, 100-character line limit and autoImplicit
setting were checked. Relative to the current shared node, only lean differs.
No mathematical statement, dependency list, canonical map or theorem signature
was changed in this retry.


## Fresh retained-packet self-check and delivery, 2026-10-18

The first prescribed dry run in this repair session returned
`OK (dry run): commit 0585e1774e passes the preflight and compiles; nothing pushed`.
Both the sandbox module and library module compiled with the unchanged 60-second
limit. Following the explicit instruction for a passing saved packet, I retained
its Lean source; the earlier timeout is not treated as a passing validation.

I opened the current node, source proof Step 1, the N8 timeout return and the
Q94 semantic return for 4c5d513513, and reread the retained definitions and
canonical section, diagonal, exceptional-composition and etale-locality interfaces.
The self-reading checked Equation against the alpha/kappa/sigma equation,
OpenEquation against all seven comparison equalities, and ChartEquation against
the two ordered input difference comparisons, total output comparison and nu.
The fixed finite coefficient setting, positive level, natural dimensions,
separated finite-type smooth maps and finite-type structure map remain explicit.
The additional instances for compatible open restrictions are consequences of
those restrictions, including empty opens and identity restrictions. The zero
coordinate blocks use the same Fin constructors. Etale locality is chosen from
its unique counit-normalized characterization, and kappa uses the actual beta,
pullback compositor, inverse monoidal pullback and sigma maps.

The exact main signature matches lean.statement verbatim; autoImplicit is false;
all lines fit 100 characters; all twelve proof steps remain in the docstring;
there is no Prop := True predicate. Comparison against the current shared node
found only lean changed. Comparison against the current shared Lean source
found identical declaration bodies, with only the retained author credit and
implementation comment differing. No new node, dependency module or mathematical
statement correction is made in this retry. This is an author's self-check,
not an independent review. The fresh compile and preflight, rather than any
historical success in the retained report, are the validation for this packet.
