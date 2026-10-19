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

## New nodes

`def-pur-finite-exceptional-composition` owns the finite-coefficient exceptional
compositor used by sigma. Its body is the adjunction conjugate of the specified
`Etale.unboundedEtaleLowerShriekCompIso` using the actual composite adjunction.
The source is now the existing document
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/thm-pur-composition-coherence.proof.md`,
proof Step 1, together with the recorded `pur9-def-upper-shriek-composition`
normalization. The retained LeanSearch, LeanFinder/Loogle and source searches
found no other DAG owner or exact finite-coefficient declaration.

## Dependency modules

`def-pur-co-smoothness`: the recorded legacy comparison module cannot be imported
with the actual finite-coefficient section pullback: the two API families collide
on `AlgebraicGeometry.ProEtale.derivedComparisonAdjunctionPlus`. Changing the
legacy module's TorAmplitude import instead breaks its landed importers, as the
return at e70ddfb5a03d reports. This packet therefore leaves that module untouched
and supplies `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`, using the
FiniteCoefficient TorAmplitude family and seven distinct declaration names:
`finiteComparedCoefficientFinite`, `finiteComparedCompactification`,
`finiteComparedDualizing`, `finiteComparedInvertibilityClause`,
`finiteComparedTensorClause`, `finiteComparedBaseChangeClause`, and
`IsCohomologicallySmoothFiniteCompared`. Their bodies and mathematical signatures
are the retained comparison-coordinate construction, with references renamed
consistently. The three clauses still use the actual pro-etale Dctf inverse, the
specified tensor counit mate for every representative, and the specified
base-change counit mate for every finite-type Cartesian change of base. No
absolute separatedness or geometric smoothness hypothesis is added. The node's
lean record points to this module and explains the API collision.

`def-pur-section-invariant`: `PuritySectionInvariantCompared` imports that finite
interface and uses `finiteComparedDualizing` for the actual pro-etale section
pullback. Its explicit etale presentation and two-sided Dctf inverse statement
are retained. This repairs the legacy import collision without introducing any
arbitrary comparison object.

`lem-pur-diagonal-base-change`: `PurityDiagonalBaseChangeCompared` uses the same
finite interface. Its pro-etale endpoint now names `finiteComparedDualizing`.
The two specified beta mates and inverse-beta/section-compositor diagonal chain
are unchanged. Its generic `finiteDiagonalRestriction` remains the map used by
alpha in the main module.

## Repair of returned delivery e70ddfb5a03d

R1 (H10/H13): removed the sandbox replacement for
`CohomologicalSmoothnessComparison.lean`; the existing landed file is not part
of this delivery and retains its original legacy TorAmplitude import byte for
byte. The new finite-family module and all seven distinct names are listed
above. `PuritySectionInvariantCompared` and the item explicitly import it;
the section and diagonal endpoints use its dualizing object. The returned
failures of TensorTraceTranspose and CohomologicalSmoothEtaleLocality
(`laxMonoidal_Q`) and TraceTransposeBaseChange
(`derivedComparisonAdjunctionPlus`) arose from changing the original owner.
That change is absent from this packet, so their original import graph and
original declaration names are preserved. No importer outside this packet is
edited. Source searches over Mathlib, WeilConjectures and lean/Sheaf found no
collision with any of the seven new names.

R2 (H12): changed only the new compositor node's `source.document` to the existing
proof document named above, opened it, and checked its Step 1 against the
compositor definition. It uses the exceptional composition comparison in the
dualizing-object tensor identity, exactly the role of this canonical conjugate.

## Second reading by Q21

This is the author's self-check; the maintainer supplies the independent review.
I reopened the item node, all five modules and the new definition node against
the return and the current server source. The item retains its fixed positive
finite coefficient stage, arbitrary finite-type schemes over the fixed field,
separated smooth finite-type f and g of dimensions d and e, and the actual
composite. `Statement` specializes `ModelStatement` to P.Coefficient using only
the source-implied invertible exponent. `Equation` uses alpha from the diagonal
inverse-beta chain, sigma from theta followed by inverse adjunction conjugation,
and kappa from gammaF, gammaG, inverse monoidal pullback and pullback of sigma.
The explicit schemes and factors at the formerly expensive tensor comparison
in kappa remain intact.

`OpenEquation` still asserts all seven genuine commuting equalities (three
alphas, sigma, kappa and two gammas), for arbitrary compatible source and target
opens. It factors through target base change and normalized source-open
locality; it never assumes the whole compatible open square Cartesian.
`ChartEquation` still uses the ordered literal coordinate differences,
the uniquely counit-normalized etale exceptional comparison, and the specified
nu of the affine tower. Neither compatibility predicate is True. No arbitrary
comparison is quantified in place of the specified arrows. The twelve proof
steps in the main theorem docstring are retained verbatim.

The finite co-smoothness repair changes only the API family and declaration
names. Tensor invertibility still has its inverse in pro-etale Dctf; the tensor
and beta conditions still use the actual canonical counit mates. The section
invariant is the actual pro-etale derived pullback of that dualizing object;
the explicit comparison-site presentation and diagonal inverse-beta chain
are preserved. The new compositor is actual adjunction conjugation, with no
bare existence choice. All definition data are real constructions; every
postponed theorem proof is sorry. Every universe and variable remains explicitly
bound under autoImplicit false. The small-site object/morphism universes are
u+1/u and coefficient universe u+1. Edge cases d=0, e=0, both zero, empty schemes,
empty opens and identity restrictions retain the same Fin blocks, zero sections,
unit normalizations and universal-product formulas. The positive level excludes
only n=0 as in the node. No node statement or proof is changed.

## Historical validation

The repaired five-module packet passed the prescribed scompile.py invocation
with exit code zero and no errors or warnings. The wrapper checked every file
separately, in dependency order, including temporary-name and delivered-library
checks. It retained the standard 60-second Lean limit after slot acquisition;
reported wall times also include waiting for a slot. The main delivered-library
check reported 44.5 seconds. Literal node signatures, the 100-character line
limit, unique module ownership, dependency field isolation and existence of the
corrected source path were checked. The original comparison file is absent from
the packet, so this repair has no edit to the three returned landed importers
or their original comparison dependency.

The required initial saved-packet dry run passed at cd7587906e. It still
contained both defects identified by the independent return, so it was not pushed.
The changes above repair R1 and R2 before delivery.

The repaired deliver2.py --no-push run passed compilation and server preflight
with `OK (dry run)` at b1d7e34f73. Its staged file list contains
CohomologicalSmoothnessFiniteComparison and excludes the original
CohomologicalSmoothnessComparison. The final author check confirms that R1's
seven renamed declarations, both explicit imports and the lean.note are present;
R2's source.document is the existing proof file. The mathematical statements,
canonical constructions and twelve-step proof plan are unchanged. The final
push uses the prescribed delivery wrapper against the current main branch.


## Repair of the incomplete review at 55255b8ef7a2

The return requests a recorded compiler replay; it reports no mathematical
mismatch. The retained packet was first tested unchanged with the prescribed
`deliver2.py Q21 lem-pur-diagonal-section-pasting --no-push`. On 2026-10-18
that run exited zero and printed:

```
OK (dry run): commit 58f8c1813c passes the preflight and compiles; nothing pushed
```

This is fresh execution evidence, not an inference from the historical validation
above or the maintenance handoff. The wrapper compiled all five delivered files
separately, in dependency order, including sandbox-name and library-name checks.
Its progress reached the library check of PurityDiagonalSectionPasting and then
server preflight succeeded. The wrapper rejects errors, timeouts and unexpected
warnings before printing OK. Each invocation retained the standard 60-second limit.

The author's required self-check reopened the node, all five modules, the new
compositor node, the source proof Step 1 and the earlier Q94 return. Alpha remains
the diagonal inverse-beta restriction; sigma remains the specified tensor mate
followed by inverse canonical adjunction conjugation; kappa remains the two input
comparisons, inverse monoidal pullback and pullback of sigma. The seven open
naturality equations and the ordered affine difference-coordinate equality remain
substantive. All twelve proof steps, all hypotheses and all coefficient/site
universes are retained. The dependency modules keep their distinct finite-family
names and do not replace the legacy comparison module. The empty and zero-dimension
cases checked above remain included. Every recorded principal signature was
compared literally from its declaration keyword with its source, and all five
files satisfy the line limit.

No Lean source or mathematical node field was changed in this retry. The delivery
wrapper compared and rebased the retained packet against current newtargets-dag;
the dependency copies still change only lean, and the item's only other delta is
its previously documented added statement dependencies. This report records the
missing replay and the fresh self-check. The maintainer's independent mathematical
review remains the independent review; this section does not claim that the author
performed it.
