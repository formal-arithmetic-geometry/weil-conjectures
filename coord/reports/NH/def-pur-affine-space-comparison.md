## Worker report

Module: `Sheaf.Paper.AffineSpacePurityComparison`.
Main declaration: `AlgebraicGeometry.ProEtale.AffineSpacePurity.affineSpacePurityComparison`.
The module constructs the ordered comparison recursively. Its data are actual maps and
isomorphisms; it does not choose a purity isomorphism or specialize smooth purity.
The source was read in the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/def-pur-affine-space-comparison.md`
and compared with the DAG's expanded ordered-composite statement. No statement correction,
new independent notion, or dependency replacement is made.

The following matches every input and clause of the node to its Lean expression.

| Node clause | Lean expression |
| --- | --- |
| Finite purity setting, algebraic closure of finite field, ell different from p, finite extension, positive quotient level | `P : WeilConjectures.PurityFiniteSetting.{u}`. The existing `AffineLinePurity.Ring P` is used, with its existing `ringEquiv P` to `P.Coefficient`; its zero-based index is `P.level - 1`, not an extra ramification restriction. |
| Separated finite-type k-scheme Y | `aY : Y ⟶ Spec (.of P.field.k)`, `[LocallyOfFiniteType aY]`, `[QuasiCompact aY]`, `[IsSeparated aY]`. No smoothness or affineness of Y is assumed. |
| X_0=Y, X_(d+1)=A1_(X_d), p_0=id, p_(d+1)=q_d≫p_d | Existing `iteratedAffineLine Y d` and `iteratedAffineLineProj Y d`; `lastProjection Y d` abbreviates the existing affine-line projection. These definitions make the zero stage literal and fix the order of adding coordinates. |
| Polynomial projections separated finite type; every coordinate stage finite type over k | `projection_geometry`, `tower_geometry`, the local compactification and morphism-property proofs extracted from them. Compactifiability is proved in its named obligation using the projective-line compactifications, not imposed as an input. |
| K in Db_ctf | `K : DerivedCategory.Plus ...`, the ordinary representative `Ke`, `hKe : Etale.DerivedCategory.constructibleFiniteTor ... Ke`, and `eK : (comparison ...).obj Ke ≅ K.obj`. On these Noetherian schemes the recorded finite-Tor/origin comparison identifies these coordinates with the node's intrinsic domain. Bounds, constructibility, and finite Tor amplitude are retained. |
| Witnessed bounded-below etale origin | The original pair `(Ke,eK)` is retained. For exceptional images, `stageEtale` retains Ke at zero and uses `exceptionalEtale`, the actual etale right adjoint applied to Rnu_*K, at positive stages; `stageComparison` uses eK at zero and the defining `exceptionalEtale_eq` at positive stages. No arbitrary antecedent is selected. |
| alpha_d on the origin class, independent of witnesses | `originCompositionAmbient A f g` is used at the underlying origin object. Its components are the recorded compact-support compositor on the full ambient-morphism origin category. Naturality under the identity between two witnesses is precisely the dependency's independence clause. |
| c_d inverse, obtained by conjugating alpha through pasted adjunctions | `compositionInverse`: transpose `(alpha.inv) ≫ Rg_!(epsilon_f) ≫ epsilon_g` through `rightDerivedUpperShriekHomEquiv (f ≫ g)`. The argument is literally the pasted counit, with the recorded inverse compositor. This is the inverse right mate in the stated direction, with no unspecified natural isomorphism. |
| A finite annihilating ell-power a>=1 | `annihilates P` supplies ell^(level+1)=0; the chosen exponent is positive at every positive level. `exponentUnit` supplies its invertibility on every k-scheme from the existing `primeUnit`. |
| B_a,T and its canonical comparison with A_T(1) | `shiftedLine` uses the existing `Etale.ordinaryFiniteLine`, followed by shift 2 and the existing site comparison. This is the finite-root-sheaf presentation of the same Tate line, not a second definition of a sheaf. |
| Canonical Tate-line pullback, inverse comparison followed by ordinary root pullback | `shiftedLinePullback`: `(VectorIntegrationSite.pullback ...).app ...` inverted, followed by the existing `comparedLinePullback`. `lineCoefficientIso` identifies the recorded affine-line coefficient with this same shifted finite line by its actual affine-chart pullback. |
| Arbitrary ambient tensor input and finite Tate tensor powers | `twistAction` applies the recorded `derivedTensor` to the shifted line d times. `tensorReassociation` uses `actionPullbackIso` to iterate `leftDerivedUpperStarTensorIso` and the canonical Tate-line pullback in each factor. All complexes in this construction are arbitrary ambient complexes; no extra boundedness restriction is placed on the tensor comparison. |
| Nonnegative twist additivity and shift 2d | The d-fold tensor of B_a[2] is the finite tensor-power presentation of M(d)[2d]; the zero action is the identity. The ordered recurrence fixes the tensor parentheses. All shifts are even, so regrouping adds 2d+2 without an odd-shift sign. |
| I_(d,K) from total pullback and tensor/shift identifications | `sourceReassociation` is an explicit iso from `orderedSource ... (d+1)` to `lineSource ... (orderedSource ... d)`. Its positive raw composite uses the pullback compositor, the inverse iterated tensor comparison, and inverse `lineCoefficientIso`. The zero case applies the canonical identity-pullback iso. `sourceReassociation_existsUnique` uniquely fixes the hom by HEq with this fully constructed raw composite, transporting its definitionally equal source coordinates without choosing an arbitrary iso. |
| Lp_d*K(d)[2d] | `orderedSource P Y d`: at positive d, the actual pullback along p_d followed by the Tate tensor action on X_d itself; at zero it is literally identity. It is not an iterated-pullback source left unidentified with the total source. |
| Rp_d!K, identity normalized at zero | `exceptional P Y d`: at positive d the recorded transported `rightDerivedUpperShriek`; at zero the identity functor. `lineExceptionalIso` makes only the canonical change from the affine-line compactification to the standing chosen compactification, via uniqueness of the etale right adjoint. |
| Preservation supplies the next affine-line input | `exceptional_applicability`, with its identity-inclusive form `stage_applicability`, supplies boundedness and the actual etale finite-Tor predicate for the next exceptional image, using `sf_preservation_class` and finite-Tor comparison; these are conclusions, not added hypotheses. |
| gamma_0=id | `comparisonZero` is `𝟙 K.obj`, and is the main definition's recursion base. |
| Four-arrow successor formula | `comparisonStep`: `sourceReassociation.hom ≫ lineSource.map h ≫ lineComparison ≫ exceptionalComposite`. The last arrow is uniquely fixed to the actual inverse compositor, with identity normalization at zero. The same formula works at d=0, because `exceptionalComposite` retains the canonical identity composition normalization. `lineComparison` is exactly the already recorded `affineLinePurityComparison`, transported only by the source coordinate equality and standing-compactification iso. |
| No isomorphy of gamma asserted | The result is a morphism, not an isomorphism and not an IsIso assertion. |

Dependency interfaces read and used (all recorded statement modules are imported):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`;
  `Sheaf.Paper.AffineLinePurityComparison`: its `Ring`, `ringEquiv`, `primeUnit`,
  `affineLinePurityComparison`.
- Mathlib `AlgebraicGeometry.AffineSpace`; upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`: `iteratedAffineLine`,
  `iteratedAffineLineProj`. Morphism-property convention uses the actual Mathlib classes.
- `Sheaf.Paper.DerivedPullbackTensorHom`,
  `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, and
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the finite coefficient
  realization, Tate twist convention and `ProEtale.sfFiniteExceptionalAt`.
  Their fixed-scalar finite interfaces are the upstream `upperStar.leftDerivedFunctor`,
  `derivedTensor`, and `rightDerivedUpperShriek` used here.
- `Sheaf.Paper.EtaleOriginDerivedCategory`: retained witnesses and full ambient Homs;
  `Sheaf.Paper.ProEtaleConstructibleOrigin`: `constructible_proEtale_origin`;
  `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`: the specified relative
  adjunction; its standing-compactification interface is
  `rightDerivedUpperShriekHomEquiv` and `rightDerivedUpperShriekCounit`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: `originCompositionAmbient`.
  The inverse mate is written by its actual pasted counit instead of assuming an
  unrestricted ambient adjunction. This is the specialization of Mathlib's
  `conjugateEquiv`/`conjugateIsoEquiv` and `Adjunction.comp` convention to these Homs.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `CartierKummerMap`,
  `EtaleFiniteTwistPullback`, `SupportComparisonPullbackCoherence` supply the comparison
  and finite roots-of-unity Tate line conventions. The already constructed concrete
  components used here are `VectorIntegrationSite.pullback` and
  `AffineLinePurity.comparedLinePullback` in
  `Sheaf.Paper.AffineLinePurityCoordinateMaps`.
- `Sheaf.Paper.DerivedPullbackTensorIso`: the ambient finite canonical tensor
  comparison; its actual fixed-scalar component is upstream
  `leftDerivedUpperStarTensorIso`. `inverseImageTensorIso` merely caches this same iso.
- `Sheaf.Paper.SfPreservationClass`: `AlgebraicGeometry.Scheme.sf_preservation_class`;
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian` supplies the ordinary
  finite-Tor comparison used in the proof obligation.

Edge cases checked: dimension zero; the first affine-line step and its identity
composition transport; zero K; empty Y and all empty coordinate stages; arbitrary
positive quotient levels (including levels not divisible by ramification index);
unit invertibility on the empty scheme; ell different from the characteristic inherited
from P. No claim is made at coefficient level zero, which the original conventions exclude.
The universe u is explicit, with schemes in u and fixed module coefficients in u+1;
there are no auto-bound implicit variables or extra equalities of site universes.

Searches actually run:

- `msearch.py ... leanfinder "affine space purity comparison map ordered composite"`:
  eight affine-space geometry hits, no canonical purity comparison.
- `msearch.py ... loogle "AffineSpace purity comparison"`: zero matches, with
  unknown-identifier feedback for the unqualified AffineSpace query.
- `msearch.py ... grep "affineSpacePurityComparison|affineSpace.*Purity" "Sheaf/"`:
  zero matches. This is supplemented by direct searches of the actual project below.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib for affine-space
  purity, ordered comparison, Tate powers and exceptional-composition interfaces.
  Also searched the node ID in `lean/WeilConjectures`. The upstream smooth/affine-space
  modules explicitly give existence isomorphisms, not this normalized recursively
  specified morphism. Their existence-only data cannot replace this definition.
- Direct Mathlib monoidal-directory search for `tensorPow|tensorPower` found no generic
  implementation matching this shifted finite Tate action. Existing sheaf-level
  `coefficientTwistPower` was read; this delivery uses the existing finite line in
  fixed-scalar derived tensor coordinates, not a replacement sheaf-level definition.

Every new postponed proof is a named theorem with its full proof plan in its docstring:
`annihilates`, `projection_geometry`, `tower_geometry`, `tower_noetherian`,
`lineSource_obj_eq`,
`exponentUnit`, `sourceReassociation_existsUnique`, `exceptionalEtale_eq`,
`exceptional_applicability`, `stage_applicability`, and
`exceptionalComposite_existsUnique`. These are the coefficient, geometry, source
coordinates, origin-preservation and compositor-normalization clauses of this node.
All definitions have real data. No STATEMENT-DISPUTED issue was found.

The only theorem-backed choices are the two explicitly unique coordinate transports.
`sourceReassociation_existsUnique` fixes the hom by HEq to the fully constructed
`sourceReassociationRaw`. `exceptionalComposite_existsUnique` fixes it by HEq to
`exceptionalCompositeRaw`, whose positive component is the actual pasted-counit
inverse mate and whose zero component is the canonical identity-composition map.
Neither statement is a bare Nonempty existence assertion. After substituting the
endpoint equalities the hom equality is reflexive; equality with that fixed hom gives
uniqueness. This meets the rule permitting postponed proof of a property that uniquely
determines the data. The main definition uses `orderedRec`, a transparent abstract dependent recursion,
with literal identity base `comparisonZero` and the specified `comparisonStep`.

## Second reading by NH

This dispatcher-started worker was instructed not to start another agent. This section
records a second clause-by-clause self-reading of the node and module; the independent
maintainer review remains the delivery review, not an invented second worker.

The reading rejected a preliminary smooth-purity specialization because it did not
construct the required ordered morphism and introduced extra geometric input instances.
It also rejected an intermediate recursive source normal form without an explicit total
source identification. The final source uses p_d itself and finite Tate tensor powers
on X_d. Its I_d is fixed to the actual canonical pullback/tensor composite, retaining
both computed endpoints before their unique coordinate transport. The generic tensor
iteration caches exactly these operations before specializing the finite coefficient.

The final `comparisonStep` has no dependent case split: at every stage it is exactly
I_d.hom, lineSource applied to the previous map, the recorded affine-line comparison,
and the normalized inverse compositor. `stageEtale`/`stageComparison` retain the original
Ke/eK at zero and the canonical etale exceptional antecedent at positive stages.
`stage_applicability` derives all required boundedness and finite-Tor conditions.
The zero inverse compositor is the canonical identity-composition map; the positive
one is the inverse mate defined from the actual compact-support compositor and pasted
counit. No arbitrary map or isomorphism, smooth-purity conclusion, extra geometric
hypothesis, ramification divisibility condition, or isomorphy of gamma is introduced.

The table above was checked against every clause of the expanded DAG statement and the
current blueprint source. Coefficient indexing was checked against Ring and ringEquiv.
The empty scheme, zero object, dimension zero and first successor were rechecked.
Compactification and tower properties are supplied locally from the named geometry
obligations, avoiding overly broad global typeclass instances. Every variable and
universe is bound explicitly. No node field besides lean is changed.

Final elaboration details: `C`, `Plus`, `boundedBelow`, and `etaleFiniteTor`
are abbreviations of the already recorded category and predicates, caching their
fixed-scalar instance parameters. `tower_noetherian` is the source-implied Noetherian
geometry clause. In the inverse compositor the HasCompactification instance is supplied
for the actual written composite q_d≫p_d, transported along iteratedAffineLineProj_succ;
at zero it is transported along the identity-composition equation. These add no inputs.
The generic `identityCompositeMap` caches the same canonical right-adjoint congruence.

`ComparisonHom` abbreviates the displayed hom type, so the recursion reuses exactly
the same derived-category instance in its motive and successor. It adds no structure
or condition to the map.

`orderedRec` checks the dependent recursor with its family abstract;
`comparisonZero` is the actual identity in the normalized zero coordinates.
The main definition applies these to `ComparisonHom` and the literal four-arrow
`comparisonStep`. This factoring avoids repeated kernel normalization of the large
finite coefficient instance; it introduces no postponed data or new condition.

## Validation

The exact delivered module passed `scompile.py NH def-pur-affine-space-comparison
lean/Sheaf/Paper/AffineSpacePurityComparison.lean` in both the isolated sandbox
(53.7 seconds) and its actual library namespace (34.1 seconds), with no unexpected
warning or error. The final source has no diagnostic options or scratch declarations.
