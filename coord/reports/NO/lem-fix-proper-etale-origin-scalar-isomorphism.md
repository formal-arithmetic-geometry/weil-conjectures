## Worker report

The module `Sheaf.Paper.ProperEtaleOriginScalarIsomorphism` states
`AlgebraicGeometry.ProEtale.properEtaleOriginScalarIsomorphism`. Its proof is
`sorry`. The other declarations construct only the canonical presentation changes
needed to express the named-map formula; none has postponed data.

Hypothesis and clause correspondence:

- `p : Z ⟶ Y` with `[IsProper p]` is the proper morphism; `[QuasiCompact p]`
  and `[QuasiSeparated p]` needed by the helper mate follow from properness.
- `{A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]` and
  `φ : A →+* B` give exactly the finite commutative rings and their map.
- The étale side is the ordinary unbounded `Etale.DerivedCategoryModule`.
  Coefficients are `ULift.{u+1,u} A` and `ULift.{u+1,u} B`, following the
  published small-site size convention. The pro-étale side is the existing
  ordinary `Scheme.proEtaleDerivedCategory`; no completion or constructible
  subcategory is used. Both schemes have the original universe `u`; site
  object and morphism universes are never identified.
- `E : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology
  (ModuleCat (ULift A)))` supplies `E_e` and its bounded-below property.
- `properOriginEtaleTensor (RingHom.ulift φ) Z E.obj` is the existing étale derived tensor
  of `E_e` with `Etale.scalarCoefficient (RingHom.ulift φ) Z`, the actual
  restricted constant B coefficient in degree zero. The hypothesis `hH`
  says precisely that this tensor has some lower cohomological bound.
- `finiteCoefficientIntrinsicDerivedComparison Z A` is the published
  canonical realization of ν_Z* in constant-ring module sheaves; its value
  on `E.obj` is the `E` in the node.
- `directImageScalarExtension` is the existing universal derived extension
  along the constant-ring map. `directImageScalarComparison φ p` is the
  specified B-linear counit mate, not an arbitrary map of its endpoints.
  The first conjunct asserts `IsIso` of exactly its component at this E.
- The second conjunct gives the precise scalar-restriction formula.
  Its left side is the restriction of that same component followed by
  `scalarMateRestrictionPush`, the published canonical restriction/direct-image
  identification. On the right, `properOriginEtaleProjection` is the actual
  `Etale.rightDerivedLowerStarProjectionMap`, followed by the canonical
  coefficient pullback identification `Etale.scalarCoefficientPullbackIso`.
  It is conjugated by `properOriginTensorIso` and `properOriginMateIso` at
  exactly `E_e` and `H_e`. In composition order the factors are
  `US(b_E⁻¹)`, `q_Y⁻¹`, `F_Y(π_e)`, `b_H`, and `R_p(q_Z)`.
  Here q is the canonical constant-B tensor comparison expressed through
  the normalized `US = tensor B` identifications. This is the node's tensor
  conjugation formula in the scalar-restriction presentation.
- There is no flatness, projective-dimension, Noetherian, finite-type base,
  or bound on `(Rp_* E_e) tensor B` hypothesis.

The canonical helper constructions use actual published maps:
`properOriginPushIso` applies the adjunction hom-equivalence identity to
identify the two constant-ring structural maps, then derives
`SheafOfModules.pushforwardCongr`. `properOriginRestrictionIso` pastes the
identity-on-sections restriction squares through intrinsic realization.
`properOriginTensorIso` pastes the normalized étale scalar/tensor isomorphism,
that restriction square, and `Scheme.FiniteCompactScalar.siteScalarIso`.
The latter is the normalized scalar-adjunction comparison, not a choice of
an arbitrary natural isomorphism. `properOriginFixedMateIso` includes the
actual `fixedComparisonDirectImageMatePlus` into the unbounded categories,
using its existing invertibility theorem and endpoint compatibilities.
`properOriginMateIso` transports that same mate through the canonical
realization and structural-map identifications.

Dependency declarations read and used (including through the canonical
presentation helpers):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` and its recorded intrinsic
  comparison helper module `ProEtaleFiniteModuleIntrinsicComparison`:
  `finiteCoefficientIntrinsicDerivedComparison` and its exact realization.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `proEtaleSiteComparison`, `proEtaleSiteComparisonModules`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.Paper.ProEtaleScalarMateNormalization`:
  `scalarMateRestriction`, `scalarMateRestrictionPush`, and the recorded
  normalization of `directImageScalarComparison` to the projection mate.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  the derived scalar adjunction and its conservative restriction assertion.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `Etale.rightDerivedLowerStarProjectionMap`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `ringedTopoiCanonicalDerivedTensorComparison` with its K-flat normalization.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus`,
  `isIso_fixedComparisonDirectImageMatePlus` and its counit normalization.
- Proof-plan imports: `WeilConjectures.AlgebraicGeometry.ProperBasic`,
  `Sheaf.SixFunctors.GeometricInverseImageConstantModule`,
  `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale`, and
  `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`.
- Additional existing canonical presentation helpers:
  `Sheaf.Paper.FiniteCompactSupportScalarTransport` (only its generic
  `Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso` and `siteScalarIso`,
  neither imposing Noetherian assumptions),
  `Scheme.sfRealizationRestriction`,
  `Scheme.sfIntrinsicDerivedDirectImageComparison`,
  `Functor.rightDerivedFunctorNatIso`, and
  `SheafOfModules.pushforwardCongr`.

Edge cases checked: empty schemes, the identity morphism, the zero input,
identity ring map A=B, and the zero ring B all retain their literal meanings
and satisfy the claimed conclusion. Nonflat ring maps are included. For
A=Z/4, B=Z/2, E_e=Z/2, the negative Tor groups of H_e persist without a
lower bound, so `hH` correctly excludes that input. The input E_e=0 is
included for every coefficient map. No boundedness of a tensor of the
pushforward is inferred.

Searches for an existing exact statement:

- `msearch.py ... leanfinder` with “Proper pushforward scalar extension
  comparison is invertible for bounded etale origin proetale derived module
  complexes”: eight unrelated algebraic-étale and Kähler differential hits.
- `msearch.py ... loogle '"Proper", "projection"'`: no hits.
- `msearch.py ... grep 'scalarMate|[Pp]roper.*[Pp]rojection'`: two Euclidean
  projection documentation hits, no match.
- `msearch.py ... leansearch` with “The canonical proper pushforward scalar
  extension mate on proetale complexes of bounded etale origin is an
  isomorphism”: eight underived module pushforward/pullback or unrelated
  Kähler differential hits.
- `rg` of WeilConjectures and Sheaf for scalar mate/proper projection names,
  and literal item-id search in WeilConjectures: no exact theorem. The
  existing proper finite-coefficient extension theorem is étale-only with
  Noetherian assumptions; the compact-support transport theorem concerns a
  different functor and also has additional hypotheses. Neither is this item.

No statement correction, new node, dependency-record repair, or disputed
statement is needed. The source and five-step proof were checked in local
Stacks `etale-cohomology.tex` (0F0G) and the recorded canonical comparison
modules. Only the item's `lean` record changes.

Validation: scompile passed for the complete module in sandbox and library modes
(6.7 s and 6.1 s), with no errors or warnings. The prescribed deliver2 dry run also passed preflight and compilation (commit
77e76483b0d); nothing was pushed by that dry run.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
