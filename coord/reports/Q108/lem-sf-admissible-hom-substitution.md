## Worker report

Item: lem-sf-admissible-hom-substitution. Module:
`Sheaf.Paper.AdmissibleHomSubstitution`. The two concluding declarations are
`WeilConjectures.AdmissibleHomSubstitution.admissible_hom_substitution` and
`WeilConjectures.AdmissibleHomSubstitution.coefficient_square`. All theorem proofs
are `sorry`; definitions contain actual data. The other declarations are the
canonical maps, their well-definedness interfaces and the field normalizations
needed to state this same obligation. No statement correction or new node is made.

Hypotheses and clauses, checked against the node:

- `D : FiniteFieldDatum.{u}` and `C : D.CoefficientDatum` give the finite-field
  convention, algebraic closure, prime ell, ell different from p and fixed Qbar.
  `E`, its Field/Algebra/FiniteDimensional instances, and `n`, `hn : 1 ≤ n`
  give exactly the coefficient convention. Positive quotient exponents use `m+1`;
  every positive exponent occurs, including 1. There is no exponent-zero case.
- `S : SixFunctorOperationDatum D C E n hn` is the recorded construction datum.
  Neither conclusion assumes `SixFunctorDatum`, biduality, an anti-equivalence,
  Hom comparison invertibility, or the package axioms. The coefficient clause
  uses the corresponding operation datum `S'` for its target coefficient field.
- `X Y : SixFunctorSpace D` are finite-type schemes over the geometric field.
  The two `IsSeparated` instances give separatedness of these schemes.
  `f : X ⟶ Y` is over that field; `IsSeparated f.hom.left`,
  `LocallyOfFiniteType f.hom.left`, `QuasiCompact f.hom.left` give the stated
  separated finite-type morphism.
- `Realization.finite m`, `.integral`, `.rational`, `.closure` select the actual
  coefficient categories. `domain` is `finiteTorConstructible` in the finite
  ambient derived category, `finiteTorConstructibleIntegral` on integral objects,
  and the entire recorded constructible category in each field case. Thus `hM`,
  `hU`, `hV` are the three stated input assumptions. The output is not restricted
  to this predicate.
- `internalHom` reuses `finiteIntrinsicDerivedInternalHom`,
  `constructibleIntegralHom`, `rationalDerivedInternalHom` and
  `commonStageDerivedInternalHom`. For the latter three, the lifts only supply
  the published pair predicate; neither object nor morphism is replaced.
  `rationalPairPermitted` and `commonPairPermitted` state the geometric
  well-definedness obligations explicitly rather than adding them as hypotheses.
- `directImage` uses `proEtaleConstantDerivedDirectImage` in the finite ambient
  category, `S.higher.integral.direct`, `S.higher.rational.direct`, and
  `S.closure.commonStage.direct`. The integral inclusion comparison is exactly
  `S.higher.integralDirectImage`; the operation datum also fixes its Roos model
  by `integralDirectLimit`/`integralDirectLimitObject`. Hence using the bounded
  constructible realization of the integral value specifies the ambient map,
  and does not assert finite-Tor preservation of its output.
- `imageHom H R U` is precisely `J_U`, contravariant in its argument.
  `substitution H R c` is `mapIso c` followed by ordinary direct image. The
  first two conjuncts identify its hom and inverse components with
  `R.map (H.map (1,c.hom))` and `R.map (H.map (1,c.inv))`. Its type itself
  supplies the natural isomorphism. The third conjunct writes its naturality
  square on every arrow from a finite-Tor constructible input `N` to `M`.
- `finiteShift` and `integralShift` use
  `RingedHomUniverses.sourceShift`, whose `leftShift_existsUnique` fixes the
  signed cochain reindexing, followed by `R.commShiftIso (-r)`.
  `integralConstructibleShift` lifts that exact ambient composite through the
  fully faithful constructible inclusion and the recorded image comparison.
- `rationalImageComparison` has identity components in the published unchanged
  integral-object coordinates. `RationalShiftNormalization` conjugates the
  localization of the completed signed map by this comparison and the actual
  localization shift isomorphisms. Thus `rationalShifts` is chosen from a
  uniqueness statement that determines each component, not from mere existence.
- `inclusionHom` is the inverse of the recorded compositum-to-stage Hom
  comparison followed by the normalized scalar identity in both input variables;
  the first variable has the required opposite/inverse orientation.
  `commonImageComparison` has a component formula using this map and the
  specified direct-image stage comparison. `CommonShiftNormalization` applies
  at EVERY finite field F and inserts the inclusion shift maps.
  `ImageShiftNaturality` transports between arbitrary Hom-pair representatives,
  so the common-stage existence/uniqueness statement determines the full family,
  including pairs whose entries originally have different stages.
- `sourceShift` selects these four maps. The final conjunct, for every integer
  `r`, is exactly `j_c(M[r]) ≫ s_V = s_U ≫ (j_c(M))⟦-r⟧'`, the node's
  displayed equation in Lean's diagrammatic composition order.
- In the coefficient declaration, `E'`, `S'`, and `b` describe the target
  coefficient realization. `CX`, `CY`, `t`, `α` expose the stipulated
  coefficient functors, tensor comparison, and pullback comparison. The formula
  is valid on a natural comparison diagram between these actual realizations;
  in particular the stipulated reduction, scalar transport, localization and
  common-stage diagrams supply its parameters. The two comparison maps in the
  conclusion are NOT parameters.
- `tensor` is the published finite tensor, `constructibleIntegralTensor`,
  `rationalDerivedTensor`, or `commonStageDerivedTensor`. `transpose` uses the
  published finite closed adjunction, or `podIntegralClosed`,
  `podRationalClosed`, `podCommonClosed`. Their normalizations use the actual
  completion unit, bilinear scalar localization, and all common finite stages.
  Residue inverses are supplied by `dlAdicGeometricResidueInvertible`, not an
  additional geometric assumption.
- `homComparison` is exactly the transpose of
  `t.app (H(M,U),M) ≫ CX.map (evaluation M U)`. The tensor comparison direction
  is tensor-of-images to image-of-tensor; it is a natural transformation,
  not an isomorphism assumption. `imageComparison` is literally
  `(mateEquiv imageAdjunction imageAdjunction α).natTrans`.
- `U'`, `V'`, `hU'`, `hV'`, and isomorphisms `u`, `v`, `c'` give the stated
  target inputs and identifications. `hc : CX.map c.hom ≫ v.hom = u.hom ≫ c'.hom`
  is exactly the compatibility hypothesis. No extra assumption about h or gamma
  is made; no assumption that CX(M) has finite Tor amplitude is silently inserted.
- `sigma` is `gamma.app (H(M,U)) ≫ R'.map (h_(M,U) ≫ H'(1,u))`.
  `coefficient_square` states precisely `CY.map j_c ≫ sigma_V = sigma_U ≫ j_c'`,
  at `CX.obj M`. Its proof docstring expands evaluation transposition,
  mate naturality and the final pasted calculation, including completed and
  scalar-transport interpretations.

Dependencies read and reused:

- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`, together
  with `SixFunctorSpace`, `SixFunctorHigherOperations`, `SixFunctorCommonStages`,
  their actual operations, adjunctions, integral image and scalar comparisons.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the four actual Hom and tensor
  constructions, pair domains, rational object/arrow formulas,
  `commonStageHomObject`, `commonStageHomComparison`, and scalar-unit comparisons.
- `Sheaf.Paper.SfDerivedDirectImage`: `sfCompletedDerivedDirectImage`, the
  finite derived direct image, and `SfIntegralDirectImage`'s specified Roos
  interpretation. The operation datum supplies the already recorded functorial
  model on the constructible inputs here, so no arbitrary Roos object is chosen.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructible`,
  `finiteTorConstructibleIntegral`, and the field-coefficient convention.
- `def-weil-scheme-morphism-properties` is a convention node, not a declaration:
  the used properties are Mathlib `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact` and the original over-category maps.
- Additional already landed statement dependencies: `cor-coef-integral-internal-hom`
  (`Sheaf.Paper.IntegralConstructibleInternalHom`,
  `integral_constructible_internalHom`); `lem-pod-derived-automorphism-hom-evaluation`
  (`Sheaf.Paper.DerivedAutomorphismHomEvaluation`, its normalized partial closed
  transposes); `def-dl-a1-locally-constructible-adic-heart`
  (`Sheaf.Paper.DlLocallyConstructibleAdicHeart`,
  `dlAdicGeometricResidueInvertible`); and
  `lem-weil-pbc-ringed-internal-hom-exact-restriction`
  (`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`,
  `RingedHomUniverses.sourceShift`). Their dependency closures were checked
  for a path back to this item: none was found.
- The stated proof dependencies are imported: ordinary universe-aware derived
  internal Hom, Hom complex, its signed shift-left interface, quasi-isomorphism
  invariance, localization predicate/universal-property API, right-derived
  CommShift, coefficient tensor-Hom model, adjunction transpose-square API,
  and `Mathlib.CategoryTheory.Adjunction.Mates.mateEquiv`.
  `lem-sf-integral-direct-image-shift-comparison` currently has no Lean record.
  No nonexistent module is imported: for the complete constructible values here,
  the actual ambient completed right-derived shift is available and transported
  by the operation datum's actual image realization. The broader ambient Roos
  functor interface of that proof node is not assumed or privately redefined.

Edge cases checked: c=id and c inverse give identity/inverse substitutions;
M=0 or U=0 causes no Nonzero condition; r=0 and positive/negative r use the
published integer signed comparison, not only a successor shift; n=1 is m=0;
empty X or Y adds no point/nonemptiness assumption; repeated coefficient fields
use the scalar unitor explicitly; different original common stages are covered
by ImageShiftNaturality; noninvertible t, h, alpha and gamma are allowed. Site
object and morphism universes retain the published u+1 and u convention. No
arbitrary equality of independent universes is imposed.

Searches:

- msearch leanfinder: "Derived internal Hom target substitution is naturally
  isomorphic and commutes with source shifts and canonical coefficient change
  after derived pushforward". Eight generic shift/mapDerived results; none
  states this actual operation-only assertion.
- msearch loogle: `CategoryTheory.ihom, "naturality"`. Four ordinary closed
  coevaluation/evaluation naturality lemmas, not the node.
- msearch grep: `sourceShift|internalHom.*natur|leftShift.*natur` in
  `Algebra/Homology`. No exact match.
- msearch leansearch: "Postcomposition in derived internal Hom is natural in
  the source and commutes with signed source shifts and coefficient change after
  right derived pushforward". Eight generic postcomposition/shift or right-derived
  natural-transformation results, not the four actual coefficient realizations.
- rg searches of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib, and
  `dag/lean_names_upstream.json` for the item id, substitution names,
  internalHom/shift naturality and the new namespace found no exact declaration.
  `DerivedHomSubstitution.coherence` was read in full: it assumes
  `SixFunctorDatum` and closed-change comparison isomorphisms, so is the stronger
  hypothesis twin expressly distinguished in this node's stage-1 review.
  Its closed-domain interface would also assert output-domain preservation which
  the present node does not assume. It is therefore not an existing match.

## Second reading by Q108

Self-reading with the node, latest blueprint proof Steps 2--3, and final Lean
module open. No second agent was started, as the dispatcher brief expressly
forbids it; the maintainer's independent delivery review remains independent.
The hypothesis/clause correspondence above was checked again against the final
signatures rather than inferred from names.

Corrections during this reading: made the common-stage inclusion comparison's
endpoints explicit; added ImageShiftNaturality to the common-stage uniqueness
normalization so different-stage representatives determine the family as well;
removed unused stronger-twin imports; retained only the actual operation datum;
confirmed h and gamma are constructions, with no invertibility assumptions.
Rechecked the contravariant naturality and both displayed equations in Lean's
composition order. No change to the node's mathematical statement was needed.
The module has no `SixFunctorDatum` binder, no `let` in theorem signatures,
no local notation/instances, no data sorry, and every postponed theorem has its
source, matching item tag and a natural-language proof in its docstring.
