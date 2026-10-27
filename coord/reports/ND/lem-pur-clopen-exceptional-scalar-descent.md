## Worker report

Item: `lem-pur-clopen-exceptional-scalar-descent`. Module:
`Sheaf.Paper.ClopenExceptionalScalarDescent`, main declaration
`WeilConjectures.PurityFiniteSetting.clopenExceptionalScalarDescent`.
The second theorem, `clopenExceptionalScalarDescent_system`, states the system
clause of this same node. Both proofs are `sorry`; all helper definitions contain
real data or explicit predicates. This delivery does not change the mathematical
statement, proof, or proof dependencies of the node.

The source read was Zheng, Construction 5.15 and Lemmas 5.16 and 5.22,
printed pages 35–36, together with the current blueprint at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md`.
The latter's last coefficient-unit sentence is interpreted by evaluation of the
same natural isomorphism, not by introducing another dualizing object.

Hypotheses, one by one:

- `P : PurityFiniteSetting.{u}` is the recorded finite coefficient setting:
  `P.field` gives the algebraic closure of a finite field, `P.coefficients` gives
  the prime, its inequality with the characteristic, and the fixed coefficient
  closure, while `P.extension` is the finite subextension E. Its valuation ring,
  uniformizer and positive quotients are the existing Padic constructions.
  The irrelevant selected positive level in P does not restrict any stage:
  the system packages retain every positive quotient, indexed by n+1.
- `X Y : Over (Spec (.of P.field.k))` are k-schemes. For each of X and Y the
  instances `LocallyOfFiniteType (W.left ↘ Spec (.of P.field.k))` and
  `QuasiCompact (W.left ↘ Spec (.of P.field.k))` mean finite type over k.
- `g : X ⟶ Y` is over k. `IsSeparated g.left`,
  `LocallyOfFiniteType g.left` and `QuasiCompact g.left` impose separated finite
  type on g. There is no separatedness instance on the structure map of Y.
- `{I : Type w} [Finite I]` allows every finite indexing type, including empty.
  `Xi : I → Scheme.{u}` and `j : ∀ i, Xi i ⟶ X.left` are the actual components
  and inclusions. Both immersion classes are required for every j i.
- `_hdisjoint` is pairwise disjointness of the ranges for unequal indices;
  `_hcover` is equality of their union with `Set.univ`. Neither demands a
  nonempty index or component.
- `c : Compactification g.left` is the one common compactification. Everywhere
  the component compactification is exactly `c.precomp (j i)`, with the same
  proper part. `clopenScalarComponent` and `clopenScalarInclusion` only bundle
  `j i ≫ (X.left ↘ Spec k)` and j i as an Over object and map. Their four small
  instance adapters derive finite type by composition and quasi-compactness
  from the closed immersion; they add no component hypotheses.

Clauses, one by one:

1. **Prescribed comparisons, not arbitrary natural isomorphisms.** The conclusion
   produces the published `ClopenExceptionalAllCoefficients` record R. At each
   coefficient field its `strict` field is
   `StrictClopenExceptionalComparison`, with its counit-normalized system rho,
   prescribed compact-support compositor and finite evaluation formulas.
   `ClopenExceptionalCoefficientComparison.coherence` fixes the transported
   system map to that rho, its finite maps to the counit comparisons, and its
   rational maps to localization on pure tensors. These existing definitions
   are imported and reused, never restated as private variants.
2. **The actual derived-system equation.** `ClopenStrictScalarSquare.right_square`
   says, for every input L, `Ti.map rhoA ≫ si.right = rScalar.inv ≫
   rB.map sg.right ≫ rhoB ≫ GiB.map target`. With the canonical scalar/restriction
   and shared-target identifications this is exactly
   `s_gi ∘ T(rhoA) = (rhoB T) ∘ rB(s_g)`.
   Equality for every object is equality of natural transformations by
   `NatTrans.ext`; this is not an assertion just about finite evaluations.
   The theorem `clopenExceptionalScalarDescent_system` supplies that square for
   the prescribed coefficient change and exceptional transports and the two
   recorded compact-support normalizations. They express the node's already
   fixed constructions, not extra assumptions on the schemes.
3. **The left square and counits.** `left_square` is the square with the two
   `compact.projection` maps and the clopen compact-support compositor.
   `insertion_mate` fixes its insertion comparison to the mate of the actual
   `StrictEtaleInverseTransport` restriction map, using the prescribed
   restriction/direct-image adjunctions. `target.unit` identifies the ordinary
   scalar functors on Y by their tensor-unit maps; `target.representative`
   specifies the induced transformation on localized complexes. The exceptional
   transports' coherence fixes their `right` maps to the prescribed counit mates.
4. **Every finite extension from the named E.** The last quantifiers in the main
   theorem run over every finite coefficient stage B and literal containment
   `h : P.extension ≤ B.val`. `clopenBaseInclusion P B h` is
   `(Shrink.algEquiv _ B.val).symm` composed with the actual subfield inclusion.
   Thus the target is the published small model of E', and the inclusion is the
   one inside the fixed closure. No equality of coefficient and site universes
   and no extra arbitrary field embedding is assumed. `ClopenBaseScalars`
   supplies the compact-support and exceptional comparisons at this extension.
   In `ClopenBaseScalarLaws` the left maps satisfy the existing
   `SfCompactSupportIntegralBetaSpec`, which fixes their finite quotient
   tensor-unit transposes. The right maps equal `mateEquiv` of those left maps'
   inverses. The first universally quantified K equation is exactly the
   integral scalar square using `integralPullbackScalarComparison`.
5. **Ramified coefficient tower.** The last conjunct of `ClopenBaseScalarLaws`
   gives e>0 with `(span {image(varpi_E)})^n = (varpi_E')^(e*n)` as ideals for
   every n≥1. The target ideal is exactly `Padic.coefficientExtensionIdeal`.
   This characterizes the ramification exponent without replacing a uniformizer
   by a new arbitrary parameter. The system theorem accepts the recorded
   `StrictEtaleCoefficientChange` with its full monotone quotient index; hence
   it applies both to the same-source-uniformizer tower B_n and its prescribed
   ramified reindexing. `StrictEtaleCoefficientTransport` retains the generator,
   quotient-transition, finite-evaluation and complex-localization formulas.
6. **Identity and successive extensions.** No extension quantifier excludes an
   equality. The inherited stage actions are `StageSystem.Morphism`s; their
   `coh` fields express the identity and successive-extension equations under
   the actual stage tensor identifications. The scalar maps are fixed mates,
   so the system identity/composition comparisons from
   `EtaleCoefficientSystemAdjoint` apply to exactly these maps, not newly chosen
   isomorphisms. The scalar/restriction square is asserted for all B≤C,
   including B=C, by `ClopenScalarLaws`.
7. **O-linearity, DU and actual total limit.** `ClopenScalarLaws` requires
   `Functor.Linear` over the appropriate coefficient valuation ring for the base
   and every stage integral exceptional functor. The comparisons are morphisms
   in those linear categories. `ClopenBaseRealizationLaws` identifies the base
   integral functors, strict support/adjoint data and the included comparison
   arrow with a `ClopenSystemIntegralRealization`. Its published `limits` field
   retains ordinary scalar restriction with section normalization, derived DU,
   compatible-family limit projection equations, and the total-limit unit
   normalization. Its `integralComparison_map` is kappa inverse followed by
   that actual realized system arrow. The heterogeneous equalities only forget
   wrappers; they do not replace a map by an arbitrary existence witness.
8. **Rationalization.** At the base, `ClopenBaseScalarLaws` identifies both
   rational scalar comparisons with the raw localization of the integral maps,
   and asserts the rational scalar square with
   `rationalPullbackScalarComparison`. For stages, `ClopenScalarLaws` does the
   same for `R.action.β` and `R.actionI.β`, then states the rational square with
   the actual `stageTransition`s. `clopenStageScalarRestriction` changes
   coordinates using `operationStageTransitionIso` on both sides of the
   recorded rational pullback scalar comparison. Thus all squares concern
   actual raw localized categories, with no Karoubi replacement.
9. **Common-stage descent and independence.** `R.commonStageComparison` is a
   natural isomorphism between the actual `StageSystem.Morphism.functor`s and
   `P.clopenCommonStagePullback`. The inherited `stageComparisonMap` and
   `commonStageMap` equations fix its component to the class of the finite-stage
   rho, using `StageSystem.PairCategory.mkHom`. Thus its map is defined on the
   quotient of common-stage representatives; naturality and both inverse
   equations hold there. The explicit stage scalar square identifies the same
   component after any common finite extension. The base-to-stage square also
   identifies the original E comparison with this family.
10. **Coefficient unit and dualizing objects.** The previously published
    `integralUnitComparison`, `rationalUnitComparison`, `finiteUnitComparison`
    and `commonStageUnitComparison` evaluate R's same comparisons at the actual
    regular coefficient unit. The definitions
    `clopenIntegralDualizingScalar` and `clopenRationalDualizingScalar`, applied
    to g or its component, evaluate the scalar
    maps at that unit and then apply G to
    `constantCoefficientConstructibleScalarIso` or its canonical rationalization.
    These are the prescribed 1 tensor b ↦ b unit identifications. Specializing
    the universally quantified scalar square at the unit and applying
    naturality of the target rho gives exactly the dualizing-object square
    with these definitions; there is no independently chosen omega comparison.
11. **Empty components.** `ClopenEmptyScalarLaws` requires `ClopenZeroComparison`
    for the strict rho, finite rho, transported system rho, base integral and
    rational rho, every stage integral/rational rho, and common-stage rho.
    This predicate explicitly says that both objects are `IsZero` and every
    arrow equals the displayed comparison. If I is empty, `∀ i : I` is vacuous
    and the cover equation forces X empty. No inhabitance or nonzero condition
    is inserted anywhere.

Recorded dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- Mathlib `AlgebraicGeometry.IsProper`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsOpenImmersion`, and `IsClosedImmersion`, with their full morphism signatures.
- `WeilConjectures.Compactification.RefinementCategory` and its public definitions:
  `AlgebraicGeometry.Compactification`, `.precomp`, and `.Refinement`.
- `Sheaf.Paper.ClopenCounitAdjointComparison`:
  `clopenCounitAdjointComparison_finite` and `_system`; the corresponding
  `ClopenCounitComparison` and `StrictClopenExceptionalComparison` records from
  `Sheaf.Paper.ClopenStrictSystemComparison`.
- `Sheaf.Paper.ClopenSystemIntegralRealization`:
  `ClopenSystemIntegralRealization`, `ClopenSystemIntegralLimit`,
  `ClopenSystemIntegralTransport`, and `clopenSystemIntegralRealization`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `WeilConjectures.ConstructibleExceptionalCoefficients.System`, with the actual
  coefficient categories, scalar changes and support normalizations from its
  public Data module. The clopen comparison data refer to those constructions.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `integralPullbackScalarComparison`,
  `rationalPullbackScalarComparison`, and the actual common-stage pullback.
- `Sheaf.Paper.EtaleCoefficientSystemAdjoint`:
  `AlgebraicGeometry.etaleCoefficientSystemAdjoint`,
  `StrictEtaleCoefficientChange`, `StrictEtaleCoefficientTransport`,
  `StrictEtaleInverseTransport`, and `StrictEtaleExceptionalTransport`, including
  their full coherence predicates, identity and composition interfaces.
- The added, already-landed statement-dependency
  `def-pur-clopen-strict-system-comparison` owns the actual system categories,
  `clopenExceptionalSystem` and clopen finite/integral/rational restrictions.
- The added, already-landed `def-weil-compact-support-coefficient-action` owns
  `SfCompactSupportCoefficientAction` and `SfCompactSupportIntegralBetaSpec`.
- The added, already-landed `def-weil-algebraically-closed-coefficients` owns
  `AlgebraicallyClosedCoefficients.Coefficient`, `.coefficientInclusion`,
  `GeneralAlgebraicallyClosedCoefficients.stageTransition`, and the actual pair
  category. `operationStageTransitionIso` is its operation-coordinate comparison.
- `Sheaf.Paper.ConstantCoefficientScalarNormalization` provides the two canonical
  scalar unit isomorphisms used in the two dualizing scalar definitions.

All published proof-dependency modules are imported, as are Mathlib's actual
`mateEquiv` and mate-pasting definitions. The still-unrecorded separate scalar-mate
coherence node is not assumed as a new premise or given a made-up declaration.
The main docstring contains all ten proof steps and their node citations.

Existing definition reuse and the import-cycle exception:
`ClopenExceptionalCoefficientComparison` and `ClopenExceptionalAllCoefficients`
are already defined in `Sheaf.Paper.FiniteClopenExceptionalRestriction` and used
by other landed statements. This delivery imports those definitions and their
normalization predicates; it never invokes that module's downstream theorem
`finiteClopenExceptionalRestriction`. Adding the reverse proof import of this
new module into that old module would create an import cycle. Per
`stages/2-statements.md` §3(7), that reverse proof import is explicitly listed
here as omitted. This is an interface-location issue for the maintainer to
factor before that downstream proof is implemented, not a logical dependence
on the downstream theorem. No cyclic DAG dependency is added.

Edge cases checked before and during elaboration: empty I; an empty component
among nonempty components; X empty; level n=1; identity extension; ramified
extension with e>1; successive extensions; nonseparated finite-type Y; different
site/coefficient-model universes. In particular, no Fintype enumeration, global
separatedness of Y, nonempty scheme, positive cardinality of I, or coefficient
universe equality occurs in the signature. The theorem retains the ordinary
unbounded strict-system localization and actual total inverse limit, not only
per-degree cohomology statements.

Searches actually run:

- LeanFinder: “Clopen exceptional inverse image comparisons commute with finite
  coefficient extension and descend to common stage algebraic closure
  coefficients”. Eight hits were unrelated field-embedding/cardinal and Galois
  lifting coherence declarations; none states this comparison square.
- Loogle: `CategoryTheory.conjugateEquiv, CategoryTheory.whiskerLeft,
  CategoryTheory.NatIso`. Zero hits, with the explicit unknown-identifier result
  for `CategoryTheory.whiskerLeft`; this was not an exact-match finding.
- Loogle: `CategoryTheory.mateEquiv`. Returned the existing mates equivalence,
  its unit/counit and vertical/horizontal composition lemmas. These are reused;
  none states the geometric coefficient descent.
- LeanSearch: “Scalar extension compatibility for the counit normalized
  exceptional inverse image comparison of a clopen immersion”. Eight hits,
  including ordinary module scalar-adjunction counits and scheme-module open
  restriction counits; none gives strict-system exceptional descent.
- msearch grep: `clopen|scalar.*adjoint` in Mathlib CategoryTheory: zero hits.
- `rg` in the upstream `lean/WeilConjectures` for the item id: no occurrence.
  Keyword searches of upstream and `lean/Sheaf/Paper` found the already published
  clopen restriction/scalar comparison definitions and the existing aggregate
  clopen comparison records; these were reused. No theorem with this exact
  strict-system scalar square and integral/common-stage descent was found.
- Blueprint search `clopen scalar` returned `def-pur-supported-cup`, whose
  supported-cup notion is different. The ancestor is `def-pur-section-invariant`.

No new independent notion, definition node, dependency module, or statement
correction was needed. All helper declarations belong to the specified scalar
comparison itself and are listed in `lean.declarations`. No statement dispute
or source error was found. Compilation and delivery use only the prescribed
single-file wrappers; no shared source was edited and no global build was run.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
