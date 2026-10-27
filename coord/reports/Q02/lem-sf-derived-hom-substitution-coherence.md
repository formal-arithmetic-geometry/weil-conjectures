## Worker report

Item: `lem-sf-derived-hom-substitution-coherence`, stage 2, Q02.
Module: `Sheaf.Paper.DerivedHomSubstitutionCoherence`.
Main declaration: `WeilConjectures.DerivedHomSubstitution.coherence`.
All declarations in the module belong to this node. There are no new independent
notions or dependency-interface replacements. The natural-language statement is
unchanged. The item additionally cites the already landed
`lem-weil-pbc-ringed-internal-hom-exact-restriction`, whose independently sized,
uniquely normalized signed source-shift construction the module actually uses.
The privately imported `lem-coef-integral-residue-tor` is a proof ingredient
for uniqueness of the field-family normalization, not a statement dependency:
its equality of integral constructible and integral finite-Tor predicates
covers every underlying object of the raw rationalized category. No stronger
input hypothesis is introduced.

The previous worker's message was about a stage-1 resplit prohibition. This
packet does not resplit the node. The current split and Q44's reviewed proof are
retained; this packet supplies the requested stage-2 interface.

The module constructs the canonical maps, then states two theorems with `sorry`:
`coefficient_square` is the formal evaluation-transpose/mate calculation for any
allowed comparison with the recorded interfaces, and `coherence` states the
finite, completed, rational and algebraically closed shift squares and the
actual A5 coefficient squares. The former also covers a supplied realization
comparison. All definitions have real data. In particular, the finite and
completed shift maps use the existing representative-normalized ringed-site
source shift, not an arbitrary isomorphism. The field maps are selected by
`fieldShifts` from the uniqueness clause of `coherence`; that clause specifies
both their descent normalization and naturality, so the theorem determines the
whole family up to equality.

Clause-by-clause translation:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime p, positive a, q=p^a, finite field and algebraic closure | Explicit section binder `D : FiniteFieldDatum.{u}`. Its `prime`, `exponent_pos`, `cardinality_eq`, `card_base` and algebraic-closure fields retain these assumptions. |
| Prime ell distinct from p and fixed Qbar | Explicit `C : D.CoefficientDatum`; `C.prime`, `C.different`, `C.Qbar`, and its field/algebra/closure instances. |
| Finite coefficient extension, valuation ring, uniformizer, positive n | `E : Type u`, `[Field E]`, `[Algebra (Padic C.l) E]`, `[FiniteDimensional (Padic C.l) E]`, `n : ℕ`, `hn : 1 ≤ n`. The datum uses `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and `coefficientExtensionRing`, not replacement rings. |
| Six-functor datum with constructible exceptional adjunctions and A5 domains | `S : SixFunctorDatum D C E n hn`; it extends the actual operation datum, including its exceptional adjunctions. The proof only uses Hom, direct image, their models, and coefficient comparisons. |
| Separated finite-type k-schemes | `X Y : SixFunctorSpace D` and `[IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]`. Membership in `SixFunctorSpace D` supplies the finite-type structure morphism. |
| Separated finite-type morphism | `f : X ⟶ Y`, `[IsSeparated f.hom.left]`, `[LocallyOfFiniteType f.hom.left]`, `[QuasiCompact f.hom.left]`. This is an over-k morphism. |
| Actual internal Hom, finite-Tor inputs | `hom A` composes the recorded `sixFunctorDomainHom` with its actual output inclusion. Its inputs are the actual `P.FullSubcategory`; it does not introduce another Hom. The four A's are `S.finiteClosed X`, `S.integralClosed X`, `S.rationalClosed X`, and `S.commonClosed X`. At the two field stages P is top, as the finite-Tor definition prescribes. |
| Actual ordinary direct image and J_U | `functor A (Sstage.direct f) U` is the curry/flip of that same Hom, followed by the datum's ordinary direct image. Its output is the actual bounded coefficient category, not an assumed finite-Tor output. |
| U,V and isomorphism c | `substitution A R {U V} (c : U ≅ V)`. It is a natural isomorphism, not merely a family of isomorphic objects. |
| j_c(M)=R H(1,c), including contravariant naturality | `substitution` is `Functor.isoWhiskerRight ((Functor.curry.obj (hom A)).flip.mapIso c) R`. Its component is the specified mapped Hom arrow, its inverse uses c inverse, and its `NatIso` type includes the full naturality square on the opposite finite-Tor category. This construction works at each actual coefficient stage. |
| All integer source shifts and displayed square | `ShiftSquare`, asserted for `finiteShift S f`, `completedShift S f`, `s.rational`, every `s.stage E₀`, and `s.closure`. It says `j_c(N) ≫ s_V = s_U ≫ j_c(M)⟦-r⟧'`. All r are integers. |
| M[r] and its canonical identifications | `ShiftFamily` takes a finite-Tor object N with `e : N.obj ≅ M.obj⟦r⟧`. Taking N to be the inherited shifted object and e its canonical identification gives exactly the node's formula. The more general coordinate presentation includes transport to any identified representative. It never requires a second shift choice on a nested full subcategory. `ShiftNaturality` pins this transport, rather than allowing arbitrary dependence on e. |
| Signed reindexing with (-1)^(r*d), localized | `finiteShift` and `integralShift` invoke `CategoryTheory.RingedHomUniverses.sourceShift`. Its `LeftNormalization` and `LeftFormula` specify the fixed product-projection formula with `(r*d).negOnePow`. `realizedShift` applies its inverse, applies the actual ambient direct image, composes with the canonical `CommShift` of that right-derived functor, and lifts through the full ambient inclusion. |
| Completed integral comparison | `completedShift` uses `S.integralModelComparison` and `S.higher.integralDirectImage`, with `sfCompletedDerivedDirectImage` as the ambient functor. No equality is deduced solely from reductions. |
| Rational and common-stage images of the signed comparisons | `FieldNormalization` consists of `ShiftTransport` along the recorded rationalizations and common-stage inclusions, followed by naturality in both Hom variables. It also specifies each embedded finite coefficient field. `ShiftTransport` inserts the actual sigma arrows and coefficient `CommShift` components, including the output shift. The existential-unique field family is the construction of the specified comparisons, not an extra input hypothesis. |
| Allowed coefficient comparison T_X,T_Y | `CoefficientSquare C f CC` uses `C : SixFunctorCoefficientComparison S S' T` and `CC : SixFunctorClosedChange A A' (T X)`. The concrete `CoefficientCoherence` instantiates these with the datum's integral reductions, rationalization, all coefficient-field transitions, and all inclusions into the common-stage category. `coefficient_square` provides the same conclusion for any other allowed comparison, including a realization, with precisely these interfaces. |
| Evaluation-defined h, with tensor comparison and transpose | `homComparison CC M U` is `A'.closed.transpose` of `CC.comparison.tensor.inv.app ...` followed by the coefficient image of `A.closed.evaluation M U`, then the actual output inclusion. It is computed from evaluation, not assumed as an arbitrary map. |
| Ordinary-image gamma is the pullback mate | `sigma` takes the actual natural transformation `(C.directAdjunction f).right.hom`. The dependency's `ExchangeProjectionAdjunctionComparison` retains the unit and counit equations relating this right comparison to its specified pullback comparison. These pin the mate; no replacement gamma is supplied. |
| U',V',u,v,c' and their compatibility | `CoefficientSquare` quantifies these objects and isomorphisms. Its hypothesis is `T.map c.hom ≫ v.hom = u.hom ≫ c'.hom`, exactly `v ∘ T(c) = c' ∘ u` in diagrammatic order. |
| Sigma formula | `sigma` is `gamma.app (H(M,U)) ≫ R'.map (homComparison ... ≫ H'.map (1,u))`, exactly the displayed formula. `baseSigma` specializes u to identity only for the field-shift normalization. |
| Coefficient equation | The conclusion of `CoefficientSquare` is `TY.map j_c ≫ sigma_V = sigma_U ≫ j_c'`, in the actual target coefficient category. Endpoint associativity is Lean's functor composition and `≫`. |
| No invertibility assertion on arbitrary ambient h | `homComparison` and `sigma` have morphism types. `coefficient_square` inverts neither of them and assumes no ambient `IsIso` hypothesis. The allowed finite-Tor closed model is the existing A5 interface. |
| Integral, rationalized and common finite-stage conventions | Actual data are used throughout: completed ambient right-derived direct image; `S.higher.rationalization`; `(S.closure.coefficientStages E₀).rationalization`; `S.closure.coefficientTransition`; `S.closure.commonStageComparison`. No field-to-finite reduction is introduced. |

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.CoefficientDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its public dependency
  `CoefficientExtension` supplies the valuation ring, uniformizer, quotient ring
  and transition constructions.
- `Sheaf.Paper.SixFunctorDatum`: `SixFunctorDatum`, `SixFunctorClosedDomain`,
  `sixFunctorDomainHom`, `sixFunctorDomainChange`, `SixFunctorClosedChange`, and
  the actual finite/integral/rational/common closed-model comparisons. Its
  operation-stage module supplies `SixFunctorPushStage`,
  `SixFunctorCoefficientComparison`, `sixFunctorFiniteHom`, actual
  rationalizations, and stage models. These records were read with their
  normalization fields, not just their names.
- `Sheaf.Paper.FiniteTorAmplitudeSites` and its public `FiniteTorAmplitude`:
  `finiteTorConstructible`, `finiteTorConstructibleIntegral`, and
  `finiteTorFieldCoefficientCategory`. The nested finite-Tor input domain is the
  one used by `SixFunctorDatum` itself.
- `def-weil-scheme-morphism-properties` is a collection of referenced notions,
  without a declaration of its own. The over-category, `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` are the existing scheme notions.
- `Sheaf.Paper.DerivedPullbackTensorHom`: actual finite, integral, rational and
  common-stage Hom constructions, especially
  `commonStageDerivedInternalHom_existsUnique` and its conjugated common-stage
  morphism formula. These are inherited by the datum's closed-domain records.
- `Sheaf.Paper.SfDerivedDirectImage`: `sfCompletedDerivedDirectImage`,
  `SfIntegralDirectImage`, and the actual finite-reduction projection interface.
  The finite ambient image is
  `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`:
  `CategoryTheory.RingedHomUniverses.sourceShift`, `leftShift_existsUnique`,
  `LeftNormalization`, and `LeftFormula`. This already landed node is added to
  statement dependencies because these canonical maps occur in definition data.
- `Sheaf.Paper.IntegralResidueTor`: `WeilConjectures.integral_residue_tor`,
  specifically its equality of integral-constructible and integral finite-Tor
  predicates. This is used only in the proof plan for uniqueness of the field
  family, not in a definition or statement; it is not in `stmt_deps`.
- Proof imports retain `OrdinaryModuleDerivedInternalHom`,
  `WeilConjectures.Algebra.Homology.DerivedInternalHomShiftLeft`,
  `WeilConjectures.Algebra.Homology.HomComplex`,
  `RingedDerivedClosedSymmetricMonoidal`, `CoefficientRingedTensorHomModel`, and
  Mathlib `CategoryTheory.Adjunction.Mates`. The generic mate dependency is
  `CategoryTheory.mateEquiv`, as its node's `mathlib_match` says.

Edge cases checked before and during writing:

- `n=1` is retained; `hn` excludes only the node's forbidden zero level.
- `r=0`, negative r, zero objects, and the empty scheme are retained. The fixed
  ringed-site normalization uses integer signs and reindexing for all r.
- `c = Iso.refl U` and identity coefficient transitions are included. The
  substitution is constructed by `mapIso`; no nonidentity requirement is used.
- Neither f nor either scheme is required to be proper or smooth.
- U,V are arbitrary finite-Tor inputs, not just dualizing objects.
- Field shifts include arbitrary morphisms and shifted-source identifications;
  normalization is not restricted to integral-arrow representatives or one
  arbitrarily selected common stage.
- The site and module sizes remain those of the recorded operations. The generic
  realization assembly allows independent ambient category sizes; it uses the
  independent-universe ringed Hom interface and imposes no new site-universe
  equality.
- No ambient Hom comparison is asserted invertible. Finite reductions are never
  used as a substitute for equality in the completed category.

Searches for a pre-existing statement (2026-10-22):

- `msearch.py leanfinder`, query “Naturality of derived internal Hom
  postcomposition by an isomorphism with signed source shift and coefficient
  comparison”: eight hits about `Localization.SmallShiftedHom.postcompEquiv`,
  `SingleFunctors.postcompIsoOfIso`, and generic closed-adjunction naturality.
  None states this actual all-stage operation/comparison result.
- `msearch.py leanfinder`, query “Naturality of an evaluation transpose internal
  Hom comparison under change of coefficients and direct image”: eight hits,
  including `ihom.ev_naturality`, `ihom.coev_naturality`, and
  `expComparison_ev`. These are constituents, not the item.
- `msearch.py loogle`, query `"ihom", "naturality"`: four hits,
  `ihom.ev_naturality`, `ihom.coev_naturality`, and their reassociated forms.
  Read their full source signatures in `Monoidal/Closed/Basic.lean`.
- `msearch.py grep`, query `derivedInternalHom|sourceShift|ihomComparison` in
  `Algebra/Homology`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item ID,
  `DerivedHomSubstitution`, `homSubstitution`, and `derivedHomSubstitution` found
  no existing item declaration before writing. Searches for signed Hom/source
  shifts found the existing `RingedInternalHomShiftOfUniverses` interface, which
  is reused. The ordinary small-site `DerivedInternalHomShiftLeft` statement
  alone gives a `Nonempty` isomorphism, so it was not used to select an
  unnormalized comparison.
- The blueprint proof Steps 2--3 were read at the recorded main-20261015 source
  place. The current DAG statement and its seven reviewed proof steps were read.

Validation: all compilation uses the prescribed `scompile.py` against the live
published build. The complete module compiles in both wrapper modes within the
fixed 60-second limit; the only expected warnings are the two named theorem
proofs using `sorry`. Diagnostic probe files are removed from the packet. The
node signature is copied verbatim from `theorem coherence` up to `:=`.
No mathematical statement correction, STATEMENT-DISPUTED flag, or unresolved
node fault is claimed.

Delivery verification: the initial complete packet passed `deliver2.py --no-push`.
The saved packet passed the initial repair dry run before the H2 correction.
The correction below is validated again before delivery.

## Repair of return H2 (2026-10-22)

Returned head: `015b2d46a82f`. Removed
`lem-coef-integral-residue-tor` from the item's `stmt_deps`, as requested.
Its private import and proof-docstring mention remain: the equality is a proof
ingredient for the field-family uniqueness argument, not definition data.
The module and the entire `lean` record are unchanged. The genuine statement
dependency `lem-weil-pbc-ringed-internal-hom-exact-restriction` remains because
`finiteShift` and `integralShift` use `RingedHomUniverses.sourceShift`, whose
data are selected by `leftShift_existsUnique`. The node's statement, proof,
and proof dependencies are unchanged.

Self-check against the current read-only main node: the only differing
top-level fields are `lean` and `stmt_deps`; the latter adds only the
source-shift dependency. The module SHA-256 remains
`45add7e146249dbf12899ad15393f704b1000b685d28cdf9cb9ad6daa54351ee`.
The recorded theorem signature remains verbatim. No independent second
reading is claimed by this repair worker; the maintainer's returned review
checked all mathematical clauses and requested only this dependency correction.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
