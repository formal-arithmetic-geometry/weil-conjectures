## Worker report

This repairs the immutable returned head dd3317667dc5. The first prescribed dry run
of the retained packet passed mechanically (27a5b9ecb3); reading the packet confirmed
that the mathematical faults in the return remained. The module was consequently
rewritten, rather than re-pushing that mechanically accepted packet.

The module is `Sheaf.SixFunctors.CoefIntegralFiniteExtension`; the main declaration
remains `WeilConjectures.coef_integral_finite_extension`. Helpers are in namespace
`WeilConjectures.IntegralFiniteExtension` and are all registered in `lean.declarations`.
The source is the current main-20261015 blueprint, sec-smooth-purity/sk-lem-sp-tower,
order 2494, including its proof; the original DAG statement is retained.

The explicit main binders render every hypothesis: `D : FiniteFieldDatum`, `l : ℕ`
with `[Fact l.Prime]` and `hl : l ≠ D.p`; `E,L : Type u` with fields, `Padic l` algebra
structures and finite-dimensionality; `ι : E →ₐ[Padic l] L`; `X : Scheme.{u}` with
`X.Over (Spec (.of D.k))` and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`
on its structure morphism. No equality of independent site universes was added.
The recorded scalar extension is `integralScalarExtensionOfUniverses` throughout.

`DualizingDatum` is presentation data for the dualizing objects already constructed
by `prop_coef_integral_dualizing`: its object is in `sfIntegralConstructibleCategory`,
its `reduction` identifies each positive finite reduction with the recorded
`integralDualizingFiniteTerm`, and its `coherent` field is the transition equation
with `integralDualizingExceptionalTransition`. The separately stated
`dualizingDatum_nonempty` obtains these data from that proposition, using the
finite-type dimension bound. This removes the old invalid use of unrelated
arbitrary finite isomorphisms. It adds no mathematical hypothesis on X or the
coefficient fields. The theorem works for every such coherent presentation.

Clause-by-clause rendering of the conclusion:

* Exactness is `∃ (_ : T.CommShift ℤ), T.IsTriangulated` in `Conclusion`.
  Finite-limit/finite-colimit preservation on the derived category is gone.
* Preservation of the bounded constructible category is `∀ K :
  sfIntegralConstructibleCategory l E X, sfIntegralConstructible l L X (T.obj K.obj)`.
* The canonical finite dualizing comparison `finiteEtaleU` is explicitly the
  exceptional-adjunction transpose of inverse compact-support comparison, extension
  of `finiteDualizingEtaleCounit`, and the coefficient-unit map.
  `finiteRealizationRestriction` transports the scalar-unit-normalized restriction
  square; `finiteU` is the corresponding intrinsic scalar-adjunction transpose.
* `quotient` is the canonical identification of a target reduction of T with finite
  scalar extension of a source reduction. Its definition uses the specified
  `completedScalarComparison`, the tensor-unit-normalized reduction adjunctions,
  and `PurCompactSupport.tensorSquare` for the actual completed coefficient square.
* `u_existsUnique` specifies the actual integral morphism by the finite counit
  equations through `wE.reduction`, `wL.reduction`, `quotient`, and `finiteU`.
  `u` takes the morphism from this unique-existence theorem. Its data are therefore
  determined by the equations; this is not a choice of an arbitrary isomorphism.
  The docstring explains construction on the coherent full target tower and
  uniqueness by the reduction/limit mapping sequence and Mittag-Leffler finiteness.
* `homMap` is exactly the tensor-Hom adjunction transpose of scalar-extended
  evaluation, using the representative-normalized scalar tensor comparison.
  `v` conjugates this map by the specified completion maps at K, M and RHom(K,M).
  The invertibility assertion quantifies only constructible K,M, not the ambient
  category. `tensorModel` merely restricts the recorded `IntegralHom` presentation
  to the existing flat-term resolving class; it introduces no new tensor notion.
* `beta` is definitionally `v K omegaE` followed by
  `IntegralHom.hom.map (Prod.mkHom (𝟙 _) u)`. There is no independent Verdier iso.
  `Conclusion` asserts `IsIso` of u, of v on constructible inputs, and of beta on
  constructible inputs. Every map is already defined before these assertions.
* The evaluation equations in `Conclusion` compare tensor of the actual v (and
  separately beta) followed by the target evaluation with `extendedEvaluation`.
  That definition displays scalar extension of source evaluation and each
  completion factor; the beta equation then composes with the actual u.
* The double-dual equation uses `IntegralVerdier.delta` on both sides:
  target delta followed by the target dual of beta equals T(source delta)
  followed by beta at the source dual. Completeness of that dual comes from the
  recorded `scalarInternalHom_complete`; no extra input condition is imposed.
* Finite-quotient compatibility is three actual morphism equations. The u equation
  is its finite-counit square. The v equation uses `IntegralHom.comparison` on
  both sides and the finite evaluation transpose `homMap`, conjugated by the
  canonical `quotient` maps. The beta equation uses the recorded
  `IntegralVerdier.comparison`, the finite evaluation transpose and `finiteU`.
  None of these equations merely says that a functor preserves an isomorphism.
* `unit` is the multiplication isomorphism conjugated by the specified completion
  map. `IdentityConclusion` states equations for u, v and beta against that unit.
* `comp` is the ordinary balanced tensor associator conjugated by all three
  completion maps. `CompositionConclusion` states both associator/unit equations,
  the u, v and beta composition equations with associators at their endpoints,
  and the associator pentagon for a fourth finite coefficient field. The main
  theorem quantifies every third field, embedding, dualizing presentation and
  representative-normalized tensor presentation.

Dependency declarations actually used for the statement are:

* `IntegralVerdier.dual`, `delta`, `comparison`, `SignedSymmetry`, and `Ambient`
  from `Sheaf.SixFunctors.IntegralVerdier`.
* `IntegralHom.TensorPresentation`, `ReductionPresentation`, `hom`, `flat`, and
  `comparison` from `Sheaf.Paper.IntegralHomReduction`.
* `integralScalarExtensionOfUniverses` from
  `Sheaf.Paper.IntegralScalarExtensionUniverses`.
* `completedCoefficientMap`, its residue characterization, and
  `completedScalarComparison` from `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
* `scalarInternalHom_complete` from
  `Sheaf.Paper.IntegralOperationsScalarComparisons`.
* `PurCompactSupport.scalarTensor`, `tensorSquare`, `tensorComposition`,
  `tensorIdentity`, `finiteReductionIso`, and completed coefficient identity and
  composition equations from `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`.
* `finiteDualizingEtaleAdjunction`, `finiteDualizingEtaleCounit`,
  `finiteDualizingOrigin`, `finiteDualizingRealization`, and the generic normalized
  restriction square from `Sheaf.SixFunctors.FiniteDualizing`.
* `Etale.ExceptionalCoefficients.comparisonInverse` and `unitIso` from
  `Sheaf.Paper.ExceptionalCoefficientComparison`.
* `normalizedDVRReductionTransition` from `Sheaf.Paper.NormalizedDVREffectivity`;
  `integralDualizingExceptionalTransition` from `FiniteDualizing`.
* `sfIntegralConstructibleCategory` and its exact object predicate from
  `Sheaf.Paper.SfIntegralConstructible`.
* `pbcDerivedExtend`, `pbcDerivedRestrict`, and `pbcDerivedScalarAdjunction` from
  `Sheaf.Paper.BoundedConstructibleTower`, retaining the standard localization.
* The global datum, finite-type and separated structure, actual integer inclusions
  and finite quotient maps are those reexported by these recorded modules.

The item's `stmt_deps` additionally cites the already landed integral Hom reduction,
integral scalar-operation comparisons, and compact-support coefficient comparison
nodes used by these constructions. Traversal of their statement and proof dependency
graphs found no path back to this item. The other already recorded proof modules
are imported privately as the plan for stage 3. No dependency module or new node
was needed. All definition data are real constructions; each postponed theorem is
named, registered, and has a source and natural-language proof docstring.

Edge cases checked: identity field embeddings with the same dualizing presentation;
E=L=F and insertion of an identity at either associator endpoint; a fourth field
and both parenthesizations; zero objects and empty X; the first positive quotient
(n=0 in the recorded indexing); ramified extensions at intervening target levels,
not only multiples of the ramification index. The finite maps use the actual
same-index quotient homomorphism and hence include those intervening levels.
There is no nonemptiness hypothesis on X and no ambient Hom invertibility claim.

Searches retained from the original packet: LeanFinder for finite coefficient
extension/internal Hom/Verdier duality returned eight ordinary free/sheaf/dual
matches and no integral derived comparison; Loogle for
`integralScalarExtensionOfUniverses, IntegralHom.hom, integral_verdier_biduality`
had no recognized identifier; Mathlib CategoryTheory grep for scalar extension,
IntegralHom and dualizing found only generic duality. Searches in the upstream
WeilConjectures tree and side library found the separate interfaces listed above,
not this theorem. During repair, LeanFinder for canonical finite-extension
comparison defined by finite counit reductions and evaluation transpose returned
`IsBaseChange.toDualBaseChange`, `IsBaseChange.dual`, ordinary dual modules and
FGModuleCat evaluation: none is this notion. Loogle for `Adjunction.homEquiv,
Functor.mapIso` gave zero hits (unknown identifier). Local DAG/side/upstream grep
for coherent finite counits, finite extension and dualizing found the interfaces
used above, not a duplicate construction. No new mathematical notion is defined.

## Second reading by NM

I made a separate clause-by-clause self-check after rewriting, with the current
blueprint statement, its proof, the returned five points and the Lean file open.
The dispatcher forbids starting other agents; this section records a self-check,
not a claimed independent review by another worker. The maintainer performs the
independent reading.

F1: the arbitrary-isomorphism package was removed. The finite u is a literal
counit transpose; the integral u has a unique finite-counit characterization; v
is a literal evaluation transpose; beta is a composition of those maps. IsIso
assertions apply to these definitions. Coherence was added to the dualizing
presentation data because arbitrary unrelated finite identifications do not give
the integral dualizing object with its normalized reductions.

F2: every compatibility now occurs as a nontrivial morphism equation. I checked
the directions of the first, contravariant Hom argument: quotient.hom.op in the
finite squares, unit.inv.op in identity laws, comp.inv.op in the composition laws.
The double-dual equation contains the actual `IntegralVerdier.delta`, and the
beta finite square contains the actual `IntegralVerdier.comparison`. The earlier
functor-preserves-isos clause, mere naturality clause and docstring-only laws are
gone. No reflexive f=f substitute is present.

F3: exactness is CommShift with IsTriangulated, with no finite-limit or
finite-colimit substitute on the derived category.

F4: invertibility of v is quantified over the published constructible full
subcategory. Its definition may be evaluated on complete ambient objects so that
the double-dual/composition formulas have their proper inputs; this does not add
an ambient invertibility assertion.

F5: the original second reading's claims are explicitly retracted by this report.
A successful preflight alone was not treated as mathematical validation. The
finite reduction squares, actual delta and all unit/associator endpoints were
checked directly against the repaired definitions.

Validation: the rewritten module compiled with `scompile.py`; after the final
import and signature updates, `deliver2.py NM lem-coef-integral-finite-extension
--no-push` printed `OK (dry run): commit 4a936449a0 passes the preflight and compiles;
nothing pushed`. The final packet has no compiler diagnostic and passes the
maintainer's server preflight.
