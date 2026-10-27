## Worker report

The module `Sheaf.Paper.FinitePurityCounitSystem` states
`AlgebraicGeometry.ProEtale.FinitePurityCounit.finiteCounitSystem : System`.
Its only postponed theorem is that statement. `System` is a proposition spelling
out all the clauses, not a premise assumed by the theorem. `AdjunctionAt` contains
actual adjunction data on the full `IsCtf` subcategories. Its components and counits
are constrained to the already published gamma, exceptional counit, and trace.
The three helper definitions are actual canonical composites, with no choice of
an arbitrary map and no postponed proof in their data.

Source read: the complete current file
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/sk-thm-purity-transport.proof.md`,
and the item's reviewed eight-step proof. The source supplies finite reduction,
identification with the specified exceptional adjoint on the same finite-Tor
categories, and integration normalization. No statement correction is made.

Hypothesis and clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed finite field and its algebraic closure, characteristic p | Every geometric field quantifies `D : FiniteFieldDatum.{u}`, whose `D.k` is the fixed algebraic closure of `D.k₀`. |
| Prime ell different from p | `(ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p)`. |
| Fixed coefficient algebraic closure | Finite arbitrary-ring operations are independent of this choice; the special finite-quotient clauses quantify `P : PurityFiniteSetting.{u}`, retaining its actual coefficient closure, finite subextension, positive level and uniformizer quotient. The prime-ring general construction is exactly the existing `finiteGeneralRingPrimeSetting`. |
| Separated finite-type k-schemes X,Y | `X.Over`, `Y.Over`, and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on both structure maps. The equivalent bundled `Over` encoding is retained verbatim in the base-change clause. |
| Smooth separated k-morphism, pure dimension d >= 0 | `(f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f] (d : ℕ) [SmoothOfRelativeDimension d f]`. |
| All finite commutative ell-primary rings | `(A : Type (u + 1)) [CommRing A] [Finite A]`, any positive `n` with `((ell ^ n : ℕ) : A) = 0`. This includes zero and nonregular rings. Different annihilating powers admit a common maximum; no flatness is imposed. |
| The same bounded constructible finite-Tor categories | `ObjectProperty.FullSubcategory (IsCtf A T)`, with the existing intrinsic pro-etale finite-stratification, boundedness and all-module-sheaf Tor test. No replacement by all bounded constructible complexes. This is the fixed-module presentation of the dependency's exact section-action equivalence. |
| Actual F=Rf!, G=f!, J=f*(-)(d)[2d] | `proCompact A f`, `exceptional A f`, `proSource A f (line A (ell ^ n) hA X d)`, restricted by `ObjectProperty.lift`. The ordered shifted-Tate `line` is the existing exponent-normalized line. |
| Inverse diagonal/DNC orientation and tensor transpose gamma | `OrientationNormalized` fixes each `alpha` using the actual diagonal mate, t=1 normalized Rees comparison and integration-transposed bundle arrow; `AdjunctionAt.purity_components` fixes gamma to `proGamma`. |
| Actual exceptional adjunction and its specified counit | `AdjunctionAt.exceptionalAdjunction` and `.exceptional_counit`, the latter equal to `proCounit A f K.obj`. A fixed pair of functors and this counit determine the adjunction, so it cannot replace the specified adjunction with another normalization. |
| t=epsilon F(gamma) is a counit | `AdjunctionAt.adjunction` is literally `F ⊣ J`; `.counit` is `proTrace`, whose published definition is `F.map proGamma ≫ proCounit`. `.unit` is the exceptional unit followed by inverse purity. Triangle identities are part of `Adjunction`. |
| Not only objectwise isomorphisms | `.purity` is a natural isomorphism of the restricted functors, with prescribed components; `.adjunction` contains the natural Hom bijections and actual unit/counit. |
| Exponent independence | `System.adjunctions` includes the exact `FiniteGeneralRingLevelIndependence` predicate for the very same alpha. It identifies gamma after the generator-normalized common-level Tate comparisons; composing with the fixed counit identifies traces and hence adjunctions. |
| Scalar extension and specified a,b,c | `proScalar`, `proLambda`, `proCompactCoefficientMap`/`proCompactCoefficientInverse`, and `proCoefficientMap`. The latter three have the published scalar/site/origin mate formulas. `CoefficientLineComparison` pins the root, scalar-generator and derived-single normalizations of a; it is not an arbitrary line isomorphism. |
| Purity coefficient equation | `System.coefficient` states `T_X.map gammaA ≫ c = a ≫ gammaB`, as well as invertibility of a,b,c on the stated inputs and preservation of the scalar-extended finite-Tor input. |
| Displayed counit coefficient equation | The same field states `F_B.map a ≫ tB = b_inverse ≫ T_Y.map tA`, with both paths starting at `F_B T_X J_A K`. This is the node's composition-order convention translated into Lean's left-to-right `≫`. |
| Transitive coefficient comparisons and adjunctions | `System.transitive` states the a and b cocycles using `scalarAssociator`, which directly wraps the existing normalized balanced-tensor associator. `System.coefficient` also states the unit equation for actual `AdjunctionAt` values. Together with its actual counit equation these give transitivity as adjunctions, not only objects. |
| Orientation/tensor composition identities | `System.composition` retains the exact finite `SpCompositionFactors.FiniteEquations` statement, including orientation, tensor-map and gamma equations, with all three orientations normalized as above. |
| Cartesian base-change identities | `System.baseChange` retains the complete finite_factors signature and its three displayed equations, including orientation, tensor and gamma, for arbitrary v and the actual pullback square. |
| All finite reduction trace identities | The six fields `reductionPurity`, `reductionTrace`, `reductionUnitTrace`, `reductionComposition`, `reductionBaseChange`, `reductionOrientation` spell out the six recorded dependency statements, on the actual intrinsic `P.Ring` objects and canonical comparison arrows. No ramification or flatness restriction is added. |
| Affine-line counit and projective integration | `affineIntegration` is the actual `VectorTraceScalar.affineTrace` after inverse ordered coefficient descent and normalized Tate pullback. At d=1 that trace is exactly projective-line trace restricted by extension by zero. `affineIntegrationCounit` is inverse coefficient-first projection followed by `1_K tensor affineIntegration` and the coefficient-unit constraints. |
| Iterated affine-space normalization, including nonregular A | `System.affine` asserts equality of the ordinary gamma transpose with this formula for every d and every finite A. `AdjunctionAt.site_trace` transports that exact equation to every original finite-Tor pro-etale K and every ordinary representative, with the actual site and origin counits. Thus it gives the same normalization for all pro-etale inputs, not only extended inputs or the unit. |

The existential Noetherianity, quasi-compactness and compactifiability proof data
in `System.adjunctions` are conclusions supplied by the theorem. The compatibility
fields display those proof instances solely to type the recorded interfaces. They
are consequences of the standing finite-type/separated hypotheses, not extra
geometric restrictions. Their inclusion as interface arguments does not exclude
any of the schemes in `adjunctions`. The local instance bindings use exactly the
existential witnesses and their compactification.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  its field/coefficient closure, Ring, Coefficient and positive-level data.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`, with the actual Over setting and
  ordinary compactification composite.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`,
  `SmoothOfRelativeDimension`; the latter's natural dimension includes d=0.
- `Sheaf.Paper.ProfiniteFiniteConstantLocalModel` and its public imports:
  `HasFiniteConstantProfiniteLocalModel`, `HasFiniteScalarConstantLocalModel`,
  `IsConstantModelConstructible`, `ConstantModelConstructibleFiniteTor`.
- `Sheaf.Paper.ExceptionalInverseImageExistence`:
  `CondensedRing.exceptionalInverseImage_exists`; and
  `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`:
  `localizingExceptionalAdjoint_preserves_finiteConstructible`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the recorded coefficient
  twists interface; the finite line actually used is the public `line` and
  its normalized `CoefficientLineComparison`/`tensorPower` interface from
  `Sheaf.Paper.FiniteSmoothPurityMaps` and `FiniteSmoothCoefficientArrows`.
- `Sheaf.SecSmoothPurity.FiniteGeneralRing`: `finiteGeneralRingSmoothPurity`,
  and its public data module's `FiniteGeneralRingLevelIndependence`,
  `finiteGeneralRingPrimeSetting`, `FiniteGeneralRingAt`.
- `Sheaf.SecSmoothPurity.ReductionCompatibilities`:
  `reductionCompatibilities_unit`, `_composition`, `_purity`; the prescribed
  coefficient arrows themselves come from `FiniteSmoothCoefficientArrows`.
- `Sheaf.Paper.SmoothPurityCompositionFactors`:
  `SpCompositionFactors.finite`, `FiniteEquations` and its canonical compositors.
- `Sheaf.Paper.SmoothPurityBaseChangeFactors`:
  `SmoothPurityBaseChange.finite_factors`, with actual exceptional exchanges.
- `Sheaf.Paper.FiniteReductionOfPurity`: all six public finiteReductionOf*
  statements; their full signatures are the corresponding System fields.
- `Sheaf.Paper.ProjectionPurityAgreement`:
  `PurityFiniteSetting.projection_purity_agreement`, retaining every positive
  coefficient level and its integration-transposed diagonal normalization.
- Proof interfaces imported: `SmoothTrace`, `ReductionDirectImage`,
  `ReductionExceptional`, `ScalarExtensionFunctor`, `FiniteRingSiteTensorTranspose`,
  `FiniteDiscreteOrdinaryEquivalence`, `EtaleProEtaleCoefficientCompatibility`,
  `VectorTraceScalarDescent`. The finite discrete equivalence's full signature
  includes exact section-action, termwise derived extension, tensor, finite-Tor
  intervals and the same compactification composite.
- `WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative`:
  `Etale.derivedTensorSingleUnitIso`, the existing constant-coefficient right unit.
- Mathlib proof leaves: `Adjunction.mkOfHomEquiv` and its unit/counit formulas,
  `Adjunction.comp` and `comp_counit_app`, and finite-type Noetherianity from
  `Mathlib.AlgebraicGeometry.Noetherian`. These are used directly, without nodes
  duplicating them.

Edge cases checked before writing: d=0 uses the empty tensor and identity ordered
affine adjunction; an empty source can be smooth of several supplied dimensions,
and there is no assertion that an arbitrary supplied d must be zero. Empty schemes,
the zero complex and the zero coefficient ring are admitted. Identity ring maps
and equal finite-reduction levels are included. The nonregular example
F_ell[epsilon]/(epsilon^2), and nonflat quotients A→B, have all the stated domains:
only finite Tor objects are used and no regularity, Gorenstein or flatness binder
appears. Finite rings at two different annihilating powers can be compared after
passing to their common maximum. The site keeps object universe u+1 and morphism
universe u; coefficient modules use u+1, as in the recorded interfaces.

Searches for an existing declaration:

1. msearch.py leanfinder, query “Smooth purity as a coherent system of finite
   coefficient adjunctions with specified counits and affine integration normalization”:
   eight hits, all smooth-ring descent or definitions; no sheaf-theoretic system.
2. msearch.py loogle `CategoryTheory.Adjunction.ofNatIsoRight`: five exact generic
   adjunction-transport hits. They give the categorical construction used by the
   proof but not the specified finite purity, scalar, geometric or integration laws.
3. msearch.py grep `purity|Purity|upperShriek`, Mathlib CategoryTheory: no hits.
4. msearch.py leansearch “smooth purity finite coefficient counit scalar extension”:
   eight hits concerning ModuleCat scalar adjunction counits and descent, no system.
5. rg in `lean/WeilConjectures` and `lean/Sheaf` for finite counits, purity adjunctions
   and the item id: no declaration for this node. Related existing pieces include
   `FiniteSmoothAdjunctionData`, `FiniteSmoothAdjunctionGeneralBase`, the `Transport*`
   definitions, `FiniteSiteCounitProjectionTransport` and `FiniteCompositorCounit`.
   They supply individual maps, prime-power level systems, or all-coefficient
   transport statements, rather than this finite-ring normalized counit system.
6. Full declarations and docstrings of the dependency interfaces were read, including
   finiteGeneralRing's actual normalized orientation and its common-exponent formula.
   The dependency maps and predicates are reused, not independently redefined.

No STATEMENT-DISPUTED issue, node correction, new independent notion, or dependency
repair was needed. The System and AdjunctionAt structures are helper declarations
for this node's own system assertion, permitted in its owning module. The scalar
and integration definitions name literal canonical composites of existing maps.

## Second reading by NI

The dispatcher explicitly prohibited starting other agents and assigned independent
review to the maintainer. This section records the author's separate second pass;
it does not claim an independent reviewer has already approved the delivery.

I reopened the full node and the module and matched every hypothesis and clause
in the table above. The checks concentrated on actual counits, same finite-Tor
categories, and the affine formula at arbitrary finite A. I checked the direction
of the unit equation: T_X eta_A, then a at F_A M, then J_B b, has the same source
and target as eta_B. For the cocycle the order is T_BC(a_AB), a_BC, J_C alpha_Y,
versus alpha_X followed by a_AC. The counit paths have source F_B T_X J_A K and
target T_Y K. The affine formula uses the actual inverse coefficient descent and
Tate pullback before the ordered trace, not an arbitrary iso or an independently
postulated trace. The `site_trace` field applies it to every original K and every
ordinary representative. The orientation, tensor, gamma, and all six finite
reduction clauses are explicitly retained. Compilation and preflight results are
recorded below once available.

## Validation

The final module compiled through `scompile.py NI
lem-pur-transport-finite-counit-system` on 2026-10-26, with exit code 0 and no
errors or warnings: 26.1 seconds for the sandbox check and 26.5 seconds for the
module check, both below 60 seconds. All profiling options and probe modules
were removed. There is exactly one `sorry`, in the named theorem with the complete
eight-step proof docstring. The source node and delivered node differ only in
`lean`; the declaration signature is copied verbatim.
