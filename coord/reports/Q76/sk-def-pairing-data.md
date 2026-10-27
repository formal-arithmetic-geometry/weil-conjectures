## Worker report

Q76, 2026-10-24. This is a substantive repair of returned immutable head
ccb35eef308e, following the defects re-verified from 677972139168. The saved
packet's initial dry run passed mechanically (610023db5ee), but that packet was
not pushed: the mathematical defects required the changes below.

`Sheaf.Paper.PairingData` defines eight actual morphisms of coefficient complexes,
and `WeilConjectures.SixFunctorDatum.pairingData` bundles them at the specified
geometric fibre together with their canonical point tensor/unit system. Four
auxiliary definition nodes supply the missing normalized finite tensor transport
and coefficient-unit comparison. Their two existence-and-uniqueness theorems have
`sorry` proofs, complete proof docstrings, and corresponding assertions in their
owning nodes. Every definition has real data; the selected comparisons are fixed
by uniqueness and full representative normalizations, not by bare nonemptiness.

Return repair, point by point:

1. H3: each `*PairingCup` starts with the actual
   `(T.<stage> ...).tensorIso ... |>.inv`. Each `*NormalizedSmoothTrace` applies
   its explicit zero-line comparison and ends with the actual
   `(T.<stage> ...).unitIso.hom`. There are no unapplied generic coordinate
   formulas. `pairingFiniteSupport`, `pairingFiniteDirect`,
   `pairingIntegralSupport`, and `pairingIntegralDirect` use the respective
   `S.*Coherence.supportDomain/directDomain` proofs to supply the exact finite-Tor
   point objects required by those tensorators. Tensor normalization is actually
   applied in all four cups. Finite support, direct image, projection and counits
   all use `S.finite`. The zero-line comparisons are actually applied in all four
   traces. The main bundle contains these eight converted maps and the same
   canonical comparison system used by their definitions.
2. H2/H13: the packet no longer contains `SixFunctorMixedSupportCupProduct.lean`
   or a `def-sf-cup.json` override. Thus the held module and NL's reviewed record
   are left byte-identical to the base. The item module forms its finite cup
   using `CompactSupportFiniteProjection.component` from the landed
   `def-sf-constructible-projection-mates`, now added to `stmt_deps`. The other
   three cups use the selected datum's own exchange components. No held record
   is rewritten and no fixed upstream support is substituted for `S.finite`.
3. H9: `PoincareOperations.lean`, its `sk-def-ops.json` override and the unused
   import are removed from this delivery. The maps use the literal cohomology
   composites `Fib_s(S.support.obj K)` and `Fib_s(S.direct.obj L)`. The main item
   is not a redefinition of the additional duality/degree-extraction material
   of `sk-def-ops`.
4. Source citations use the stable `main-20261015` blueprint snapshot named in
   the node; no delivered docstring cites the moving `blueprint/latest` path.

Hypotheses and clauses of the item, in order:

- The prime p, exponent a>0, cardinality q=p^a, base finite field k_0 and its
  chosen algebraic closure k are `D : FiniteFieldDatum.{u}`. The distinct prime
  l and the fixed algebraic closure of Q_l are `C : D.CoefficientDatum`, including
  `C.different`. The finite coefficient extension is `{E : Type u} [Field E]
  [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]`. Its valuation ring,
  uniformizer and finite quotient are the existing `Padic` constructions. The
  positive exponent n is written `m+1`, covering every n>=1, with its bound
  `Nat.succ_le_succ (Nat.zero_le m)`.
- `d : ℕ` and `G : PoincareDualitySetting D.k₀ d` give exactly the smooth
  relative-dimension-d, separated, quasi-compact, geometrically connected model.
  Smoothness supplies locally finite type, hence quasi-compactness gives finite
  type. `pairingGeometricSpace D d G` is the existing geometric base change with
  structure morphism `G.structureMorphism D.k`; the target `sixFunctorPoint D`
  is Spec k. The bundled definition obtains separatedness and smooth relative
  dimension by the existing base-change instances. Its components are defined
  more generally and then specialized to this exact geometry.
- `S : SixFunctorDatum D C E (m+1) ...` is the recorded operation system, with
  constructible exceptional right adjoints, stage tensors and coherent exchanges.
  The finite input category is `finiteTorConstructibleCategory`, and the integral
  one is `finiteTorConstructibleIntegral ... |>.FullSubcategory`. The existing
  rational and common-stage constructible field-coefficient categories supply
  their inputs. All sites are the existing small pro-etale sites. Integral
  tensors are completed; rationalization and common finite extensions are the
  dependency constructions, never private replacements.
- Coefficient lines and twists are `sfOrientationReducedLine` and
  `sfOrientationIntegralLineOn`, and their rational/common-stage images. These
  recorded lines include the twist d and shift [2d]. The four `pairing*Zero`
  comparisons identify their twist-zero point lines with the exact unit object
  that occurs in the respective point system's `unitIso`.
- The expressions `F.obj ((S.<stage>.support f c).obj K)` and
  `F.obj ((S.<stage>.direct f).obj L)` are precisely RΓ_c and RΓ. For finite and
  integral coefficients, the support/direct helpers retain bounded
  constructibility and add the finite-Tor membership furnished by S, without
  adding a hypothesis to K or L. Their underlying objects are literally those
  of these operations.
- `pairingFiniteSiteCup` evaluates the recorded constructible projection at K
  and `pairingFiniteDirect S X L`, then applies `S.finite.support.map` to the
  tensor of the identity with `pairingFiniteCounit`. The latter is exactly the
  counit of `S.finite.pullDirectAdjunction`. The fixed-scalar projection's tensor
  is transported to the intrinsic tensor by
  `pairingFiniteRealizationTensor`, and then to S's finite tensor by
  `S.finiteTensorNormalization`. Both source and target comparisons are applied.
- For the other three stages, `pairingStageCup` is literally projection at
  `(K, S.direct.obj L)` followed by
  `S.support.map (T.obj K |>.map (S.pullDirectAdjunction.counit.app L))`.
  `integralTensorNormalization`, `rationalTensorNormalization`, and
  `commonStageTensorNormalization` identify the source stage tensor with the
  tensor used by the chosen point system, and their inverses are applied before
  the image of this composite.
- Thus each `*PairingCup` has source
  `Fib_s(Ra_!K) ⊗ Fib_s(Ra_*L)` and target `Fib_s(Ra_!(K ⊗ L))`, as a morphism
  in its coefficient derived category. The inverse point tensorator is the
  first composed arrow, not a separately stored possibility for conversion.
- `O : SfOrientationDatum S` retains the full coherent canonically normalized
  orientation family. The four traces use `SixFunctorOrientation O`,
  `.integralComponent`, `.rationalComponent`, and `.commonComponent`. They map
  this orientation by the corresponding support functor, then apply its
  constructible exceptional-adjunction counit. `smoothTraceOfOrientation`
  states this common formula; rational/common formulas write it out directly.
- The trace target is then converted by `pairingFiniteZero`,
  `pairingIntegralZero`, `pairingRationalZero`, or `pairingCommonZero`, and the
  forward point-unit isomorphism. The common formula additionally applies the
  base rational system's `unit_eq` through its common-stage inclusion. The finite
  comparison uses the recorded quotient reduction and the unique
  scalar-multiplication-normalized `pairingFiniteUnit`. Therefore each resulting
  target is the coefficient tensor unit Λ itself, and each source is
  RΓ_c(X,Λ_X(d)[2d]).
- `pairingPointIdentifications` retains the actual
  `PointFibreDerivedTensorCanonical` witness of `pointFibreDerivedTensor`. All
  eight arrows in `pairingData` refer to that same defined system. Neither
  properness nor ambient exceptional-adjoint admissibility is added. The
  compactification parameter is the one used by the recorded support operation.

Dependency declarations used (full signatures and docstrings read):

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`.
  `WeilConjectures.AlgebraicGeometry.PoincareDualitySetting`:
  `AlgebraicGeometry.PoincareDualitySetting`, `.geometricFiber`, `.structureMorphism`.
  The geometric dependency nodes' Mathlib matches supply spectrum, pullback,
  smooth relative dimension, separatedness, finite type and connectedness.
- `Sheaf.Paper.SixFunctorDatum`, `SixFunctorOperationDatum`, and its stage
  interfaces: `SixFunctorDatum`, `SixFunctorPushStage`, `SixFunctorExchangeData`,
  `SixFunctorSpace`, `sixFunctorPoint`, `sixFunctorStructure`, the support/direct
  domain proofs, tensor normalizations, and all recorded adjunctions.
- `Sheaf.Paper.ConstructibleProjectionMates`:
  `CompactSupportFiniteProjection.component`, `.partialTensor`, `.torPull`.
  `Sheaf.Paper.SixFunctorOrientation`: `SixFunctorOrientation` and its three
  higher-stage components; `SfOrientationDatum` and the shifted coefficient lines
  are the existing orientation interface.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`, `FiniteTorAmplitudeSites`,
  `DerivedPullbackTensorHom`: the constructible finite-Tor categories,
  `finiteIntrinsicDerivedTensor`, `finiteIntrinsicClosed`,
  `finiteIntrinsicTensorModels`, and the higher-stage tensor constructions.
- `Sheaf.Paper.FiniteCoefficientPoint`, `PointFibreDerivedTensor`:
  `pointFiniteSections`, `pointFibreIntegralAmbient`, `pointRationalFibre`,
  `pointQbarFibre`, `pointFibreDerivedTensor`,
  `PointFibreDerivedTensorComparisonData.tensorIso`, `.unitIso`.
- Helper dependencies: `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicModuleEquivalence`, `sfIntrinsicRealizationUnit`;
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; Mathlib's `HomologicalComplex.ιTensorObj`,
  `Functor.LaxMonoidal.μ`, exact-functor localization comparisons and the signed
  total tensor. Existing canonical operations and units are reused throughout.

Edge cases checked: m=0 means n=1 and is admitted; d=0 uses the unshifted
zero-twist line and the same counits; zero K or L is allowed; the formulas remain
well-typed on the empty scheme even though the main bundle requires the supplied
geometrically connected setting. Affine space is allowed without properness.
No degree-zero truncation is imposed on the cohomology complexes. Independent
small-site object and morphism universes remain u+1 and u. The finite coefficient
point functor explicitly uses the same locally-small module-derived model as its
canonical tensor system, through `HasDerivedCategory.ofIsGrothendieckAbelian`;
this is an instance choice, not an extra hypothesis or a universe equality.

Searches: the item search ledger records LeanFinder's mixed-support/purity query
(eight analytic orientation/volume hits), Loogle's adjunction/monoidal query
(twelve generic monoidal-adjunction identities), Mathlib grep for
`mixedSupportCupProduct|smoothTrace|pointFibreDerivedTensor|sfOrientation` (zero),
and LeanSearch's pro-etale pairing query (eight field-normalized-trace hits).
Project rg and the prescribed item-id search found existing finite etale pairings,
which do not give these four intrinsic pro-etale coefficient-complex maps. The
existing held cup notion is not copied into a dependency module. New-node search
results are stored in their `mathlib_searches`, including the actual machine
search responses. LeanSearch finds generic local generators and `ιTensorObj`;
Loogle's generator/tensorator query gives zero; Mathlib grep finds unrelated
coefficient-unit and module-presentation entries. The relevant generic APIs are
used. `blueprint_refs.py search` gives zero for 'pairing realization' and only
`def-pur-frame-class` for 'tensor generator'. Exact new-name rg across DAG,
WeilConjectures and Sheaf gives no output. The existing ordinary
`lem-exc-intrinsic-realization-tensor-complex` provides bare chain-isomorphism
nonemptiness, not the full normalized derived square; it cannot determine the
canonical comparison required here. Similarly the generic intrinsic tensor-right
comparison is bare nonemptiness. No exact normalized transport or unit comparison
was found. No statement correction and no STATEMENT-DISPUTED claim are needed.

## New nodes

`def-pod-pairing-tensor-generators` owns `PairingFiniteRealization.lean`. It defines
the homogeneous fixed-scalar total tensor generator and its scalar-unit
realization, reusing the existing exact equivalence. Source: the finite cup's
coordinate change in the item's blueprint display; signed totals and realization
are the recorded dependencies. The searches above found the general summand
inclusion, which is used, but no such normalized realization-generator interface.

`def-pod-pairing-tensor-normalization` owns
`PairingFiniteTensorNormalization.lean`. It defines normalized chain comparisons
and the full derived comparison square on every pair whose realizations are
K-flat, with equality on every homogeneous local pure tensor. Source: the same
finite cup coordinate change. Existing chain-isomorphism nonemptiness does not
supply this predicate or the localization square, as checked in the node/source
search. Its definitions are predicates and comparison types, with no sorry data.

`def-pod-pairing-finite-tensor-transport` owns
`PairingFiniteTensorTransport.lean`. It states unique existence of precisely that
normalized natural isomorphism and defines it by that unique specification.
Source: the same finite cup display and the tensor/realization dependencies.
The proof docstring explains local generation, sheafification, signed totals,
K-flat descent and uniqueness on all resolutions. The node includes the exact
existence-and-uniqueness claim of its postponed theorem. Searches found no exact
canonical normalized derived transport, only the bare ordinary comparisons.

`def-pod-pairing-coefficient-unit` owns `PairingCoefficientUnit.lean`. It defines
the coefficient unit in degree zero, its scalar-normalization predicate, states
unique existence, and defines the specified comparison. Source: the trace's
coefficient-unit identification in the second blueprint display. The predicate
requires the right-unitor equation on every K-flat representative and
x⊗a↦ax on local generators. The proof docstring explains descent and uniqueness.
Searches found generic complex tensor units and unitor APIs, not this interface
for the already selected intrinsic closed tensor system.

## Second reading by Q76

The dispatcher prohibits starting other agents. This is a separate self-check of
the five files against the item and four new nodes; the maintainer supplies the
independent review. I checked both endpoints of all eight composed maps, actual
application of every tensorator/unit map, finite-Tor membership, identity of the
finite support used in cup and trace, stage tensor normalization, zero-twist
normalization, and the complete geometry of the bundle. I removed the two
returned dependency overrides and their modules, replaced all stale record and
report claims about unapplied coordinate maps, and retained the canonical-model
witness. The two postponed uniqueness assertions match their new nodes and carry
complete proof plans. No diagnostic declaration or file-local notation remains.
All variables and universes are explicit; both auto-implicit options are false.

Validation: all five delivered modules compiled individually, in dependency
order, with scompile.py against the live published build. Consolidated library
compile times were 5.3s (unit), 12.4s (generators), 17.2s (normalization), 2.3s
(transport), and 15.2s (item); no errors or unexpected warnings. The final delivery
dry run is recorded below when complete.

Final dry run: `deliver2.py Q76 sk-def-pairing-data --no-push` returned
`OK (dry run): commit 81acc8c1593 passes the preflight and compiles; nothing pushed`.
The first repaired dry run's four missing `import_flags` fields were supplied as
empty lists; combined citation brackets were split into individual citations.
The saved packet's additional held-cup dependency was removed, and the landed
constructible projection dependency is the only existing-node addition.
