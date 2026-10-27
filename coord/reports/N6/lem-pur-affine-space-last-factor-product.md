## Worker report

The module `Sheaf.Paper.AffineSpaceLastFactorProduct` states
`AlgebraicGeometry.ProEtale.AffineSpaceLastFactorProduct.affineSpace_lastFactor_product`.
Its proof is the sole `sorry` in the delivery. All helper definitions have actual data.
The original mathematical statement, proof and proof dependencies are unchanged.
Two already-landed definition dependencies are added:
`def-pur-finite-product-compactification-data` owns the existing
`finiteProductChosenForward`, `finiteProductComposition` and `FiniteProductGeometry`,
which supply the concrete maps with arbitrary displayed Cartesian models and normalized
compactification changes; `def-pur-finite-forward-tensor-symmetry` owns the actual
signed derived swap. No new independent notion or dependency module is needed.

The meaning of each hypothesis and clause is as follows (helper names in this list
are in namespace `AlgebraicGeometry.ProEtale.AffineSpaceLastFactorProduct`).

* The finite-field and finite-coefficient conventions, including ell different from
  the characteristic, the finite coefficient extension and its positive exponent,
  are the argument `P : WeilConjectures.PurityFiniteSetting.{u}`. The fixed-scalar
  presentation uses the existing `AffineLinePurity.Ring P`: this is
  `ULift (O_E/(varpi_E^((P.level-1)+1)))`. The recorded positive level identifies
  `(P.level-1)+1` with `P.level`, as in `AffineLinePurity.ringEquiv`. This is the
  coefficient of the recorded affine-space comparison, with no new scalar action.
* The separated finite-type k-scheme is `Y`, with structure morphism `aY` and
  `[IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]`. An explicit structure
  morphism matches the recorded affine-space comparison interface. All other schemes
  and maps are the polynomial affine projections and their base changes; no extra
  geometric hypotheses are imposed.
* Write `m=d+1`. Thus `d : Nat` covers exactly every integer m at least one.
  In `Assertion`, `X_m` is `iteratedAffineLine Y (d+1)`, `p` is its recorded
  `iteratedAffineLineProj`, `X_1` is `AffineSpace PUnit Y` and `a` its structure map.
  `X_(m+1)` is literally its last relative affine line, `q=lastProjection Y (d+1)`,
  and `r=AffineSpace.map PUnit p`. `AffineSpace.isPullback_map` identifies the actual
  common Cartesian model, with `sq.w : q ≫ p = r ≫ a`. The total projection is
  definitionally the next iterated projection. Both orderings use that same scheme.
* `M=positiveTate P X_m d` is the ordered (d+1)-fold tensor of the recorded
  `shiftedLine P X_m`. Its first factor is that line itself and every later factor
  is appended by the recorded tensor bifunctor, giving A(m)[2m].
  `N=shiftedLine P X_1` is T=A(1)[2]. The source H of the total compact support is
  literally `((tensor A W).obj ((inverseImage A q).obj M)).obj
  ((inverseImage A r).obj N)`. This is T_(m+1) under exactly the indicated
  q* T_m tensor r* T identification in the question. No unspecified isomorphism
  or orientation is introduced. The conclusion is in these identified coordinates.
* `V_m`, `U`, and `V_(m+1)` are the actual values of `rightDerivedLowerShriek` for
  `p`, `a` and `q ≫ p`, on M, N and H. `Equation` retains three separate antecedents
  `DerivedCategory.constructibleFiniteTor` for these three outputs. This is the
  recorded fixed-scalar predicate of `def-weil-finite-tor-amplitude`.
* Both complete tensor domains are retained as
  `d : FiniteForwardProductDomain ... sq M N` and
  `d' : FiniteForwardProductDomain ... sq.flip N M`. These include the input tensor,
  the first and transposed projection tensors, the exchanged tensor, and the
  exterior tensor, all bounded below and of etale origin. The swapped input tensor
  is the input clause in d'. No domain antecedent is replaced by a conclusion.
* `exchange A sq N` is the actual component
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap ... sq.flip ca` at N.
  It is E: p* U -> Rq_! r* N. Its q compactification is precisely ca base changed
  along p, as required by the finite chosen-compactification exchange definition.
  `_hE` and `_hE'` retain both exchange invertibility assumptions.
* `_hPFq`, `_hPFp`, `_hPFr`, `_hPFa` retain exactly the four specified projection
  transformations, at (q,r*N,M), (p,M,U), (r,q*M,N) and (a,N,V_m). Each uses
  `finiteForwardProjectionMap`, literally the component of the counit-defined PF.
  The q and r compactifications are the indicated base changes.
* `composition` is the existing `finiteProductComposition`, transporting the
  normalized `originCompositionAmbient` from the same chosen compactifications.
  `_hAlpha` and `_hAlpha'` retain the two product-compositor invertibilities.
  The theorem's affine specialization installs compactifications from the existing
  `projection_geometry`, `affineTraceLineCompactification` and base changes. These
  are derived applicability data, not additional assumptions on the schemes.
* `kappa` is a supplied isomorphism from the actual total compact support of H to
  V_m tensor U. The antecedent `kappa.inv = forward A sq M N d.external` fixes it
  to the specified binary construction. `forward` is the existing
  `finiteProductChosenForward` with the exact six factors: signed symmetry, PF_a,
  Ra_! of signed symmetry, Ra_! of (Ex tensor identity), Ra_! of PF_r, alpha_(a,r).
  Its inverse is exactly the inverse six-factor construction specified in
  `thm-sf-kunneth-relative`. Only this explicit construction is used. In particular
  there is no argument of type `SixFunctorDatum` or `RelativeProductPresentation`.
* `inverseProjection` is exactly Pi: Rq_!(sigma_(Q,R)) followed by PF_(q,R,M)^(-1)
  followed by sigma_(W,M). The tensor symmetry is the recorded
  `finiteForwardTensorSymmetry`, obtained from the signed homotopy-complex swap.
* The equality concluding `Equation` is `kappa.hom = inv alpha ≫ Rp_!(Pi) ≫
  Rp_!(1_M tensor inv E) ≫ inv P_U`. Lean composition is left-to-right, so this
  is precisely the displayed formula in the node. It is equality of actual derived
  morphisms. It contains neither an integration map nor a permutation-invariance
  claim for purity. The unused right unitor mentioned in the node is unnecessary
  in this binary-product formula.

Dependency declarations read and used:

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its
  quotient ring/ULift conventions.
* `Sheaf.Paper.AffineSpacePurityComparison`: `C`, `tensor`, `inverseImage`,
  `action`, `shiftedLine`, `lastProjection`, `projection_geometry`; its public
  `Sheaf.Paper.AffineLinePurityComparison` exposes `Ring` and `ringEquiv`.
  The coefficient twists are the compared ordinary finite Tate line fixed in this
  recorded definition, not another twist. `IntrinsicCoefficientTwistsUnrestricted`
  and the finite twist comparison remain publicly imported through this module.
* `Sheaf.Paper.FiniteForwardProductSymmetry`: `finiteForwardTensorSymmetry`,
  `finiteForwardProjectionMap`, `FiniteForwardProductDomain`; its source was read
  in full, including the six-factor construction and `finiteForwardProduct_symmetry`.
* `Sheaf.Paper.FiniteProductCompactification`: `FiniteProductGeometry`,
  `finiteProductChosenForward`, `finiteProductComposition`. The latter is the
  actual conjugation of the recorded `originCompositionAmbient` by the canonical
  compactification comparisons. These definitions are owned by the already-landed
  `def-pur-finite-product-compactification-data`, now cited in stmt_deps; the binary
  compactification comparison theorem is not added to obtain its data. The signed
  swap is owned by `def-pur-finite-forward-tensor-symmetry`, also cited in stmt_deps.
  Their recorded signatures and docstrings were reread for this repair.
* `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: `originCompositionAmbient`
  and its identity normalization, through the above canonical composition factor.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: supplied coefficient interface
  was read; the finite transformations used here are its documented existing
  finite specializations in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`
  (`projectionMapOfCompactification`) and `.LowerShriekBaseChange`
  (`rightDerivedLowerShriekOfCompactificationBaseChangeMap`). No replacement of the
  finite transformations by arbitrary supplied maps is made.
* `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `sfIntrinsicCompactSupport`
  is the intrinsic Rg_* j_! realization. The recorded forward-product module uses
  its fixed-scalar coordinate form `rightDerivedLowerShriekOfCompactification`
  (same exact open extension followed by proper derived image). This delivery
  stays in that already-recorded coordinate system throughout; it does not mix
  intrinsic tensor objects with fixed-scalar arrows or define new compact support.
* `Sheaf.Paper.FiniteTorAmplitudeSites` and its public dependencies:
  `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor`, the recorded
  fixed-scalar condition, not an assumed vanishing theorem or a stronger predicate.
* `Sheaf.Paper.RelativeKunneth`: `relativeKunnethIso`, `relativeKunnethMap` and their
  signatures/docstrings were read. Those require an abstract six-functor datum;
  this item expressly stipulates only their explicit binary construction. Hence
  the finite factor composite above fixes kappa without invoking that theorem.
* Mathlib `AlgebraicGeometry.AffineSpace`, `AffineSpace.map`, `isPullback_map` and
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` give the affine products and
  the scheme properties (the latter dependency is a convention-only node).
* The already stated proof dependencies are imported: `TwistPreservesFiniteness`,
  `ProEtaleConstructibleOrigin`, and finite `Derived.TensorResolution`, together
  with the statement modules already publicly imported above.

Edge cases checked: d=0 gives m=1 and both Tate factors are single shifted lines;
all positive coefficient exponents occur, including n=1 and ramified coefficient
extensions, since the recorded Ring uses the level-1 reindexing. m=0 is excluded
exactly as in the node. The empty base and nonreduced separated finite-type bases
are allowed; every geometric map and Cartesian model is a polynomial construction.
The paired signed symmetries are retained even when signs are trivial (ell=2).
The theorem never assumes smoothness of the base, purity of the constant object,
a tensor symmetry isomorphism as independent data, or an integration identity.
Universe u is explicit; the coefficient and ModuleCat lifts are exactly the recorded
fixed-scalar convention. Every variable is explicitly bound (`autoImplicit false`).

Searches for an existing statement (2026-10-25):

* msearch.py leanfinder, query "The compact support Kunneth isomorphism for affine
  space and the affine line is the inverse projection formula computed through
  the opposite projection": eight affine-space chart and polynomial-spectrum
  hits, including `AffineSpace.SpecIso_inv_over`; no compact-support equality.
* msearch.py loogle, query `"Kunneth"`: zero hits.
* msearch.py leansearch, query "The inverse finite coefficient compact support
  Kunneth product is obtained using the other projection and tensor symmetry":
  tensor commutativity, Kronecker and Cartesian braiding hits; no sheaf product map.
* msearch.py grep, regex `kunneth|lastFactorProduct|compactSupport.*product`,
  Mathlib/AlgebraicGeometry: zero hits.
* rg in lean/WeilConjectures and lean/Sheaf for the item id, last-factor names and
  compact-support/Kunneth patterns: no exact statement; the finite forward symmetry
  and the arbitrary-compactification composite are the reusable components.
  Upstream ordinary/exceptional Kunneth declarations do not state this equality.
* Read the current blueprint/latest integration paragraph and the recorded item's
  complete five-step proof. The example CompactObject Sheaf module is withdrawn;
  its node now records the identical upstream declaration, which was noted when
  checking the requested example and record convention.

Validation: scompile.py compiled both sandbox and final library-path module successfully
(12.0 s and 8.2 s), without errors or warnings. No source files in the shared repository
were edited and no direct git command was run there. No statement dispute or correction.

## Second reading by N6

The dispatcher brief forbids starting other agents and assigns independent review to
the maintainer. This section records a separate in-thread rereading, not a claim of
another worker's independent review. I reopened the full node and the final Lean file.
The critical checks were the direction and order of both symmetries in Pi, the direction
of the compositor, and the stipulated binary construction. `inverseProjection` has
Rq_!(Q tensor R) as source and M tensor Rq_!R as target; after applying Rp_!, the map
`((tensor A X).obj M).map (inv E)` has exactly the needed source and target. Inverting
PF_p then lands in V_m tensor U. The hypothesis on kappa has the opposite direction
and pins its inverse to the six-arrow forward product, rather than assuming the
conclusion itself. Both tensor domains, all three finite-Tor output hypotheses, four
projection invertibilities, both exchanges and both relevant compositors are present.
The d+1 indexing matches m>=1, and positiveTate has d+1 shifted-line factors. The total
object is the explicit H under the node's stipulated Tate identification. The actual
last-coordinate scheme map and base change are used. Compiler repairs corrected the
implicit coordinate argument of isPullback_map and the orientation of compactification
transport; neither changed the mathematical statement. No new node, dependency repair,
arbitrary canonical map, or source correction is present.

## Return repair: H2

The independent review of immutable head `2bea48e4b2fa` found one metadata defect:
the added theorem dependency `lem-pur-finite-product-compactification` was being used
only to reach definitions already owned by `def-pur-finite-product-compactification-data`.
Rebased the sandbox node on the current main node, preserving every main field other
than `lean` and the authorized additional definition dependencies. Replaced that added
theorem dependency by the owning definition node and updated `lean.note`. Also followed
the advisory to cite `def-pur-finite-forward-tensor-symmetry` for sigma. Both definition
nodes already exist on the current base, with existing:true records for the same
modules and declarations imported by the delivery. No dependency node is edited.

The Lean file remains byte-identical to the reviewed delivery: SHA256
`2a544dd1ecd71ed969c24b0832e787cd3168fd7694e8d3ca56aa6cb5b19be3d8`.
The maintainer's clause-by-clause mathematical approval therefore still applies.
A second in-thread reading checked the new ownership records against the definitions
of `FiniteProductGeometry`, `finiteProductChosenForward`, `finiteProductComposition`,
and `finiteForwardTensorSymmetryNat`/`finiteForwardTensorSymmetry`, and verified that
all existing original theorem statement/proof dependencies remain present. The original
mathematical statement, proof, proof_deps and declaration signature are unchanged.
