## Worker report

Module: `Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame`.
Main declaration:
`AlgebraicGeometry.DiagonalDifferenceReesFrame.diagonal_difference_rees_frame`.
The only postponed proof is this theorem. Its docstring gives all eight DAG proof
steps and their dependency names. `NormalFrame` and `CentredChart` expand the
witnesses in this item's conclusion; they do not replace any underlying
geometric notion. `CentredChart.map` is a real composite, with no postponed data.
There are no new DAG nodes, dependency repairs, or statement corrections.

I read the current node, every statement dependency and its recorded interface,
the proof dependencies' bindings, the role/stage rules and delivery-errors H.
I opened the current blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md`.
The example CompactObject module has been withdrawn; its node points to the
upstream definition. This delivery follows the required module-mode header.

Hypotheses, individually:

| Node hypothesis | Lean |
| --- | --- |
| Arbitrary field k | `(k : Type u) [Field k]` |
| Affine k-schemes U,V | `{U V : Scheme.{u}} [IsAffine U] [IsAffine V]`, `aU`, `aV` |
| Both are of finite type over k | `[LocallyOfFiniteType aU] [LocallyOfFiniteType aV]`; quasi-compactness follows from their affine sources, so this is finite type |
| h is a k-map | `(h : U ⟶ V)` and `hk : h ≫ aV = aU` |
| h smooth, separated, pure relative dimension d≥0 | `[IsSeparated h] [SmoothOfRelativeDimension d h]`, `(d : ℕ)` |
| Given etale V-chart u | `(c : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale c]`, and `hc` asserting its projection is h |
| No injectivity, positive rank or nonempty hypothesis | No such binder occurs |

The conclusion, clause by clause:

| Node clause | Lean |
| --- | --- |
| W, first projection, diagonal | `pullback h h`, `pullback.fst h h`, `pullback.diagonal h` |
| Ordered coordinates | The frame parameter is `fun i ↦ c.appTop (AffineSpace.coord V i)` |
| Differences y_i-x_i | Every difference map is written directly as `AffineSpace.homOfVector (pullback.fst h h)` with `snd.appTop (x i) - fst.appTop (x i)` |
| Open neighbourhood O of the whole diagonal and factorization s | `CentredChart.O`, `.s`, `.section_diagonal`; the equality forces containment of the entire image |
| Difference map etale over U | `.etale`; the map is over U by the definition of `homOfVector` |
| Cartesian square with left identity and bottom zero | `.zero_square : IsPullback s (𝟙 U) ... (AffineSpace.zeroSection ... U)` |
| Scheme-theoretic zero fibre, not pointwise equality | The preceding `IsPullback` is in Scheme |
| Ideal I, E=I/I², canonical psi | Diagonal `.ker`, `ConormalGradedAlgebra.piece ... 1`, `ConormalGradedAlgebra.symmetricComparison ...`; `.symmetric` asserts this actual map is an isomorphism |
| Normalized E ≅ Ω_(U/V) | `NormalFrame.conormal` with `.sign`, for every global a, using an actual ideal lift whose value is p2*a-p1*a |
| Correct sign [y(a)-x(a)] ↦ da | `.sign` has exactly that order of subtraction and the universal `relativeDifferentialsDerivation.d` on its right side |
| Ordered conormal basis corresponds to u*dt_i | `.differentialFrame` is an isomorphism from the free module sheaf; `.differentialFrame_value` sends each standard generator to d(c*t_i). Composing with `.conormal.symm` is the ordered conormal frame |
| Specific phi_N from relative Spec and this basis | `.normal`, `.normal_coordinate`; the latter uses the actual degree-one inclusion and `coneAlgebraIso`, the relative-Spec counit. The canonical psi's generator formula identifies this with relative Spec of psi and the frame |
| Over U, preserving augmentation sections | `.normal_over`, `.normal_zero` |
| Open restriction of the normal frame | `.normal_coordinate` quantifies over EVERY `T : U.Opens`, using the restriction of the same free generators and degree-one map |
| Use every normalized Rees-cone comparison | `.comparison_independent` and `.zero_endpoint` universally quantify over q satisfying the recorded `ReesConeNormalized`; the recorded existence theorem is imported |
| Zero coordinates (y_i-x_i)/t mod t | `.charts` gives f_i/t before reduction; `.zero_endpoint` reduces the same map along the actual zero-fibre inclusion; the q hypothesis is precisely the degree-one a/t mod t formula of the dependency, with `.normal_coordinate` fixing the frame |
| Independence of normalized comparison | `.comparison_independent` equates the composites for q and q', not an arbitrary cone automorphism |
| Actual extended-Rees deformation of s in O | `.deformation_model` identifies `s.ker.deformationSpace` with the inverse image of O in the diagonal's actual extended-Rees space; `.model_ambient` and `.model_parameter` preserve the ambient map and parameter |
| Actual induced deformation map | `CentredChart.map = deformation_model.hom ≫ deformation`; both sources are the recorded extended-Rees construction, expressed under its open-restriction isomorphism |
| t ↦ t and v_i ↦ (y_i-x_i)/t | `.charts` on EVERY ambient affine A contained in O, with the actual gluing-colimit leg. It uses `Ideal.extendedReesAlgebraT` and the Laurent representative `C f_i * T (-1)` |
| Deformation map etale | `.deformation_etale`; composing with the isomorphism `.deformation_model` gives etaleness of `.map` |
| Endpoint e at 1 | `.one_inclusion` uses the published `deformationSpaceOneFibre`; `.one_endpoint` is the equality with the difference map followed by the standard t=1 inclusion |
| Endpoint phi_N at 0 | `.zero_inclusion` uses the published `normalConeToDeformationSpace`; `.zero_endpoint` identifies the endpoint with q then phi_N followed by the standard t=0 inclusion |
| Agreement on smaller centred neighbourhoods and open restriction | The theorem's second conjunct compares ANY two `CentredChart` witnesses on ANY common open `T`, by the actual `Scheme.homOfLE` maps on inverse-image opens. This includes intersections and further open restriction. The chart formulas themselves quantify over all affine opens, hence commute with section restrictions |
| Change of etale chart gives the induced differential frame change | The last conjunct quantifies over every second etale chart and normalized frame. It supplies mutually inverse matrices M,H, expresses the new differentials using M, and asserts that exactly the same M changes the normal coordinate functions. Since U is affine these section equations are the sheaf frame-change equations; their restrictions hold on every open |
| d=0: O≅U | `.rank_zero : d = 0 → IsIso s` |
| d=0: E=0 and Sym(0)=O_U | `.rank_zero_conormal`, `.rank_zero_symmetric` |
| d=0: identity deformation data | `.rank_zero_deformation` together with `.deformation_over`, `.normal_over` and `.normal_zero`; affine space on the empty coordinate type is canonically its base |
| Empty U allowed | No `Nonempty U`, no point choice, no nonzero-ring hypothesis on section rings |

Representation details that matter for review:

* On affine U, the normalization for all global a determines the conormal sheaf
  map: the differential module is generated by these da, and their localizations
  generate on principal opens. Thus this does not omit a local normalization.
* The deformation restriction model is not an unconstrained isomorphism. It
  preserves both the ambient map and t. Extended-Rees rings are actual subrings
  of Laurent-polynomial rings, t is a non-zero-divisor, and their elements are
  generated by r, t and a/t. Therefore those two equations force the canonical
  map on a/t after multiplication by t. This also applies to the zero ring.
* The map with literal source D_s O is provided as `.map`. The restricted global
  zero fibre is the normal cone of the original diagonal, as in the node; this
  is why the endpoint equations can retain its fixed normalized comparisons.
* The free-sheaf frame and the degree-one coordinate formula determine phi_N;
  merely assuming that an arbitrary zero-preserving isomorphism exists would
  not have been sufficient.

Statement dependencies used:

* `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `Scheme`, `Scheme.Hom`.
* `def-pc-fibre-product`: Mathlib `Limits.pullback`, `.fst`, `.snd`, `.diagonal`.
* `def-sbc-affine-space`: its mathlib_match `AlgebraicGeometry.AffineSpace`,
  `.coord`, `.homOfVector`, `.map`; coordinates use `ULift (Fin d)`.
* `def-sbc-smooth-morphisms`, `def-weil-etale-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth` and `.Etale`,
  `SmoothOfRelativeDimension`, `Etale`.
* `def-weil-scheme-morphism-properties` is the recorded convention node. Its
  referenced properties are `IsSeparated` and `LocallyOfFiniteType` here.
* `def-sbc-closed-immersion-ideal-sheaf`: Mathlib `Scheme.Hom.ker`.
* `lem-pur-conormal-graded-algebra`:
  `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra`, `.presentation`, `.piece`,
  `.power`, `.powerInclusion`, `.representative`, `.symmetricComparison`.
* `def-sc-relative-differential-sheaf`:
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `Scheme.Hom.relativeDifferentials`, `.relativeDifferentialsDerivation`.
* `def-pur-normal-bundle`: its recorded
  `Sheaf.Paper.PurityNormalProjection` imports the owning `PurityNormalBundle`
  module; its `normalCone`, `projection`, `zeroSection` are used. The actual Rees
  cone is distinguished and compared via the recorded normalized comparison.
* `def-asd-vector-bundle-zero-section`:
  `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`, the relative-Spec
  anti-equivalence used by `PurityNormalBundle` and `coneAlgebraIso`; standard
  affine zero sections use the published `AffineSpace.zeroSection`.
* `def-pur-rees-cone-normalization`:
  `Sheaf.AlgebraicGeometry.ReesConeNormalization`, `coneAlgebraIso`,
  `ReesConeNormalized`.
* `lem-pur-rees-cone-normalized-existence`:
  `Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence`,
  `AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison_exists`.
* `def-pur-dnc-section-family`:
  `Sheaf.Paper.PurityDncFamilyIntrinsic` imports the owning
  `WeilConjectures.AlgebraicGeometry.DeformationToNormalCone` construction.
  This statement uses its geometric part `Scheme.Hom.deformationSpaceProj`,
  `.deformationSpaceOneFibre`, and the ideal's actual `deformationSpace`,
  `reesPresheaf`, `normalConeToDeformationSpace`. No coefficient setting is
  imposed on this geometric theorem.

All stated proof-dependency modules are imported, with plain imports for those
needed only by the proof. There is no import of the downstream
`Sheaf.Paper.DiagonalDncChartNormalization`, avoiding a proof-import cycle.

Searches for existing material (2026-10-24):

* `msearch.py ... leansearch "Etale coordinates on a smooth diagonal identify
  its normal cone and give the homogeneous normalized Rees deformation frame"`:
  eight hits, including `exists_etale_mvPolynomial`, formal-etale criteria and
  `RingHom.Etale`; no complete match.
* `msearch.py ... leanfinder "Etale coordinate differences identify the normal
  cone of the smooth diagonal and give normalized extended Rees deformation
  coordinates"`: eight hits on standard-etale presentations and existence of
  etale polynomial charts; no complete match.
* `msearch.py ... loogle "KaehlerDifferential, Algebra.FormallyEtale"`:
  differential vanishing and differential base-change equivalences; no centred
  diagonal square, normal frame or Rees endpoint statement.
* `msearch.py ... grep "normalCone|ReesConeNormalized|conormal.*frame"
  AlgebraicGeometry`: zero Mathlib hits.
* `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, plus the exact item-id grep upstream:
  no declaration of this item. The downstream chart-normalization module has
  related partial statements (`chartCoordinateDifferences_neighbourhood`,
  `chartDiagonalConormal_differentials`, `chartNormalCoordinateMap_spec`) but
  lacks this combined Rees-generator/endpoint/restriction statement. No existing
  difference map or normal-cone construction is redefined here: the existing
  operations are applied directly in the types. The two structures only package
  this theorem's witnesses and constraints.

Edge cases checked before and during writing:

* For d=0 the centred zero square forces s to be an isomorphism; the free
  sheaf on `ULift (Fin 0)` is zero and the target of the deformation is A¹_U.
* For empty U, global section rings are zero rings; all witness and equation
  types remain valid and the matrix dimension-zero assertions are harmless.
* A disconnected double etale cover shows why the unshrunk zero fibre need not
  be the diagonal. O is existential and the scheme-theoretic Cartesian square
  is retained; no injectivity condition is imposed on c.
* Positive characteristic, imperfect fields and arbitrary natural d are allowed.
* The displayed sign is p2 minus p1, and the same sign is used in the Rees
  representatives and differential frame. There is no hidden transpose in the
  M(j,i) matrix convention.
* Nonaffine O and arbitrary (possibly nonaffine) base opens T are allowed.

No `STATEMENT-DISPUTED` issue was found. The source statement is unchanged.

Validation: compiled with the prescribed `scompile.py` against the live server,
in module mode, with explicit universes and both auto-implicit options disabled.
The main theorem has `sorry`, as stage 2 requires; all definitions have real data.

## Second reading by Q79

I reopened the source node and the final file for a second pass. This is an
author rereading, not a claimed independent peer review: the dispatcher brief
forbids spawning other agents and assigns independent review to the maintainer.

The pass checked every row above against the actual field or conclusion. It
caught the need to state neighbourhood agreement and chart-change matrices
explicitly, to state the normal-coordinate formula on all base opens, and to
retain the literal D_s O source. The final theorem includes the two compatibility
conjuncts; `normal_coordinate` quantifies over all opens; and
`deformation_model`, its ambient/parameter equations and `CentredChart.map`
provide the actual restricted-section map. Rank-zero deformation invertibility
was also added explicitly. No dependency or node statement changed.
