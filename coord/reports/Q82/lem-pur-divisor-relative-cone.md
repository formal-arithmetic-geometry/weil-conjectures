## Worker report

Repaired the substantive return on immutable head `796e2f5338c0`. The initial
saved-packet dry run passed (`6b5526f33c`), but the required self-check confirmed
that its signature still contained the returned defects. This delivery changes
the statement interface and its report; it is not an unchanged re-push.

The sole postponed theorem is
`AlgebraicGeometry.Etale.relativeConeSupportComparison`, in
`Sheaf.AlgebraicGeometry.PurityRelativeCone`. The concrete construction remains
Mathlib's mapping cone shifted by -1. `relativeFiberMap` is imported and used,
and no theorem or definition chooses data from a sorried existence assertion.
The helper structures package the equations in this node's statement; they do
not define a replacement support theory, a replacement resolution, or an
arbitrary comparison map.

The statement and its helper structures render the node as follows. All names
below, unless qualified, are in `AlgebraicGeometry.Etale.RelativeCone`.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Scheme T | `T : Scheme.{u}` |
| Closed immersion and its actual open complement | `i : Z ⟶ T`, `[IsClosedImmersion i]`; the theorem's relative group uses `Scheme.Etale.mk i.openComplement.ι` |
| An arbitrary abelian etale sheaf, with its supplied nonnegative injective resolution | `F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1}`, `I : InjectiveResolution F` |
| Either small site | The conclusion supplies systems `E` on `T.smallEtaleTopology` and `P` on `Scheme.ProEt.topology T`, with the open-immersion predicate on their object arrows; the pro-etale ambient object is restricted to be etale over T, exactly the neighbourhoods used by the node |
| Actual A and B, extended by zero | `sections J V I.cocomplex` and `sections J W I.cocomplex`; specialize V to the terminal object and W to the open complement |
| A and B compute derived sections | `computation J (evaluationFunctor J V) I q` and the same construction at W are actual canonical isomorphisms, defined by `I.isoRightDerivedObj` composed with `extendHomologyIso.symm`; there are no equalities of unrelated homology and right-derived objects |
| Actual restriction and relative cone | `restrictionComplex J f I.cocomplex` and `fiber J f I.cocomplex`; `fiber` is literally `mappingCone ...` shifted by -1 |
| K is the kernel of restriction | `Realization.kernelIso` identifies the dependency's termwise supported-section complex with `kernel (restrictionComplex ...)`; `kernel_components` specifies its composite with the kernel inclusion in every nonnegative degree (negative degrees are zero) |
| Inclusion k ↦ (k,0) is a quasi-isomorphism | `Realization.κ`, `κ_components`, and `κ_quasiIso`; the two component equations specify the first coordinate and the zero second coordinate |
| Canonical identification with R^q Γ_Z | `Realization.e`; `normalization` is `H(kernelIso.hom) ≫ H(κ) ≫ e.hom = computation.inv` |
| The displayed etale e is the same identification | The theorem explicitly quantifies `e : ∀ q, relativeCohomology ... ≅ supportCohomology i q F` and equates its hom with the E-realization of `supportRestrictionArrow i` |
| Forgetting support under that identification | `Realization.forget` equates `e.hom ≫ (NatTrans.rightDerived (forgetSupport J f) q).app F` with homology of the first cone projection followed by the canonical absolute computation |
| Localization boundary, including its sign | `Realization.localization` equates `H(boundary).hom ≫ e.hom` with the shift-homology isomorphism, the connecting morphism `exact.δ` of the kernel short exact sequence, and the supported-section computation. `boundary` is the shifted `mappingCone.inr`, i.e. (0,-b) after changing from Mathlib's cone coordinate to the node's signed coordinate |
| Coefficient naturality and R^q Γ_Z maps | `System.coefficients` uses an arbitrary actual lift φ with the augmentation equation for α, then equates `H(relativeFiberMap) ≫ e'.hom` with `e.hom ≫ (supportedSectionsFunctor.rightDerived q).map α`; its second conjunct is `TriangleSquare` for these prescribed section maps |
| Resolution independence | In `System.coefficients`, take α = identity and any two resolutions I and I'. This quantifies every augmentation-preserving comparison lift, rather than an arbitrary isomorphism. Applying it twice also gives independence of the lift |
| Etale-neighbourhood restriction | `System.objects` uses actual object arrows v and w and the square `f' ≫ v = w ≫ f`; take V' an etale neighbourhood and W' its inverse image of W. The e-equation uses `NatTrans.rightDerived (supportRestriction ...)`, and the second conjunct gives the projection and boundary squares |
| W' ⊆ W, enlarging support | In the same `objects` field take v = identity, w the inclusion W' → W, and f' = w ≫ f; no neighbourhood is substituted for this separate case |
| Canonical topology comparison | `pullbackSections` evaluates the comparison adjunction unit followed by the direct image of β. `IsLift` imposes `L(I.ι^0) ≫ β^0 = γ ≫ K.ι^0`. Thus a and b are defined section maps, not existential arbitrary arrows |
| Comparison exists and is invertible for ν⁻¹F | `TopologyComparison.lift_exists` supplies augmented lifts; `sections_isIso` gives the actual objectwise derived pullbacks, and `cone_isIso` gives invertibility of the homology map of their `relativeFiberMap` for γ = identity, in every q ≥ 0 |
| Comparison carries the supported identification | `TopologyComparison.support` equates the map conjugated by E.e and P.e with the map induced on the actual kernel complexes by the unit-plus-lift section square, transported by the canonical right-derived computation isomorphisms |
| Comparison forget-support and boundary compatibilities | `TopologyComparison.projection_boundary` states the two chain-level commutative squares for these actual comparison section maps |
| Comparison independence and coefficient compatibility | `lift_independence` compares any two augmented lifts of the same γ. `coefficients` equates the two homology composites for α and Lα, with arbitrary augmentation-preserving resolution lifts |
| Comparison etale restriction and support enlargement | `TopologyComparison.objects` equates the two actual cone chain-map composites for object squares; the neighbourhood and identity-on-V enlargement squares are separate specializations as above |
| Arbitrary pro-etale coefficient map ν⁻¹F → F' | All of `lift_exists`, `support`, and `lift_independence` quantify this actual γ and a resolution K of F'. `postcomposition` equates the map for γ ≫ δ with the composite for γ and the resolution lift of δ. Taking γ = identity gives exactly composition of the comparison with any map ν⁻¹F → F', with the supported-class identification specified by `support` |

The generic site notation is a presentation of the same objectwise section
construction needed for the restriction clauses. At the terminal/open pair on
the etale site, it is definitionally the imported `relativeSectionComplex` and
`relativeCohomology`. The theorem's e has those exact dependency types. On the pro-etale side, `Etale V.hom` restricts the ambient objects to the
etale neighbourhoods of T named by the node (including the identity of T);
no naturality at arbitrary extra pro-etale neighbourhoods is added. Its
supported functor is the recorded
`CategoryTheory.Sheaf.supportedSectionsFunctor`, which applies equally to
abelian pro-etale sheaves. The dependency's separate pro-etale ModuleCat
specialization is not used in place of abelian coefficients.

The old etale alias `relativeProjection := relativeForgetComplex` is removed.
`projection` now gives the general two-complex formula needed also for the
pro-etale side and for neighbourhood objects; at the etale terminal/open pair
it is the formula of the imported `relativeForgetComplex`. There is a single
such helper, and no second etale support or relative-cohomology definition.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.RelativeEtaleCohomology`: `relativeSectionComplex`,
  `relativeCohomology`, `relativeFiberMap`, `relativeForgetComplex`, and its
  section-complex definitions.
- `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `CategoryTheory.Sheaf.supportedSectionsFunctor`, its additive instance,
  `AlgebraicGeometry.Etale.supportRestrictionArrow`, `supportSections`,
  `supportCohomology`, and `supportCohomologyIso`. `computation` uses exactly
  the same `I.isoRightDerivedObj` as `supportCohomologyIso`.
- Mathlib's recorded `Scheme`, `IsClosedImmersion`, `IsOpenImmersion`,
  `Scheme.smallEtaleTopology`, `Scheme.ProEt` / `Scheme.ProEt.topology`,
  `InjectiveResolution`, actual mapping cones and shifts, `kernel`,
  `ShortComplex.ShortExact.δ`, `InjectiveResolution.isoRightDerivedObj`,
  `NatTrans.rightDerived`, `extendHomologyIso`, and the shift-homology iso.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`; the abelian realization used in maps is
  `ProEtale.comparisonAdjunction`, `comparisonUpperStar` and
  `comparisonLowerStar` from the imported upstream comparison framework.
- Proof-dependency modules are imported without `public`, including the
  kernel-cone quasi-isomorphism, injective restriction, objectwise comparison,
  comparison acyclicity, derived-map-via-lift, Leray, and exact-sequence APIs.

Edge cases were checked against the actual formulas: empty support has r =
identity and an acyclic cone; full support has the empty-open section complex
zero and the relative group is absolute cohomology. Zero coefficients yield
zero derived groups even for a nonzero acyclic resolution. In degree zero,
`localization` uses H^-1(B) = 0 through its shift isomorphism, so it does not
drop the zero-degree case. Negative complex degrees remain supplied by the
extension-by-zero construction. Identity coefficient maps, identity object
squares, equality W' = W, the empty scheme, and arbitrary (including zero)
γ are retained. The cone sign check is D(a,b) = (da,-ra-db) in the raw shifted
Mathlib coordinates; replacing the second coordinate by its negative gives
D(a,b_signed) = (da,ra-db_signed), and shifted inr becomes (0,-b).

Searches retained from the saved packet and repeated for this repair:

- `msearch.py ... leanfinder` with “relative section mapping cone computes
  cohomology with support naturally under etale proetale comparison”: eight
  hits about CM5b mapping-cone factorizations and etale loci, no matching theorem.
- `msearch.py ... loogle InjectiveResolution.isoRightDerivedObj`: the remote
  index reported unknown identifier and zero hits. Direct Mathlib source
  inspection found and read its exact declaration and naturality lemmas.
- `msearch.py ... grep 'relativeConeSupportComparison|RelativeCone|isoRightDerivedObj'
  Algebra/Homology`: zero indexed hits. Direct `rg` found the actual extension,
  shift, connecting-map and right-derived APIs in pinned Mathlib; those APIs
  are reused.
- `rg` in `WeilConjectures` and `lean/Sheaf` found no declaration of this
  theorem or these helper names. Unrelated relative categorical-cone modules
  and supported quasi-coherent cones are not the abelian section-cone theorem.
- Direct search for this node id in upstream `WeilConjectures` found no match.

No mathematical node correction, new independent definition node, or dependency
record repair is needed. All helper declarations belong to the realization and
compatibility assertions of this node and are listed in `lean.declarations`.

## Second reading by Q82

This is a separate self-check pass of the worker, not a claim that another
agent read the packet: this dispatch explicitly forbids starting other agents.
The maintainer performs the independent review.

Read the node and every structure field again, following the table above. The
returned object equalities are replaced by canonical isomorphism constructions.
The support identification is tied to Hκ by `normalization`, and its forget and
boundary fields use the derived kernel inclusion and the actual localization
connecting map. Neither is an equation of a term with itself. The old duplicate
etale projection alias, tautological support equation, Iso.ext uniqueness clause,
and arbitrary existential section maps have been removed.

The new resolution clause compares actual augmented lifts over identity
coefficients. The object clause includes both the neighbourhood pullback square
and the independent identity-on-ambient-object support-enlargement square.
Both site systems use abelian sheaves and have the same support realization.
The topology comparison uses the adjunction unit and an augmented lift, is
independent of that lift in cohomology, and has explicit coefficient, object,
projection, boundary and kernel-support equations. Its final clause has the
actual arbitrary γ : ν⁻¹F → F', not an endomorphism of an unrelated resolution.
The report identifies the corresponding fields precisely rather than attributing
missing clauses to generic cone-functoriality equations.

The first repaired-packet preflight exposed a source-reader namespace mismatch:
it treated the shortened `end RelativeCone` after a dotted namespace as closing
the whole namespace. The module now uses explicit nested namespace blocks,
with the same Lean declaration names. No project tool was changed.
