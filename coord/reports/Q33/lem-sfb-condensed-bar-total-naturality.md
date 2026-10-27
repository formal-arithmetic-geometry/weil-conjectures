## Worker report

Item: `lem-sfb-condensed-bar-total-naturality`, group Q33, stage 2.
Module: `Sheaf.CategoryTheory.CondensedBarTotalNaturality`.
Primary declaration: `CategoryTheory.CondensedBar.augmentation_resolution_naturality`.
The nine declarations recorded together in `lean.declarations` render the entire node.
Seven theorems have `sorry` proofs; the two definitions have actual data. The node's
statement, statement dependencies, proof and proof dependencies are unchanged.

The retained sandbox contained no delivery files at the beginning of this retry.
The live node has its independently reviewed stage-1 split and no Lean attachment.
This packet adds the actual stage-2 module and its attachment; it does not resubmit
the unchanged stage-1 split. There is no repair note for this item.

The blueprint source was read at
`main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`:
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
As the node explicitly records, its internal-bar argument is an agent expansion
supporting that paragraph, with the external internal-condensed reference still WANTED.
The eleven reviewed node proof steps supply the detailed proof plans in the docstrings.

Hypotheses and objects, clause by clause:

| Node | Lean rendering |
| --- | --- |
| Commutative condensed ring A on the coherent profinite site | `A : CondensedBar.Ring.{u}`, the existing `CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1})`. This admits arbitrary condensed rings, including the zero ring, with no topological presentation. Its underlying `A.toMon` has the existing `ringComm` instance. |
| Chosen universes and ordinary derived categories | Explicit `universe u`; profinite objects in u, abelian sections in u+1, and `HasDerivedCategory.{u+2}` for the categories actually localized. There are no auto-bound implicits. |
| Profinite group G | `G : Type u` with `Group`, `TopologicalSpace`, `IsTopologicalGroup`, `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`. For compact Hausdorff groups this is the usual profinite condition. |
| Internal A-modules | Existing `CondensedBar.Modules A`, definitionally `Profinite.CondensedAction.Modules A.toMon`, hence the existing `CategoryTheory.Mod` of the abelian sheaf tensor category. |
| Internal A-linear action of the condensed group, and equivariant maps | Existing `CondensedBar.Equivariant A G`, which is the landed `Profinite.CondensedAction.ActionModule A.toMon G`. Its action is by `C(S,G)` on every profinite S and commutes with all base changes. Its morphisms are the landed equivariant internal linear maps. |
| Forgetful functor U | Existing `CondensedBar.forgetAction`, preserving exactly the underlying module and morphism. |
| Invariants after every profinite base change | `V : Invariants A G`, the existing normalized invariant inclusion, fixed-section image condition and adjunction. The quantification over all base changes is in the recorded `FixedAll` used by `V.image`. |
| Free parameter A[S], internal Hom, and generalized functions | `F : InternalFunctions A` uses the existing `freeParameter` and its displayed `internalHom` isomorphism. Evaluation is the recorded natural family over every T→S and continuous T→P, not global sections only. |
| The specified action-dependent inhomogeneous bar | `B : BarDiagram (G := G) F`, the existing cosimplicial diagram with first action face, product interior faces, final face and unit degeneracies. `cochains B` is its alternating coface complex. |
| Nonnegative complexes and double complex D(I) | `I J : CochainComplex (Equivariant A G) ℕ`; existing `doubleComplex B I`. The recorded `B.term` identifies each bar term with `F.functor (power G p)` on the underlying module. |
| Finite-diagonal total and sign d_bar+(-1)^p d_I | Existing `totalCochains B` and its actual total summand inclusions `ιTotal`; no second totalization is defined. |
| Invariant augmentations b_I | Existing `a : Augmentation V B`, `t : TotalAugmentation V B a`, with bar-zero constant-function normalization and the recorded summand formula. No `Computation`, `Model` or augmentation quasi-isomorphism is assumed. |
| Nonnegative equivariant injective resolutions | Mathlib `InjectiveResolution N` has the actual natural-number cocomplex, termwise injectivity, and augmentation quasi-isomorphism `I.ι`. Its `I.cochainComplex` and `I.ι'` are the ordinary integer-indexed extension and augmentation. |
| Abelian and Grothendieck structures | The existing `ActionAbelian A G` retains the landed addition. The derived section uses `IsGrothendieckAbelian.{u+1}` on this category. These are structure witnesses for the categorical facts supplied by `product_action_inflation` with the second group trivial, as in proof step 1; they impose no additional condition on A or G. Enough injectives and K-injective resolutions come from the imported existing results. |
| U exact and preserving injectives, for the final derived claims | Named section instances `hUlim : PreservesFiniteLimits U`, `hUcolim : PreservesFiniteColimits U`, `hUinj : U.PreservesInjectiveObjects`. `include hUlim hUcolim hUinj` explicitly retains all three in both derived theorems even where their expressions do not force them. No such assumption is used for the earlier arbitrary-complex signed-homotopy assertions. |

Conclusions, clause by clause:

| Node conclusion | Declaration and formula |
| --- | --- |
| Every equivariant chain map induces the total map by postcomposition and commutes with augmentations | `total_chainMap_naturality`: the `ιTotal` equation specifies `(totalCochains B).map f` on every (p,q) summand; its second conjunct is `t_I ≫ Tot(f) = Γ(f) ≫ t_J`. The existing `B.maps` gives the internal-Hom postcomposition interpretation of its `cochains` components. The fact that this is a chain map, with identity and composition laws, is already part of `totalCochains B` as a functor. |
| Given f-g=d_J h+h d_I, the signed formula is a total homotopy | `total_signedHomotopy` takes an actual `h : Homotopy f g` and returns `H : Homotopy (Tot f) (Tot g)`. Its summand equation is `ι_(p,q) ≫ H_(n,m) = (-1 : ℤ)^p • (C^p(h_(q,m-p)) ≫ ιOrZero_(p,m-p,m))`. For m=n-1 and q>0 this is exactly the displayed formula in the node. `Homotopy.comm` is the equation dH+Hd=Tot(f)-Tot(g). The same formula specifies zero on the q=0 boundary. |
| Compatibility with the invariant-source homotopy | The second conjunct of `total_signedHomotopy` states `(t_I).f n ≫ H.hom n m = V.functor.map (h.hom n m) ≫ (t_J).f m` for all n,m, the actual degree-minus-one compatibility. Applying the additive `V.functor.mapHomotopy h` is precisely Γ(h). |
| Existence of every resolution lift and independence of lifts after localization | `total_resolution_lifts`: an existential augmentation-preserving f for every u, I, J, then equality of `totalLocalization B` applied to any two lifts of the same u. `totalLocalization` is explicitly totalization followed by extension by zero and the ordinary `DerivedCategory.Q`. |
| Identity lifts between resolutions give mutually inverse derived isomorphisms | `total_resolution_change` quantifies over arbitrary forward and backward identity lifts, asserting `IsIso` of the actual localized forward map and both inverse equations. Thus the inverse is the actual localized backward lift. |
| Identity and composition compatibility, including arbitrary choices of composite lifts | `total_resolution_functorial` states that every identity endolift localizes to the identity, and that any lift k of u≫v gives the composite of the localized arbitrary lifts f and g of u and v. The specialization u=v=1 is the three-resolution cocycle law. |
| Canonical derived-unit comparisons on each column | `total_column_derived_naturality` supplies isomorphisms c for every p, N, I, asserts invertibility of the ordinary derived unit on UI, and fixes `c_I.hom ≫ η_UI = RF_p(Q Uι_I)`. Because η_UI is invertible this determines c uniquely. There is no arbitrary unnormalized comparison or choice of data from mere existence. |
| Column maps precisely equal the derived internal-Hom maps | The second conjunct of `total_column_derived_naturality` is `RF_p(Q Uu[0]) ≫ c_J.hom = c_I.hom ≫ Q F_p(Uf)`. `F_p=F.functor (power G p)` has the recorded isomorphism to internal Hom from A[G^p]. The source uses U applied to the integer single complex; the canonical existing `Functor.singleMapHomologicalComplex` identifies it with the single complex on UN, so no module or size changes. |
| The invariant-source map is RΓ_G(u[0]) | First conjunct of `augmentation_resolution_naturality`, using the existing `resolutionComparison V I` and `resolutionComparison V J`. These are the mapped augmentation followed by the inverse ordinary total-derived unit, not arbitrary cohomology isomorphisms. |
| Localized augmentation square and consequently independence of resolutions and naturality | `augmentationComparison` is the actual morphism `(resolutionComparison V I).hom ≫ Q(extendMap (t_I))`. The final theorem's second conjunct states `RΓ(u[0]) ≫ β_J = β_I ≫ Q Tot(f)` for every u, every two resolutions, and every augmentation-preserving f. With u=1 this identifies β along the canonical isomorphisms just stated; arbitrary u gives naturality. Lift independence and coherence come from the preceding declarations. The comparison is intentionally a morphism, matching the node's final proof step, which separates its invertibility into another result. |

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, through the
  bar-data module and the existing commutative bundled specialization.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its module-object
  structure; reached through the existing `Modules` abbreviation.
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `forgetAction`,
  `FixedAll`, `Invariants`; these are reexported by the bar-data module.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `Ring`, `Modules`, `Equivariant`,
  `InternalFunctions`, `BarDiagram`, `cochains`, `Augmentation`, `doubleComplex`,
  `totalCochains`, `TotalAugmentation`, `ActionAbelian`, `extend`, `resolutionComparison`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `Injective`,
  `InjectiveResolution`; also its integer extension API from the bar module.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal`, and Mathlib's total-complex
  API reexported through the bar module: `HomologicalComplex₂`, `total`, `ιTotal`,
  `ιTotalOrZero`, `ComplexShape.ε₂` and finite diagonal conventions.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and `singleFunctor`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  universal right-derived-functor and unit specification is imported. The formulas
  deliberately retain `Functor.rightDerivedFunctor`, the existing universal pair
  already used in `CondensedBar.resolutionComparison`. In these Grothendieck
  categories the functorial monomorphic K-injective resolutions exist, so this
  pair meets the recorded specification as well as the weaker arbitrary-resolution
  specification; uniqueness of the universal pair identifies the two. No alternate
  derived functor is defined here.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`:
  existing `Functor.rightDerivedFunctorUnitQ` makes the ordinary-complex normalization
  explicit, including the canonical Q/quotient/Qh identifications.

All modules of stated proof dependencies are imported, including the product-action,
Grothendieck enough-injectives, tensor-closed sheaf modules, right-adjoint limits,
injective-resolution lift and homotopy uniqueness, K-injective computation,
specified-resolution naturality, and functorial degreewise-injective K-injective
resolution modules. No import cycle was encountered. No dependency interface repair
or additional DAG notion was needed.

Edge cases checked before drafting and again against the compiled statement:

- p=0: the sign is +1, and the augmentation compatibility is the invariant homotopy.
- q=0: when m=n-1 and n=p, p>m, so the target summand in `ιTotalOrZero` is zero.
  The surviving term h^1 d_I^0 in the homotopy equation is retained by `Homotopy.comm`.
- n=0: `Homotopy.zero` forces every component with no preceding total degree to zero;
  the all-index summand formula has exactly this behavior.
- A=0, the zero module/complex, and G trivial: all existing definitions remain typed;
  no nonzero, faithful, flat or nontrivial condition has been imposed.
- Empty profinite test objects: `InternalFunctions` still quantifies over all test
  objects and base changes, with its original natural-function evaluation.
- Identity module maps with different resolutions: arbitrary forward and backward
  lifts are included, with both inverse equations, and the final square uses these
  actual maps. Identity endolifts and arbitrary lifts of composites are explicit.
- No projectivity of A[G^p], exactness of internal Hom, bar-augmentation
  quasi-isomorphism, or arbitrary comparison isomorphism is assumed.
- The derived statements are object-level equalities of derived morphisms and
  isomorphisms, before applying any cohomology functor.

Searches for existing statements:

- `msearch.py`, LeanFinder: "Naturality and signed total homotopy of the internal
  condensed equivariant bar construction". Eight hits, on Dold--Kan homotopy and
  alternating-face naturality; none states this internal condensed assertion.
- `msearch.py`, Loogle: `"bar", "homotopy"`. Zero hits.
- `msearch.py`, Mathlib grep:
  `(bar|condensed|Condensed).*(homotop|naturality)|(homotop|naturality).*(bar|condensed|Condensed)`.
  Two hits: `CondensedMod.hom_naturality_apply` and `CondensedSet.hom_naturality_apply`;
  neither concerns totalization or injective resolutions.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` with the same expression, and exact
  item-id grep of `lean/WeilConjectures`: no exact upstream statement. Project hits
  include product-bar comparison and norm-algebraic-closure bar augmentation; these
  have different hypotheses and conclusions. Existing bar-data and generic
  homotopy/localization APIs were reused rather than copied.
- Targeted source inspection found and reused `Functor.rightDerivedFunctorUnitQ`,
  `ιTotalOrZero`, and the existing resolution-comparison normalization.

Validation: `scompile.py Q33 lem-sfb-condensed-bar-total-naturality` compiled the
single delivered module under both the sandbox and actual library module names.
The last run took 3.5 s and 4.7 s respectively and was clean apart from expected
stage-2 sorry notices. All source lines are at most 100 characters. The only node
field changed is `lean`; its primary signature is copied verbatim from the module.
No statement dispute or correction is asserted.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
