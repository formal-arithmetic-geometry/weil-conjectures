## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceDerivedChowTransformRestriction` states
`AlgebraicGeometry.AlgebraicSpace.derived_chow_transform_restriction`, with `sorry`.
It also packages the existing projective scheme over Spec A, an actual open subscheme,
and the actual Yoneda map of its inclusion. These are real definitions of the geometric
objects used in this theorem, not new choices of functors or replacement notions.
No statement correction, dependency repair, new DAG node, or mathematical dispute is needed.
The original accepted split, proof, provenance and review are preserved.

The inherited BLOCKED ending described the stage-1 unchanged-split gate. The current
queue lists this item at stage 2, and its node has no Lean record. The stage handoff in
coord/brief-stage2.md §0 explicitly permits recording this reviewed split's Lean statement.
The initial sandbox contained only dispatcher .brief files, with no retained module.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Universe convention | Explicit `universe u w`; schemes and rings at u, arbitrary localization morphism universe w; the usual `HasDerivedCategory` family for the fixed base. No equality of site object and morphism universes. |
| A commutative ring | `A : CommRingCat.{u}`, including the zero ring. |
| Algebraic spaces X,T,Z over Spec A | `X T Z : AlgebraicSpace (Spec A)`. All use their existing small étale structure-module models. |
| X -> Spec A | `s : X ⟶ schemeSpace (Over.mk (𝟙 (Spec A)))`. The representable identity S-scheme is terminal, so this is precisely the structure morphism, not a freely variable action. |
| Separated X/A | `_hsep : MapIsSeparated s`, the representable closed relative diagonal. |
| Finite presentation: quasi-compact | `_hqc : MapIsQuasiCompact s.hom.hom`. |
| Finite presentation: quasi-separated | `_hqs : MapIsQuasiCompact (Limits.pullback.diagonal s.hom.hom)`. |
| Finite presentation: locally finitely presented on étale charts | `_hlfp : MapIsLocallyOfFinitePresentation s`. These three clauses are the usual finite-presentation condition. |
| n >= 0 and P = projective n-space | `n : ℕ`; `chowProjectiveSpace A n` is the recorded `ProjectiveSpace` with coordinate type `ULift (Fin (n+1))` and its structure map. This includes n=0 and uses n+1, not n, coordinates. |
| T = X times_A P, with projections p,q | `p`, `q`, and `_hT : IsLimit (BinaryFan.mk p q)`. The category is spaces over Spec A, so its product is exactly this relative product. The limit witness permits every representative. |
| h:Z -> T closed | `h` and `_hh : IsRepresentableWith (fun _ _ k ↦ IsClosedImmersion k.left) h.hom.hom`, the predicate used by `ClosedSubspace`; no abstract mono in place of closed immersion. |
| b=p h and c=q h | Lean composition is left-to-right, so these are `h ≫ p` and `h ≫ q`. |
| V open in P | `V : (chowProjectiveSpace A n).left.Opens`; `chowProjectiveOpen` retains V's scheme and structure map; `chowProjectiveOpenInclusion` is the Yoneda map of `V.ι`. |
| Restriction to X times_A V | `T_V,a,q_V,_hTV : IsPullback a q_V q v`, where v is that actual inclusion. These are merely a representative and maps of the inverse-image open, with no new geometric hypothesis. |
| W=c inverse(V), j=c restricted to W | `W,wZ,j,_hW : IsPullback wZ j (h ≫ q) v`. This is the inverse-image open with its restricted c. |
| j closed, so W a scheme | `_hj` is the same representable-closed-immersion predicate as for h. Applying its scheme test to the identity V represents W by a closed subscheme of V. W is permitted as an algebraic space because being a scheme follows, with no choice required in the statement. |
| b_W étale | `_hbW : IsEtale (wZ ≫ h ≫ p).hom.hom`. |
| E in D_QCoh(O_T) | `E : T.DerivedQCoh`, the FULL subcategory of the fixed derived category with quasi-coherent cohomology, not D(QCoh). |
| Kernel restriction | `_hE : Nonempty ((derivedTensorPullback a).obj E.obj ≅ (derivedTensorPullback a).obj ((DerivedCategory.singleFunctor T.SmallModules 0).obj ((smallModuleDirectImage h).obj (SheafOfModules.unit Z.smallStructureRings))))`. The single functor is applied AFTER ordinary h_*, exactly `(h_* O_Z)[0]`; it is not replaced by Rh_* in the hypothesis. a is an open immersion by its cartesian square, so La^* is restriction. |
| Every K in D_QCoh(O_X) | The source of both functors in the conclusion is `X.DerivedQCoh`, embedded by `X.derivedQCohProperty.ι`. |
| Lp^*K tensor^L E | `derivedTensorPullback p` followed by `(Functor.curry.obj T.derivedDualityModel.closed.tensor).flip.obj E.obj`. Currying and flipping fix the RIGHT factor E and leave the first factor K variable. |
| Rq_* followed by restriction to V | `derivedDirectImage q ⋙ derivedTensorPullback (chowProjectiveOpenInclusion A n V)`. The latter derived pullback is ordinary restriction for the open inclusion. |
| Rj_*(b_W^*K) | `derivedTensorPullback (wZ ≫ h ≫ p) ⋙ derivedDirectImage j`. Under `_hbW` this is exactly the étale exact restriction b_W^*, as stated in the node's last sentence. Writing its canonical Lb_W^* uses the existing functor; no arbitrary restriction or replacement functor is assumed. |
| Natural isomorphism in D(O_V) | `Nonempty (F ≅ G)` for these two functors into `(schemeSpace (chowProjectiveOpen A n V)).DerivedModules`. A functor isomorphism includes the morphisms and all naturality equations in K. This is a derived isomorphism, not merely isomorphisms of cohomology objects. |

Dependency declarations used (their source signatures and docstrings were read):

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `Modules`, and small étale structure sheaf.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the unchanged Mathlib `SheafOfModules` category used by the small-model calculus.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.singleFunctor`; no second derived category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  existing `SheafOfModules.IsQuasicoherent` predicate, used through `derivedQCohProperty`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: the underlying
  `AlgebraicGeometry.ProjectiveSpace` and `ProjectiveSpace.over`; no twist is needed here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleDirectImageModel`,
  `moduleDirectImage`, `moduleTensorPullback`, through the fixed small-model functors.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace`: `ClosedSubspace`, whose
  exact representable-closed predicate is used for h and j.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, available for the representative
  calculus; `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, underlying the fixed K-injective direct image.
- Added already-landed statement dependencies, with no redefinition or record repair:
  `def-sfb-space-derived-module-calculus` owns `DerivedModules`, `DerivedQCoh`,
  `smallModuleDirectImage`, `derivedDirectImage` and `derivedDualityModel` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`;
  `def-sfb-space-derived-tensor-pullback` owns `derivedTensorPullback` in
  `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`;
  `def-sfb-space-morphism-properties` owns `MapIsSeparated` and
  `MapIsLocallyOfFinitePresentation` in `AlgebraicSpaceMorphismProperties`;
  `def-sfb-proper-curve-moduli` owns `MapIsQuasiCompact` in `ProperCurveModuli`;
  `def-trf-scheme-algebraic-space` owns `schemeSpace` in `EnlargedEtaleRingedSite`.
  These existing nodes are appended to stmt_deps as authorized by §5.

All stated proof dependencies are imported plainly (not publicly), except those
already needed publicly for the signature. `lem-sfb-space-derived-etale-chart-calculus`
and `lem-sfb-space-qcqs-derived-projection-formula` currently have no Lean record;
there is no import to add for these future proof inputs. They are not needed to
TYPE this stage-2 statement. The docstring carries the six-step accepted proof.

Edge cases checked before writing: V empty and hence W empty; W empty even with V
nonempty; X empty; A the zero ring; n=0 (one coordinate); K=0; E=0 when its restriction
permits that; arbitrary unbounded K and E; non-flat closed h and j. No nonemptiness,
Noetherianity, flatness of h, finite presentation of j, perfectness, or boundedness
has been added. The typed cartesian squares cover the full and empty opens and any
isomorphic product representatives. Finite presentation of X is retained even though
the restriction computation uses the more local hypotheses.

Searches actually made using the prescribed msearch wrapper:

- LeanFinder: `Restriction of a derived Chow Fourier Mukai transform equals closed
  immersion pushforward of etale pullback`: 8 ordinary scheme-restriction hits,
  including `Scheme.Modules.restrictFunctorIsoPullback` and `restrictFunctorComp`.
  None states this unbounded algebraic-space kernel computation.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, DerivedCategory`: 0 hits, unknown
  identifier AlgebraicGeometry.AlgebraicSpace in Mathlib's search environment.
- Mathlib grep: `Chow|FourierMukai` under AlgebraicGeometry: 0 hits.
- Direct rg in lean/WeilConjectures and lean/Sheaf:
  `lem-sfb-space-derived-chow-transform-restriction|chow.*[Tt]ransform|[Cc]how.*[Rr]estriction|derivedChow`:
  0 hits. Further concept searches located the existing small-model calculus,
  canonical derived pullback, normalized tensor model and morphism-property modules.
- Direct name collision search in dag/lean_names_upstream.json, lean/WeilConjectures
  and lean/Sheaf for `chowProjectiveSpace|chowProjectiveOpen|derived_chow_transform_restriction`:
  0 hits before delivery.

Source read: literature/stacks-project/spaces-more-morphisms.tex, Tag 0CTS,
lemma-compute-Fourier-Mukai-for-derived-chow, its full displayed formula and proof,
and the preceding derived-Chow construction. The generalized local hypotheses of
this already-reviewed DAG node are exactly the hypotheses used in that computation.
The source's notation K|_W is ordinary étale restriction, equivalently Lb_W^*K.

## Second reading by O1

Performed a separate checking pass with both the node and the completed module open;
no additional agent was started, as the dispatch brief prohibits it. This is a worker
self-check; the maintainer's independent reading remains the delivery review.

Checked the orientation of both cartesian squares: a is the open restriction over q,
and wZ is the open restriction over c=h followed by q. Checked that the BinaryFan
product is in spaces over Spec A, so it is a product over A. Checked n+1 homogeneous
coordinates, the terminal representable base, all four structure-map hypotheses,
both representable closed-immersion predicates, and the étale hypothesis on the actual
composite wZ,h,p. Checked the kernel uses ordinary h_* BEFORE degree-zero embedding,
and that a^* restricts both sides of the assumed isomorphism. Checked the tensor order
by reading Functor.curryObj and its flip: the functor is K maps to Lp^*K tensor E.
Checked that conclusion is an iso of functors on the full D_QCoh subcategory and that
its codomain is the derived module category of V. The right side uses the node's
explicit identification Lb_W^*=b_W^*, rather than postulating an unrelated functor.
No mismatch requiring a statement change was found. The reading found one omitted
available proof import, SpaceAffineModuleHigherImageVanishing, and added it.

Validation: the first server scompile run compiled both sandbox and library module
names cleanly (8.7 s and 9.0 s). After the proof-import correction, all required
checks are rerun with scompile.py and deliver2.py.
