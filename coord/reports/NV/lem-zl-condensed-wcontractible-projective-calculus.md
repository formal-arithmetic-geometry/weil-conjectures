## Worker report

The module states the whole bounded-projective cone and scalar calculus of
lem-zl-condensed-wcontractible-projective-calculus. Its only theorem is
AlgebraicGeometry.ProEtale.CondensedRing.condensed_wcontractible_projective_calculus;
its proof is exactly `sorry`. Four data helpers have complete bodies. No statement,
proof, or proof dependency of the accepted node was changed. The item's stmt_deps gains
one already published definition node, def-zl-condensed-lisse-evaluation-model, whose
recorded A/F/D constructions the statement uses. There are no new nodes or dependency
repairs.

Source read: Hemo--Richarz--Scholbach, arXiv:2305.18131, the local PDF, Section 3,
(3.1)--(3.2), Remark 3.2, Definition 3.3 and its stability paragraph, Definition 3.5,
Lemma 4.1(1)--(2) and its proof, and Proposition 4.3(3)'s scalar square. The accepted
node makes the usual finite-projective representative argument explicit. Its six
proof steps are reproduced as a proof plan in the theorem docstring.

Hypotheses and clauses, checked against the node with the module open:

- Arbitrary commutative condensed ring: `(Λ : Profinite.CondensedRing.{u})`
  and `[IsCommMonObj Λ.X]`. No continuous-function presentation, discreteness,
  characteristic, admissibility, or flatness condition is imposed.
- Scheme and weak contractibility: `(T : Scheme.{u}) [IsAffine T]`
  and `[IsWContractibleRing Γ(T, ⊤)]`, using the recorded ring class on T's
  structure-ring sections, rather than on the coefficient section ring B.
- Coefficients and ordinary derived category: `projectiveCalculusCategory Λ T`
  is exactly `Evaluation.D (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)`.
  This is the existing ordinary DerivedCategory of internal module sheaves,
  canonically equivalent to the sectionwise SheafOfModules category by the
  dependency's `InternalAbelianSheafModule.sectionModuleEquivalence`.
- B = Γ(T,Λ_T): `projectiveCalculusRing` transparently specializes `Evaluation.A`
  at the terminal pro-etale object `Scheme.ProEt.mk (𝟙 T)`.
  F_T: `projectiveCalculusRealization` transparently specializes the recorded
  `Evaluation.F`, with its terminal-object proof. It uses the actual constant-section
  counit, constant derived realization, derived coefficient extension and the
  sectionwise/internal module equivalence; there is no auxiliary functor.
- Dualizable: the existing `CategoryTheory.IsDualizable`, definitionally
  `Nonempty (HasRightDual K)`. HasRightDual supplies a dual, evaluation, coevaluation
  and both exact-pairing triangle identities for the existing ordinary derived tensor.
- Perfect means `DerivedCategory.IsPerfectRingComplex`, exactly the dependency's
  bounded finite-projective model predicate.
- Every f between perfect Q,Q': the first universal block binds Q,Q', f and the
  two perfectness hypotheses. It then binds arbitrary q,q', four integer bounds,
  strict lower/upper bounds, projectivity and finite generation in every degree,
  and arbitrary identifying isomorphisms e,e'. No representatives are silently chosen.
- A chain map represents f: `∃ v : q ⟶ q'`, followed by
  `DerivedCategory.Q.map v ≫ e'.hom = e.hom ≫ f`.
- The cone is bounded finite-projective: the next existential binds its integer
  bounds and states both strict bounds and `Module.Projective`/`Module.Finite`
  for every term of `CochainComplex.mappingCone v`. Its next conjunct gives
  the degreewise isomorphism to `q'.X i ⊞ q.X (i+1)` in the node's order.
  Mathlib's mappingCone is the standard cone, with the shifted-source summand
  ordered first internally; its canonical biproduct symmetry gives the stated order.
  The differential is part of that standard construction, not arbitrary data.
- Any cone of F_T(f): arbitrary K, g and h are quantified, with
  `Triangle.mk (F.map f) g h ∈ distTriang _`. The conclusion gives an actual
  derived isomorphism `K ≅ F.obj (DerivedCategory.Q.obj (mappingCone v))`
  (under Nonempty) and `IsDualizable K`. This includes any choice of cone.
- Zero: `IsDualizable (F.obj 0)` uses the zero object, via scoped ZeroObject.
- Every integer shift: the next universal block quantifies all perfect Q and all
  `m : ℤ` and states `IsDualizable ((F.obj Q) ⟦m⟧)`.
- Isomorphism invariance: all K,K', an isomorphism under Nonempty, and dualizability
  of K imply dualizability of K'. Swapping K and K' also gives the reverse implication.
- All dualizable arrows: arbitrary K,K',u with dualizability of both endpoints give
  perfect Q,Q', a map f, endpoint isomorphisms e,e', and the exact commuting equation
  `F.map f ≫ e'.hom = e.hom ≫ u`. This is an isomorphism of arrows, not merely
  independent isomorphisms of their endpoints.
- The scalar map R→B is fixed, not arbitrary: `projectiveCalculusScalarSection`
  constructs its underlying function. A section r at the profinite point is the
  sheaf morphism Z→Λ adjoint to n↦n*r. Apply the existing monoidal pullback p_T^*
  and evaluate on the sheafification-unit section 1 at T. The theorem binds σ
  as a ring homomorphism and requires `∀ r, σ r = projectiveCalculusScalarSection Λ T r`.
  This determines σ uniquely and is exactly pullback on global sections. The
  existential bundles the canonical function's ring laws with its scalar assertions;
  it is not an existence-based definition of data.
- For every perfect P over R: the scalar block uses the recorded
  `condensedScalarRing Λ.X`, `RingDerivedScalarExtension.moduleDerivedExtension σ`
  and `condensedScalarRealization Λ.X T`. It states perfection of the extended
  complex and dualizability of L_T(P).
- Natural derived isomorphism: the last Nonempty contains a natural isomorphism of
  functors restricted along `ObjectProperty.ι DerivedCategory.IsPerfectRingComplex`.
  Its components are exactly L_T(P) ≅ F_T(B⊗^L_R P). It retains naturality for all
  morphisms between perfect objects, rather than just separate isomorphisms.
- Nonflat case: there is no flatness hypothesis on σ, B or Λ, anywhere in the file.

Dependency declarations read and used:

- Sheaf.Topology.ProfiniteCondensedRing: `Profinite.CondensedRing` (Mon of abelian
  sheaves on the coherent profinite site).
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its morphisms.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt` and `Scheme.ProEt.topology`.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: `condensedRingObj`,
  `coefficientRing` and `isCommMonObj_condensedRingObj`; its monoidal
  `upperStarFromPoint` is used in the scalar-section helper.
- Sheaf.CategoryTheory.RingedSiteModules: `ringedSiteModules` is the exact
  sectionwise SheafOfModules encoding. The evaluation model already uses its
  canonical internal-module counterpart and recorded sectionModuleEquivalence;
  no alternative category of sheaves is defined here.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory` and its `Q`.
- Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral:
  `DerivedCategory.IsPerfectRingComplex`, including its complete existential model.
- Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor:
  `realizationRing`, `realizationModules`, `commutativeSiteDerivedConstantModuleFunctor`;
  these are constituents of Evaluation.F, retained unchanged.
- Sheaf.AlgebraicGeometry.CondensedScalarRealization: `condensedScalarRing`,
  `condensedScalarRealization`, with the recorded scalar counit and K-flat model.
- WeilConjectures.RingTheory.ProEtale.WContractible: `IsWContractibleRing`, extending
  IsWStrictlyLocalRing and requiring extremally disconnected connected components.
- Sheaf.AlgebraicGeometry.RingDerivedScalarExtension:
  `CategoryTheory.RingDerivedScalarExtension.moduleDerivedExtension`, the canonical
  left adjoint of the existing derived restriction functor.
- Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel: `Evaluation.A`, `Evaluation.D`,
  `Evaluation.F` and the underlying section-ring reconstruction. The three abbrevs
  only specialize these to Λ_T and the terminal object; no new notion is introduced.
- Mathlib.Algebra.Homology.HomotopyCategory.MappingCone: `CochainComplex.mappingCone`;
  also read homotopyCofiber.XIsoBiprod to check its summand convention.
- WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic:
  `CategoryTheory.IsDualizable`, inherited through the recorded derived tensor imports.

Imports for the proof plan: CondensedWContractibleLisseEvaluation;
Mathlib DerivedCategory.KProjective and HomotopyCategory.KProjective;
WeilConjectures.Algebra.Homology.BoundedFlatKFlat;
Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings. Projective and finite-module
classes and triangulated comparison tools are already publicly available through
these dependencies. The nonpublic imports implement the node's recorded proof plan.

Edge cases checked mathematically before and after writing:

- Empty T and the zero condensed ring are permitted; B is the zero ring and all
  statements reduce to zero categories or zero complexes. No nonempty scheme,
  nontrivial ring or positive rank hypothesis occurs.
- Zero Q, zero Q', zero arrows, and representatives with all terms zero are allowed.
  Bounds are arbitrary integers, without ordering assumptions or a minimum length.
  The cone of zero→Q' is Q'; the cone of Q→zero is Q[1].
- Identity arrows give contractible cones, compatible with the distinguished-cone
  formulation; no injectivity or surjectivity of chain maps is imposed.
- Negative, zero and positive shifts are all covered by m : ℤ.
- Nonflat scalar extension Z→Z/p is covered: a bounded projective representative
  computes the derived extension, even though tensoring arbitrary modules is not exact.
  Finite-free splitting survives tensoring and gives finite projectivity over B.
- The chosen q and q' are arbitrary specified bounded representatives, not just
  models selected by a global equivalence. The equation includes both model isomorphisms.

Searches actually run using batch2/msearch.py (logged by the wrapper):

- leanfinder: "Bounded finite projective complexes on a weakly contractible affine
  scheme realize dualizable condensed sheaves and cones and derived scalar extension
  preserve perfectness". Eight hits, including Condensed.profiniteSolid,
  LightCondensed.instIsGrothendieckAbelianLightCondMod and internally projective
  light-condensed criteria. None states this ordinary-derived condensed cone/scalar theorem.
- leansearch: "Perfect complexes over global sections of a weakly contractible affine
  scheme give dualizable condensed sheaves compatible with cones and derived base change".
  Eight hits: Sheaf.coneΓ, Condensed, instAbelianCondensedMod, condensed limits,
  affine-scheme global sections and Condensed.free. No match.
- loogle: "CochainComplex.mappingCone, DerivedCategory.IsPerfectRingComplex".
  The service returned zero hits and "unknown identifier DerivedCategory.IsPerfectRingComplex";
  that declaration is project-local, not an indexed Mathlib name. No exact match found.
- grep: "mappingCone|IsPerfectRingComplex|IsDualizable", Mathlib/Algebra/Homology.
  Twenty-five wrapper hits locate generic mapping-cone files; those definitions
  are used rather than copied.
- Direct rg of WeilConjectures and Sheaf for
  "wcontractible.*projective|projective.*calculus|mappingCone.*condensed|condensed.*mappingCone"
  found no existing full theorem. The prescribed node-id grep of WeilConjectures
  found no declaration. Searches of scalar-map APIs located Evaluation.scalarMap,
  profiniteScalarMap, componentComparisons and the existing scalar realization;
  none exposed the canonical R→B on arbitrary schemes as a standalone declaration.
  The helper computes its function using the existing inverse-image and constant-sheaf
  adjunction rather than choosing an unconstrained ring map.

No statement fault or STATEMENT-DISPUTED finding. Compiler validation uses scompile.py
only. The full module compiled cleanly in sandbox and library mode before delivery;
final dry-run and push results are recorded by deliver2.py.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
