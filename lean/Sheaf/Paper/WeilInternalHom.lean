/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.Paper.WeilTensorProduct
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete
import Sheaf.CategoryTheory.RingedPresentationTransport
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses

/-!
# Internal Hom with completed coefficients and its Weil Frobenius

Source: main-20261015 blueprint, sec-algebraic-groups-lie-algebras/sk-p-cyclotomic,
definition 2914 (blueprint: def-wf-internal-hom).

The integral Hom is the recorded K-injective construction on all module sheaves.
Its restriction to complete objects is rationalized bilinearly. The transport comparison
is fixed on Hom-product projections and on K-injective representatives; no arbitrary
comparison isomorphism is selected. The output Frobenius lives in the ambient category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct SheafOfModules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

/-- The existing ringed-site derived Hom, with the actual site object and arrow universes.
Source: Stacks 08J7; blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
abbrev wfOrdinaryDerivedHom :
    (PbcCompletedDerived X d)ᵒᵖ × PbcCompletedDerived X d ⥤ PbcCompletedDerived X d :=
  derivedInternalHomOfUniverses.{u + 1, u, u + 1, u + 2}
    (ProEt.topology X) (pbcAdicCompletion X d)

/-- Hom into a complete object is complete, with no restriction on its first argument.
Source: Stacks 099A, 099B and 0A0E; definition 2914 (blueprint: def-wf-internal-hom).
Proof: pass to a small presentation in the module universe. The Koszul reflector
identifies invertibility of the published completion unit with local derived ideal
completeness. Apply lem-sf-ringed-rhom-derived-complete (099A), and transport back.
Exact presentation equivalences preserve Hom, section localization and all local tests
by lem-weil-pbc-ringed-presentation-transport. Apply the reflector once more. -/
theorem wfDerivedHom_complete (M : PbcCompletedDerived X d)
    (N : WfCompleteCategory X d r a ha) :
    WfIsComplete X d r a ha ((wfOrdinaryDerivedHom X d).obj (op M, N.obj)) := by
  sorry

/-- Restriction of the existing Hom bifunctor, without a further completion of its output.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfIntegralHom :
    (WfCompleteCategory X d r a ha)ᵒᵖ × WfCompleteCategory X d r a ha ⥤
      WfCompleteCategory X d r a ha :=
  ObjectProperty.lift (WfIsComplete X d r a ha)
    (((ObjectProperty.ι (WfIsComplete X d r a ha)).op.prod
      (ObjectProperty.ι (WfIsComplete X d r a ha))) ⋙ wfOrdinaryDerivedHom X d)
    (fun MN ↦ wfDerivedHom_complete X d r a ha MN.1.unop.obj MN.2)

/-- Objects of rational Hom are exactly the integral Hom objects.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfRationalHomObj (p : A) (M N : WfAmbientRationalCategory X d r a ha p) :
    WfAmbientRationalCategory X d r a ha p :=
  ⟨(wfIntegralHom X d r a ha).obj (op M.obj, N.obj)⟩

/-- Bilinear localization, including the product of the two scalar denominators.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom).
Proof: sheaf Hom is A-linear in precomposition and postcomposition. The functorial
K-injective replacement and localization retain these identities. The full complete
subcategory has the same arrows. Extend this bilinear map by tensoring both Hom
modules with A[1/p]. The universal property of tensor products gives existence and
uniqueness with exactly the displayed pure-tensor formula. -/
theorem wfRationalHomMap_exists (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :
    ∃! b : (M' ⟶ M) →ₗ[Localization.Away p] (N ⟶ N') →ₗ[Localization.Away p]
        (wfRationalHomObj X d r a ha p M N ⟶ wfRationalHomObj X d r a ha p M' N'),
      ∀ (f : M'.obj ⟶ M.obj) (g : N.obj ⟶ N'.obj) (s t : Localization.Away p),
        b (s ⊗ₜ[A] f) (t ⊗ₜ[A] g) =
          (s * t) ⊗ₜ[A] (wfIntegralHom X d r a ha).map (Prod.mkHom f.op g) := by
  sorry

/-- The unique bilinear extension, rather than a chosen unspecified action on fractions.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfRationalHomMap (p : A) (M M' N N' : WfAmbientRationalCategory X d r a ha p) :=
  (wfRationalHomMap_exists X d r a ha p M M' N N').exists.choose

/-- Identity and composition laws for the extended contravariant/covariant Hom action.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom).
Proof: check pure tensors using the integral bifunctor laws. Precomposition reverses
the first-variable arrows. Commutativity of localized scalars gives equality of the
products of four scalars. Bilinearity then extends both identities to all arrows. -/
theorem wfRationalHom_laws (p : A) :
    (∀ M N : WfAmbientRationalCategory X d r a ha p,
      wfRationalHomMap X d r a ha p M M N N (𝟙 M) (𝟙 N) = 𝟙 _) ∧
    ∀ (M M' M'' N N' N'' : WfAmbientRationalCategory X d r a ha p)
      (f : M' ⟶ M) (f' : M'' ⟶ M') (g : N ⟶ N') (g' : N' ⟶ N''),
      wfRationalHomMap X d r a ha p M M'' N N'' (f' ≫ f) (g ≫ g') =
        wfRationalHomMap X d r a ha p M M' N N' f g ≫
          wfRationalHomMap X d r a ha p M' M'' N' N'' f' g' := by
  sorry

/-- The ambient rational internal-Hom bifunctor.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfRationalHom (p : A) :
    (WfAmbientRationalCategory X d r a ha p)ᵒᵖ ×
      WfAmbientRationalCategory X d r a ha p ⥤ WfAmbientRationalCategory X d r a ha p where
  obj MN := wfRationalHomObj X d r a ha p MN.1.unop MN.2
  map {MN PQ} f :=
    wfRationalHomMap X d r a ha p MN.1.unop PQ.1.unop MN.2 PQ.2 f.1.unop f.2
  map_id MN := (wfRationalHom_laws X d r a ha p).1 MN.1.unop MN.2
  map_comp f g := (wfRationalHom_laws X d r a ha p).2 _ _ _ _ _ _ f.1.unop g.1.unop f.2 g.2

variable (e : Aut X)

/-- The section map of the specified coefficient-transport adjunction unit.
Source: Stacks 03CR; blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfModuleTransportUnit (M : pbcModules X (pbcAdicCompletion X d)) (U : X.ProEt) :
    M.val.obj (op U) →
      ((pbcIsoModulePullback e.hom d).obj M).val.obj
        (op ((proEtaleBaseChange e.hom).obj U)) :=
  ((proEtaleRingModuleAdjunction e.hom (pbcAdicCompletion X d)
    (pbcAdicCompletion X d) (asIso (completedCoefficientMap e.hom d))).unit.app M).val.app
      (op U)

/-- Evaluation at the identity object of the slice, on the actual sheaf Hom.
Source: Stacks 03CR; blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfModuleHomEvaluation (M N : pbcModules X (pbcAdicCompletion X d)) (U : X.ProEt)
    (φ : (SheafOfModules.homObj (R := pbcAdicCompletion X d) M N).val.obj (op U))
        (x : M.val.obj (op U)) :
    N.val.obj (op U) :=
  (φ.app (op (Over.mk (𝟙 U)))).hom x

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ordinary Hom comparison is fixed by transport of local linear maps.
Source: definition 2914; Stacks 03CR and 08J7 (blueprint: def-wf-internal-hom).
Proof: transport a morphism on each slice through the exact module equivalence. Its
inverse transports through the inverse equivalence. The displayed equation says that
evaluation on transported sections commutes with the specified adjunction units.
Inverse-image sections are locally generated by these unit sections; restrictions
of the equation therefore determine the map uniquely, also on every further slice. -/
theorem wfModuleHomTransport_exists :
    ∃! beta : ∀ M N : pbcModules X (pbcAdicCompletion X d),
      (pbcIsoModulePullback e.hom d (hf := Iso.isIso_hom e)).obj
          (SheafOfModules.homObj (R := pbcAdicCompletion X d) M N) ≅
        SheafOfModules.homObj (R := pbcAdicCompletion X d)
          ((pbcIsoModulePullback e.hom d (hf := Iso.isIso_hom e)).obj M)
          ((pbcIsoModulePullback e.hom d (hf := Iso.isIso_hom e)).obj N),
      ∀ (M N : pbcModules X (pbcAdicCompletion X d)) (U : X.ProEt)
        (φ : (SheafOfModules.homObj (R := pbcAdicCompletion X d) M N).val.obj (op U))
        (x : M.val.obj (op U)),
        wfModuleHomEvaluation X d
          ((pbcIsoModulePullback e.hom d (hf := Iso.isIso_hom e)).obj M)
          ((pbcIsoModulePullback e.hom d (hf := Iso.isIso_hom e)).obj N)
          ((proEtaleBaseChange e.hom).obj U)
          (((beta M N).hom.val.app (op ((proEtaleBaseChange e.hom).obj U))).hom
            (wfModuleTransportUnit X d e
              (SheafOfModules.homObj (R := pbcAdicCompletion X d) M N) U φ))
          (wfModuleTransportUnit X d e M U x) =
        wfModuleTransportUnit X d e N U (wfModuleHomEvaluation X d M N U φ x) := by
  sorry

/-- Transport of the ordinary sheaf Hom, with its local evaluation normalization.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfModuleHomTransport := (wfModuleHomTransport_exists X d e).exists.choose

/-- Exact transport of the signed Hom complex is fixed on every product projection.
Source: Stacks 0A8X; blueprint definition 2914 (blueprint: def-wf-internal-hom).
Proof: an equivalence preserves the products defining every homogeneous component.
Use wfModuleHomTransport on each factor. Its compatibility with precomposition and
postcomposition identifies d_I φ - (-1)^n φ d_C, hence gives a chain isomorphism.
Product projections determine each component uniquely. -/
theorem wfHomComplexTransport_exists
    (C I : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    ∃! beta : ((pbcIsoModulePullback e.hom d).mapHomologicalComplex (.up ℤ)).obj
        (homComplex (R := pbcAdicCompletion X d) C I) ≅
      homComplex (R := pbcAdicCompletion X d)
        (((pbcIsoModulePullback e.hom d).mapHomologicalComplex (.up ℤ)).obj C)
        (((pbcIsoModulePullback e.hom d).mapHomologicalComplex (.up ℤ)).obj I),
      ∀ (n p q : ℤ) (h : p + n = q),
        beta.hom.f n ≫
            WeilConjectures.coefficientHomComponent.{u + 1, u + 1, u}
              (ProEt.topology X) (pbcAdicCompletion X d) _ _ n p q h =
          (pbcIsoModulePullback e.hom d).map
            (WeilConjectures.coefficientHomComponent.{u + 1, u + 1, u}
              (ProEt.topology X) (pbcAdicCompletion X d) C I n p q h) ≫
              (wfModuleHomTransport X d e (C.X p) (I.X q)).hom := by
  sorry

/-- The uniquely specified transport of the Hom complex.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfHomComplexTransport (C I : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :=
  (wfHomComplexTransport_exists X d e C I).exists.choose

/-- The augmentation for the already fixed functorial K-injective replacement.
Source: Stacks 079P and 08J7 (blueprint: def-wf-internal-hom). -/
def wfHomResolutionUnit : 𝟭 (CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) ⟶
    WeilConjectures.coefficientHomResolution.{u + 1, u + 1, u}
      (ProEt.topology X) (pbcAdicCompletion X d) :=
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (ProEt.topology X) (pbcAdicCompletion X d)).1
  CochainComplex.toKInjectiveResolution _

/-- For a K-injective target the Hom of the resolution augmentation is invertible.
Source: Stacks 0A95 and 08J7 (blueprint: def-wf-internal-hom).
Proof: the augmentation is a quasi-isomorphism between K-injective complexes.
lem-pur-rhom-well-defined-universes applies with identity on the source, so Q
inverts its Hom map. This statement also covers an already K-injective replacement. -/
theorem wfHomResolutionMap_isIso
    (C I : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) [I.IsKInjective] :
    IsIso (DerivedCategory.Q.map
      (((homComplexFunctor (R := pbcAdicCompletion X d)).obj (op C)).map
        ((wfHomResolutionUnit X d).app I))) := by
  sorry

/-- Canonical computation with any K-injective target: factorization, then augmentation.
Source: Stacks 08J7 and 0A95 (blueprint: def-wf-internal-hom). -/
def wfHomKInjectiveModel
    (C I : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) [I.IsKInjective] :
    (wfOrdinaryDerivedHom X d).obj (op (DerivedCategory.Q.obj C), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (homComplex (R := pbcAdicCompletion X d) C I) :=
  WeilConjectures.coefficientHomResolutionIso (ProEt.topology X) (pbcAdicCompletion X d) C I ≪≫
    (@asIso _ _ _ _ _ (wfHomResolutionMap_isIso X d C I)).symm

/-- Derived transport is uniquely fixed by the preceding Hom-complex isomorphism.
Source: Stacks 03CR and 08J7; definition 2914 (blueprint: def-wf-internal-hom).
Proof: the exact inverse module equivalence preserves acyclic complexes, so adjunction
on homotopy categories shows that transport preserves K-injectives. For C and a
K-injective I, localize wfHomComplexTransport and use the termwise factorization.
The displayed square uses the fixed K-injective-model comparison on both sides.
These squares are natural and invert quasi-isomorphisms. Localization gives the
natural isomorphism. Every pair has such representatives, proving uniqueness. -/
theorem wfDerivedHomTransport_exists :
    ∃! alpha : wfOrdinaryDerivedHom X d ⋙ pbcIsoAmbientPullback e.hom d ≅
      ((pbcIsoAmbientPullback e.hom d).op.prod (pbcIsoAmbientPullback e.hom d)) ⋙
        wfOrdinaryDerivedHom X d,
      ∀ (C I : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) [I.IsKInjective],
        alpha.hom.app (op (DerivedCategory.Q.obj C), DerivedCategory.Q.obj I) ≫
          (wfOrdinaryDerivedHom X d).map (Prod.mkHom
            ((pbcIsoModulePullback e.hom d).mapDerivedCategoryFactors.inv.app C).op
            ((pbcIsoModulePullback e.hom d).mapDerivedCategoryFactors.hom.app I)) ≫
          (wfHomKInjectiveModel X d
            (((pbcIsoModulePullback e.hom d).mapHomologicalComplex (.up ℤ)).obj C)
            (((pbcIsoModulePullback e.hom d).mapHomologicalComplex (.up ℤ)).obj I)).hom =
        (pbcIsoAmbientPullback e.hom d).map (wfHomKInjectiveModel X d C I).hom ≫
          (pbcIsoModulePullback e.hom d).mapDerivedCategoryFactors.hom.app
            (homComplex (R := pbcAdicCompletion X d) C I) ≫
          DerivedCategory.Q.map (wfHomComplexTransport X d e C I).hom := by
  sorry

/-- The canonical derived comparison, normalized on all K-injective representatives.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfDerivedHomTransport := (wfDerivedHomTransport_exists X d e).exists.choose

/-- Restrict the canonical comparison to complete objects in both variables.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfIntegralHomTransport (M N : WfCompleteCategory X d r a ha) :
    (wfCompletePullback X d r a ha e).obj ((wfIntegralHom X d r a ha).obj (op M, N)) ≅
      (wfIntegralHom X d r a ha).obj
        (op ((wfCompletePullback X d r a ha e).obj M),
          (wfCompletePullback X d r a ha e).obj N) :=
  ObjectProperty.isoMk _ ((wfDerivedHomTransport X d e).app (op M.obj, N.obj))

/-- The rational comparison is fixed by localization of each integral component.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom).
Proof: tensor the integral comparison and its inverse with 1. Integral naturality
extends bilinearly to localized arrows, since the coefficient identification fixes
every scalar, including p. Objects of raw scalar localization are integral objects,
so the displayed component formula also proves uniqueness. -/
theorem wfRationalHomTransport_exists (p : A) :
    ∃! alpha : wfRationalHom X d r a ha p ⋙ wfAmbientRationalPullback X d r a ha e p ≅
      ((wfAmbientRationalPullback X d r a ha e p).op.prod
        (wfAmbientRationalPullback X d r a ha e p)) ⋙ wfRationalHom X d r a ha p,
      ∀ M N : WfCompleteCategory X d r a ha,
        alpha.hom.app (op ⟨M⟩, ⟨N⟩) =
          (ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p).map
            (wfIntegralHomTransport X d r a ha e M N).hom := by
  sorry

/-- The alpha comparison in the displayed direction of the source.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfRationalHomTransport (p : A) :=
  (wfRationalHomTransport_exists X d r a ha e p).exists.choose

end AlgebraicGeometry.Scheme

namespace WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.Scheme
variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- RHom_E on the existing ambient completed rational category.
Source: blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
abbrev wfInternalHom : (WfAmbient D c X₀ E)ᵒᵖ × WfAmbient D c X₀ E ⥤ WfAmbient D c X₀ E :=
  wfRationalHom (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
    1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Internal-Hom Frobenius is alpha followed by RHom(phi_K inverse, phi_L).
It is an ambient isomorphism; constructible restriction is a separate assertion.
Source: main-20261015 blueprint definition 2914 (blueprint: def-wf-internal-hom). -/
def wfInternalHomFrobenius (K L : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj
        ((wfInternalHom D c X₀ E).obj
          (op (wfWeilCarrier D c X₀ E K), wfWeilCarrier D c X₀ E L)) ≅
      (wfInternalHom D c X₀ E).obj
        (op (wfWeilCarrier D c X₀ E K), wfWeilCarrier D c X₀ E L) :=
  (wfRationalHomTransport (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
    1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)
    (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E)).app
      (op (wfWeilCarrier D c X₀ E K), wfWeilCarrier D c X₀ E L) ≪≫
    (wfInternalHom D c X₀ E).mapIso
      ((wfWeilStructure D c X₀ E K).symm.op.prod (wfWeilStructure D c X₀ E L))

end WeilConjectures
