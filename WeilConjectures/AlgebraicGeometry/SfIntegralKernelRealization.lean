/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfExactLocalizationTriangle
public import WeilConjectures.AlgebraicGeometry.SfRecollementRestriction
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleLinear
import WeilConjectures.AlgebraicGeometry.IntegralOperationsPreserveConstructible
import WeilConjectures.AlgebraicGeometry.SfIntegralOpenKernelCompactSupport
import WeilConjectures.AlgebraicGeometry.SfIntegralClosedKernelRoos

/-! # Constructibility and operation vertices of the completed sheaf kernel -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary completed-coefficient localization presentation.
Source: blueprint localization, integral sheaf sequence
(blueprint: lem-sf-integral-kernel-operation-realization). -/
abbrev sfIntegralKernelAmbient {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :=
  sfExactLocalizationPresentation (sfRecollementModuleOpen l E i)
    (sfRecollementModuleClosed l E i) (sfRecollementModuleCounit l E i)
    (sfRecollementModuleUnit l E i)

private theorem linear_of_monic_counit
    {R : Type*} [Ring R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (F : C ⥤ C) (ε : F ⟶ 𝟭 C) (hε : ∀ M, Mono (ε.app M)) : F.Linear R := by
  constructor
  intro M N f a
  letI := hε N
  apply (cancel_mono (ε.app N)).mp
  calc
    _ = ε.app M ≫ (a • f) := ε.naturality _
    _ = a • (ε.app M ≫ f) := Linear.comp_smul _ _ _ _ _ _
    _ = a • (F.map f ≫ ε.app N) := congrArg (a • ·) (ε.naturality f).symm
    _ = _ := (Linear.smul_comp _ _ _ _ _ _).symm

private theorem linear_of_epic_unit
    {R : Type*} [Ring R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (F : C ⥤ C) (η : 𝟭 C ⟶ F) (hη : ∀ M, Epi (η.app M)) : F.Linear R := by
  constructor
  intro M N f a
  letI := hη M
  apply (cancel_epi (η.app M)).mp
  calc
    _ = (a • f) ≫ η.app N := (η.naturality _).symm
    _ = a • (f ≫ η.app N) := Linear.smul_comp _ _ _ _ _ _
    _ = a • (η.app M ≫ F.map f) := congrArg (a • ·) (η.naturality f)
    _ = _ := (Linear.comp_smul _ _ _ _ _ _).symm

private theorem sfIntegralKernel_ambient_linear {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    (sfIntegralKernelAmbient l E i).openTerm.Linear
        (Padic.coefficientExtensionIntegers l E) ∧
      (sfIntegralKernelAmbient l E i).closedTerm.Linear
        (Padic.coefficientExtensionIntegers l E) := by
  let R := Padic.coefficientExtensionIntegers l E
  let C := scalarReductionSource.{u, u} l E X
  letI : Linear R C := coefficientModuleLinear l E X
  have ho : (sfRecollementModuleOpen l E i).Linear R :=
    linear_of_monic_counit _ (sfRecollementModuleCounit l E i)
      (fun M ↦ (sfRecollementModule_shortExact l E i M).mono_f)
  have hc : (sfRecollementModuleClosed l E i).Linear R :=
    linear_of_epic_unit _ (sfRecollementModuleUnit l E i)
      (sfRecollementModule_closed_adjunction l E i).1
  have hs : integralCoefficientLinear l E X = coefficientDerivedLinear l E X := by
    apply coefficientLinear_ext
    intro K K' a f
    rw [(integralCoefficientLinear_existsUnique l E X).exists.choose_spec]
    rw [coefficientDerived_eq]
    rfl
  change (sfRecollementModuleOpen l E i).mapDerivedCategory.Linear R ∧
    (sfRecollementModuleClosed l E i).mapDerivedCategory.Linear R
  change @Functor.Linear _ _ _ _ _ _ _ _ (integralCoefficientLinear l E X)
      (integralCoefficientLinear l E X) _ ∧
    @Functor.Linear _ _ _ _ _ _ _ _ (integralCoefficientLinear l E X)
      (integralCoefficientLinear l E X) _
  rw [hs]
  letI : Linear R (DerivedCategory C) := coefficientDerivedLinear l E X
  letI : DerivedCategory.Q.Linear R := Localization.functor_linear R
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ _) (HomologicalComplex.quasiIso C (.up ℤ))
  constructor
  · exact (Localization.functor_linear_iff DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ)) R
      ((sfRecollementModuleOpen l E i).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (sfRecollementModuleOpen l E i).mapDerivedCategory).mp inferInstance
  · exact (Localization.functor_linear_iff DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ)) R
      ((sfRecollementModuleClosed l E i).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (sfRecollementModuleClosed l E i).mapDerivedCategory).mp inferInstance

/-- The exact kernel and closed image preserve the integral constructible objects,
and are the recorded completed operations, with their canonical coefficient action.
Source: blueprint localization proof, integral paragraphs before the sheaf sequence;
Stacks 09AH, 09BM, 099N; Bhatt--Scholze 6.5 and 6.7.6
(blueprint: lem-sf-integral-kernel-operation-realization).

Proof: use `integralOperations_preserve_constructible` for the two recorded
integral pullbacks; invertibility in every residue field follows from hk and the
structure map (on Z use i followed by that of X). Use the specified completed
coefficient inverse-image maps. Uniqueness of the open adjoint and the ringed
short exact sequence identify the kernel, with its inclusion, with ordinary open
extension after restriction. The ordinary-to-completed immersion comparison is
normalized by the given completion unit. Immersion inverse image and exact open
extension preserve products and carry the augmented Roos triangle to the augmented
Roos triangle of the corresponding finite-reduction tower. The strict open reduction
comparison identifies its finite reductions
with finite open extension, preserving one common cohomological interval. Exact
open extension preserves products, hence completeness. The normalized compact-support
realization identifies this extension with the recorded compact-support value.
Closed direct image is exact and commutes with the reduction tower and its limit,
so preserves completeness and has the specified finite closed-image reductions.
Apply `sfIntegralDirectImage_constructible` to the recorded i-pullback, using
the finite-type closed immersion and its finite cohomological bound. The
closed-image direct-image/limit comparison identifies the ordinary exact image
with the recorded Roos direct image, with all quotient projections. Transport
constructibility across this isomorphism. Equivalently its finite closed-image
reductions have the original interval. For the open term use finite open extension
on each reduction and the original common interval; product/Roos preservation
gives its derived completeness. The normalized compact-support realization at
(j,id) identifies this object with the recorded value. Constant coefficient
sections commute with all these operations; the sheaf maps are linear, and their
termwise localizations preserve the canonical derived scalar action. Restriction
to the full constructible subcategory retains that action. Empty complements and
zero objects are included; all bounds concern the same interval at every level. -/
theorem sfIntegralKernel_operation_realization
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) :
    letI := sfRecollementNoetherian k X
    let S := sfIntegralConstructible l E X
    let A := sfIntegralKernelAmbient l E i
    ∃ (ho : ∀ K : S.FullSubcategory, S (A.openTerm.obj K.obj))
      (hc : ∀ K : S.FullSubcategory, S (A.closedTerm.obj K.obj)),
      SfIntegralRecollementVertices l E k hk i j (sfRecollementRestriction S A ho hc) ∧
      (sfRecollementRestriction S A ho hc).openTerm.Linear
        (Padic.coefficientExtensionIntegers l E) ∧
      (sfRecollementRestriction S A ho hc).closedTerm.Linear
        (Padic.coefficientExtensionIntegers l E) := by
  classical
  letI : IsNoetherian X := sfRecollementNoetherian k X
  letI : LocallyOfFiniteType (U ↘ Spec (.of k)) := (sfRecollementOpenFiniteType k j).1
  letI : QuasiCompact (U ↘ Spec (.of k)) := (sfRecollementOpenFiniteType k j).2.1
  letI : QuasiCompact j := (sfRecollementOpenFiniteType k j).2.2
  let S := sfIntegralConstructible l E X
  let A := sfIntegralKernelAmbient l E i
  have residueUnit (W : Scheme.{u}) (f : W ⟶ X) (w : W) :
      Invertible (l : W.residueField w) := by
    let φ := ((Scheme.ΓSpecIso (.of k)).inv ≫
      (f ≫ X ↘ Spec (.of k)).appTop ≫ W.Γevaluation w).hom
    exact (Eq.mp (congrArg IsUnit (map_natCast φ l)) (hk.map φ)).invertible
  letI : ∀ x : X, Invertible (l : X.residueField x) := residueUnit X (𝟙 X)
  letI : ∀ z : Z, Invertible (l : Z.residueField z) := residueUnit Z i
  letI : ∀ t : U, Invertible (l : U.residueField t) := residueUnit U j
  have hjK (K : S.FullSubcategory) :
      sfIntegralConstructible l E U ((integralDerivedPullback l E j).obj K.obj) :=
    ((integralOperations_preserve_constructible l E j).1 K.obj K.property).1
  have hiK (K : S.FullSubcategory) :
      sfIntegralConstructible l E Z ((integralDerivedPullback l E i).obj K.obj) :=
    ((integralOperations_preserve_constructible l E i).1 K.obj K.property).1
  have hopen (K : S.FullSubcategory) :
      Nonempty (A.openTerm.obj K.obj ≅
        (sfIntegralCompactSupportValue l E k hk
          (Compactification.ofIsOpenImmersion j) ⟨_, hjK K⟩).obj) :=
    sfIntegralOpenKernel_compactSupport l E k hk i j hij K (hjK K)
  have ho (K : S.FullSubcategory) : S (A.openTerm.obj K.obj) := by
    obtain ⟨e⟩ := hopen K
    exact S.prop_of_iso e.symm
      (sfIntegralCompactSupportValue l E k hk
        (Compactification.ofIsOpenImmersion j) ⟨_, hjK K⟩).property
  have hc (K : S.FullSubcategory) : S (A.closedTerm.obj K.obj) := by
    have : (kernel (sfRecollementModuleUnit l E i)).Additive :=
      sfRecollementModuleOpen_additive l E i
    have : PreservesFiniteLimits (kernel (sfRecollementModuleUnit l E i)) :=
      sfRecollementModuleOpen_limits l E i
    have : PreservesFiniteColimits (kernel (sfRecollementModuleUnit l E i)) :=
      sfRecollementModuleOpen_colimits l E i
    obtain ⟨δ, hδ⟩ := sfExactLocalizationPresentation_distinguished
      (sfRecollementModuleOpen l E i) (sfRecollementModuleClosed l E i)
      (sfRecollementModuleCounit l E i) (sfRecollementModuleUnit l E i)
      (kernel.condition (sfRecollementModuleUnit l E i))
      (sfRecollementModule_shortExact l E i) K.obj
    exact S.ext_of_isTriangulatedClosed₃ _ hδ (ho K) K.property
  obtain ⟨hla, hlb⟩ := sfIntegralKernel_ambient_linear l E i
  letI : A.openTerm.Linear (Padic.coefficientExtensionIntegers l E) := hla
  letI : A.closedTerm.Linear (Padic.coefficientExtensionIntegers l E) := hlb
  refine ⟨ho, hc, ?_, inferInstance, inferInstance⟩
  constructor
  · intro K
    obtain ⟨e⟩ := hopen K
    exact ⟨hjK K, ⟨S.isoMk e⟩⟩
  · intro K
    exact sfIntegralClosedKernel_roos l E i K.obj K.property.1 (hiK K).1

end WeilConjectures
