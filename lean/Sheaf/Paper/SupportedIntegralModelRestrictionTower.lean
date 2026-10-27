module

public import Sheaf.Paper.SupportedIntegralRestrictionComparison
import Mathlib.CategoryTheory.Sites.Adjunction
import Sheaf.Paper.SupportedIntegralFiniteQuotients
import Sheaf.Paper.SupportedIntegralEndpointReconstruction
import Sheaf.Paper.SupportedIntegralRestrictionSquare
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Supported integral restriction and strict quotient tower comparison

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), first paragraph
(blueprint: lem-sfb-supported-integral-model-restriction-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.SupportedIntegral
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

private theorem marked_unique
    {A B J : Type*} [Category A] [Category B] [Category J]
    (V : A ⥤ B) [V.Full] [V.Faithful] (F G : J ⥤ A) (H : J ⥤ B)
    (d : F ⋙ V ≅ H) (e : G ⋙ V ≅ H) :
    ∃! i : G ≅ F, Functor.whiskerRight i.hom V ≫ d.hom = e.hom := by
  let W := (Functor.whiskeringRight J A B).obj V
  let i : G ≅ F := W.preimageIso (e ≪≫ d.symm)
  have hi : Functor.whiskerRight i.hom V = e.hom ≫ d.inv :=
    W.map_preimage _
  refine ⟨i, ?_, ?_⟩
  · change Functor.whiskerRight i.hom V ≫ d.hom = e.hom
    rw [hi, Category.assoc, d.inv_hom_id, Category.comp_id]
  · intro j hj
    apply Iso.ext
    apply W.map_injective
    change Functor.whiskerRight j.hom V = Functor.whiskerRight i.hom V
    rw [hi, ← hj, Category.assoc, d.hom_inv_id, Category.comp_id]

private theorem pointScalar_one : pointScalar R 1 = 𝟙 _ := by
  apply Mod.hom_ext
  ext V f
  apply ULift.ext
  exact one_mul _

private theorem pointScalar_add (a b : R) :
    pointScalar R (a + b) = pointScalar R a + pointScalar R b := by
  apply Mod.hom_ext
  ext V f
  apply ULift.ext
  change ContinuousMap.const V.unop (a + b) * f.down =
    ContinuousMap.const V.unop a * f.down + ContinuousMap.const V.unop b * f.down
  exact add_mul (ContinuousMap.const V.unop a) (ContinuousMap.const V.unop b) f.down

private theorem pointScalar_mul (a b : R) :
    pointScalar R (a * b) = pointScalar R b ≫ pointScalar R a := by
  apply Mod.hom_ext
  ext V f
  apply ULift.ext
  change (ContinuousMap.const V.unop a * ContinuousMap.const V.unop b) * f.down =
    ContinuousMap.const V.unop a * (ContinuousMap.const V.unop b * f.down)
  exact mul_assoc _ _ _

private instance pointPullFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (pointPull R X) := by
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  infer_instance

private instance pointPullAdditive (X : Scheme.{u}) : (pointPull R X).Additive := by
  have : PreservesBinaryBiproducts (pointPull R X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _

private theorem scalar_one (X : Scheme.{u}) : scalar R X 1 = 𝟙 _ := by
  dsimp only [scalar]
  rw [pointScalar_one, (pointPull R X).map_id, Category.id_comp, Iso.inv_hom_id]
  apply NatTrans.ext
  funext M
  change (λ_ M).inv ≫ (𝟙 (𝟙_ (Modules R X)) ▷ M) ≫ (λ_ M).hom = 𝟙 M
  rw [id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

private theorem scalar_add (X : Scheme.{u}) (a b : R) :
    scalar R X (a + b) = scalar R X a + scalar R X b := by
  apply NatTrans.ext
  funext M
  dsimp only [scalar]
  simp only [pointScalar_add, (pointPull R X).map_add, Preadditive.comp_add,
    Preadditive.add_comp, (tensoringLeft (Modules R X)).map_add]

private theorem scalar_mul (X : Scheme.{u}) (a b : R) :
    scalar R X (a * b) = scalar R X b ≫ scalar R X a := by
  dsimp only [scalar]
  rw [pointScalar_mul, (pointPull R X).map_comp]
  apply NatTrans.ext
  funext M
  change (λ_ M).inv ≫
      (((regularIso R X).inv ≫
        ((pointPull R X).map (pointScalar R b) ≫
          (pointPull R X).map (pointScalar R a)) ≫ (regularIso R X).hom) ▷ M) ≫
        (λ_ M).hom =
    ((λ_ M).inv ≫
      (((regularIso R X).inv ≫ (pointPull R X).map (pointScalar R b) ≫
        (regularIso R X).hom) ▷ M) ≫ (λ_ M).hom) ≫
    ((λ_ M).inv ≫
      (((regularIso R X).inv ≫ (pointPull R X).map (pointScalar R a) ≫
        (regularIso R X).hom) ▷ M) ≫ (λ_ M).hom)
  simp only [comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc (regularIso R X).hom (regularIso R X).inv M,
    Iso.hom_inv_id, MonoidalCategory.id_whiskerRight, Category.id_comp]

private instance scalarSectionModule (X : Scheme.{u}) (M : Modules R X)
    (V : X.ProEtᵒᵖ) : Module (ULift.{u + 1} R) (M.X.obj.obj V) where
  smul a x := (((scalar R X a.down).app M).hom.hom.app V) x
  one_smul x := by
    have h := congrArg (fun t : End (𝟭 (Modules R X)) ↦
      ((t.app M).hom.hom.app V) x) (scalar_one R X)
    exact h
  mul_smul a b x := by
    have h := congrArg (fun t : End (𝟭 (Modules R X)) ↦
      ((t.app M).hom.hom.app V) x) (scalar_mul R X a.down b.down)
    exact h
  smul_zero a := map_zero _
  smul_add a x y := map_add _ _ _
  add_smul a b x := by
    have h := congrArg (fun t : End (𝟭 (Modules R X)) ↦
      ((t.app M).hom.hom.app V) x) (scalar_add R X a.down b.down)
    exact h
  zero_smul x := by
    have h := congrArg (fun t : End (𝟭 (Modules R X)) ↦
      ((t.app M).hom.hom.app V) x) (scalar_add R X 0 0)
    change (((scalar R X (0 + 0)).app M).hom.hom.app V) x =
      (((scalar R X 0).app M).hom.hom.app V) x +
        (((scalar R X 0).app M).hom.hom.app V) x at h
    rw [add_zero] at h
    exact (add_eq_left.mp h.symm)

private def coordinateFunctor (X : Scheme.{u}) :
    Modules R X ⥤ Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} R)) where
  obj M :=
    ⟨{ obj V := ModuleCat.of (ULift.{u + 1} R) (M.X.obj.obj V)
       map {V W} f := ModuleCat.ofHom
         { toFun := M.X.obj.map f
           map_add' := map_add _
           map_smul' := fun a x ↦ by
             exact ConcreteCategory.congr_hom
               (((scalar R X a.down).app M).hom.hom.naturality f).symm x }
       map_id V := by
         ext x
         exact ConcreteCategory.congr_hom (M.X.obj.map_id V) x
       map_comp f g := by
         ext x
         exact ConcreteCategory.congr_hom (M.X.obj.map_comp f g) x },
      Presheaf.isSheaf_of_isSheaf_comp (Scheme.ProEt.topology X) _
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) Ab.{u + 1}) M.X.property⟩
  map {M N} f := ⟨{
    app V := ModuleCat.ofHom
      { toFun := f.hom.hom.app V
        map_add' := map_add _
        map_smul' := fun a x ↦ by
          have h := congrArg (fun g : M ⟶ N ↦ (g.hom.hom.app V) x)
            ((scalar R X a.down).naturality f)
          exact h.symm }
    naturality V W g := by
      ext x
      exact ConcreteCategory.congr_hom (f.hom.hom.naturality g) x }⟩

private instance coordinateFunctorAdditive (X : Scheme.{u}) :
    (coordinateFunctor R X).Additive where
  map_add := by
    intros
    ext V x
    rfl

private theorem coordinates (X : Scheme.{u}) : Nonempty (Coordinates R X) := by
  let F := coordinateFunctor R X
  let U := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) Ab.{u + 1})
  have : PreservesFiniteLimits U := by
    have : PreservesFiniteLimits (U ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) Ab.{u + 1})))
    exact preservesFiniteLimits_of_reflects_of_preserves U (sheafToPresheaf _ _)
  have : PreservesFiniteColimits U := by
    let G := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) Ab.{u + 1}
    have : G.IsLeftAdjoint := by
      let A := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom (ULift.{u + 1} R))
      have : A.IsLeftAdjoint :=
        (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1}
          (Int.castRingHom (ULift.{u + 1} R))).isLeftAdjoint
      exact inferInstanceAs
        (A ⋙ forget₂ (ModuleCat.{u + 1} ℤ) Ab.{u + 1}).IsLeftAdjoint
    let e : Sheaf.composeAndSheafify (Scheme.ProEt.topology X) G ≅ U :=
      Functor.isoWhiskerLeft U
        (sheafificationNatIso (Scheme.ProEt.topology X) Ab.{u + 1}).symm ≪≫
          Functor.rightUnitor U
    have : (Sheaf.composeAndSheafify (Scheme.ProEt.topology X) G).IsLeftAdjoint :=
      (CategoryTheory.Sheaf.adjunction (Scheme.ProEt.topology X)
        (Adjunction.ofIsLeftAdjoint G)).isLeftAdjoint
    have : U.IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
    infer_instance
  have : PreservesFiniteLimits (F ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits
      (Mod.forget (condensedRingObj (Profinite.continuousCoefficientRingObj R) X)))
  have : PreservesFiniteColimits (F ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits
      (Mod.forget (condensedRingObj (Profinite.continuousCoefficientRingObj R) X)))
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F U
  have : PreservesFiniteColimits F := preservesFiniteColimits_of_reflects_of_preserves F U
  exact ⟨{ functor := F, underlying := Iso.refl _, normalization := fun _ _ _ ↦ rfl }⟩

private theorem resolutions (X : Scheme.{u}) : Resolutions R X := by
  let : IsGrothendieckAbelian.{u + 1} (Modules R X) := inferInstance
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} R))) :=
    inferInstance
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} R))) :=
    inferInstance
  let := CategoryTheory.tower_grothendieck (Modules R X)
  let := CategoryTheory.tower_grothendieck
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
  let := CategoryTheory.tower_grothendieck
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} R)))
  let := CategoryTheory.tower_grothendieck Ab.{u + 1}
  exact {}

private theorem descentOfClassical
    {T S : Scheme.{u}} {tree : QcqsOpenClosedTree T} (p : tree.Path S)
    (π : R) (ℓ : ℕ) (c : Coordinates R T)
    (hclass : ∀ (M : Models R S) (n : ℕᵒᵖ),
      IsClassical ((sheafCompose (Scheme.ProEt.topology T)
        (forget (ModuleCat.{u + 1} (ULift.{u + 1} R)))).obj
          ((((supportedQuotients R p π) ⋙ towerMap c.functor).obj M).obj n)))
    (hquot : ∀ (M : Models R S) (n : ℕ) (V : T.ProEtᵒᵖ),
      (((((supportedQuotients R p π) ⋙ towerMap c.functor).obj M).obj (op n)).obj.obj V).smul
        (ULift.up (π ^ (n + 1))) = 0)
    (hell : ∀ (M : Models R S) (n : ℕ), ∃ k : ℕ, ∀ (V : T.ProEtᵒᵖ)
      (x : ((((supportedQuotients R p π) ⋙ towerMap c.functor).obj M).obj (op n)).obj.obj V),
      (ℓ ^ k) • x = 0) : Nonempty (Descent R p π ℓ c) := by
  classical
  let H := supportedQuotients R p π ⋙ towerMap c.functor
  let V := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T
  let U := comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T
  let adj := comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} R)) T
  let F := H ⋙ towerMap U
  have hc (M : Models R S) (n : ℕᵒᵖ) : IsIso (adj.counit.app ((H.obj M).obj n)) := by
    obtain ⟨_, _, _, _, _, he⟩ :=
      proEtaleClassicalSheavesModules T (ULift.{u + 1} R)
    exact adj.isIso_counit_app_iff_mem_essImage.mpr ((he _).mp (hclass M n))
  let e : F ⋙ towerMap V ≅ H := NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents
      (fun n ↦ asIso (adj.counit.app ((H.obj M).obj n)))
      (fun f ↦ adj.counit.naturality ((H.obj M).map f)))
    (fun f ↦ by
      apply NatTrans.ext
      funext n
      exact adj.counit.naturality ((H.map f).app n))
  refine ⟨{
    functor := F
    identification := e
    quotientAction := ?_
    ellPower := ?_
    unique := ?_ }⟩
  · intro M n W
    exact hquot M n ((Scheme.toProEt T).op.obj W)
  · intro M n
    obtain ⟨k, hk⟩ := hell M n
    exact ⟨k, fun W x ↦ hk ((Scheme.toProEt T).op.obj W) x⟩
  · intro G e'
    exact marked_unique (towerMap V) F G H e e'

private def pulledIdentification
    {T₀ T S : Scheme.{u}} (t : T₀ ⟶ T)
    {tree : QcqsOpenClosedTree T} (p : tree.Path S) (π : R) (ℓ : ℕ)
    (c₀ : Coordinates R T₀) (c : Coordinates R T) (d : Descent R p π ℓ c)
    (b : PullbackCoordinates R t c₀ c) :
    d.functor ⋙ towerMap (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) t) ⋙
        towerMap (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T₀) ≅
      supportedQuotients R p π ⋙
        towerMap (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) t) ⋙
        towerMap c₀.functor := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1} R)
  let U := upperStar A t
  let V := comparisonUpperStar A T
  let E := Etale.upperStar A t
  let V₀ := comparisonUpperStar A T₀
  let P := CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) t
  let W := Functor.whiskeringRight ℕᵒᵖ (Sheaf T.smallEtaleTopology A)
    (Sheaf (Scheme.ProEt.topology T₀) A)
  let W' := Functor.whiskeringRight ℕᵒᵖ (Modules R T)
    (Sheaf (Scheme.ProEt.topology T₀) A)
  exact Functor.isoWhiskerLeft d.functor
      (Functor.whiskeringRightObjCompIso E V₀ ≪≫
        W.mapIso (comparisonUpperStarCompUpperStarIso A t).symm ≪≫
        (Functor.whiskeringRightObjCompIso V U).symm) ≪≫
    Functor.isoWhiskerRight d.identification (towerMap U) ≪≫
    Functor.isoWhiskerLeft (supportedQuotients R p π)
      (Functor.whiskeringRightObjCompIso c.functor U ≪≫ W'.mapIso b.upper ≪≫
        (Functor.whiskeringRightObjCompIso P c₀.functor).symm)

private theorem pulledIdentification_normalization
    {T₀ T S : Scheme.{u}} (t : T₀ ⟶ T)
    {tree : QcqsOpenClosedTree T} (p : tree.Path S) (π : R) (ℓ : ℕ)
    (c₀ : Coordinates R T₀) (c : Coordinates R T) (d : Descent R p π ℓ c)
    (b : PullbackCoordinates R t c₀ c) (M : Models R S) (n : ℕᵒᵖ) :
    ((pulledIdentification R t p π ℓ c₀ c d b).hom.app M).app n =
      (comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) t).inv.app ((d.functor.obj M).obj n) ≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) t).map
        ((d.identification.hom.app M).app n) ≫
      b.upper.hom.app (((supportedQuotients R p π).obj M).obj n) := by
  simp [pulledIdentification, Functor.whiskeringRightObjCompIso]

/-- Supported integral finite models are reconstructed by the actual strict finite-level
etale restriction arrows, compatibly with the entire quotient augmentation and every module map.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), first paragraph,
closed-fibre heart comparison
(blueprint: lem-sfb-supported-integral-model-restriction-tower).

Proof in words, following all eight DAG steps.
1. Use lem-sfb-internal-module-operations-transport and
   lem-sfb-integral-quotient-resolution-normalization to pass to section coordinates,
   retaining constant scalars and all quotient maps. The ring is Noetherian and its
   positive uniformizer quotients are finite. Since ell belongs to (pi), the quotient
   of exponent n is killed by ell^n. Every chain edge is exact and scalar linear by
   lem-weil-pbc-proetale-ringed-open-closed, so it carries the ordinary quotient and
   its actual projection to the ordinary quotient after extension.
2. Lem-sfb-finite-model-sheaf-quotient-constructible, the finite-discrete coefficient
   equivalence and lem-pe-finite-discrete-scalar-constant-models show that each supported
   ordinary quotient is constructible. Refine the finite strata at each open/closed
   edge, putting the zero module on the complementary stratum. This also retains its
   quotient-ring action and ell-power annihilation.
3. Apply det-pe-constructible-comparison-classical and sk-thm-pe-classical-sheaves.
   Full faithfulness descends every actual quotient transition and every actual map
   of finite models uniquely. It gives the functorial marked uniqueness in Descent.
   Lem-weil-pbc-comparison-pullback gives identification_0; the comparison square and
   adjunction mate give precisely pullback_normalization.
4. The strict two-term reductions [L --pi^n--> L] have transition (pi,1).
   Lem-sfb-finite-scalar-local-model-complete and
   lem-sfb-finite-scalar-model-ordinary-quotient-comparison identify their total limit
   with the ordinary quotient tower, carrying the original augmentation to quotientUnit.
   This step includes torsion scalar models and does not identify the individual
   derived reduction with its ordinary quotient.
5. Open extension preserves countable products by det-sf-open-closed-extension-zero-limits;
   closed direct image does so as a right adjoint. Exact countable products on pro-etale
   module sheaves and lem-cbc-exact-product-functor-strict-limit transport the normalized
   augmentation through every support edge. The identity chain uses the identity map.
6. Lem-weil-pbc-proetale-immersion-limit-preservation transports the augmentation through
   t^*, without any quasi-compact-complement hypothesis on t. Apply
   lem-sfb-ringed-restriction-strict-limit-coherence to identify the actual horizontal
   restriction with the total limit of the finite pro-etale restriction arrows.
7. Lem-coef-derived-sections-scalar-coherence and sk-prop-sf-comparison identify the finite
   etale and pro-etale derived sections. Sk-thm-pe-direct-image-comparison and
   lem-weil-pbc-mate-pasting retain the actual restriction square. Apply these comparisons
   to strict towers, using lem-coef-sequence-global-sections-evaluation and
   lem-weil-pbc-tower-derived-evaluation-normalization. Evaluation detects cohomology
   isomorphisms, so the normalized tower comparison is invertible.
8. Apply total derived inverse limit (lem-weil-pbc-ringed-strict-tower-homotopy-limit)
   to the resulting arrow isomorphism. Its two endpoint normalization equations are
   the maps augmentedSections constructs from the actual supported quotient augmentation.
   All constructions are natural in the full category of finite models. The torsion
   rigidity hypothesis is retained for the consuming argument, though reconstruction
   does not need it. Zero, empty, torsion and mixed-chain cases use the same formulas;
   no image-completeness assertion occurs.
-/
theorem supported_integral_model_restriction_tower
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (π : R)
    (hR :
      (∃ e : R ≃+* ℤ_[ℓ], Continuous e ∧ Continuous e.symm ∧ e π = (ℓ : ℤ_[ℓ])) ∨
      (letI := spectralNorm.nontriviallyNormedField (Padic ℓ) E
       ∃ e : R ≃+* Padic.coefficientExtensionIntegers ℓ E,
         Continuous e ∧ Continuous e.symm ∧
         Ideal.span ({e π} : Set (Padic.coefficientExtensionIntegers ℓ E)) =
           Padic.coefficientExtensionMaximalIdeal ℓ E))
    {T₀ T S : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace T₀] [QuasiSeparatedSpace T₀]
    (t : T₀ ⟶ T) [IsClosedImmersion t]
    (ht : ∀ (F : Sheaf T.smallEtaleTopology Ab.{u + 1}),
      Scheme.IsTorsionAbelianSheaf F → ∀ q : ℕ,
        Function.Bijective (Etale.cohomologyMap t F q))
    (tree : QcqsOpenClosedTree T) (p : tree.Path S) :
    ∃ (hAb : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Ab.{u + 1})),
      letI := hAb
      ∃ (hT : Resolutions R T) (hT₀ : Resolutions R T₀),
      letI := hT
      letI := hT₀
      ∃ (c₀ : Coordinates R T₀) (c : Coordinates R T) (d : Descent R p π ℓ c),
        Nonempty (RestrictionComparison R t p π ℓ c₀ c d) := by
  have _ := ht
  classical
  let hT := resolutions R T
  let hT₀ := resolutions R T₀
  let hAb := hT.abelianTower
  refine ⟨hAb, hT, hT₀, ?_⟩
  obtain ⟨c₀⟩ := coordinates R T₀
  obtain ⟨c⟩ := coordinates R T
  obtain ⟨⟨b⟩, hc, hq, he⟩ :=
    supported_integral_finite_quotients R ℓ E π hR t tree p c₀ c
  obtain ⟨d⟩ := descentOfClassical R p π ℓ c hc hq he
  let e₀ := pulledIdentification R t p π ℓ c₀ c d b
  have he₀ := pulledIdentification_normalization R t p π ℓ c₀ c d b
  obtain ⟨l, r, hl, hr⟩ :=
    supported_integral_endpoint_reconstruction R ℓ E π hR t tree p c₀ c d b e₀ he₀
  have hs := supported_integral_restriction_square R ℓ E π hR t tree p c₀ c d b e₀
    he₀ l r hl hr
  let e : integralArrows R t p ≅ etaleArrows R t d.functor :=
    NatIso.ofComponents (fun M ↦ Arrow.isoMk (l.app M) (r.app M) (hs M))
      (fun f ↦ by
        apply Arrow.hom_ext
        · exact l.hom.naturality f
        · exact r.hom.naturality f)
  refine ⟨c₀, c, d, ⟨{
    pullback := b
    identification₀ := e₀
    pullback_normalization := he₀
    iso := e
    source_normalization := ?_
    target_normalization := ?_ }⟩⟩
  · exact hl
  · exact hr

end AlgebraicGeometry.ProEtale.SupportedIntegral
