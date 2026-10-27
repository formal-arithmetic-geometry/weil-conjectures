module

public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Ambient integral direct image through strict completed-coefficient towers

Source: latest blueprint, fix-cor-verdier-exchange.proof.md, Step 3, integral
shift compatibility; Stacks 0941 and 07A6
(blueprint: def-sf-ambient-integral-direct-image).

The existing finite direct images and Roos presentations are reexported unchanged.
The ambient realization first reduces into the actual derived system category, then
restricts scalars, derives sectionwise direct image on strict towers, and takes the
unbounded total inverse limit. Site and coefficient universes remain independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)

/-- Direct image of commutative ring sheaves in the common coefficient universe.
Source: Stacks 03DA (blueprint: def-sf-ambient-integral-direct-image). -/
abbrev sfAmbientRingPush :
    Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)} :=
  (proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)

/-- The finite coefficient structure map extends the literal constant-section map.
Source: Stacks 03DA and 0H7J (blueprint: def-sf-ambient-integral-direct-image). -/
def sfAmbientFiniteRingMap (n : ℕ) :
    integralCoefficientCommRingSheaf l E Y n ⟶
      (sfAmbientRingPush.{t, u} f).obj (integralCoefficientCommRingSheaf l E X n) :=
  ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}).homEquiv
    _ _).symm
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))))

private theorem sfAmbientFiniteRingMap_naturality (A B : CommRingCat.{max u (t + 1)})
    (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map a ≫
        ((sheafificationAdjunction (ProEt.topology Y)
          CommRingCat.{max u (t + 1)}).homEquiv _
            ((sfAmbientRingPush.{t, u} f).obj
              ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj B))).symm
          (Functor.whiskerLeft (proEtaleBaseChange f).op
            (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B))) =
      ((sheafificationAdjunction (ProEt.topology Y)
        CommRingCat.{max u (t + 1)}).homEquiv _ _).symm
          (Functor.whiskerLeft (proEtaleBaseChange f).op
            (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A))) ≫
        (sfAmbientRingPush.{t, u} f).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map a) := by
  apply (sheafificationAdjunction (ProEt.topology Y)
    CommRingCat.{max u (t + 1)}).homEquiv _ _ |>.injective
  dsimp only [constantSheaf, Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun z ↦ z.app ((proEtaleBaseChange f).op.obj U))
    ((sheafificationAdjunction (ProEt.topology X)
      CommRingCat.{max u (t + 1)}).unit.naturality ((Functor.const X.ProEtᵒᵖ).map a))

/-- The canonical completed coefficient map is determined by all finite projections.
Source: blueprint order 1468; Stacks 03CO and 03DA
(blueprint: def-sf-ambient-integral-direct-image).
Proof: the constant-section maps commute with each coefficient quotient, since both
composites extend the same map of constant presheaves. They therefore give a cone
from the completed sheaf on Y to the direct image of the quotient system on X.
Sectionwise direct image preserves limits, so its image of the defining completion
cone is limiting. Its universal property gives the displayed map, and its jointly
monic projections give uniqueness. This argument takes place at size max u (t+1)
without changing the small pro-etale site. -/
theorem sfAmbientCoefficientMap_existsUnique :
    ∃! φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
        (sfAmbientRingPush.{t, u} f).obj
          (completedIntegralCommRingSheafUnrestricted l E X),
      ∀ n : ℕ,
        φ ≫ (sfAmbientRingPush.{t, u} f).map
            (completedIntegralCommRingProjectionUnrestricted l E X n) =
          completedIntegralCommRingProjectionUnrestricted l E Y n ≫
            sfAmbientFiniteRingMap l E f n := by
  let G := (proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{max u (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)
  let H := sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let DY := integralCoefficientSheafSystem l E Y
  let DX := integralCoefficientSheafSystem l E X
  let ρ (n : ℕ) := H.map (sfAmbientFiniteRingMap l E f n)
  let α : DY ⟶ DX ⋙ G := NatTrans.ofOpSequence ρ (by
    intro n
    dsimp only [DY, DX, integralCoefficientSheafSystem, Functor.comp_map]
    rw [Functor.ofOpSequence_map_homOfLE_succ,
      Functor.ofOpSequence_map_homOfLE_succ]
    dsimp only [integralCoefficientSheafTransition, ρ, H, G]
    have hh := sfAmbientFiniteRingMap_naturality f _ _
      (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
          ((Padic.coefficientExtensionTransition l E (n + 1)).comp
            (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact congrArg
      (fun z ↦ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
        (z.hom.app U)) hh)
  let c : Cone (DX ⋙ G) := ⟨limit DY, (limit.cone DY).π ≫ α⟩
  let h := isLimitOfPreserves G (limit.isLimit DX)
  let g : H.obj (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
      H.obj ((sfAmbientRingPush.{t, u} f).obj
        (completedIntegralCommRingSheafUnrestricted l E X)) := h.lift c
  let φ := H.preimage g
  have hφ (n : ℕ) :
      φ ≫ (sfAmbientRingPush.{t, u} f).map
          (completedIntegralCommRingProjectionUnrestricted l E X n) =
        completedIntegralCommRingProjectionUnrestricted l E Y n ≫
          sfAmbientFiniteRingMap l E f n := by
    apply H.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    ext U x
    exact congrArg (fun z ↦ z.hom.app U x) (h.fac c (op n))
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply H.map_injective
  apply h.hom_ext
  intro n
  ext U x
  exact congrArg (fun z ↦ z.hom.app U x) ((hψ n.unop).trans (hφ n.unop).symm)

/-- The structural map selected by its unique finite-coordinate characterization.
Source: Stacks 03CO and 03DA (blueprint: def-sf-ambient-integral-direct-image). -/
def sfAmbientCoefficientMap :=
  (sfAmbientCoefficientMap_existsUnique l E f).exists.choose

/-- Completed-module direct image with its canonical scalar action on sections.
Source: Stacks 03D1 (blueprint: def-sf-ambient-integral-direct-image). -/
def sfAmbientModulePush : scalarReductionSource l E X ⥤ scalarReductionSource l E Y :=
  SheafOfModules.pushforward.{max u (t + 1)} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    ⟨Functor.whiskerRight (sfAmbientCoefficientMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- Sectionwise direct image is additive with its completed scalar action.
Source: Stacks 03D1 (blueprint: def-sf-ambient-integral-direct-image).
Proof: precomposition sends a sum of module morphisms to the sum of their section
maps. Restriction of the scalar action leaves these additive maps unchanged. -/
theorem sfAmbientModulePush_additive : (sfAmbientModulePush l E f).Additive := by
  constructor
  intro M N a b
  ext U x
  rfl

attribute [instance] sfAmbientModulePush_additive

/-- The ordinary direct image on actual strict completed-module towers.
Source: Stacks 0941 and 03D1 (blueprint: def-sf-ambient-integral-direct-image). -/
def sfAmbientTowerPush :
    (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ (ℕᵒᵖ ⥤ scalarReductionSource l E Y) :=
  (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource l E X)
    (scalarReductionSource l E Y)).obj (sfAmbientModulePush l E f)

/-- Additivity on towers is the existing componentwise additive functor instance.
Source: Stacks 0941 (blueprint: def-sf-ambient-integral-direct-image). -/
instance sfAmbientTowerPushAdditive : (sfAmbientTowerPush l E f).Additive :=
  inferInstanceAs ((Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource l E X)
    (scalarReductionSource l E Y)).obj (sfAmbientModulePush l E f)).Additive

/-- Unbounded derived direct image on strict towers, using their simultaneous
K-injective resolutions. Source: Stacks 0941 and 07A6
(blueprint: def-sf-ambient-integral-direct-image). -/
abbrev sfAmbientDerivedTowerPush :
    coefficientSequenceRestrictedDerived l E X ⥤ coefficientSequenceRestrictedDerived l E Y :=
  (sfAmbientTowerPush l E f).rightDerivedFunctor

/-- The actual ambient realization of the integral direct-image formula.
Reduction is the recorded coefficient calculus, characterized on one flat-term
K-flat representative by its strict quotient system. Its adjunction to the fixed
sequence-limit functor determines it up to the natural isomorphism used here.
After exact scalar restriction, the total derived tower image has nth evaluation
Res_n Rf_{*,n}(K tensor^L A_{E,n+1}), by the ringed direct-image restriction
comparison. Its transitions are induced by the same quotient maps, since the
completed structural map is normalized by all finite projections. The final total
inverse limit is the functorial strict-tower realization of the displayed Rlim;
its Roos triangle is the recorded derived-limit presentation.
Source: blueprint order 1468; Stacks 0941, 07A6 and 0D6E
(blueprint: def-sf-ambient-integral-direct-image). -/
def sfAmbientIntegralDirectImage :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction ⋙
    coefficientSequenceDerivedRestriction l E X ⋙ sfAmbientDerivedTowerPush l E f ⋙
      coefficientConstantTowerLimit l E Y

end WeilConjectures
