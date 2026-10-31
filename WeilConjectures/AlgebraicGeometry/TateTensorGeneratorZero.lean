/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TateTensorGeneratorCompatibility
import WeilConjectures.AlgebraicGeometry.ComparisonPureSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence

/-! Tensor-degree construction of the integral Tate quotient comparison.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-generator-zero)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local instance] Sheaf.monoidalCategory

local instance (priority := 4000) (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} T
local instance (priority := 4000) (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, u} T
local instance (priority := 4000) (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} T

private theorem scalarExtensionSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] scalarExtensionSmall


private def scalarUnitPresheaf (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :=
  (PresheafOfModules.restrictScalars (scalars T ell n)).obj
    (SheafOfModules.unit ((adicLisseForget T).obj
      ((pbcAdicRings T (datum.{u} ell)).obj (op n)))).val

private def scalarUnitFixed (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (coefficient ell (n + 1)) where
  obj U := (scalarUnitPresheaf T ell n).obj U
  map f := (scalarUnitPresheaf T ell n).map f
  map_id U := by
    ext x
    exact ConcreteCategory.congr_hom ((scalarUnitPresheaf T ell n).presheaf.map_id U) x
  map_comp f g := by
    ext x
    exact ConcreteCategory.congr_hom ((scalarUnitPresheaf T ell n).presheaf.map_comp f g) x

private theorem scalarUnitFixed_isSheaf
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    Presheaf.IsSheaf (ProEt.topology T) (scalarUnitFixed T ell n) := by
  apply Presheaf.isSheaf_of_isSheaf_comp (ProEt.topology T) _
    (forget₂ _ AddCommGrpCat.{u + 1})
  exact (SheafOfModules.unit ((adicLisseForget T).obj
    ((pbcAdicRings T (datum.{u} ell)).obj (op n)))).isSheaf

private def scalarUnitRaw (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    (Functor.const T.ProEtᵒᵖ).obj
      (ModuleCat.of (coefficient ell (n + 1)) (coefficient ell (n + 1))) ⟶
    scalarUnitFixed T ell n where
  app U := ModuleCat.ofHom (Y := (scalarUnitFixed T ell n).obj U)
    { toFun := (scalars T ell n).app U
      map_add' := map_add ((scalars T ell n).app U).hom
      map_smul' := fun r x ↦ ((scalars T ell n).app U).hom.map_mul r x }
  naturality U V f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact ConcreteCategory.congr_hom ((scalars T ell n).naturality f) a

private def scalarUnitLift (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    (constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} (coefficient ell (n + 1)))).obj
      (ModuleCat.of (coefficient ell (n + 1)) (coefficient ell (n + 1))) ⟶
    (⟨scalarUnitFixed T ell n, scalarUnitFixed_isSheaf T ell n⟩ : Sheaf _ _) :=
  ⟨sheafifyLift _ (scalarUnitRaw T ell n) (scalarUnitFixed_isSheaf T ell n)⟩

private def realizeToUnit (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (coefficient ell (n + 1))))
    (g : M ⟶ ⟨scalarUnitFixed T ell n, scalarUnitFixed_isSheaf T ell n⟩) :
    (realization T ell n).obj M ⟶
    SheafOfModules.unit ((adicLisseForget T).obj
      ((pbcAdicRings T (datum.{u} ell)).obj (op n))) :=
  (PresheafOfModules.sheafificationHomEquiv (scalars T ell n)).symm
    { app U := g.hom.app U
      naturality f := by
        ext x
        exact ConcreteCategory.congr_hom (g.hom.naturality f) x }

private theorem realizeToUnit_generator
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (coefficient ell (n + 1))))
    (g : M ⟶ ⟨scalarUnitFixed T ell n, scalarUnitFixed_isSheaf T ell n⟩)
    (W : T.ProEtᵒᵖ) (x : M.obj.obj W) :
    (realizeToUnit T ell n M g).val.app W
      ((toSheafify (ProEt.topology T)
        (M.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W x) = g.hom.app W x := by
  let q : (finiteCoefficientModulePresheaf T.ProEt (coefficient ell (n + 1))).obj M.obj ⟶
      scalarUnitPresheaf T ell n :=
    { app U := g.hom.app U
      naturality f := by
        ext y
        exact ConcreteCategory.congr_hom (g.hom.naturality f) y }
  have h := congrArg (PresheafOfModules.toPresheaf
    ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (coefficient ell (n + 1))))).map
      ((PresheafOfModules.sheafificationHomEquiv (scalars T ell n)
        (F := SheafOfModules.unit ((adicLisseForget T).obj
          ((pbcAdicRings T (datum.{u} ell)).obj (op n))))).apply_symm_apply q)
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at h
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h W) x

set_option maxHeartbeats 2000000 in
-- The section calculation unfolds both module sheafification and scalar-extension transports.
/-- The coefficient-unit case of the normalized quotient comparison.

Source: smooth-purity transport, Step 2, degree-zero coefficient multiplication.
(blueprint: lem-pur-tate-tensor-generator-zero)

Proof: identify the comparison pullback of the constant finite coefficient module
with the constant pro-etale coefficient module, using the unit constraint of the
comparison functor. Its additive sheafification, with scalars extended along
`scalars`, is the unit module of the finite coefficient sheaf: the map sends a
constant section a to `scalars(a)`. Identify scalar extension of the completed
coefficient unit with the finite coefficient unit by multiplication s tensor r
maps to s times projection(r). Compose the former map with the inverse of the
latter unit isomorphism. On a constant a its value is scalars(a) tensor 1, as
required. All root tuples have empty index set, so their compatibility hypothesis
is vacuous. The construction uses no invertibility assumption and also applies
to the empty scheme. -/
theorem tateTensorQuotient_generator_zero
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    ∃ f : (realization T ell n).obj (finiteSheaf T ell n 0) ⟶ quotientLine T ell n 0,
      GeneratorCompatible T ell n 0 f := by
  let A := coefficient.{u} ell (n + 1)
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
  let g : finiteSheaf T ell n 0 ⟶
      ⟨scalarUnitFixed T ell n, scalarUnitFixed_isSheaf T ell n⟩ :=
    Functor.OplaxMonoidal.η F ≫ scalarUnitLift T ell n
  let φ := pbcAdicProjection T (datum.{u} ell) n
  let s := (SheafOfModules.scalarExtension_constraint_coherence
    (pbcAdicCompletion T (datum.{u} ell))
    ((pbcAdicRings T (datum.{u} ell)).obj (op n)) φ).some
  let e : quotientLine T ell n 0 ≅
      SheafOfModules.unit ((adicLisseForget T).obj
        ((pbcAdicRings T (datum.{u} ell)).obj (op n))) :=
    (@eqToIso (pbcModules T ((pbcAdicRings T (datum.{u} ell)).obj (op n)))
      inferInstance _ _
      ((completedAdicChangeData T φ).choose_spec.choose (integralLine T ell 0))) ≪≫
        s.unitIso
  refine ⟨realizeToUnit T ell n _ g ≫ e.inv, ?_⟩
  intro U W v a z x _hx
  simp only [one_smul, id_eq]
  change e.inv.val.app W ((realizeToUnit T ell n _ g).val.app W _) = _
  erw [realizeToUnit_generator]
  change e.inv.val.app W ((scalarUnitLift T ell n).hom.app W
    ((Functor.OplaxMonoidal.η F).hom.app W _)) = _
  simp only [finiteTateEtalePowerGenerator]
  erw [(comparison_pure_sections A T).2]
  have hl := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_sheafifyLift (ProEt.topology T)
      (scalarUnitRaw T ell n) (scalarUnitFixed_isSheaf T ell n)) W) a
  change (scalarUnitLift T ell n).hom.app W
    ((toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A))).app W a) =
        (scalars T ell n).app W a at hl
  rw [hl]
  change (eqToHom
    ((completedAdicChangeData T φ).choose_spec.choose (integralLine T ell 0)).symm).val.app W
    (s.unitIso.inv.val.app W ((scalars T ell n).app W a)) = _
  rw [s.unit_inv]
  rfl

end AlgebraicGeometry.Scheme.PurityIntegralTower
