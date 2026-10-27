/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NP, T3, V6
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.SixFunctors.FiniteExceptional
public import Sheaf.SixFunctors.CompactCoefficientComposition
public import Sheaf.Paper.PurityFiniteExceptionalComposition
public import Sheaf.Paper.FiniteReductionRootCharts
import all Sheaf.Paper.ExceptionalCoefficientComparison
import Sheaf.CategoryTheory.Adjunction.CoefficientExchange
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek

/-!
# Finite coefficient reduction preserves the canonical exceptional mates

Source: main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
thm-pur-finite-reduction-of-purity.proof.md, Steps 2 and 4
(blueprint: lem-pur-finite-adjoint-mate-compatibility).

The first three clauses are written in the canonical etale-origin coordinates of
`def-pur-co-smoothness`. Every bounded constructible pro-etale object has such an
origin. Comparison is fully faithful there, preserves the Tor interval, and identifies
pullback, tensor, compact supports and the constructible exceptional adjunction.
Consequently these are equations of the specified pro-etale maps for every input,
independently of its origin witness. The last clause uses the recorded intrinsic
pro-etale finite-Tor subcategories and their normalized adjunction directly.

## Main statements

* `PurityFiniteSetting.finite_adjoint_mate_tensor`: the canonical tensor-map square.
* `PurityFiniteSetting.finite_adjoint_mate_composition`: the exceptional compositor square.
* `PurityFiniteSetting.finite_adjoint_mate_baseChange`: every Cartesian extraordinary square.
* `FiniteExceptional.finite_adjoint_mate_transpose`: the transpose of every morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor Etale.upperStar Etale.lowerStar

section CompositionMate
universe v w
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type w}
  [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
  [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]
  {Lf : C₀ ⥤ C₁} {Rf : C₁ ⥤ C₀} {Lg : C₁ ⥤ C₂} {Rg : C₂ ⥤ C₁}
  {Lh : C₀ ⥤ C₂} {Rh : C₂ ⥤ C₀}
  {Lf' : D₀ ⥤ D₁} {Rf' : D₁ ⥤ D₀} {Lg' : D₁ ⥤ D₂} {Rg' : D₂ ⥤ D₁}
  {Lh' : D₀ ⥤ D₂} {Rh' : D₂ ⥤ D₀}
  {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂}

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A coherent left-adjoint coefficient composition square induces the right-mate square.
The composite mate has the composite counit equation by naturality of the first counit.
Apply pointwise coefficient exchange to the two adjunction compositors and remove the
identity horizontal functors. Source: reduction proof Step 2, compatibility with
exceptional composition (blueprint: lem-pur-finite-adjoint-mate-compatibility). -/
private theorem finiteMate_composition
    (af : Lf ⊣ Rf) (ag : Lg ⊣ Rg) (ah : Lh ⊣ Rh)
    (bf : Lf' ⊣ Rf') (bg : Lg' ⊣ Rg') (bh : Lh' ⊣ Rh')
    (p : Lf ⋙ Lg ≅ Lh) (p' : Lf' ⋙ Lg' ≅ Lh')
    (qf : Lf ⋙ Q₁ ≅ Q₀ ⋙ Lf') (qg : Lg ⋙ Q₂ ≅ Q₁ ⋙ Lg')
    (qh : Lh ⋙ Q₂ ≅ Q₀ ⋙ Lh')
    (K : C₂)
    (δf : Q₀.obj (Rf.obj (Rg.obj K)) ⟶ Rf'.obj (Q₁.obj (Rg.obj K)))
    (δg : Q₁.obj (Rg.obj K) ⟶ Rg'.obj (Q₂.obj K))
    (δh : Q₀.obj (Rh.obj K) ⟶ Rh'.obj (Q₂.obj K))
    (hδf : Lf'.map δf ≫ bf.counit.app (Q₁.obj (Rg.obj K)) =
      qf.inv.app (Rf.obj (Rg.obj K)) ≫ Q₁.map (af.counit.app (Rg.obj K)))
    (hδg : Lg'.map δg ≫ bg.counit.app (Q₂.obj K) =
      qg.inv.app (Rg.obj K) ≫ Q₂.map (ag.counit.app K))
    (hδh : Lh'.map δh ≫ bh.counit.app (Q₂.obj K) =
      qh.inv.app (Rh.obj K) ≫ Q₂.map (ah.counit.app K))
    (hc : Q₂.map (p.hom.app (Rh.obj K)) ≫ qh.hom.app (Rh.obj K) =
      qg.hom.app (Lf.obj (Rh.obj K)) ≫ Lg'.map (qf.hom.app (Rh.obj K)) ≫
        p'.hom.app (Q₀.obj (Rh.obj K))) :
    Q₀.map ((conjugateIsoEquiv ah (af.comp ag) p).hom.app K) ≫
        δf ≫ Rf'.map (δg) =
      δh ≫ (conjugateIsoEquiv bh (bf.comp bg) p').hom.app (Q₂.obj K) := by
  let qp : (Lf ⋙ Lg) ⋙ Q₂ ≅ Q₀ ⋙ (Lf' ⋙ Lg') :=
    Functor.associator Lf Lg Q₂ ≪≫ Functor.isoWhiskerLeft Lf qg ≪≫
      (Functor.associator Lf Q₁ Lg').symm ≪≫ Functor.isoWhiskerRight qf Lg' ≪≫
        Functor.associator Q₀ Lf' Lg'
  have hp :
      (Lf' ⋙ Lg').map (δf ≫ Rf'.map (δg)) ≫
        (bf.comp bg).counit.app (Q₂.obj K) =
      qp.inv.app ((Rg ⋙ Rf).obj K) ≫ Q₂.map ((af.comp ag).counit.app K) := by
    have hn := bf.counit.naturality (δg)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn
    have hn' := congrArg Lg'.map hn
    simp only [Functor.map_comp] at hn'
    simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp,
      Adjunction.comp_counit_app, Category.assoc]
    rw [reassoc_of% hn', ← Lg'.map_comp_assoc, hδf, Lg'.map_comp,
      Category.assoc, hδg]
    have hq := qg.inv.naturality (af.counit.app (Rg.obj K))
    dsimp only [Functor.comp_map, Functor.comp_obj] at hq
    simp only [qp, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    rw [reassoc_of% hq]
  have hcube : Adjunction.coefficientPullbackSquare
      (TwoSquare.mk (𝟭 C₀) Lh (Lf ⋙ Lg) (𝟭 C₂) p.hom)
      (TwoSquare.mk (𝟭 D₀) Lh' (Lf' ⋙ Lg') (𝟭 D₂) p'.hom)
      qh qp (Q₀.leftUnitor.hom ≫ Q₀.rightUnitor.inv)
      (Q₂.leftUnitor.hom ≫ Q₂.rightUnitor.inv) (Rh.obj K) := by
    simpa only [Adjunction.coefficientPullbackSquare, qp, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.id_map, Functor.comp_map, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id,
      Functor.comp_obj, Functor.id_obj, TwoSquare.mk, Category.assoc] using hc
  have hh := Adjunction.coefficient_exchange_of_counit_at ah (af.comp ag) bh (bf.comp bg)
    (TwoSquare.mk (𝟭 C₀) Lh (Lf ⋙ Lg) (𝟭 C₂) p.hom)
    (TwoSquare.mk (𝟭 D₀) Lh' (Lf' ⋙ Lg') (𝟭 D₂) p'.hom) K
    ((conjugateEquiv ah (af.comp ag) p.hom).app K)
    ((conjugateEquiv bh (bf.comp bg) p'.hom).app (Q₂.obj K))
    (conjugateEquiv_counit ah (af.comp ag) p.hom K)
    (conjugateEquiv_counit bh (bf.comp bg) p'.hom (Q₂.obj K))
    qh qp (Q₀.leftUnitor.hom ≫ Q₀.rightUnitor.inv)
    (Q₂.leftUnitor.hom ≫ Q₂.rightUnitor.inv) (δh)
    (δf ≫ Rf'.map (δg)) hδh hp hcube
  have hi₀ : (Q₀.leftUnitor.hom ≫ Q₀.rightUnitor.inv).app (Rh.obj K) =
      𝟙 (Q₀.obj (Rh.obj K)) := by simp
  have hi₂ : (Q₂.leftUnitor.hom ≫ Q₂.rightUnitor.inv).app K = 𝟙 (Q₂.obj K) := by simp
  rw [hi₀, hi₂, (Rg' ⋙ Rf').map_id (Q₂.obj K), Functor.id_map] at hh
  have he := Category.id_comp
    (δh ≫ (conjugateEquiv bh (bf.comp bg) p'.hom).app (Q₂.obj K))
  have he' := Category.comp_id
    (Q₀.map ((conjugateEquiv ah (af.comp ag) p.hom).app K) ≫ (δf ≫ Rf'.map δg))
  have hh' := he.symm.trans (hh.trans ((Category.assoc _ _ _).symm.trans he'))
  simpa only [conjugateIsoEquiv_apply_hom] using hh'.symm

end CompositionMate

namespace WeilConjectures

namespace PurityFiniteSetting

/-- Finite-type schemes over the standing field are Noetherian.
Source: Stacks 01T6, using the quasi-compact structure morphism. -/
private theorem finiteMate_noetherian (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))] : IsNoetherian T := by
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of P.field.k))
  have : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of P.field.k))
  exact ⟨⟩

variable (P : PurityFiniteSetting.{u}) (m : ℕ+) (hmn : (m : ℕ) ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The tensor-map square, with its actual scalar, pullback, tensor and coefficient-unit
identifications. TensorCompatibility uses the source order f^*K tensor omega and the
canonical counit/projection mate, as in clause 2 of def-pur-co-smoothness.
Source: reduction proof Step 2, tensor formula
(blueprint: lem-pur-finite-adjoint-mate-compatibility). -/
def finiteAdjointMateTensorClause (K : Etale.DerivedCategoryModule P.Coefficient Y) : Prop :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  Etale.ExceptionalCoefficients.TensorCompatibility
    (RingHom.ulift.{u + 1, u + 1} (P.finiteReductionRingHom m m.property hmn)) f K

/-- The composition square, with both exceptional coefficient maps and the functorial
image of the second one. Compactifications here are the standing Nagata choices.
Source: reduction proof Step 2, exceptional composition
(blueprint: lem-pur-finite-adjoint-mate-compatibility). -/
def finiteAdjointMateCompositionClause {Z : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (g : Y ⟶ Z) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (K : Etale.DerivedCategoryModule P.Coefficient Z) : Prop :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  letI := hasCompactification_of_finiteType_over_field P.field.k Y Z g
  letI := hasCompactification_of_finiteType_over_field P.field.k X Z (f ≫ g)
  let φ := RingHom.ulift.{u + 1, u + 1} (P.finiteReductionRingHom m m.property hmn)
  (Etale.scalarExtension φ X).map ((finiteExceptionalComposition P.Coefficient f g).hom.app K) ≫
      Etale.ExceptionalCoefficients.mateMap φ f
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) g).obj K) ≫
      (Etale.rightDerivedUpperShriek
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing P.coefficients.l P.extension m))) f).map
        (Etale.ExceptionalCoefficients.mateMap φ g K) =
    Etale.ExceptionalCoefficients.mateMap φ (f ≫ g) K ≫
      (finiteExceptionalComposition
        (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension m))
        f g).hom.app ((Etale.scalarExtension φ Z).obj K)

/-- The extraordinary square for an arbitrary Cartesian square, on any input K.
The coefficient-object comparison is its component at the coefficient unit, followed
by the canonical pullback-unit isomorphism, exactly as in def-pur-co-smoothness.
Source: reduction proof Step 2, inverse-exchange counit mate
(blueprint: lem-pur-finite-adjoint-mate-compatibility). -/
def finiteAdjointMateBaseChangeClause {X' Y' : Scheme.{u}}
    [X'.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    (u' : X' ⟶ X) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    (sq : IsPullback u' f' f v) (K : Etale.DerivedCategoryModule P.Coefficient Y) : Prop :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  letI : IsSeparated f' :=
    MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  letI : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  letI : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  letI := hasCompactification_of_finiteType_over_field P.field.k X' Y' f'
  let φ := RingHom.ulift.{u + 1, u + 1} (P.finiteReductionRingHom m m.property hmn)
  (Etale.scalarExtension φ X').map
      ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app K) ≫
      Etale.ExceptionalCoefficients.mateMap φ f'
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.obj K) ≫
      (Etale.rightDerivedUpperShriek
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing P.coefficients.l P.extension m))) f').map
        ((Etale.scalarPullbackIso φ v).inv.app K) =
    (Etale.scalarPullbackIso φ u').inv.app
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).obj K) ≫
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing P.coefficients.l P.extension m))) u').leftDerivedFunctor.map
        (Etale.ExceptionalCoefficients.mateMap φ f K) ≫
      (Etale.rightDerivedUpperShriekBaseChangeMap
        (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension m))
        sq).app ((Etale.scalarExtension φ Y).obj K)

variable [Xsep : IsSeparated (X ↘ Spec (.of P.field.k))]
variable [Ysep : IsSeparated (Y ↘ Spec (.of P.field.k))]
variable [fbase : f.IsOver (Spec (.of P.field.k))]

include Xsep Ysep fbase

include P m hmn in
/-- Finite reduction preserves theta, including the coefficient-unit identification.
Source: reduction proof Step 2 (blueprint: lem-pur-finite-adjoint-mate-compatibility).
Proof: finite-type schemes over the standing field are Noetherian. Specialize the
already proved generic finite-ring tensorCompatibility calculation to the actual
quotient ring map. It identifies the ordered projection counit transpose, including
the canonical tensor domain and coefficient-unit map. The smooth and constructible
hypotheses are retained, although this equation holds on every input. -/
theorem finite_adjoint_mate_tensor (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (hK : Etale.DerivedCategory.boundedConstructibleFiniteTor P.Coefficient Y K) :
    P.finiteAdjointMateTensorClause m hmn f K := by
  have _ := Xsep
  have _ := Ysep
  have _ := fbase
  have := finiteMate_noetherian P X
  have := finiteMate_noetherian P Y
  have := hasCompactification_of_finiteType_over_field P.field.k X Y f
  have _ := hK
  exact Etale.ExceptionalCoefficients.tensorCompatibility
    (RingHom.ulift.{u + 1, u + 1} (P.finiteReductionRingHom m m.property hmn)) f K

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] Etale.rightDerivedUpperShriekAdjunction
  Etale.rightDerivedUpperShriek
  Etale.unboundedEtaleLowerShriekCompIso in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Reduction preserves c_{g,f}, the canonical comparison for exceptional composition.
Source: reduction proof Step 2 (blueprint: lem-pur-finite-adjoint-mate-compatibility).
Proof: smooth exceptional pullback preserves finite Tor amplitude, so its image
and scalar extension are bounded below. Apply etaleCompactScalarComposition at that
image. The coefficient mates satisfy mateMap_counit; naturality of the first counit
computes the counit equation for their composite. The private finiteMate_composition
calculation then applies pointwise coefficient exchange to the compact-support
compositors. Their adjunction conjugates are exactly finiteExceptionalComposition,
which gives the stated exceptional composition square. -/
theorem finite_adjoint_mate_composition {Z : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (K : Etale.DerivedCategoryModule P.Coefficient Z)
    (hK : Etale.DerivedCategory.boundedConstructibleFiniteTor P.Coefficient Z K) :
    P.finiteAdjointMateCompositionClause m hmn f g K := by
  have _ := hK
  have _ := Xsep
  have _ := Ysep
  have _ := fbase
  have : IsNoetherian X := finiteMate_noetherian P X
  have : IsNoetherian Y := finiteMate_noetherian P Y
  have : IsNoetherian Z := finiteMate_noetherian P Z
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  let := hasCompactification_of_finiteType_over_field P.field.k Y Z g
  let := hasCompactification_of_finiteType_over_field P.field.k X Z (f ≫ g)
  let φ := RingHom.ulift.{u + 1, u + 1} (P.finiteReductionRingHom m m.property hmn)
  let B := (P.finiteReductionSetting m m.property).Coefficient
  have : HasInvertibleExponent P.Coefficient Z :=
    P.finiteComparedInvertibleExponent (Z ↘ Spec (.of P.field.k))
  obtain ⟨a₀, b₀, ht⟩ := hK.2
  have : SmoothOfRelativeDimension (d + e) (f ≫ g) := inferInstance
  have hG :=
    Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
      P.Coefficient (f ≫ g) (d + e) a₀ b₀
      ⟨⟨hK.1, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht⟩, ht⟩
  have hplus := hG.1.1.1.1
  have hSplus := Etale.ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ X _
    ⟨_, _, hG.2⟩
  have hc := Etale.etaleCompactScalarComposition φ f g
    ⟨_, hplus⟩ ⟨⟨_, hSplus⟩, rfl⟩
  rw [← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ f,
    ← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ g,
    ← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ (f ≫ g)] at hc
  have hh := finiteMate_composition
    (Lf := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f)
    (Lg := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) g)
    (Lh := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) (f ≫ g))
    (Lf' := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
    (Lg' := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) g)
    (Lh' := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g))
    (Rf := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f)
    (Rg := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) g)
    (Rh := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) (f ≫ g))
    (Rf' := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} B) f)
    (Rg' := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} B) g)
    (Rh' := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} B) (f ≫ g))
    (Q₀ := Etale.scalarExtension φ X) (Q₁ := Etale.scalarExtension φ Y)
    (Q₂ := Etale.scalarExtension φ Z)
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) f)
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) g)
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) (f ≫ g))
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f)
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) g)
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) (f ≫ g))
    (Etale.unboundedEtaleLowerShriekCompIso P.Coefficient f g)
    (Etale.unboundedEtaleLowerShriekCompIso B f g)
    (Etale.ExceptionalCoefficients.chosenCompactSupportIso φ f)
    (Etale.ExceptionalCoefficients.chosenCompactSupportIso φ g)
    (Etale.ExceptionalCoefficients.chosenCompactSupportIso φ (f ≫ g)) K
    (Etale.ExceptionalCoefficients.mateMap φ f
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) g).obj K))
    (Etale.ExceptionalCoefficients.mateMap φ g K)
    (Etale.ExceptionalCoefficients.mateMap φ (f ≫ g) K)
    (Etale.ExceptionalCoefficients.mateMap_counit φ f _)
    (Etale.ExceptionalCoefficients.mateMap_counit φ g K)
    (Etale.ExceptionalCoefficients.mateMap_counit φ (f ≫ g) K) hc
  change _ = _
  dsimp only [finiteExceptionalComposition, B, φ, Coefficient, Ring,
    coefficientCommRing, ringCommRing,
    finiteReductionSetting] at hh ⊢
  exact hh

/-- Reduction preserves the extraordinary comparison for every Cartesian square.
At the coefficient unit these are precisely the dualizing-object comparisons.
Source: reduction proof Step 2 (blueprint: lem-pur-finite-adjoint-mate-compatibility).
Proof: smooth exceptional pullback preserves finite Tor amplitude, so its image
and scalar extension are bounded below. The proved compact_scalar_exchange_left
calculation supplies the compact-support coefficient square for the given Cartesian
square. Invert its four isomorphisms and cancel the two vertical scalar comparisons.
This gives the inverse-exchange coefficient cube at the exceptional image of K.
The specified extraordinary maps are mates of inverse exchange, and mateMap has its
specified counit equation. coefficient_exchange_of_counit_at gives precisely the
displayed extraordinary square. No flatness or invertibility of v is assumed. -/
theorem finite_adjoint_mate_baseChange {X' Y' : Scheme.{u}}
    [X'.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    (u' : X' ⟶ X) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    [u'.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (sq : IsPullback u' f' f v) (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (hK : Etale.DerivedCategory.boundedConstructibleFiniteTor P.Coefficient Y K) :
    P.finiteAdjointMateBaseChangeClause m hmn f u' f' v sq K := by
  have _ := Xsep
  have _ := Ysep
  have _ := fbase
  have := finiteMate_noetherian P X
  have := finiteMate_noetherian P Y
  have := finiteMate_noetherian P X'
  have := finiteMate_noetherian P Y'
  have := hasCompactification_of_finiteType_over_field P.field.k X Y f
  have : IsSeparated f' :=
    MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  have : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  have : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have := hasCompactification_of_finiteType_over_field P.field.k X' Y' f'
  have : HasInvertibleExponent P.Coefficient Y :=
    P.finiteComparedInvertibleExponent (Y ↘ Spec (.of P.field.k))
  let φ := RingHom.ulift.{u + 1, u + 1} (P.finiteReductionRingHom m m.property hmn)
  let B := (P.finiteReductionSetting m m.property).Coefficient
  obtain ⟨a₀, b₀, ht⟩ := hK.2
  have hG :=
    Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
    P.Coefficient f d a₀ b₀
    ⟨⟨hK.1, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht⟩, ht⟩
  have hM := hG.1.1.1.1
  have hSM := Etale.ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ X _
    ⟨_, _, hG.2⟩
  let := Etale.isIso_rightDerivedLowerShriekBaseChangeMap P.Coefficient sq
  let := Etale.isIso_rightDerivedLowerShriekBaseChangeMap B sq
  let eA := asIso (Etale.rightDerivedLowerShriekBaseChangeMap P.Coefficient sq)
  let eB := asIso (Etale.rightDerivedLowerShriekBaseChangeMap B sq)
  let a := Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) f
  let b := Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) f'
  let ae := Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f
  let be := Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f'
  let αU := Etale.ExceptionalCoefficients.chosenCompactSupportIso φ f
  let αV := Etale.ExceptionalCoefficients.chosenCompactSupportIso φ f'
  have hfwd := Etale.ExceptionalCoefficients.compact_scalar_exchange_left φ sq
    ⟨_, hM⟩ ⟨⟨_, hSM⟩, rfl⟩
  rw [← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ f,
    ← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ f'] at hfwd
  have hcube : Adjunction.coefficientPullbackSquare eA.inv eB.inv αU αV
      (Etale.scalarPullbackIso φ u').inv (Etale.scalarPullbackIso φ v).inv
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).obj K) := by
    unfold Adjunction.coefficientPullbackSquare
    change (Etale.upperStar (ModuleCat.{u + 1} B) v).leftDerivedFunctor.map
        (αU.hom.app _) ≫ eB.hom.app _ ≫
          (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
            ((Etale.scalarPullbackIso φ u').hom.app _) =
      (Etale.scalarPullbackIso φ v).hom.app _ ≫
        (Etale.scalarExtension φ Y').map (eA.hom.app _) ≫ αV.hom.app _ at hfwd
    have hi := IsIso.inv_eq_inv.mpr hfwd
    have hh := congrArg (fun z ↦ αV.hom.app
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) u').leftDerivedFunctor.obj
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).obj K)) ≫
      z ≫ (Etale.upperStar (ModuleCat.{u + 1} B) v).leftDerivedFunctor.map
        (αU.hom.app ((Etale.rightDerivedUpperShriek
          (ModuleCat.{u + 1} P.Coefficient) f).obj K))) hi
    simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
      Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app_assoc, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id] using hh.symm
  have hh := Adjunction.coefficient_exchange_of_counit_at a b ae be eA.inv eB.inv K
    ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app K)
    ((Etale.rightDerivedUpperShriekBaseChangeMap B sq).app
      ((Etale.scalarExtension φ Y).obj K))
    (mateEquiv_counit a b eA.inv K)
    (mateEquiv_counit ae be eB.inv ((Etale.scalarExtension φ Y).obj K))
    αU αV (Etale.scalarPullbackIso φ u').inv (Etale.scalarPullbackIso φ v).inv
    (Etale.ExceptionalCoefficients.mateMap φ f K)
    (Etale.ExceptionalCoefficients.mateMap φ f'
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.obj K))
    (Etale.ExceptionalCoefficients.mateMap_counit φ f K)
    (Etale.ExceptionalCoefficients.mateMap_counit φ f' _) hcube
  exact hh.symm

end PurityFiniteSetting

namespace FiniteExceptional

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
variable {T U : Scheme.{u}}
  [T.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
  [IsSeparated (T ↘ Spec (.of D.k))] [IsSeparated (U ↘ Spec (.of D.k))]
variable (h : T ⟶ U) [h.IsOver (Spec (.of D.k))]
  [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] (c : Compactification h)

/-- Reduction identifies the actual adjoint transpose for every separated finite-type h.
The indices r and s are predecessors: the coefficient exponents are r+1 and s+1.
Source: reduction proof Step 2, unit calculation for an arbitrary morphism a
(blueprint: lem-pur-finite-adjoint-mate-compatibility).
Proof: (1) expand the A-transpose as eta followed by G_A(a);
(2) naturality of b at a moves Q(G_A(a)) across b;
(3) the unit normalization of lem-coef-finite-exceptional replaces Q(eta_A)
followed by b and G_B(q) with eta_B; (4) compose with G_B(q inverse) and
G_B(Q(a)), and use functoriality. The result is the B-transpose of
q inverse followed by Q(a). This is precisely def-weil-pbc-adjunction-mate
specialized to a morphism. The domain is the recorded intrinsic small-pro-etale
finite-Tor constructible subcategory, without a smoothness hypothesis on h. -/
theorem finite_adjoint_mate_transpose {r s : ℕ} (hsr : s ≤ r)
    (M : (domain l E T r).FullSubcategory)
    (L : (domain l E U r).FullSubcategory)
    (a : (F l E D hl h c r).obj M ⟶ L) :
    (Q l E T hsr).map
        ((adjunction l E D hl h c r).unit.app M ≫ (G l E D hl h c r).map a) ≫
        (b l E D hl h c hsr).app L =
      (adjunction l E D hl h c s).unit.app ((Q l E T hsr).obj M) ≫
        (G l E D hl h c s).map
          ((q l E D hl h c hsr).inv.app M ≫ (Q l E U hsr).map a) := by
  rw [Functor.map_comp, Category.assoc]
  rw [show (Q l E T hsr).map ((G l E D hl h c r).map a) ≫
      (b l E D hl h c hsr).app L =
      (b l E D hl h c hsr).app ((F l E D hl h c r).obj M) ≫
        (G l E D hl h c s).map ((Q l E U hsr).map a) from
    (b l E D hl h c hsr).naturality a]
  rw [← Category.assoc]
  have hu := unit_mateEquiv (adjunction l E D hl h c r)
    (adjunction l E D hl h c s) (q l E D hl h c hsr).inv M
  change (Q l E T hsr).map ((adjunction l E D hl h c r).unit.app M) ≫
      (b l E D hl h c hsr).app ((F l E D hl h c r).obj M) = _ at hu
  rw [hu, Category.assoc, ← Functor.map_comp]
  rfl

end FiniteExceptional
end WeilConjectures
