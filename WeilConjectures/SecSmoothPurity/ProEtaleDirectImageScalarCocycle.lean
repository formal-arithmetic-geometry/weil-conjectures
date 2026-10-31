/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
public import WeilConjectures.SecSmoothPurity.ReductionDirectImageComparison

import all WeilConjectures.SecSmoothPurity.OrdinaryRestrictionPullbackSquare
import all WeilConjectures.SecSmoothPurity.ProEtaleOpenScalarCocycle
import WeilConjectures.SecSmoothPurity.ScalarAssociatorConjugate
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coefficient cocycle for the ambient direct-image mate

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.proof.md, Step 4; Stacks Tags 07A7 and 0E47
(blueprint: lem-sp-proetale-direct-image-scalar-cocycle).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] directImageConstantAdjunction
  proEtaleRingDerivedAdjunction proEtaleConstantRingComparison proEtaleRingModulePullback
  completedAdicDerivedChange reductionDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  scalarExtensionFunctor_composition

/-- The inverse tensor comparison is the scalar mate of the exact restriction square. -/
private theorem scalarPullbackMate
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (q : Z ⟶ Y) :
    mateEquiv
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ))
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ))
      (TwoSquare.mk _ _ _ _ (directImageScalarPullbackIso φ q).inv) =
    TwoSquare.mk _ _ _ _ (coefficientRightSquare φ q).hom := by
  unfold directImageScalarPullbackIso proEtaleReductionPullbackIso
  change mateEquiv _ _ ((mateEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply]
  dsimp only [coefficientRightSquare, proEtaleRingRestrictionDerivedPullback,
    mapDerivedCategorySquareIso]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    TwoSquare.mk, Category.assoc]
  rfl

/-- Scalar mates carry restriction composition to the specified pullback composition. -/
private theorem scalarPullbackCocycle
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {Z Y : Scheme.{u}} (q : Z ⟶ Y)
    (M : proEtaleDerivedCategory Y A) :
    (proEtaleConstantRingDerivedPullback C q).map
        ((scalarExtensionFunctor_composition φ ψ Y).hom.app M) ≫
      (directImageScalarPullbackIso (ψ.comp φ) q).hom.app M =
    (directImageScalarPullbackIso ψ q).hom.app ((scalarExtensionFunctor φ Y).obj M) ≫
      (scalarExtensionFunctor ψ Z).map ((directImageScalarPullbackIso φ q).hom.app M) ≫
      (scalarExtensionFunctor_composition φ ψ Z).hom.app
        ((proEtaleConstantRingDerivedPullback A q).obj M) := by
  let a := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ)
  let b := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ)
  let c := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Y) ψ)
  let d := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) ψ)
  let e := proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := Y) (ψ.comp φ))
  let f := proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := Z) (ψ.comp φ))
  let w := (TwoSquare.mk _ _ _ _ (directImageScalarPullbackIso φ q).inv).vComp
    (TwoSquare.mk _ _ _ _ (directImageScalarPullbackIso ψ q).inv)
  have hw : w.whiskerRight (scalarExtensionFunctor_composition φ ψ Z).inv =
      (TwoSquare.mk _ _ _ _ (directImageScalarPullbackIso (ψ.comp φ) q).inv).whiskerLeft
        (scalarExtensionFunctor_composition φ ψ Y).inv := by
    apply mateSquare (a.comp c) e (b.comp d) f
    rw [mateEquiv_hcomp, scalarPullbackMate, scalarPullbackMate, scalarPullbackMate,
      scalarAssociatorConjugate, scalarAssociatorConjugate]
    ext N : 1
    simpa only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_hom_app,
      associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc,
      TwoSquare.mk, TwoSquare.natTrans]
      using derivedCoefficientComp φ ψ q N
  let e₁ := isoWhiskerRight (scalarExtensionFunctor_composition φ ψ Y)
      (proEtaleConstantRingDerivedPullback C q) ≪≫
    directImageScalarPullbackIso (ψ.comp φ) q
  let e₂ := isoWhiskerLeft (scalarExtensionFunctor φ Y) (directImageScalarPullbackIso ψ q) ≪≫
    isoWhiskerRight (directImageScalarPullbackIso φ q) (scalarExtensionFunctor ψ Z) ≪≫
    isoWhiskerLeft (proEtaleConstantRingDerivedPullback A q)
      (scalarExtensionFunctor_composition φ ψ Z)
  have he : e₁ = e₂ := by
    apply Iso.ext_inv
    ext N
    simpa only [e₁, e₂, w, Iso.trans_inv, isoWhiskerLeft_inv, isoWhiskerRight_inv,
      TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
      NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_hom_app,
      associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc,
      TwoSquare.mk, TwoSquare.natTrans, scalarExtensionFunctor]
      using (congr_app hw N).symm
  simpa only [e₁, e₂, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Category.assoc]
    using congrArg (fun t ↦ t.hom.app M) he

/-- Counit transposition carries a pullback coefficient cocycle to its direct-image cocycle. -/
private theorem scalarMateCocycle
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {L₁ : A ⥤ D} {R₁ : D ⥤ A} {L₂ : B ⥤ E} {R₂ : E ⥤ B}
    {L₃ : C ⥤ F} {R₃ : F ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃)
    {S : A ⥤ B} {s : D ⥤ E} {T : B ⥤ C} {t : E ⥤ F}
    {U : A ⥤ C} {v : D ⥤ F}
    (l₁ : S ⋙ L₂ ⟶ L₁ ⋙ s) (l₂ : T ⋙ L₃ ⟶ L₂ ⋙ t)
    (l₃ : U ⋙ L₃ ⟶ L₁ ⋙ v) (α : S ⋙ T ⟶ U) (β : s ⋙ t ⟶ v)
    (hc : ∀ K, L₃.map (α.app K) ≫ l₃.app K =
      l₂.app (S.obj K) ≫ t.map (l₁.app K) ≫ β.app (L₁.obj K)) (M : D) :
    α.app (R₁.obj M) ≫ (mateEquiv a c (TwoSquare.mk _ _ _ _ l₃)).natTrans.app M =
      T.map ((mateEquiv a b (TwoSquare.mk _ _ _ _ l₁)).natTrans.app M) ≫
        (mateEquiv b c (TwoSquare.mk _ _ _ _ l₂)).natTrans.app (s.obj M) ≫ R₃.map (β.app M) := by
  dsimp only [TwoSquare.natTrans]
  apply (c.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [mateEquiv_counit]
  rw [show L₃.map (R₃.map (β.app M)) ≫ c.counit.app _ =
    c.counit.app _ ≫ β.app M from c.counit.naturality _]
  rw [reassoc_of% (mateEquiv_counit b c (TwoSquare.mk _ _ _ _ l₂) _)]
  have hn := l₂.naturality ((mateEquiv a b (TwoSquare.mk _ _ _ _ l₁)).natTrans.app M)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← t.map_comp_assoc, mateEquiv_counit, t.map_comp]
  have ht := β.naturality (a.counit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at ht
  simp only [Category.assoc, TwoSquare.mk]
  rw [ht]
  rw [← reassoc_of% (hc (R₁.obj M))]

/-- The specified counit mates commute with successive scalar extension, naturally in E.
Source: blueprint direct-image proof Step 4; Stacks Tags 07A7 and 0E47
(blueprint: lem-sp-proetale-direct-image-scalar-cocycle).

Proof:
1. Use the coefficient-composition calculation for exact restriction/pullback squares
from lem-sp-proetale-open-scalar-cocycle. Its private derivedCoefficientComp is stated
for every scheme morphism: its proof is the identity-on-sections restriction calculation,
descended by exact localization. It has no open-immersion hypothesis.
2. By definition, the inverse of directImageScalarPullbackIso is the inverse scalar mate
of precisely that restriction square. The mate-pasting identities and
lem-sp-scalar-associator-conjugate identify the two inverse pullback pastings.
Equality of inverses gives the forward pullback cocycle for the prescribed associators.
3. Transpose both direct-image composites through the C-coefficient geometric adjunction.
The mate-counit equation, naturality of the C counit, naturality of the second pullback
comparison, and functoriality reduce both transposes to the pullback cocycle followed
by scalar extension of the A counit. Naturality of the scalar associator identifies
the final factors. Injectivity of the adjunction bijection gives the displayed equation.
4. Every comparison is a natural transformation on the ordinary unbounded categories.
The argument imposes no boundedness, properness, flatness or Tor-dimension condition. -/
theorem proEtaleDirectImageScalarCocycle
    (ℓ : ℕ) [Fact ℓ.Prime]
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (_hA : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)
    (_hB : ∃ n : ℕ, ∀ b : B, (ℓ ^ n) • b = 0)
    (_hC : ∃ n : ℕ, ∀ c : C, (ℓ ^ n) • c = 0)
    (φ : A →+* B) (ψ : B →+* C)
    {Z Y : Scheme.{u}} (q : Z ⟶ Y) (E : Scheme.proEtaleDerivedCategory Z A) :
    (scalarExtensionFunctor_composition φ ψ Y).hom.app
        ((directImageConstantPush A q).obj E) ≫
      (directImageScalarComparison (ψ.comp φ) q).app E =
    (scalarExtensionFunctor ψ Y).map ((directImageScalarComparison φ q).app E) ≫
      (directImageScalarComparison ψ q).app ((scalarExtensionFunctor φ Z).obj E) ≫
      (directImageConstantPush C q).map
        ((scalarExtensionFunctor_composition φ ψ Z).hom.app E) := by
  exact scalarMateCocycle
    (directImageConstantAdjunction A q) (directImageConstantAdjunction B q)
    (directImageConstantAdjunction C q)
    (directImageScalarPullbackIso φ q).hom (directImageScalarPullbackIso ψ q).hom
    (directImageScalarPullbackIso (ψ.comp φ) q).hom
    (scalarExtensionFunctor_composition φ ψ Y).hom
    (scalarExtensionFunctor_composition φ ψ Z).hom
    (scalarPullbackCocycle φ ψ q) E

end AlgebraicGeometry.ProEtale
