/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.CategoryTheory.Adjunction.MateSymmRestrict
public import WeilConjectures.CategoryTheory.Adjunction.MateTransposeIsIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.EtaleConstructible

/-!
# Étale base change for the extension by zero on bounded constructible complexes

For an étale morphism `f : X ⟶ Y` of separated `k`-schemes of finite type, the derived
extension by zero `D(f_!)` of `ℚ̲̄_ℓ`-modules preserves bounded constructible complexes (since `f_!`
preserves constructible sheaves,
`ProEtale.CondensedRing.isConstructibleModuleObject_weaklyEtaleLowerShriek_of_etale`), so that the
adjunction `D(f_!) ⊣ Lf^*` of the ambient derived categories restricts to bounded constructible
complexes (`ProEtale.CondensedRing.boundedConstructibleEtaleExtensionByZeroAdjunction`). On the
ambient derived categories, the extension by zero satisfies base change along any morphism
(`ProEtale.CondensedRing.isIso_mateEquiv_symm_derivedWeaklyEtaleLowerShriek`): its exchange
morphism is the iterated mate of the weakly étale base change map
(`ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

section Ambient

variable {U V U' V' : Scheme.{u}} {h : U ⟶ V} {h' : U' ⟶ V'} {πU : U' ⟶ U} {πV : V' ⟶ V}

/-- **Weakly étale base change for the extension by zero** on the ambient derived categories:
for a cartesian square with `h` and `h'` weakly étale, the exchange morphism
`πU^* ⋙ h'_! ⟶ h_! ⋙ πV^*` (the left mate of the composition isomorphism of the pullbacks) is
an isomorphism. -/
theorem isIso_mateEquiv_symm_derivedWeaklyEtaleLowerShriek (hsq : IsPullback πU h' h πV)
    [WeaklyEtale h] [WeaklyEtale h'] :
    IsIso ((mateEquiv (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction 𝐐 h)
      (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction 𝐐 h')).symm
        (pullbackSquareComparison 𝐐 hsq.flip.toCommSq).hom) := by
  have := isIso_baseChangeMap_of_weaklyEtale 𝐐 hsq.flip
  rw [baseChangeMap, Adjunction.exchangeRight_eq_mateEquiv] at this
  exact isIso_mateEquiv_symm_of_isIso_mateEquiv _ _
    (derivedUpperStarLowerStarAdjunction 𝐐 πU) (derivedUpperStarLowerStarAdjunction 𝐐 πV) _

end Ambient

section Etale

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [Etale f.left]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSeparated X.hom] [IsSeparated Y.hom] in
/-- **Extension by zero along an étale morphism preserves constructibility**: for an étale
morphism `f : X ⟶ Y` of separated `k`-schemes of finite type and a constructible sheaf `M` of
`ℚ̲̄_ℓ`-modules on `X`, the extension by zero `f_! M` is constructible. -/
theorem isConstructibleModuleObject_weaklyEtaleLowerShriek_obj
    {M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj 𝐐 X.left)}
    (hM : IsConstructibleModuleObject (condensedRingObj 𝐐 X.left) M) :
    IsConstructibleModuleObject (condensedRingObj 𝐐 Y.left)
      ((weaklyEtaleLowerShriek 𝐐 f.left).obj M) :=
  have := isNoetherian_of_locallyOfFiniteType X.hom
  have := isNoetherian_of_locallyOfFiniteType Y.hom
  isConstructibleModuleObject_weaklyEtaleLowerShriek_of_etale 𝐐 f.left hM

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSeparated X.hom] [IsSeparated Y.hom] in
/-- The derived extension by zero along an étale morphism preserves bounded constructible
complexes. -/
theorem boundedConstructible_weaklyEtaleLowerShriek_mapDerivedCategory_obj
    (K : Dᵇc(X.left)⟦𝐐⟧) :
    boundedConstructible (condensedRingObj 𝐐 Y.left)
      ((weaklyEtaleLowerShriek 𝐐 f.left).mapDerivedCategory.obj K.obj) :=
  ⟨(weaklyEtaleLowerShriek 𝐐 f.left).bounded_mapDerivedCategory_obj (X := K.obj) K.property.1,
    fun n ↦ (isConstructibleModuleObject_weaklyEtaleLowerShriek_obj ℓ f (K.property.2 n)).of_iso
      ((weaklyEtaleLowerShriek 𝐐 f.left).mapDerivedCategoryHomologyFunctorIso n |>.app K.obj)⟩

/-- The extension by zero `f_!` along an étale morphism, on bounded constructible complexes. -/
noncomputable def boundedConstructibleEtaleExtensionByZero :
    Dᵇc(X.left)⟦𝐐⟧ ⥤ Dᵇc(Y.left)⟦𝐐⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ (weaklyEtaleLowerShriek 𝐐 f.left).mapDerivedCategory)
    (boundedConstructible_weaklyEtaleLowerShriek_mapDerivedCategory_obj ℓ f)

/-- The adjunction `f_! ⊣ f^*` on bounded constructible complexes, for `f` étale: the
restriction of the adjunction `D(f_!) ⊣ Lf^*` of the ambient derived categories. -/
noncomputable def boundedConstructibleEtaleExtensionByZeroAdjunction :
    boundedConstructibleEtaleExtensionByZero ℓ f ⊣
      boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := X) f.left :=
  (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction 𝐐 f.left).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

end Etale

end AlgebraicGeometry.ProEtale.CondensedRing
