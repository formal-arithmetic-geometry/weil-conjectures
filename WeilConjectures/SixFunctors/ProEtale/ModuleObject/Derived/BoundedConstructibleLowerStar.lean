/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissage
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!

# The derived pushforward and the derived lower shriek on bounded constructible complexes

This file continues `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
(same setting, notation and namespaces) with the functors that need Deligne's finiteness theorem
for `Rf_*`, for each of the three `ℓ`-adic coefficient rings `ℚ̲̄_ℓ`, `E̲` and `𝒪̲_E`:

* `boundedConstructible_rightDerivedLowerStar_obj`: `Rf_*` preserves bounded constructible
  complexes;
* `boundedConstructibleLowerStar`, `boundedConstructibleLowerStarCompatibility`: the restriction
  of `R((f)_*⟦Λ⟧)` to `Dᵇc(-)⟦Λ⟧`;
* the adjunction `Lf^* ⊣ Rf_*` (`boundedConstructibleUpperStarLowerStarAdjunction`) and the
  composition isomorphism `boundedConstructibleLowerStarComp`;
* the derived lower shriek `Rf_!^c := i_! ⋙ Rp_*` for a compactification `c`
  (`boundedConstructibleLowerShriekOfCompactification`) and `Rf_!` for the compactification
  `compactificationOverField f` (`boundedConstructibleLowerShriek`), with their compatibilities
  with the derived lower shrieks on the ambient derived categories.
* the monoidal closed structure on `Dᵇc(X)⟦Λ⟧`: `isMonoidalClosed_boundedConstructible`
  (`Dᵇc(X)⟦Λ⟧` is stable under `RHom(-, -)`, by noetherian induction from the lisse case,
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom`, using
  `boundedConstructible_rightDerivedLowerStar_obj` for open immersions), `boundedConstructibleHom`,
  `boundedConstructibleHomObjCompatibility` and the tensor-hom adjunctions
  `boundedConstructibleTensorHomAdjunction₂`, `boundedConstructibleTensorHomAdjunction`.

## Proof of the finiteness theorem

By dévissage (`AlgebraicGeometry.ProEtale.prop_of_boundedConstructibleModule`) it suffices that
`Rf_*` carries a constructible sheaf `F` in degree `0` to a bounded constructible complex: it lies
in degrees `≥ 0`, it is bounded above
(`WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound`), and its cohomology
sheaves are constructible
(`WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible`).

## Why a separate file

These declarations were stated in `BoundedConstructible`, with the finiteness theorem `sorry`ed.
Its proof cannot be given there: the finiteness of the direct image of a constructible sheaf goes
through the comparison of `𝒪̲_E`-modules with `E̲`-modules, which imports
`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`, and that file imports
`BoundedConstructible`. The declarations are therefore here, after
`EllAdicRationalization` and the finiteness results, with the same names, namespaces and
statements.

-/

-- The `privateModule` linter alone takes about 20 s on `BoundedConstructible`.
set_option linter.privateModule false

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The pushforward -/

section Devissage

variable {X Y : Over (Spec (.of k))} (f : X ⟶ Y)

omit [Fact (ringChar k).Prime] in
/-- Dévissage for `Rf_*`: the derived pushforward preserves bounded constructible complexes as
soon as the bounded constructible complexes on `Y` form a triangulated subcategory and the direct
image of every constructible sheaf in degree `0` is bounded above with constructible cohomology
sheaves. -/
private lemma boundedConstructible_rightDerivedLowerStar_obj_of_single
    (htri : (boundedConstructible (condensedRingObj Λ Y.left)).IsTriangulated)
    (hb : ∀ F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left),
      IsConstructibleModuleObject (condensedRingObj Λ X.left) F →
      ∃ b : ℤ, ((R((f.left)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b)
    (hc : ∀ F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left),
      IsConstructibleModuleObject (condensedRingObj Λ X.left) F →
      ∀ q : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Y.left)
        ((DerivedCategory.homologyFunctor _ q).obj
          ((R((f.left)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj F))))
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))}
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) :
    boundedConstructible (condensedRingObj Λ Y.left) ((R((f.left)_*⟦Λ⟧)).obj K) := by
  let P := boundedConstructible (condensedRingObj Λ Y.left)
  have : P.IsTriangulated := htri
  apply prop_of_boundedConstructibleModule
    (P.inverseImage R((f.left)_*⟦Λ⟧)) ?_ hK
  intro F hF
  obtain ⟨b, hb⟩ := hb F hF
  exact ⟨⟨⟨0, ((f.left)_*⟦Λ⟧).isGE_rightDerivedFunctor_obj_singleFunctor F⟩,
    ⟨b, hb⟩⟩, hc F hF⟩

end Devissage

section LowerStar

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

omit [Fact (ringChar k).Prime] in
/-- **Deligne's finiteness theorem** for `Rf_*` (blueprint `proposition-six-operations-dctf--5`;
part of blueprint `sk-def-sfb-dc-restricted-functors`): for `ℓ` invertible in `k`, the
derived pushforward along a morphism of separated `k`-schemes of finite type carries bounded
constructible complexes of `ℚ̄_ℓ`-sheaves to bounded constructible complexes (SGA 4½ [Th. finitude]
for torsion coefficients; Bhatt–Scholze, Section 6.8, for `ℚ̲̄_ℓ`). It is false for a general
condensed ring: for the constant discrete ring `𝔽_p` and the affine line over an algebraically
closed field of characteristic `p`, Artin–Schreier gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`, which
is infinite. -/
lemma boundedConstructible_rightDerivedLowerStar_obj_of_ringChar_ne
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)
      ((R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K.obj) := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  exact boundedConstructible_rightDerivedLowerStar_obj_of_single _ f inferInstance
    (finiteTypeDirectImage_single_boundedAbove ℓ f)
    (finiteTypeDirectImage_single_constructible ℓ f) K.property

set_option linter.unusedSectionVars false in
/-- **Deligne's finiteness theorem** for `Rf_*` over a field of positive characteristic `≠ ℓ`
(see `boundedConstructible_rightDerivedLowerStar_obj_of_ringChar_ne`). -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)
      ((R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K.obj) :=
  boundedConstructible_rightDerivedLowerStar_obj_of_ringChar_ne ℓ f K

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible
complexes: the restriction of `R((f)_*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable def boundedConstructibleLowerStar :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K

/-- The restricted derived pushforward is compatible with the inclusions (`ℚ̄_ℓ`-coefficient). -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes (`ℚ̄_ℓ`-coefficient):
the restriction of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully
faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⊣
      boundedConstructibleLowerStar ℓ f :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ f).symm

/-- The derived pullback `Lf^*` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleLowerStar` (`ℚ̄_ℓ`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).isLeftAdjoint

/-- The derived pushforward `Rf_*` on bounded constructible complexes is a right adjoint, its
left adjoint being `boundedConstructibleUpperStar` (`ℚ̄_ℓ`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ f).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).isRightAdjoint

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` on bounded constructible complexes
(`ℚ̄_ℓ`-coefficient): the conjugate of `boundedConstructibleUpperStarComp` under the adjunctions
`L(f ≫ g)^* ⊣ R(f ≫ g)_*` and `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`. -/
noncomputable def boundedConstructibleLowerStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleLowerStar ℓ g ≅
      boundedConstructibleLowerStar ℓ (f ≫ g) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ (f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).symm).symm

end LowerStar

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj


section LowerStar

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

set_option linter.unusedSectionVars false in
/-- **Deligne's finiteness theorem** for `Rf_*`: for `ℓ` invertible in `k`, the
derived pushforward along a morphism of separated `k`-schemes of finite type carries bounded
constructible complexes of `E`-sheaves to bounded constructible complexes (SGA 4½ [Th. finitude] for
torsion coefficients; Bhatt–Scholze, Section 6.8, for `E̲`). It is false for a general condensed
ring: for the constant discrete ring `𝔽_p` and the affine line over an algebraically closed field of
characteristic `p`, Artin–Schreier gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`, which is
infinite. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Y.left)
      ((R((f.left)_*⟦Profinite.continuousMapRingObj E⟧)).obj K.obj) := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  exact boundedConstructible_rightDerivedLowerStar_obj_of_single _ f inferInstance
    (ContinuousMapRingObj.finiteTypeDirectImage_single_boundedAbove ℓ f E)
    (ContinuousMapRingObj.finiteTypeDirectImage_single_constructible ℓ f E.1) K.property

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded constructible
complexes: the restriction of `R((f)_*⟦E̲⟧)`. -/
noncomputable def boundedConstructibleLowerStar :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.continuousMapRingObj E⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ E f K

/-- The restricted derived pushforward is compatible with the inclusions (`E`-coefficient). -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar ℓ E f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.continuousMapRingObj E⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes (`E`-coefficient): the
restriction of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f ⊣
      boundedConstructibleLowerStar ℓ E f :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.continuousMapRingObj E) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ E f).symm

/-- The derived pullback `Lf^*` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleLowerStar` (`E`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).isLeftAdjoint

/-- The derived pushforward `Rf_*` on bounded constructible complexes is a right adjoint, its
left adjoint being `boundedConstructibleUpperStar` (`E`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ E f).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).isRightAdjoint

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` on bounded constructible complexes
(`E`-coefficient): the conjugate of `boundedConstructibleUpperStarComp` under the adjunctions
`L(f ≫ g)^* ⊣ R(f ≫ g)_*` and `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`. -/
noncomputable def boundedConstructibleLowerStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleLowerStar ℓ E g ≅
      boundedConstructibleLowerStar ℓ E (f ≫ g) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ E (f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ E g).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f))
    (boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ f g).symm).symm

end LowerStar

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj


section LowerStar

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

set_option linter.unusedSectionVars false in
/-- **Deligne's finiteness theorem** for `Rf_*`: for `ℓ` invertible in `k`, the
derived pushforward along a morphism of separated `k`-schemes of finite type carries bounded
constructible complexes of `𝒪_E`-sheaves to bounded constructible complexes (SGA 4½ [Th. finitude]
for torsion coefficients; Bhatt–Scholze, Section 6.8, for `𝒪̲_E`). It is false for a general
condensed ring: for the constant discrete ring `𝔽_p` and the affine line over an algebraically
closed field of characteristic `p`, Artin–Schreier gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`, which
is infinite. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)
      ((R((f.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K.obj) := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  exact boundedConstructible_rightDerivedLowerStar_obj_of_single _ f inferInstance
    (PadicIntegersRingObj.finiteTypeDirectImage_single_boundedAbove ℓ f E)
    (PadicIntegersRingObj.finiteTypeDirectImage_single_constructible ℓ f E) K.property

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded constructible
complexes: the restriction of `R((f)_*⟦𝒪̲_E⟧)`. -/
noncomputable def boundedConstructibleLowerStar :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ E f K

/-- The restricted derived pushforward is compatible with the inclusions (`𝒪_E`-coefficient). -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar ℓ E f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes (`𝒪_E`-coefficient): the
restriction of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f ⊣
      boundedConstructibleLowerStar ℓ E f :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicIntegersRingObj ℓ E) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ E f).symm

/-- The derived pullback `Lf^*` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleLowerStar` (`𝒪_E`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).isLeftAdjoint

/-- The derived pushforward `Rf_*` on bounded constructible complexes is a right adjoint, its
left adjoint being `boundedConstructibleUpperStar` (`𝒪_E`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ E f).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).isRightAdjoint

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` on bounded constructible complexes
(`𝒪_E`-coefficient): the conjugate of `boundedConstructibleUpperStarComp` under the adjunctions
`L(f ≫ g)^* ⊣ R(f ≫ g)_*` and `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`. -/
noncomputable def boundedConstructibleLowerStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleLowerStar ℓ E g ≅
      boundedConstructibleLowerStar ℓ E (f ≫ g) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ E (f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ E g).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f))
    (boundedConstructibleUpperStarComp (Profinite.padicIntegersRingObj ℓ E) ℓ f g).symm).symm

end LowerStar

end PadicIntegersRingObj

/-! ### The derived lower shriek -/

section Shriek

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the
derived pushforward along the proper morphism `p`, both on bounded constructible complexes, for `i`
and `p` the morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.overI ⋙
    boundedConstructibleLowerStar ℓ c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦ℚ̲̄_ℓ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification ℓ c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility ℓ c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
        c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible
complexes: the functor `boundedConstructibleLowerShriekOfCompactification`
attached to the compactification `compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f)

/-- The defining equation of `boundedConstructibleLowerShriek` (`ℚ̄_ℓ`-coefficient). -/
lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek ℓ f =
      boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦ℚ̲̄_ℓ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ
    (compactificationOverField f)

end Shriek

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj


section Shriek

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the
derived pushforward along the proper morphism `p`, both on bounded constructible complexes, for `i`
and `p` the morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧ :=
  boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ c.overI ⋙
    boundedConstructibleLowerStar ℓ E c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦E̲⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Profinite.continuousMapRingObj E⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility ℓ E c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility (Profinite.continuousMapRingObj E)
        ℓ
        c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded constructible
complexes: the functor `boundedConstructibleLowerShriekOfCompactification`
attached to the compactification `compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f)

/-- The defining equation of `boundedConstructibleLowerShriek` (`E`-coefficient). -/
lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek ℓ E f =
      boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦E̲⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek ℓ E f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Profinite.continuousMapRingObj E⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ E
    (compactificationOverField f)

end Shriek

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj


section Shriek

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the
derived pushforward along the proper morphism `p`, both on bounded constructible complexes, for `i`
and `p` the morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ :=
  boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ c.overI ⋙
    boundedConstructibleLowerStar ℓ E c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦𝒪̲_E⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility ℓ E c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility
        (Profinite.padicIntegersRingObj ℓ E) ℓ
        c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded constructible
complexes: the functor `boundedConstructibleLowerShriekOfCompactification`
attached to the compactification `compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f)

/-- The defining equation of `boundedConstructibleLowerShriek` (`𝒪_E`-coefficient). -/
lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek ℓ E f =
      boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦𝒪̲_E⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek ℓ E f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ E
    (compactificationOverField f)

end Shriek

end PadicIntegersRingObj

/-! ### The monoidal closed structure: the derived hom (needs
`boundedConstructible_rightDerivedLowerStar_obj`) -/

section TensorHom

include ℓ k

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance keeps only the section variables its statement and proof mention, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- Blueprint `proposition-six-operations-dctf--15`: the bounded constructible complexes of
`ℚ̄_ℓ`-sheaves are stable under the derived hom
`RHom(-, -)`, the internal hom of `D(Mod_{ℚ̄_ℓ,X})` (SGA 4½ [Th. finitude],
1.6; Bhatt–Scholze, Section 6.8). It is false for a general condensed ring: for `Λ = ℤ/4` on a
geometric point of characteristic `3`, `Ext^i_{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
theorem isMonoidalClosed_boundedConstructible :
    (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).IsMonoidalClosed :=
  ⟨fun _ _ hK hL ↦ boundedConstructible_ihom_of_over
    (tensorHypotheses_padicAlgClRingObj ℓ).lisseHypotheses X
    (fun _ _ _ _ _ _ _ _ j _ A hA ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ j ⟨A, hA⟩)
    hK hL⟩
set_option linter.overlappingInstances false in
attribute [instance] isMonoidalClosed_boundedConstructible

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ᵒᵖ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` on bounded
constructible complexes: the internal hom of the monoidal closed structure on
the full subcategory `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the
restriction of `RHom(X)⟦ℚ̲̄_ℓ⟧` in both variables. -/
noncomputable def boundedConstructibleHom :
    (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)ᵒᵖ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleHom ℓ X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧).obj (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`.
-/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor ℓ X ⊣₂ boundedConstructibleHom ℓ X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed
structure on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleTensor ℓ X).obj K ⊣ (boundedConstructibleHom ℓ X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ ℓ).adj K


end TensorHom

namespace ContinuousMapRingObj

section TensorHom

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance keeps only the section variables its statement and proof mention, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `E`-sheaves are stable under the derived hom
`RHom(-, -)`, the internal hom of `D(Mod_{E_X})` (SGA 4½ [Th. finitude], 1.6;
Bhatt–Scholze, Section 6.8). It is false for a general condensed ring: for `Λ = ℤ/4` on a geometric
point of characteristic `3`, `Ext^i_{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
theorem isMonoidalClosed_boundedConstructible :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left)).IsMonoidalClosed :=
  ⟨fun _ _ hK hL ↦ boundedConstructible_ihom_of_over
    (tensorHypotheses_continuousMapRingObj ℓ E).lisseHypotheses X
    (fun _ _ _ _ _ _ _ _ j _ A hA ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ E j ⟨A, hA⟩)
    hK hL⟩
set_option linter.overlappingInstances false in
attribute [instance] isMonoidalClosed_boundedConstructible

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦E̲⟧ᵒᵖ ⥤ Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(X)⟦E̲⟧` on bounded
constructible complexes: the internal hom of the monoidal closed structure on the
full subcategory `Dᵇc(X)⟦E̲⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the restriction
of `RHom(X)⟦E̲⟧` in both variables. -/
noncomputable def boundedConstructibleHom :
    (Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧)ᵒᵖ ⥤
      Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤
        Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦E̲⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleHom ℓ E X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Profinite.continuousMapRingObj E⟧).obj
        (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦E̲⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor ℓ E X ⊣₂ boundedConstructibleHom ℓ E X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦E̲⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed
structure on `Dᵇc(X)⟦E̲⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleTensor ℓ E X).obj K ⊣ (boundedConstructibleHom ℓ E X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ ℓ E).adj K


end TensorHom

end ContinuousMapRingObj

namespace PadicIntegersRingObj

section TensorHom

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance keeps only the section variables its statement and proof mention, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `𝒪_E`-sheaves are stable under the derived hom
`RHom(-, -)`, the internal hom of `D(Mod_{𝒪_{E,X}})` (SGA 4½ [Th. finitude],
1.6; Bhatt–Scholze, Section 6.8). It is false for a general condensed ring: for `Λ = ℤ/4` on a
geometric point of characteristic `3`, `Ext^i_{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
theorem isMonoidalClosed_boundedConstructible :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)).IsMonoidalClosed :=
  ⟨fun _ _ hK hL ↦ boundedConstructible_ihom_of_over (lisseHypotheses ℓ E) X
    (fun _ _ _ _ _ _ _ _ j _ A hA ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ E j ⟨A, hA⟩)
    hK hL⟩
set_option linter.overlappingInstances false in
attribute [instance] isMonoidalClosed_boundedConstructible

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦𝒪̲_E⟧ᵒᵖ ⥤ Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧` on bounded
constructible complexes: the internal hom of the monoidal closed structure on
the full subcategory `Dᵇc(X)⟦𝒪̲_E⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the
restriction of `RHom(X)⟦𝒪̲_E⟧` in both variables. -/
noncomputable def boundedConstructibleHom :
    (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)ᵒᵖ ⥤ Dᵇc(X.left)⟦Profinite.padicIntegersRingObj
      ℓ E⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦𝒪̲_E⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleHom ℓ E X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧).obj
        (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦𝒪̲_E⟧`.
-/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor ℓ E X ⊣₂ boundedConstructibleHom ℓ E X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦𝒪̲_E⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed
structure on `Dᵇc(X)⟦𝒪̲_E⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleTensor ℓ E X).obj K ⊣ (boundedConstructibleHom ℓ E X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ ℓ E).adj K


end TensorHom

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
