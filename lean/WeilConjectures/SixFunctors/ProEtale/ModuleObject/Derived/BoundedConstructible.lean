/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Compactification.Over
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.Algebra.Homology.KFlat
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.CompletedCondensedCoefficients
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.IntegralLfpConstantModelComparison
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.SfIntegralDirectImageConstructible


import Sheaf.AlgebraicGeometry.BoundedConstructibleTensorPreservation
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.Paper.DerivedInternalHomFilteredColimit
import Sheaf.Paper.IntegralHomReduction
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

/-!

# The six functors on bounded constructible module objects over `Λ`

Let `Λ` be a commutative condensed ring. For a scheme `X`, the bounded constructible derived
category `D_cons(X_proét, Λ_X)` of module objects over the coefficient ring object
`Λ_X = p_X^* Λ` is the full subcategory
`ProEtale.BoundedConstructible (condensedRingObj Λ X)` of `D(Mod_{Λ_X})`
(`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`), with scoped notation
`Dᵇc(X)⟦Λ⟧`. This file restricts the six functors on `D(Mod_{Λ_X})` of the folder
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived` to these full subcategories.

## The setting

Following Bhatt–Scholze, Section 6.8, in the simplified setting of schemes over a field: fix a
prime `ℓ` and a field `k` of characteristic `p > 0` with `p ≠ ℓ`
(`[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`). All schemes are separated and of finite
type over `Spec k`: they are objects `X : Over (Spec (.of k))` of the category of schemes over
`Spec k`, with structure morphism `X.hom` locally of finite type, quasi-compact and separated.
All morphisms are morphisms `f : X ⟶ Y` of `Over (Spec (.of k))`, and the functors are those of
the underlying morphism of schemes `f.left`. In the documentation, `X` also stands for the
underlying scheme `X.left`, so that for instance `Dᵇc(X)⟦Λ⟧` is `Dᵇc(X.left)⟦Λ⟧` in the code.
No further hypothesis is imposed on the schemes or morphisms. In particular every such morphism
has a compactification, by Nagata's theorem (`AlgebraicGeometry.HasCompactification.of_over`),
with the choice `compactificationOverField f`. A compactification
`c = (X.left ⟶[i] Z ⟶[p] Y.left)` of `f.left` is a factorization in `Over (Spec (.of k))`,
through the object `c.overObj` and the morphisms `c.overI` and `c.overG` of
`WeilConjectures.Compactification.Over`.

| functor | restriction |
| --- | --- |
| `Lf^* = L((f)^*⟦Λ⟧)` | `boundedConstructibleUpperStar` |
| `Rf_* = R((f)_*⟦Λ⟧)` | `boundedConstructibleLowerStar` |
| `j_! = D((j)_!open⟦Λ⟧)`, `j` an open immersion | `boundedConstructibleOpenImmersionLowerShriek` |
| `- ⊗ᴸ -` | `boundedConstructibleTensor` |
| `RHom(-, -)` | `boundedConstructibleHom` |

The pullback, the pushforward and the extension by zero are the `ObjectProperty.lift` of the
composite of the inclusion with the functor on the ambient derived category, so they are
compatible with the inclusions by construction (`ObjectProperty.liftCompιIso`). The derived
tensor product and the derived hom are instead the monoidal closed structure of the full
subcategory `Dᵇc(X)⟦Λ⟧` (`ObjectProperty.fullMonoidalSubcategory`,
`ObjectProperty.fullMonoidalClosedSubcategory`), given by the instances
`isMonoidal_boundedConstructible` and `isMonoidalClosed_boundedConstructible`; they are again
compatible with the inclusions, the inclusion being strict monoidal (`ObjectProperty.monoidalι`).
The restricted pullback `Lf^*` is strong monoidal, with the comparison isomorphisms of the
strong monoidal derived pullback `ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`
(`monoidal_boundedConstructibleUpperStar`, by `ObjectProperty.monoidalLift`).

The derived lower shriek is not a restriction: it is assembled on bounded constructible
complexes out of the functors above. For a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`,
`Rf_!^c := i_! ⋙ Rp_*` (`boundedConstructibleLowerShriekOfCompactification`), and `Rf_!` is
`Rf_!^c` for the chosen compactification `compactificationOverField f`
(`boundedConstructibleLowerShriek`). Both are compatible with the derived lower shrieks
`Rf_!(c)⟦Λ⟧` and `R(f)_!⟦Λ⟧` on the ambient derived categories
(`boundedConstructibleLowerShriekOfCompactificationCompatibility`,
`boundedConstructibleLowerShriekCompatibility`).

The adjunctions `Lf^* ⊣ Rf_*` and `j_! ⊣ j^*` restrict along the fully faithful inclusions
(`Adjunction.restrictFullyFaithful`), and so does the composition isomorphism
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` (`boundedConstructibleUpperStarComp`). Its conjugates under these
adjunctions are the composition isomorphisms `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`
(`boundedConstructibleLowerStarComp`) and `(j ≫ j')_! ≅ j_! ⋙ j'_!` for open immersions
(`boundedConstructibleOpenImmersionLowerShriekComp`). The adjunction
`- ⊗ᴸ - ⊣₂ RHom(-, -)` is the tensor-hom adjunction of the monoidal closed category
`Dᵇc(X)⟦Λ⟧` (`boundedConstructibleTensorHomAdjunction₂`).

The exceptional inverse image `Rf^!` is not the restriction of a functor on the ambient derived
category: it is constructed on bounded constructible complexes directly, for the `ℓ`-adic
coefficient rings `E̲` and `ℚ̲̄_ℓ`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`.

## Sorried input

That the six functors preserve bounded constructible complexes is `sorry`ed:
`boundedConstructible_leftDerivedUpperStar_obj`, `boundedConstructible_rightDerivedLowerStar_obj`
and `boundedConstructible_openImmersionLowerShriek_obj`, and the instances
`isMonoidal_boundedConstructible` (`Dᵇc(X)⟦Λ⟧` contains `Λ_X` and is stable under `- ⊗ᴸ -`) and
`isMonoidalClosed_boundedConstructible` (`Dᵇc(X)⟦Λ⟧` is stable under `RHom(-, -)`).

These are theorems for the `ℓ`-adic coefficient rings, the condensed rings `E̲` of a finite
extension `E` of `ℚ_ℓ` and `ℚ̲̄_ℓ` (Deligne's finiteness theorems, Bhatt–Scholze, Section 6.8);
`Λ` is kept general here, the coefficient ring being an input of the statements.

That `Rf_*` preserves bounded constructible complexes is false for a general `Λ` (for the constant
discrete ring `𝔽_p`, `H¹(𝔸¹, 𝔽_p)` is infinite by Artin–Schreier). It is stated, and the
restricted pushforward `Rf_*`, its adjunction and the lower shriek are defined, only for the
coefficient rings of Deligne's finiteness theorems, `[IsFinitenessCoefficient ℓ Λ]`
(`WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient`), as in the
blueprint (`sk-def-sfb-dc-restricted-functors`).

Likewise, that `Dᵇc(X)⟦Λ⟧` is stable under `- ⊗ᴸ -` and `RHom(-, -)` is false for a general `Λ`
(for `Λ = ℤ/4` on a geometric point of characteristic `3`, `Tor_i` and `Ext^i` of `ℤ/2` over `ℤ/4`
are `ℤ/2` in every degree `i ≥ 0`). The instances `isMonoidal_boundedConstructible` and
`isMonoidalClosed_boundedConstructible`, and the tensor product, the internal hom and the monoidal
structure of `Lf^*` built from them, are stated only for the `ℓ`-adic rings `E̲`, `𝒪̲_E` and
`ℚ̲̄_ℓ`, `[IsEllAdicFinitenessCoefficient ℓ Λ]`, with `ℓ` different from the characteristic of `k`,
as in the blueprint (`lem-sfb-dc-tensor-preserves`, `lem-sfb-dc-hom-preserves`).

-/

@[expose] public section

-- Keep elaboration from expanding the K-injective construction of internal Hom.
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The bounded constructible derived category `D_cons(X_proét, Λ_X)` of module objects over
`Λ_X = p_X^* Λ`. -/
scoped notation "Dᵇc(" X ")⟦" Λ "⟧" =>
  AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj Λ X)

/-! ### The pullback and the pushforward -/

section UpperLowerStar

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

set_option linter.unusedSectionVars false in
/-- The derived pullback `Lf^*` on module objects over `Λ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_leftDerivedUpperStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left)))
    (hK : boundedConstructible (condensedRingObj Λ Y.left) K) :
    boundedConstructible (condensedRingObj Λ X.left) ((L((f.left)^*⟦Λ⟧)).obj K) := by
  let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ f.left).app K
  refine ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e.symm
    ((f.left)^*⟦Λ⟧.bounded_mapDerivedCategory_obj hK.1), fun n ↦ ?_⟩
  exact constructible_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e.symm)
    (constructible_of_iso (((f.left)^*⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).app K)
      (isConstructibleModuleObject_upperStar Λ f.left _ (hK.2 n)))

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible complexes: the
restriction of `L((f)^*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleUpperStar : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K.obj K.property

/-- The restricted derived pullback is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperStarCompatibility :
    boundedConstructibleUpperStar Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes:
the restriction of `ProEtale.CondensedRing.leftDerivedUpperStarComp` along the fully
faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleUpperStar Λ ℓ (f ≫ g) ≅
      boundedConstructibleUpperStar Λ ℓ g ⋙ boundedConstructibleUpperStar Λ ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility Λ ℓ (f ≫ g) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp Λ f.left g.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility Λ ℓ g).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The derived pushforward `Rf_*` on module objects over a coefficient ring `Λ` of Deligne's
finiteness theorems preserves bounded constructible complexes. For a general `Λ` this is false:
for the constant discrete ring `𝔽_p` and the affine line over an algebraically closed field of
characteristic `p`, Artin–Schreier gives `H¹(𝔸¹, 𝔽_p) = k[t] / (F - 1) k[t]`, which is infinite. -/
lemma boundedConstructible_rightDerivedLowerStar_obj [IsFinitenessCoefficient ℓ Λ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) :
    boundedConstructible (condensedRingObj Λ Y.left) ((R((f.left)_*⟦Λ⟧)).obj K) :=
  sorry

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the restriction of `R((f)_*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleLowerStar [IsFinitenessCoefficient ℓ Λ] :
    Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f K.obj K.property

/-- The restricted derived pushforward is compatible with the inclusions. -/
noncomputable def boundedConstructibleLowerStarCompatibility [IsFinitenessCoefficient ℓ Λ] :
    boundedConstructibleLowerStar Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes: the restriction of
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction [IsFinitenessCoefficient ℓ Λ] :
    boundedConstructibleUpperStar Λ ℓ f ⊣ boundedConstructibleLowerStar Λ ℓ f :=
  Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
    (boundedConstructibleLowerStarCompatibility Λ ℓ f).symm

/-- The derived pullback `Lf^*` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleLowerStar`. -/
instance isLeftAdjoint_boundedConstructibleUpperStar [IsFinitenessCoefficient ℓ Λ] :
    (boundedConstructibleUpperStar Λ ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).isLeftAdjoint

/-- The derived pushforward `Rf_*` on bounded constructible complexes is a right adjoint, its
left adjoint being `boundedConstructibleUpperStar`. -/
instance isRightAdjoint_boundedConstructibleLowerStar [IsFinitenessCoefficient ℓ Λ] :
    (boundedConstructibleLowerStar Λ ℓ f).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).isRightAdjoint

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` on bounded constructible complexes:
the conjugate of `boundedConstructibleUpperStarComp` under the adjunctions
`L(f ≫ g)^* ⊣ R(f ≫ g)_*` and `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`. -/
noncomputable def boundedConstructibleLowerStarComp [IsFinitenessCoefficient ℓ Λ]
    {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleLowerStar Λ ℓ g ≅
      boundedConstructibleLowerStar Λ ℓ (f ≫ g) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ g).comp
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f))
    (boundedConstructibleUpperStarComp Λ ℓ f g).symm).symm

end UpperLowerStar

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

include ℓ k

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

set_option linter.unusedSectionVars false in
/-- The extension by zero `j_!` along an open immersion, applied levelwise to complexes of
module objects over `Λ`, preserves bounded constructible complexes. -/
lemma boundedConstructible_openImmersionLowerShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
      (condensedRingObj Λ U.left)))
    (hK : boundedConstructible (condensedRingObj Λ U.left) K) :
    boundedConstructible (condensedRingObj Λ X.left) ((D((j.left)_!open⟦Λ⟧)).obj K) := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  refine ⟨((j.left)_!open⟦Λ⟧).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  exact constructible_of_iso
    ((((j.left)_!open⟦Λ⟧).mapDerivedCategoryHomologyFunctorIso n).app K)
    (isConstructibleModuleObject_openImmersionLowerShriek Λ j.left _ (hK.2 n))

/-- The extension by zero `j_! : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` along an open immersion on bounded
constructible complexes: the restriction of the levelwise functor `D((j)_!open⟦Λ⟧)`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriek : Dᵇc(U.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ D((j.left)_!open⟦Λ⟧))
    fun K ↦ boundedConstructible_openImmersionLowerShriek_obj Λ ℓ j K.obj K.property

/-- The restricted extension by zero is compatible with the inclusions. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekCompatibility :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ D((j.left)_!open⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `j_! ⊣ j^*` along an open immersion on bounded constructible complexes: the
restriction of `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`
along the fully faithful inclusions, the levelwise `D((j)^*⟦Λ⟧)` being identified with the
derived pullback `L((j)^*⟦Λ⟧)` that `boundedConstructibleUpperStar` restricts. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⊣ boundedConstructibleUpperStar Λ ℓ j :=
  Adjunction.restrictFullyFaithful
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j.left).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).symm
    (boundedConstructibleUpperStarCompatibility Λ ℓ j).symm

/-- The extension by zero `j_!` on bounded constructible complexes is a left adjoint, its right
adjoint being `boundedConstructibleUpperStar`. -/
instance isLeftAdjoint_boundedConstructibleOpenImmersionLowerShriek :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).IsLeftAdjoint :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).isLeftAdjoint

/-- The derived pullback `j^*` along an open immersion on bounded constructible complexes is a
right adjoint, its left adjoint being `boundedConstructibleOpenImmersionLowerShriek`. -/
instance isRightAdjoint_boundedConstructibleUpperStar_of_isOpenImmersion :
    (boundedConstructibleUpperStar Λ ℓ j).IsRightAdjoint :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).isRightAdjoint

/-- The composition isomorphism `(j ≫ j')_! ≅ j_! ⋙ j'_!` of the extensions by zero along open
immersions on bounded constructible complexes: the conjugate of
`boundedConstructibleUpperStarComp` under the adjunctions `(j ≫ j')_! ⊣ L(j ≫ j')^*` and
`j_! ⋙ j'_! ⊣ Lj'^* ⋙ Lj^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekComp {V : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] (j' : X ⟶ V)
    [IsOpenImmersion j'.left] [IsOpenImmersion (j ≫ j').left] :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ (j ≫ j') ≅
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' :=
  ((conjugateIsoEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ (j ≫ j'))
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).comp
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j'))).symm
    (boundedConstructibleUpperStarComp Λ ℓ j j')).symm

end OpenImmersion

/-! ### The derived lower shriek -/

/-- The compactification of the underlying morphism of schemes `f.left` of a morphism `f` of
separated `k`-schemes of finite type chosen by Nagata's theorem
(`AlgebraicGeometry.HasCompactification.of_over`): the compactification
`HasCompactification.compactification f.left` for the instance it provides. It is the
compactification defining `boundedConstructibleLowerShriek`. -/
noncomputable abbrev compactificationOverField {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) : Compactification f.left :=
  haveI := HasCompactification.of_over f
  HasCompactification.compactification f.left

section Shriek

include ℓ k

variable [IsFinitenessCoefficient ℓ Λ] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the derived pushforward
along the proper morphism `p`, both on bounded constructible complexes, for `i` and `p` the
morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI ⋙
    boundedConstructibleLowerStar Λ ℓ c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦Λ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility Λ ℓ c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the functor `boundedConstructibleLowerShriekOfCompactification` attached to the compactification
`compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek : Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  boundedConstructibleLowerShriekOfCompactification Λ ℓ (compactificationOverField f)

lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek Λ ℓ f =
      boundedConstructibleLowerShriekOfCompactification Λ ℓ (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦Λ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Λ⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility Λ ℓ
    (compactificationOverField f)

end Shriek


/-! ### The derived tensor product and the derived hom -/

section TensorHom

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The bounded constructible complexes of module objects over an `ℓ`-adic coefficient ring `Λ`
form a monoidal subcategory of `D(Mod_{Λ_X})` for the derived tensor product: they contain the
unit `Λ_X` and are stable under `- ⊗ᴸ -`. For a general `Λ` this is false: for `Λ = ℤ/4` on a
geometric point of characteristic `3`, `Tor_i^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`, so the
derived self-tensor of `ℤ/2` is unbounded. -/
instance isMonoidal_boundedConstructible
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible (condensedRingObj Λ X.left)).IsMonoidal := by
  refine { prop_unit := ?_, prop_tensor := ?_ }
  · exact boundedConstructible_tensor_unit Λ X
  · intro K L hK hL
    exact boundedConstructible_tensor_closure Λ X K L hK hL

/-- The bounded constructible complexes of module objects over an `ℓ`-adic coefficient ring `Λ`
are stable under the derived hom `RHom(-, -)`, the internal hom of `D(Mod_{Λ_X})`. For a general
`Λ` this is false: for `Λ = ℤ/4` on a geometric point of characteristic `3`,
`Ext^i_{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
instance isMonoidalClosed_boundedConstructible
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] :
    (boundedConstructible (condensedRingObj Λ X.left)).IsMonoidalClosed :=
  sorry

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded
constructible complexes: the tensor product of the monoidal structure on the full subcategory
`Dᵇc(X)⟦Λ⟧` (`ObjectProperty.fullMonoidalSubcategory`), the restriction of `-⊗ᴸ-(X)⟦Λ⟧` in
both variables. -/
noncomputable def boundedConstructibleTensor
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] :
    Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  curriedTensor _

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦Λ⟧ᵒᵖ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible
complexes: the internal hom of the monoidal closed structure on the full subcategory
`Dᵇc(X)⟦Λ⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the restriction of `RHom(X)⟦Λ⟧`
in both variables. -/
noncomputable def boundedConstructibleHom
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] :
    (Dᵇc(X.left)⟦Λ⟧)ᵒᵖ ⥤ Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleTensor Λ X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Λ⟧).obj K.obj :=
  Iso.refl _

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleHom Λ X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Λ⟧).obj (op K.obj) :=
  Iso.refl _

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦Λ⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction₂
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] :
    boundedConstructibleTensor Λ X ⊣₂ boundedConstructibleHom Λ X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed structure on
`Dᵇc(X)⟦Λ⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleTensor Λ X).obj K ⊣ (boundedConstructibleHom Λ X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ Λ).adj K

end TensorHom

section MonoidalUpperStar

variable [IsEllAdicFinitenessCoefficient ℓ Λ] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible complexes is
strong monoidal, with the comparison isomorphisms of `L((f)^*⟦Λ⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar Λ ℓ f).Monoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.monoidalLift _ _

end MonoidalUpperStar

end AlgebraicGeometry.ProEtale.CondensedRing
