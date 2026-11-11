/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleModuleObjectsEssentiallySmall
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Generator.Basic

/-!
# The category of ind-constructible sheaves is Grothendieck abelian

Blueprint `proposition-ind-constructible-sheaves--8`: the category `IndCons(X, Λ)` of
ind-constructible sheaves of `Λ`-modules on `X_proét` is a Grothendieck abelian category.

We first prove an abstract statement: let `A` be a Grothendieck abelian category and `P` an
essentially small property of objects of `A`. If `P.ind` (the filtered colimits of objects
satisfying `P`) contains zero and is closed under kernels, cokernels, finite products and
coproducts in `A`, then the full subcategory of `A` defined by `P.ind` is Grothendieck abelian:
it is abelian with all small colimits computed in `A` (coproducts and cokernels), filtered
colimits are exact since they are computed in `A` and the inclusion is exact, and the objects
satisfying `P` form a small separating family, since every object of `P.ind` is a filtered
colimit of such objects.

Once `IndCons(X, R)` is known to be closed under kernels, cokernels, extensions and direct sums
in the category of `R`-modules (`AlgebraicGeometry.ProEtale.IsIndConstructibleHeart R`), this
applies with `P` the constructible sheaves, which form an essentially small family
(`AlgebraicGeometry.ProEtale.constructibleModuleObjects_essentiallySmall`). The abelian structure
on `IndCons(X, R)` is the one of `Mathlib.CategoryTheory.Abelian.Subcategory`, obtained from the
closure properties recorded in `IsIndConstructibleHeart R`.

## Main results

* `CategoryTheory.ObjectProperty.isClosedUnderFiniteProducts_of_isClosedUnderExtensions`
* `CategoryTheory.ObjectProperty.isGrothendieckAbelian_ind_fullSubcategory`
* `AlgebraicGeometry.ProEtale.IsIndConstructibleHeart.isGrothendieckAbelian`
* `AlgebraicGeometry.ProEtale.CondensedRing.isGrothendieckAbelian_continuousMapRingObj`
* `AlgebraicGeometry.ProEtale.CondensedRing.isGrothendieckAbelian_padicIntegersRingObj`
* `AlgebraicGeometry.ProEtale.CondensedRing.isGrothendieckAbelian_padicAlgClRingObj`
-/

@[expose] public section

universe w v u' u

namespace CategoryTheory.ObjectProperty

open Limits

variable {A : Type u'} [Category.{v} A] [Abelian A]

/-- A property of objects of an abelian category which contains zero and is closed under
isomorphisms and extensions is closed under finite products (a binary product is an extension).
Used for blueprint `proposition-ind-constructible-sheaves--8`. -/
lemma isClosedUnderFiniteProducts_of_isClosedUnderExtensions (Q : ObjectProperty A)
    [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] [Q.IsClosedUnderExtensions] :
    Q.IsClosedUnderFiniteProducts := by
  have : Q.IsClosedUnderBinaryProducts := by
    refine ⟨fun X ⟨p⟩ ↦ ?_⟩
    let a := p.diag.obj ⟨.left⟩
    let b := p.diag.obj ⟨.right⟩
    exact Q.prop_of_iso (biprod.isoProd a b ≪≫
      (HasLimit.isoOfNatIso (diagramIsoPair p.diag)).symm ≪≫
      (limit.isLimit p.diag).conePointUniqueUpToIso p.isLimit)
      (Q.prop_biprod (p.prop_diag_obj _) (p.prop_diag_obj _))
  exact .mk'

variable (P : ObjectProperty A)

/-- If the filtered colimits of an essentially small family of objects of a Grothendieck abelian
category `A` form a subcategory containing zero and closed under kernels, cokernels, finite
products and coproducts, then this full subcategory is a Grothendieck abelian category
(blueprint `proposition-ind-constructible-sheaves--8`, abstract form). -/
theorem isGrothendieckAbelian_ind_fullSubcategory [IsGrothendieckAbelian.{w} A]
    [ObjectProperty.EssentiallySmall.{w} P] [(ind.{w} P).ContainsZero]
    [(ind.{w} P).IsClosedUnderKernels] [(ind.{w} P).IsClosedUnderCokernels]
    [(ind.{w} P).IsClosedUnderFiniteProducts]
    [∀ J : Type w, (ind.{w} P).IsClosedUnderColimitsOfShape (Discrete J)] :
    IsGrothendieckAbelian.{w} (ind.{w} P).FullSubcategory := by
  let Q := ind.{w} P
  have : HasColimitsOfSize.{w, w} A := IsGrothendieckAbelian.hasColimits.{w} A
  have : HasCoproducts.{w} Q.FullSubcategory := fun J ↦
    hasColimitsOfShape_of_closedUnderColimits (Discrete J) Q
  have : HasColimitsOfSize.{w, w} Q.FullSubcategory :=
    has_colimits_of_hasCoequalizers_and_coproducts
  have : ∀ ⦃X Y : Q.FullSubcategory⦄ (f : X ⟶ Y), PreservesLimit (parallelPair f 0) Q.ι :=
    Q.preservesKernels_ι
  have : ∀ ⦃X Y : Q.FullSubcategory⦄ (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) Q.ι :=
    Q.preservesCokernels_ι
  have : PreservesFiniteLimits Q.ι := Functor.preservesFiniteLimits_of_preservesKernels _
  have : PreservesFiniteColimits Q.ι := Functor.preservesFiniteColimits_of_preservesCokernels _
  have : PreservesColimitsOfSize.{w, w} Q.ι :=
    preservesColimits_of_preservesCoequalizers_and_coproducts _
  have hsep : HasSeparator Q.FullSubcategory := by
    obtain ⟨S, _, hSP, hPS⟩ := EssentiallySmall.exists_small_le.{w} P
    obtain ⟨ι, X, rfl⟩ := Small.exists_eq_ofObj.{w} S
    let G : ι → Q.FullSubcategory := fun i ↦ ⟨X i, le_ind _ _ (hSP _ (ofObj_apply X i))⟩
    refine ⟨∐ G, IsSeparating.isSeparator_coproduct fun Y Z f g hfg ↦ ?_⟩
    obtain ⟨J, _, _, pres, hpres⟩ := Y.property
    refine Q.hom_ext (pres.isColimit.hom_ext fun j ↦ ?_)
    obtain ⟨_, ⟨i⟩, ⟨e⟩⟩ := hPS _ (hpres j)
    have := hfg (G i) (ofObj_apply G i) (Q.homMk (e.inv ≫ pres.ι.app j))
    rw [← cancel_epi e.inv]
    simpa [FullSubcategory.comp_hom] using congrArg InducedCategory.Hom.hom this
  refine { hasSeparator := hsep, ab5OfSize := ⟨fun J _ _ ↦ ?_⟩ }
  exact HasExactColimitsOfShape.domain_of_functor J Q.ι

end CategoryTheory.ObjectProperty

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section General

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} {R : Sheaf (Scheme.ProEt.topology X) A} [MonObj R]

/-- Blueprint `proposition-ind-constructible-sheaves--8`: if `IndCons(X, R)` is closed under
extensions, it is closed under finite products (direct sums). -/
lemma IsIndConstructibleHeart.isClosedUnderFiniteProducts (hR : IsIndConstructibleHeart R) :
    (IsIndConstructibleModuleObject R).IsClosedUnderFiniteProducts :=
  have := hR.isClosedUnderExtensions
  ObjectProperty.isClosedUnderFiniteProducts_of_isClosedUnderExtensions _

/-- Blueprint `proposition-ind-constructible-sheaves--8`: if `IndCons(X, R)` is closed under
kernels, cokernels, extensions and direct sums, and the constructible sheaves of `R`-modules form
an essentially small family, then `IndCons(X, R)` (with the abelian structure of a full
subcategory closed under kernels, cokernels and finite products) is Grothendieck abelian. -/
theorem IsIndConstructibleHeart.isGrothendieckAbelian (hR : IsIndConstructibleHeart R)
    (hs : ObjectProperty.EssentiallySmall.{u + 1} (IsConstructibleModuleObject R)) :
    haveI := hR.isClosedUnderKernels
    haveI := hR.isClosedUnderCokernels
    haveI := hR.isClosedUnderFiniteProducts
    IsGrothendieckAbelian.{u + 1} (IsIndConstructibleModuleObject R).FullSubcategory := by
  have := hR.isClosedUnderKernels
  have := hR.isClosedUnderCokernels
  have := hR.isClosedUnderFiniteProducts
  have := hR.isClosedUnderColimitsOfShape_discrete
  exact ObjectProperty.isGrothendieckAbelian_ind_fullSubcategory _

end General

/-- Blueprint `proposition-ind-constructible-sheaves--8`, for sheaves of abelian groups on a
quasi-compact locally Noetherian scheme: if `IndCons(X, R)` is closed under kernels, cokernels,
extensions and direct sums, then it is Grothendieck abelian (the constructible sheaves form an
essentially small family by `constructibleModuleObjects_essentiallySmall`). -/
theorem IsIndConstructibleHeart.isGrothendieckAbelian_of_isLocallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    (hR : IsIndConstructibleHeart R) :
    haveI := hR.isClosedUnderKernels
    haveI := hR.isClosedUnderCokernels
    haveI := hR.isClosedUnderFiniteProducts
    IsGrothendieckAbelian.{u + 1} (IsIndConstructibleModuleObject R).FullSubcategory :=
  hR.isGrothendieckAbelian (constructibleModuleObjects_essentiallySmall X R)

namespace CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

/-- Blueprint `proposition-ind-constructible-sheaves--8`, for the coefficient ring `E` of a
finite extension `E` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`: the category
`IndCons(X, E)` of ind-constructible `E`-sheaves is Grothendieck abelian. -/
theorem isGrothendieckAbelian_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    haveI := (isIndConstructibleHeart_continuousMapRingObj ℓ E aX).isClosedUnderKernels
    haveI := (isIndConstructibleHeart_continuousMapRingObj ℓ E aX).isClosedUnderCokernels
    haveI := (isIndConstructibleHeart_continuousMapRingObj ℓ E aX).isClosedUnderFiniteProducts
    IsGrothendieckAbelian.{u + 1} (IsIndConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)).FullSubcategory := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  exact (isIndConstructibleHeart_continuousMapRingObj ℓ E aX)
    |>.isGrothendieckAbelian_of_isLocallyNoetherian

/-- Blueprint `proposition-ind-constructible-sheaves--8`, for the coefficient ring `ℚ̄_ℓ` and a
separated finite-type `k`-scheme `X`: the category `IndCons(X, ℚ̄_ℓ)` of ind-constructible
`ℚ̄_ℓ`-sheaves is Grothendieck abelian. -/
theorem isGrothendieckAbelian_padicAlgClRingObj {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    haveI := (isIndConstructibleHeart_padicAlgClRingObj ℓ aX).isClosedUnderKernels
    haveI := (isIndConstructibleHeart_padicAlgClRingObj ℓ aX).isClosedUnderCokernels
    haveI := (isIndConstructibleHeart_padicAlgClRingObj ℓ aX).isClosedUnderFiniteProducts
    IsGrothendieckAbelian.{u + 1} (IsIndConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).FullSubcategory := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  exact (isIndConstructibleHeart_padicAlgClRingObj ℓ aX)
    |>.isGrothendieckAbelian_of_isLocallyNoetherian

/-- Blueprint `proposition-ind-constructible-sheaves--8`, for the coefficient ring `𝒪_E` of a
finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`: the
category `IndCons(X, 𝒪_E)` of ind-constructible `𝒪_E`-sheaves is Grothendieck abelian. -/
theorem isGrothendieckAbelian_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    haveI := (isIndConstructibleHeart_padicIntegersRingObj ℓ E aX).isClosedUnderKernels
    haveI := (isIndConstructibleHeart_padicIntegersRingObj ℓ E aX).isClosedUnderCokernels
    haveI := (isIndConstructibleHeart_padicIntegersRingObj ℓ E aX).isClosedUnderFiniteProducts
    IsGrothendieckAbelian.{u + 1} (IsIndConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)).FullSubcategory := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  exact (isIndConstructibleHeart_padicIntegersRingObj ℓ E aX)
    |>.isGrothendieckAbelian_of_isLocallyNoetherian

end CondensedRing

end AlgebraicGeometry.ProEtale
