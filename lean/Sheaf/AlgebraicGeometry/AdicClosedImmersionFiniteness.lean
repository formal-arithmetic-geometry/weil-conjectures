/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero

/-!
# Finiteness of closed direct image for adic sheaves

The closed-immersion part of the affine finiteness reduction, proved from exactness and
open-closed stratification. No finiteness theorem for general direct images is used.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.ProEtale
variable {l : ℕ} [Fact l.Prime] {Z X : Scheme.{u}} [IsNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

private lemma closed_constructible {F : AdicSheaf l Z} (hF : IsAdicConstructibleSheaf F) :
    IsAdicConstructibleSheaf ((i)_*ᵃ[l].obj F) := by
  let U : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hij : IsCompl (Set.range i.base) (Set.range U.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated i
  refine (IsAdicStratifiedLisseSheaf.of_isCompl U.ι i hij.symm ?_ ?_).isAdicConstructibleSheaf
  · have hz : IsZero ((U.ι)^*ᵃ[l].obj ((i)_*ᵃ[l].obj F)) :=
      AdicSheaf.isZero_of_isZero_X
        (isZero_upperStar_lowerStar_of_disjoint _ i U.ι hij.disjoint F.X)
    exact (IsAdicLisseSheaf.of_isZero hz).isAdicStratifiedLisseSheaf
  · have : IsIso ((adicUpperStarLowerStarAdjunction l i).counit.app F).hom := by
      rw [adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_counit_app_hom]
      infer_instance
    have : IsIso ((AdicSheaf.forget Z).map
        ((adicUpperStarLowerStarAdjunction l i).counit.app F)) := this
    have := isIso_of_reflects_iso ((adicUpperStarLowerStarAdjunction l i).counit.app F)
      (AdicSheaf.forget Z)
    exact hF.isAdicStratifiedLisseSheaf.of_iso
      (asIso ((adicUpperStarLowerStarAdjunction l i).counit.app F)).symm

/-- Closed direct image preserves bounded constructibility for the adic coefficient sheaf.

Source: the closed-immersion recollement in Bhatt--Scholze, Sections 6.1 and 6.8,
and the closed-direct-image step of `sk-prop-sf-finiteness`.
(blueprint: lem-sf-adic-closed-direct-image-finiteness)

Proof: the open complement and the closed subscheme partition the noetherian target.
The direct image restricts to the original sheaf on the closed part and to zero on the
open complement. A constructible sheaf has a global finite lisse stratification on the
quasi-compact closed subscheme, so this partition proves constructibility of its direct
image. Closed direct image is exact, by the open-closed recollement. Its derived functor
therefore agrees with the functor applied to complexes, preserves both cohomological
bounds, and computes cohomology by applying closed direct image to each cohomology
sheaf. This proves boundedness and constructibility in every degree. -/
theorem bounded_constructible_rightDerivedFunctor_adicLowerStar_of_isClosedImmersion
    (A : _root_.DerivedCategory (AdicSheaf l Z))
    (hb : _root_.DerivedCategory.TStructure.t.bounded A)
    (hc : _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l Z) A) :
    (_root_.DerivedCategory.TStructure.t.bounded ⊓
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l X))
      ((i)_*ᵃ[l].rightDerivedFunctor.obj A) := by
  let U : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hij : IsCompl (Set.range i.base) (Set.range U.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  have := preservesFiniteColimits_lowerStar_of_isCompl
    (R := ULift.{u + 1} (PadicAlgCl l)) i U.ι hij
  have : PreservesFiniteColimits ((i)_*ᵃ[l] ⋙ AdicSheaf.forget X) :=
    inferInstanceAs (PreservesFiniteColimits
      (AdicSheaf.forget Z ⋙ (i)_*[WeilCoefficients.{u} l]))
  have := preservesFiniteColimits_of_reflects_of_preserves (i)_*ᵃ[l] (AdicSheaf.forget X)
  refine ObjectProperty.prop_of_iso _
    ((i)_*ᵃ[l].rightDerivedFunctorIsoMapDerivedCategory.app A).symm ⟨?_, ?_⟩
  · exact (i)_*ᵃ[l].bounded_mapDerivedCategory_obj hb
  · intro n
    exact (closed_constructible i (hc n)).of_iso
      (((i)_*ᵃ[l].mapDerivedCategoryHomologyFunctorIso n).app A)

end AlgebraicGeometry.ProEtale
