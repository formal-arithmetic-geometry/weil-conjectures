/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Recollement
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion

/-!
# The open–closed triangle at every coefficient stage
-/

@[expose] public section

universe w u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
  [IsOpenImmersion j]

/-- The derived adjunction `D(i^*) ⊣ Ri_*` on the unbounded derived categories of pro-étale
sheaves, for an arbitrary morphism `i`: the pullback `i^*` is exact, so the functor it induces
levelwise is left adjoint to the total right derived functor of `i_*`. -/
noncomputable def mapDerivedUpperStarLowerStarAdjunction (A : Type*) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] :
    D((i)^*[A]) ⊣ R((i)_*[A]) :=
  (upperStarLowerStarAdjunction A i).mapDerivedCategoryRightDerivedAdjunction

end Finite

end ProEtale

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
  [IsOpenImmersion j]

variable {Λ} in
omit [IsOpenImmersion j] in
/-- The restrictions to a closed immersion and to its quasi-compact open complement jointly
reflect isomorphisms of pro-étale sheaves of modules
(`AlgebraicGeometry.ProEtale.isIso_of_isIso_upperStar_of_isCompl`), in the
`CategoryTheory.pairFunctor` form. -/
lemma jointlyReflectIsomorphisms_upperStar_of_isCompl {R : Type (u + 1)} [Ring R]
    [IsClosedImmersion i] [QuasiCompact j] (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    JointlyReflectIsomorphisms
      (pairFunctor ((j)^*[ModuleCat.{u + 1} R]) ((i)^*[ModuleCat.{u + 1} R])) :=
  jointlyReflectIsomorphisms_pairFunctor _ _ fun _ _ φ _ _ ↦
    isIso_of_isIso_upperStar_of_isCompl i j hij φ

variable [IsClosedImmersion i] [QuasiCompact j]

/-- Blueprint `def-weil-open-closed-recollement`: Open–closed recollement.

For a closed immersion `i : Z ⟶ X` and an open immersion `j : U ⟶ X`, and `K` in the derived
category of pro-étale sheaves of `Λ`-modules on `X` (at the finite stage `Λ = A_{E,n}` and
`K ∈ Dᵇc(X, Λ)` in the blueprint), the canonical open–closed pair is
`j_! j^* K ⟶ K ⟶ Ri_* i^* K`, formed by the counit of the extension-by-zero adjunction
`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction` and the unit of
`AlgebraicGeometry.ProEtale.mapDerivedUpperStarLowerStarAdjunction`. A morphism
`w : Ri_* i^* K ⟶ (j_! j^* K)[1]` makes an *open–closed recollement triangle* if
`j_! j^* K ⟶ K ⟶ Ri_* i^* K ⟶[w] (j_! j^* K)[1]` is distinguished. -/
abbrev IsOpenClosedRecollementTriangle
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (w : R((i)_*[ModuleCat.{u + 1} Λ]).obj (D((i)^*[ModuleCat.{u + 1} Λ]).obj K) ⟶
      (D((j)_!open[ModuleCat.{u + 1} Λ]).obj (D((j)^*[ModuleCat.{u + 1} Λ]).obj K))⟦(1 : ℤ)⟧) :
    Prop :=
  IsRecollementTriangle (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j)
    (mapDerivedUpperStarLowerStarAdjunction i (ModuleCat.{u + 1} Λ)) K w

instance isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit :=
  Adjunction.isIso_unit_of_mapDerivedCategory (openImmersionLowerShriekUpperStarAdjunction _ j) _

instance isIso_mapDerivedUpperStarLowerStarAdjunction_counit :
    IsIso (mapDerivedUpperStarLowerStarAdjunction i (ModuleCat.{u + 1} Λ)).counit :=
  inferInstance

omit [QuasiCompact j] in
/-- Blueprint `prop-weil-open-closed-recollement-adjunctions`: Adjunctions of the open-closed
recollement.

For an open immersion `j : U ⟶ X` and a closed immersion `i : Z ⟶ X`, on the unbounded derived
categories of pro-étale sheaves of `Λ`-modules one has the adjunctions `j_! ⊣ j^*`
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction`) and
`i^* ⊣ Ri_*` (`AlgebraicGeometry.ProEtale.mapDerivedUpperStarLowerStarAdjunction`), and the open
unit `𝟭 ⟶ j^* j_!` and the closed counit `i^* Ri_* ⟶ 𝟭` are isomorphisms.

Both `j_!` and `j^*` are exact, so the sheaf-level adjunction passes to the derived categories
and its unit is invertible since it is so termwise (blueprint `lem-exc-proetale-open-unit`). The
pullback `i^*` is exact, so `i_*` preserves K-injective complexes and the derived counit is
computed termwise by the sheaf-level counit, an isomorphism by blueprint
`lem-exc-proetale-closed-fully-faithful`. -/
theorem isIso_openClosedRecollement_unit_and_counit :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit ∧
      IsIso (mapDerivedUpperStarLowerStarAdjunction i (ModuleCat.{u + 1} Λ)).counit :=
  ⟨inferInstance, inferInstance⟩

/-- Blueprint `prop-sf-open-closed-triangle-all-stages`, finite stage. -/
theorem existsUnique_isOpenClosedRecollementTriangle
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    ∃! w, IsOpenClosedRecollementTriangle Λ j i K w :=
  existsUnique_distTriang_recollement _ _
    (Functor.isZero_mapDerivedCategory_obj_mapDerivedCategory_obj _ _ fun F ↦
      isZero_upperStar_openImmersionLowerShriek _ j i
        (Set.disjoint_iff_inter_eq_empty.1 hij.disjoint.symm) F)
    (Functor.isZero_mapDerivedCategory_obj_rightDerivedFunctor_obj _ _ fun G ↦
      isZero_upperStar_lowerStar_of_disjoint _ i j hij.disjoint G)
    (Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory _ _
      (jointlyReflectIsomorphisms_upperStar_of_isCompl j i hij)) K

end Finite

section Adic

variable (l : ℕ) [Fact l.Prime] {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]

/-- The derived adjunction `D(j_!) ⊣ D(j^*)` of the extension by zero of sheaves of modules
over the constant `ℓ`-adic sheaf along an open immersion `j`; both functors are exact. -/
noncomputable def derivedAdicOpenImmersionLowerShriekUpperStarAdjunction :
    D((j)_!ᵃ[l]) ⊣ D((j)^*ᵃ[l]) :=
  (adicOpenImmersionLowerShriekAdjunction l j).mapDerivedCategoryAdjunctionOfKInjective

/-- The derived adjunction `D(i^*) ⊣ Ri_*` on sheaves of modules over the constant `ℓ`-adic
sheaf, for an arbitrary morphism `i`. -/
noncomputable def derivedAdicUpperStarLowerStarAdjunction :
    D((i)^*ᵃ[l]) ⊣ R((i)_*ᵃ[l]) :=
  (adicUpperStarLowerStarAdjunction l i).mapDerivedCategoryRightDerivedAdjunction

instance isIso_derivedAdicOpenImmersionLowerShriekUpperStarAdjunction_unit :
    IsIso (derivedAdicOpenImmersionLowerShriekUpperStarAdjunction l j).unit :=
  Adjunction.isIso_unit_of_mapDerivedCategory (adicOpenImmersionLowerShriekAdjunction l j) _

variable [IsClosedImmersion i]

instance isIso_derivedAdicUpperStarLowerStarAdjunction_counit :
    IsIso (derivedAdicUpperStarLowerStarAdjunction l i).counit :=
  inferInstance

variable [QuasiCompact j]

omit [IsOpenImmersion j] in
/-- The restrictions to a closed immersion and to its quasi-compact open complement jointly
reflect isomorphisms of sheaves of modules over the constant `ℓ`-adic sheaf: the underlying
sheaves are those of `ℚ̄_ℓ`-modules, where this is
`AlgebraicGeometry.ProEtale.isIso_of_isIso_upperStar_of_isCompl`. -/
lemma jointlyReflectIsomorphisms_adicUpperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    JointlyReflectIsomorphisms (pairFunctor ((j)^*ᵃ[l]) ((i)^*ᵃ[l])) :=
  jointlyReflectIsomorphisms_pairFunctor _ _ fun _ _ φ hj hi ↦ by
    have : IsIso ((j)^*[WeilCoefficients.{u} l].map φ.hom) := by
      rw [← adicUpperStar_map_hom]
      exact (inferInstance : IsIso ((AdicSheaf.forget U).map ((j)^*ᵃ[l].map φ)))
    have : IsIso ((i)^*[WeilCoefficients.{u} l].map φ.hom) := by
      rw [← adicUpperStar_map_hom]
      exact (inferInstance : IsIso ((AdicSheaf.forget Z).map ((i)^*ᵃ[l].map φ)))
    have : IsIso ((AdicSheaf.forget X).map φ) := isIso_of_isIso_upperStar_of_isCompl i j hij φ.hom
    exact isIso_of_reflects_iso φ (AdicSheaf.forget X)

/-- Blueprint `def-weil-open-closed-recollement` at the stage `ℚ̄_ℓ`: a morphism
`w : Ri_* i^* K ⟶ (j_! j^* K)[1]` makes an open–closed recollement triangle for `K` in the derived
category of sheaves of modules over the constant `ℓ`-adic sheaf if the triangle formed by the
counit of `AlgebraicGeometry.ProEtale.derivedAdicOpenImmersionLowerShriekUpperStarAdjunction`,
the unit of `AlgebraicGeometry.ProEtale.derivedAdicUpperStarLowerStarAdjunction` and `w` is
distinguished. -/
abbrev IsAdicOpenClosedRecollementTriangle (K : DerivedCategory (AdicSheaf l X))
    (w : R((i)_*ᵃ[l]).obj (D((i)^*ᵃ[l]).obj K) ⟶
      (D((j)_!ᵃ[l]).obj (D((j)^*ᵃ[l]).obj K))⟦(1 : ℤ)⟧) : Prop :=
  IsRecollementTriangle (derivedAdicOpenImmersionLowerShriekUpperStarAdjunction l j)
    (derivedAdicUpperStarLowerStarAdjunction l i) K w

/-- Blueprint `prop-sf-open-closed-triangle-all-stages`, stage `ℚ̄_ℓ`. -/
theorem existsUnique_isAdicOpenClosedRecollementTriangle
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (K : DerivedCategory (AdicSheaf l X)) :
    ∃! w, IsAdicOpenClosedRecollementTriangle l j i K w :=
  existsUnique_distTriang_recollement _ _
    (Functor.isZero_mapDerivedCategory_obj_mapDerivedCategory_obj _ _ fun F ↦
      isZero_adicUpperStar_adicOpenImmersionLowerShriek j i
        (Set.disjoint_iff_inter_eq_empty.1 hij.disjoint.symm) F)
    (Functor.isZero_mapDerivedCategory_obj_rightDerivedFunctor_obj _ _ fun G ↦
      AdicSheaf.isZero_of_isZero_X (isZero_upperStar_lowerStar_of_disjoint _ i j hij.disjoint G.X))
    (Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory _ _
      (jointlyReflectIsomorphisms_adicUpperStar_of_isCompl l j i hij)) K

end Adic

end ProEtale

end AlgebraicGeometry

namespace AlgebraicGeometry.Etale

open Scheme

section Integral

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]
  [IsClosedImmersion i]

/-- Blueprint `prop-sf-open-closed-triangle-all-stages`, integral stage `𝒪_E`. -/
theorem existsUnique_distTriang_openClosed_boundedConstructibleIntegral
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (_hK : DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X K) :
    ∃! w, Pretriangulated.Triangle.mk
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction _ j).counit.app K)
      ((mapDerivedUpperStarLowerStarAdjunction _ i).unit.app K) w ∈ distTriang _ :=
  existsUnique_distTriang_openClosed _ j i hij.eq_compl K

end Integral

end AlgebraicGeometry.Etale
