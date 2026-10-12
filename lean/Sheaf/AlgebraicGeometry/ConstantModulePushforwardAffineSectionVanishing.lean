/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity

/-! # Constant-module section vanishing at an inverse limit

Source: Stacks Project, Tags 09Z1 and 09YQ, degree-zero continuity.
(blueprint: lem-weil-pbc-constant-module-affine-section-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A section on an affine etale test scheme which vanishes at the limit already
vanishes at a later stage. This assertion concerns sections, not geometric germs.

Source: Stacks Project, Tag 09Z1, degree-zero injectivity, using Tag 09YQ.
(blueprint: lem-weil-pbc-constant-module-affine-section-vanishing).

Proof: Form the system E_j = U times_X D_j over U and its cone with vertex
U times_X Y. Pullback preserves this limit because I is cofiltered and hence
connected. The transition maps remain affine. Since U is affine and the structure
maps p_j are qcqs, every E_j is qcqs. Forget the coefficients to abelian groups.
The underlying abelian sheaf of a constant module sheaf is the constant underlying
abelian sheaf: the forgetful functor preserves colimits and finite limits and thus
commutes with sheafification. Identify these constant sheaves with the pullbacks
of the constant abelian sheaf G on U. The canonical comparison maps agree with
unitComparison under these identifications, by naturality of the constant-sheaf
pullback comparison with the adjunction unit and the pushforward composition
comparison. Apply exists_unitComparison_app_eq_zero_of_isLimit to E over U and
the terminal etale object of U. Its hypotheses hold since affine U is
quasi-separated and E_j are qcqs. This gives an arrow g:j -> i where the
restricted underlying abelian section is zero. Faithfulness of coefficient
forgetting reflects this equality as an equality of module sections.
No directed reindexing is needed: the section-continuity theorem already accepts
any small cofiltered category. Zero modules and empty fibre products satisfy the
same argument. -/
theorem exists_constantModulePushforward_affine_section_eq_zero
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : ∀ i, D.obj i ⟶ X)
    (hp : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ p j = p i)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, QuasiCompact (p i)] [∀ i : I, QuasiSeparated (p i)]
    {Y : Scheme.{u}} (ν : Y ⟶ X)
    (π : (Functor.const I).obj Y ⟶ D) (hπ : ∀ i, π.app i ≫ p i = ν)
    [QuasiCompact ν] [QuasiSeparated ν]
    (hc : IsLimit (Cone.mk Y π))
    (U : X.Etale) [IsAffine U.left] (i : I)
    (a : ((lowerStar (ModuleCat.{u + 1} Λ) (p i)).obj
      ((constantSheaf (D.obj i).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj M)).obj.obj (op U))
    (ha : (constantModulePushforwardMap Λ M (p i) ν (π.app i) (hπ i)).hom.app
      (op U) a = 0) :
    ∃ (j : I) (g : j ⟶ i),
      (constantModulePushforwardMap Λ M (p i) (p j) (D.map g) (hp g)).hom.app
        (op U) a = 0 := by sorry

end AlgebraicGeometry.Etale
