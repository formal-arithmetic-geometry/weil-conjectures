/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.SystemCompactSupportRestrictionEvaluation
import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.OpenIso
import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.OpenNormalized
import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.OpenEvaluation
import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.ProperEvaluation

/-! # Finite normalization of system coefficient restriction

Source: the coefficient-composition argument, step 7; Stacks 03DI, 070Y and 0D6E;
Zheng Construction 4.1 (blueprint: lem-sp-system-restriction-finite-normalization).

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

/-- Every section- and resolution-normalized system comparison has the prescribed
finite evaluations. This proves normalization by computation of mates, without using
faithfulness of derived evaluation.

Source: the coefficient-composition argument, step 7; Stacks 03DI, 070Y and 0D6E;
Zheng Construction 4.1 (blueprint: lem-sp-system-restriction-finite-normalization).

Proof: naturality of the constant-sheaf pullback isomorphism proves LevelComm for both
geometric maps. Use the ordinary section comparison for open extension at each level
and localize it; its summand adjunction gives openNormalized. Both system and level open
maps are the identity on the open summand and zero off it, so restrictionEvaluation and
evalJ identify their localized words, giving openEvaluation. For the proper comparison,
form the derived adjunction mate of the inverse-image coefficient square. On a
K-injective H and a K-injective resolution v of its restriction, expand this mate as
unit, inverse-image square, counit and the resolution map. The underived adjunction
triangle identity reduces it to the localized direct image of v. Thus it is the inverse
of d.properPart.iso by its normalization. K-injective representatives and naturality
extend that equality to the entire derived category. The specified evalP and evalG
are adjunction mates, and their unit/counit equations carry this mate word to its level
mate, with restrictionEvaluation identifying its vertical edges. The identical
K-injective computation at the level shows that the inverse level mate is levelProper,
whose unique derived-unit normalization is fixed by the ring-sheaf change adjunction.
Inverting the evaluated mate identity gives properEvaluation. These constructions give
every field of FiniteCompatibility, and handle identity and nonflat maps and empty
schemes without changing the argument. -/
theorem systemRestrictionFiniteNormalization (l : ℕ) [Fact l.Prime]
    {B C : Etale.SystemProjection.Coefficients.{u} l} (a : B.rings ⟶ C.rings)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (d : Comparison a j p) : Nonempty (FiniteCompatibility d) := by
  have hLevel : ∀ {U V : Scheme.{u}} (f : U ⟶ V), ∀ n : ℕ, LevelComm a f n := by
    intro U V f n
    unfold LevelComm levelMap
    change _ = (Scheme.proEtaleSheafInverseImage f CommRingCat).map _ ≫ _
    dsimp only [StrictTower.constantRingIso]
    simp only [asIso_hom]
    exact (Scheme.proEtaleConstantInverseImageMap_naturality f (a.app (op n))).symm
  have hOpen : ∀ n : ℕ, LevelComm a j n := hLevel j
  have hProper : ∀ n : ℕ, LevelComm a p n := hLevel p
  obtain ⟨o⟩ := finiteCompatibility_openIso l a j p d
  refine ⟨{
    openComm := hOpen
    properComm := hProper
    openIso := o
    openNormalized := finiteCompatibility_openNormalized l a j p d hOpen o
    openEvaluation := finiteCompatibility_openEvaluation l a j p d hOpen o
    properEvaluation := finiteCompatibility_properEvaluation l a j p d hProper
  }⟩

end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
