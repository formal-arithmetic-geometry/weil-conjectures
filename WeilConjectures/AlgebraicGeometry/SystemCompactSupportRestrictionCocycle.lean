/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestrictionEvaluation
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.CategoryTheory.DiagramSiteRealization
public import WeilConjectures.AlgebraicGeometry.DirectImageScalarRestrictionCocycle
public import WeilConjectures.SixFunctors.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.SystemOpenRestrictionCoherence
import WeilConjectures.AlgebraicGeometry.SystemProperRestrictionCoherence
import WeilConjectures.AlgebraicGeometry.SystemRestrictionFiniteNormalization

/-! # Restriction cocycle for compact support on strict coefficient systems

Source: the coefficient-composition detail of compact-support finite-field independence;
Stacks 03CZ, 03DI, 03DJ, 070Y and 0D6E; Zheng Construction 4.1
(blueprint: lem-weil-system-compact-support-restriction-cocycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

variable {l : ℕ}

private theorem sequenceMap_app (W : Scheme.{u})
    {B C : Etale.SystemProjection.Coefficients.{u} l} (a : B.rings ⟶ C.rings)
    (U : (ℕ × W.ProEt)ᵒᵖ) :
    (sequenceMap W a).hom.app U =
      ((constantSheaf.{u, u + 1, u + 1, u + 2}
        (ProEt.topology W) CommRingCat.{u + 1}).map
          (a.app (op U.unop.1))).hom.app (op U.unop.2) := by
  exact (systemMap_existsUnique.{u + 1, u, u + 1} (ProEt.topology W)
    (VaryingRing.coefficients.{u} (levels B) W)
    (VaryingRing.coefficientTransition.{u} (levels B) (steps B) W)
    (VaryingRing.coefficients.{u} (levels C) W)
    (VaryingRing.coefficientTransition.{u} (levels C) (steps C) W)
    (fun n ↦ (constantSheaf.{u, u + 1, u + 1, u + 2}
      (ProEt.topology W) CommRingCat.{u + 1}).map (a.app (op n)))
    (fun n ↦ by
      dsimp only [VaryingRing.coefficientTransition]
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg
        ((constantSheaf.{u, u + 1, u + 1, u + 2}
          (ProEt.topology W) CommRingCat.{u + 1}).map)
        (a.naturality (homOfLE (Nat.le_succ n)).op).symm)).exists.choose_spec
          U.unop.1 (op U.unop.2)

private theorem sequenceMap_comp (W : Scheme.{u})
    {B C D : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings) :
    sequenceMap W (a ≫ b) = sequenceMap W a ≫ sequenceMap W b := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rw [sequenceMap_app]
  change _ = (sequenceMap W a).hom.app U ≫ (sequenceMap W b).hom.app U
  rw [sequenceMap_app, sequenceMap_app]
  simp

private theorem sequenceMap_id (W : Scheme.{u})
    (B : Etale.SystemProjection.Coefficients.{u} l) :
    sequenceMap W (𝟙 B.rings) = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rw [sequenceMap_app]
  simp
  rfl

private def restrictionIdentifications (l : ℕ) : RestrictionIdentifications.{u} l where
  comp W _B _C _D a b := SheafOfModules.systemScalarRestrictionComposition
    (sequenceMap W a) (sequenceMap W b) (sequenceMap W (a ≫ b))
    (sequenceMap_comp W a b)
  comp_sections _ _ _ _ _ _ _ _ _ := rfl
  unit W B := SheafOfModules.systemScalarRestrictionUnit
    (sequenceMap W (𝟙 B.rings)) (sequenceMap_id W B)
  unit_sections _ _ _ _ _ := rfl

/-- Restriction of coefficients commutes coherently with compact support on entire strict
systems. This supplies all normalized data; none of the structure fields is a hypothesis.

Source: the coefficient-composition detail of the compact-support finite-field independence
argument (blueprint: lem-weil-system-compact-support-restriction-cocycle); Stacks 03CZ,
03DI, 03DJ, 070Y, 0D6E; Zheng Construction 4.1.

Proof: form the varying-ring vertical sequence sites. Module-sheaf restriction is exact,
so localize its identity-on-sections composition and unit maps. For proper direct image,
the two factorizations of the same ringed diagram-topos morphism give a comparison by
unbounded derived pushforward composition. On a target-coefficient K-injective H and a
source-coefficient K-injective resolution v of its restriction, this is the inverse of
[p_*v] after the displayed quotient and exact-restriction identifications; restriction
need not preserve K-injectives. Normalized derived-comparison composition gives the
proper cocycle. For open extension, restriction preserves the presheaf formula, the
original module on the open and zero off it, together with all transitions. Abelian
sheafification and exact localization give its normalized comparison and cocycle. Paste
the open comparison with the proper comparison. Naturality of the latter moves the
second open comparison through it; the proper and open cocycles then give the displayed
compact-support cocycle. For identity coefficient maps the resolution can be identity
on K-injectives, giving the unit there, and naturality transports it to every derived
object. Finally the inverse proper comparison is the mate of the inverse-image square:
on K-injective representatives the triangle identity identifies this mate with [p_*v].
Evaluation preserves the specified units, counits and inverse-image squares, so that mate
evaluates to the finite normalized comparison. The same section identity handles the
open part. No equality of system morphisms is deduced from equality after evaluation. -/
theorem compactSupportRestrictionCocycle (l : ℕ) [Fact l.Prime]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p] :
    ∃ c : RestrictionIdentifications.{u} l,
      ∃ d : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l)
        (a : B.rings ⟶ C.rings), Comparison a j p,
        (∀ (B C D : Etale.SystemProjection.Coefficients.{u} l)
          (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings)
          (L : VaryingRing.Derived (levels D) (steps D) X),
          (support B j p).map ((c.rho X a b).hom.app L) ≫
              (d B D (a ≫ b)).iso.hom.app L =
            (d B C a).iso.hom.app ((derivedRestriction X b).obj L) ≫
              (derivedRestriction Y a).map ((d C D b).iso.hom.app L) ≫
              (c.rho Y a b).hom.app ((support D j p).obj L)) ∧
        (∀ (B : Etale.SystemProjection.Coefficients.{u} l)
          (L : VaryingRing.Derived (levels B) (steps B) X),
          (d B B (𝟙 B.rings)).iso.hom.app L ≫
              (c.derivedUnit Y B).hom.app ((support B j p).obj L) =
            (support B j p).map ((c.derivedUnit X B).hom.app L)) ∧
        (∀ (B C : Etale.SystemProjection.Coefficients.{u} l)
          (a : B.rings ⟶ C.rings), Nonempty (FiniteCompatibility (d B C a))) := by
  let c := restrictionIdentifications.{u} l
  obtain ⟨go, o, ho, hou⟩ := systemOpenRestrictionCoherence l j c
  obtain ⟨gp, q, hq, hqu⟩ := systemProperRestrictionCoherence l p c
  let d (B C : Etale.SystemProjection.Coefficients.{u} l) (a : B.rings ⟶ C.rings) :
      Comparison a j p :=
    { openSquare := go B C a
      properSquare := gp B C a
      openPart := o B C a
      properPart := q B C a }
  refine ⟨c, d, ?_, ?_, ?_⟩
  · intro B C D a b L
    have hn := (q B C a).iso.hom.naturality ((o C D b).derived.hom.app L)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    dsimp only [d, Comparison.iso, support, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Functor.comp_map]
    simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, ho B C D a b L]
    simp only [Functor.map_comp, Category.assoc]
    rw [hq B C D a b ((VaryingRing.J (levels D) (steps D) j).obj L)]
    rw [← reassoc_of% hn]
  · intro B L
    dsimp only [d, Comparison.iso, support, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Functor.comp_map]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    rw [hqu B, ← Functor.map_comp, hou B L]
  · intro B C a
    exact systemRestrictionFiniteNormalization l a j p (d B C a)

end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
