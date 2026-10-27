/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import Sheaf.Paper.P1KummerScalarEndpoints
import Sheaf.CategoryTheory.ExactDegreeZero
import Sheaf.Paper.P1KummerScalarEndpointExistence
import Sheaf.Paper.P1KummerScalarEndpointComposition
import Sheaf.Paper.P1KummerChernScalar

/-! # Derived scalar transitivity for the fixed projective-line Kummer arrow

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts; Stacks Project, Tags 03PL and 0D6D
(blueprint: lem-sp-p1-kummer-derived-scalar).

The endpoint records specify ordinary coefficient maps on constant and root sections,
and identify their derived maps by the actual scalar adjunction. The composition
isomorphism is the published adjunction-compatible composition comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


private theorem cachedModSheafify (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance
attribute [local instance] cachedModSheafify

private theorem conjugate_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (M : D ⥤ E) (K : C ⥤ E) (α : L ⋙ M ≅ K)
    {X Y : C} {U V : D} {P Q : E}
    (u : L.obj X ≅ U) (v : L.obj Y ≅ V)
    (u' : K.obj X ≅ P) (v' : K.obj Y ≅ Q)
    (a : M.obj U ≅ P) (b : M.obj V ≅ Q)
    (hu : M.map u.hom ≫ a.hom = α.hom.app X ≫ u'.hom)
    (hv : M.map v.hom ≫ b.hom = α.hom.app Y ≫ v'.hom)
    (c : X ⟶ Y) :
    M.map (u.inv ≫ L.map c ≫ v.hom) ≫ b.hom =
      a.hom ≫ u'.inv ≫ K.map c ≫ v'.hom := by
  apply (cancel_epi (M.map u.hom)).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← M.map_comp_assoc, Iso.hom_inv_id, M.map_id, Category.id_comp, hv]
  rw [reassoc_of% (α.hom.naturality c), reassoc_of% hu]
  simp only [Iso.hom_inv_id_assoc]

private theorem scalar_chern_naturality
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (N : ℕ)
    (hA : (N : A) = 0) (hB : (N : B) = 0) (hC : (N : C) = 0)
    (T : Scheme.{u}) (a : P1KummerScalarEndpoints φ N hA hB T)
    (b : P1KummerScalarEndpoints (ψ.comp φ) N hA hC T)
    (e : P1KummerScalarEndpoints ψ N hB hC T)
    (hu : (scalarExtension ψ T).map a.unitIso.hom ≫ e.unitIso.hom =
      (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology
        φ ψ (ψ.comp φ) rfl).hom.app (ordinaryFiniteUnit A T) ≫ b.unitIso.hom)
    (hv : (scalarExtension ψ T).map a.shiftedLineIso.hom ≫ e.shiftedLineIso.hom =
      (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology
        φ ψ (ψ.comp φ) rfl).hom.app ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≫
          b.shiftedLineIso.hom)
    (c : ordinaryFiniteUnit A T ⟶ (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) :
    (scalarExtension ψ T).map (a.chernImage c) ≫ e.shiftedLineIso.hom =
      e.unitIso.hom ≫ b.chernImage c := by
  exact conjugate_naturality (scalarExtension φ T) (scalarExtension ψ T)
    (scalarExtension (ψ.comp φ) T)
    (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    a.unitIso a.shiftedLineIso b.unitIso b.shiftedLineIso e.unitIso e.shiftedLineIso hu hv c

/-- Derived coefficient transitivity preserves the specified O(1) Kummer morphism.
All three endpoint records are fixed by ordinary generators and by the actual scalar
adjunction. The two component equations identify the published composition comparison
with multiplication and shifted balancing. The last equation is in the derived category.
Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts; Stacks 03PL and 0D6D
(blueprint: lem-sp-p1-kummer-derived-scalar).

Proof: choose the normalized endpoint records for the two residue maps and phi.
The residue map to B equals the composite residue map, by uniqueness of unital
maps from Z/N. The endpoint composition theorem gives the unit and shifted-line
component equations. The scalar Chern-class theorem gives the two specifications.
Apply naturality of the composition isomorphism to the fixed residue arrow and
cancel the endpoint inverse pairs to obtain the last equation.
-/
theorem p1KummerDerivedScalar (S : Scheme.{u}) [IsNoetherian S]
    (N : ℕ) (hN : 0 < N) (hS : IsUnit (N : Γ(S, ⊤)))
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (c : ordinaryFiniteUnit (p1KummerResidue.{u} N) (ProjectiveLine S) ⟶
      (ordinaryFiniteLine (p1KummerResidue.{u} N) N
        (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N) (ZMod.natCast_self N))
        (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec (p1KummerResidue.{u} N) N
        (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N) (ZMod.natCast_self N))
      S (ordinaryFiniteP1_isUnit N S hS) c) :
    ∃ (eA : P1KummerScalarEndpoints (p1KummerResidueMap N A hA) N
        (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N) (ZMod.natCast_self N)) hA
        (ProjectiveLine S))
      (eB : P1KummerScalarEndpoints (φ.comp (p1KummerResidueMap N A hA)) N
        (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N) (ZMod.natCast_self N)) hB
        (ProjectiveLine S))
      (e : P1KummerScalarEndpoints φ N hA hB
        (ProjectiveLine S)),
      ordinaryFiniteP1ChernSpec A N hA S (ordinaryFiniteP1_isUnit N S hS)
        (eA.chernImage c) ∧
      ordinaryFiniteP1ChernSpec B N hB S (ordinaryFiniteP1_isUnit N S hS)
        (eB.chernImage c) ∧
      ((scalarExtension φ (ProjectiveLine S)).map eA.unitIso.hom ≫ e.unitIso.hom =
        (ProEtale.pbcFixedScalarExtensionComp (ProjectiveLine S).smallEtaleTopology
          (p1KummerResidueMap N A hA) φ (φ.comp (p1KummerResidueMap N A hA)) rfl).hom.app
            (ordinaryFiniteUnit (p1KummerResidue.{u} N) (ProjectiveLine S)) ≫ eB.unitIso.hom) ∧
      ((scalarExtension φ (ProjectiveLine S)).map eA.shiftedLineIso.hom ≫
          e.shiftedLineIso.hom =
        (ProEtale.pbcFixedScalarExtensionComp (ProjectiveLine S).smallEtaleTopology
          (p1KummerResidueMap N A hA) φ (φ.comp (p1KummerResidueMap N A hA)) rfl).hom.app
            ((ordinaryFiniteLine (p1KummerResidue.{u} N) N
              (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N) (ZMod.natCast_self N))
              (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫ eB.shiftedLineIso.hom) ∧
      ((scalarExtension φ (ProjectiveLine S)).map (eA.chernImage c) ≫
          e.shiftedLineIso.hom = e.unitIso.hom ≫ eB.chernImage c) := by
  classical
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨eA⟩ := p1KummerScalarEndpointExistence (ProjectiveLine S) N hN
    (ordinaryFiniteP1_isUnit N S hS) (p1KummerResidue.{u} N) A
    (p1KummerResidueMap N A hA)
    (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N) (ZMod.natCast_self N)) hA
  obtain ⟨eB⟩ := p1KummerScalarEndpointExistence (ProjectiveLine S) N hN
    (ordinaryFiniteP1_isUnit N S hS) (p1KummerResidue.{u} N) B
    (φ.comp (p1KummerResidueMap N A hA))
    (congrArg (ULift.up : ZMod N → p1KummerResidue.{u} N) (ZMod.natCast_self N)) hB
  obtain ⟨e⟩ := p1KummerScalarEndpointExistence (ProjectiveLine S) N hN
    (ordinaryFiniteP1_isUnit N S hS) A B φ hA hB
  obtain ⟨hu, hv⟩ := p1KummerScalarEndpointComposition eA eB e
  refine ⟨eA, eB, e, p1KummerChernScalar _ eA c hc,
    p1KummerChernScalar _ eB c hc, hu, hv, ?_⟩
  exact scalar_chern_naturality _ _ _ _ _ _ _ eA eB e hu hv c

end AlgebraicGeometry.Etale
