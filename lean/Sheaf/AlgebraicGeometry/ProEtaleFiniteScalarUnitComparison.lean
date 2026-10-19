/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleUnderlying
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Finite scalar restriction and pro-etale adjunction units

Source: Stacks Project, Tag 03D3, lemma-adjoint-push-pull-modules; coefficient-naturality
refinement in the blueprint (blueprint: lem-exc-proetale-finite-scalar-unit-comparison).
The inverse image is the recorded transported-action functor, including for noncommutative
rings. The unit is normalized by its actual small-model module Kan-extension unit.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {R S : Type (u + 1)} [Ring R] [Finite R] [TopologicalSpace R] [DiscreteTopology R]
  [Ring S] [Finite S] [TopologicalSpace S] [DiscreteTopology S] (φ : R →+* S)

/-- Pointwise coefficient change on the defining continuous functions.
Source: blueprint coefficient maps, Stacks Tag 09A5
(blueprint: lem-exc-proetale-finite-scalar-unit-comparison). -/
noncomputable def finiteScalarPresheafMap (T : Scheme.{u}) :
    finiteCoefficientPresheaf T R ⟶ finiteCoefficientPresheaf T S where
  app W := RingCat.ofHom
    { toFun := fun s ↦
        ⟨fun x ↦ φ (s x), (continuous_of_discreteTopology : Continuous φ).comp s.continuous⟩
      map_one' := by ext x; exact φ.map_one
      map_mul' := fun a b ↦ by ext x; exact φ.map_mul (a x) (b x)
      map_zero' := by ext x; exact φ.map_zero
      map_add' := fun a b ↦ by ext x; exact φ.map_add (a x) (b x) }
  naturality _ _ a := by ext s; rfl

/-- Sheafify pointwise composition with the unital ring homomorphism.
Source: blueprint coefficient maps, Stacks Tags 09A5 and 00W1
(blueprint: lem-exc-proetale-finite-scalar-unit-comparison). -/
noncomputable def finiteScalarRingMap (T : Scheme.{u}) :
    finiteCoefficientRingSheaf T R ⟶ finiteCoefficientRingSheaf T S :=
  (presheafToSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).map
    (finiteScalarPresheafMap φ T)

/-- The specified restriction of scalars leaves the underlying abelian sheaf unchanged.
Source: blueprint P_T; Stacks, Modules on Sites, restriction of scalars
(blueprint: lem-exc-proetale-finite-scalar-unit-comparison). -/
noncomputable def finiteScalarRestriction (T : Scheme.{u}) :
    FiniteCoefficientModules T S ⥤ FiniteCoefficientModules T R :=
  SheafOfModules.restrictScalars (finiteScalarRingMap φ T)

/-- Sectionwise direct image with action through the adjunct of the canonical c_f.
This uses the recorded noncommutative coefficient map rho without a CommRing assumption.
Source: blueprint f_{C,*}; Stacks Tags 03D1 and 03D3
(blueprint: lem-exc-proetale-finite-scalar-unit-comparison). -/
noncomputable def finiteScalarModuleDirectImage (C : Type (u + 1)) [Ring C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C] :
    FiniteCoefficientModules X C ⥤ FiniteCoefficientModules Y C :=
  SheafOfModules.pushforward.{u + 1} (F := Scheme.proEtaleBaseChange f)
    (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology X)
    (finiteCoefficientDirectImageMap f C)

/-- The actual module Kan-extension unit section, transported back from the small model.
Restriction through c_f inverse changes only its scalar action. This section fixes the
adjunction used below, so an arbitrarily twisted adjunction is excluded.
Source: Stacks Tag 03D3 and the blueprint's specified lifted adjunction
(blueprint: lem-exc-proetale-finite-scalar-unit-comparison). -/
noncomputable def finiteScalarModuleUnitSection (C : Type (u + 1)) [Ring C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    (N : FiniteCoefficientModules Y C) (W : Y.ProEtᵒᵖ) (m : N.val.obj W) :
    ((finiteCoefficientModulePullback f C).obj N).val.obj
      ((Scheme.proEtaleBaseChange f).op.obj W) :=
  (((SheafOfModules.pullbackPushforwardAdjunction
    (finiteCoefficientModelRingUnit f C)).unit.app
      ((Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf Y C)).obj N)).val.app
        ((AsSmall.up : Y.ProEt ⥤ Scheme.proEtaleSiteModel Y).op.obj W)) m

private theorem finiteScalarRingMap_directImage :
    finiteScalarRingMap φ Y ≫ finiteCoefficientDirectImageMap f S =
      finiteCoefficientDirectImageMap f R ≫
        (Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).map
          (finiteScalarRingMap φ X) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    RingCat.{u + 1}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change toSheafify _ _ ≫ (finiteScalarRingMap φ Y).hom ≫
      (finiteCoefficientDirectImageMap f S).hom =
    toSheafify _ _ ≫ (finiteCoefficientDirectImageMap f R).hom ≫ _
  change toSheafify _ _ ≫ sheafifyMap _ (finiteScalarPresheafMap φ Y) ≫ _ = _
  rw [← Category.assoc, ← toSheafify_naturality]
  have h (C : Type (u + 1)) [Ring C] [Finite C]
      [TopologicalSpace C] [DiscreteTopology C] :
      toSheafify (Scheme.ProEt.topology Y) (finiteCoefficientPresheaf Y C) ≫
        (finiteCoefficientDirectImageMap f C).hom =
      finiteCoefficientDirectImagePresheafMap f C := by
    exact ((sheafificationAdjunction (Scheme.ProEt.topology Y)
      RingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  rw [Category.assoc, h S, ← Category.assoc, h R]
  ext W x
  have hn := congrArg (fun t ↦ t.app ((Scheme.proEtaleBaseChange f).op.obj W))
    (toSheafify_naturality (Scheme.ProEt.topology X) (finiteScalarPresheafMap φ X))
  exact RingHom.congr_fun (congrArg RingCat.Hom.hom hn)
    (x.comp ⟨(pullback.fst W.unop.hom f).continuous.connectedComponentsMap,
      (pullback.fst W.unop.hom f).continuous.connectedComponentsMap_continuous⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def scalarDirectImageComparison :
    finiteScalarModuleDirectImage f S ⋙ finiteScalarRestriction φ Y ≅
      finiteScalarRestriction φ X ⋙ finiteScalarModuleDirectImage f R :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W ↦
        LinearEquiv.toModuleIso
          (X₁ := (((finiteScalarModuleDirectImage f S ⋙
            finiteScalarRestriction φ Y).obj M).val.obj W))
          (X₂ := (((finiteScalarRestriction φ X ⋙
            finiteScalarModuleDirectImage f R).obj M).val.obj W))
          { __ := AddEquiv.refl _
            map_smul' := fun r m ↦ by
              change @SMul.smul ((finiteCoefficientRingSheaf X S).obj.obj
                ((Scheme.proEtaleBaseChange f).op.obj W))
                (M.val.obj ((Scheme.proEtaleBaseChange f).op.obj W)) inferInstance
                ((finiteCoefficientDirectImageMap f S).hom.app W
                ((finiteScalarRingMap φ Y).hom.app W r)) m =
                @SMul.smul ((finiteCoefficientRingSheaf X S).obj.obj
                  ((Scheme.proEtaleBaseChange f).op.obj W))
                  (M.val.obj ((Scheme.proEtaleBaseChange f).op.obj W)) inferInstance
                  ((finiteScalarRingMap φ X).hom.app ((Scheme.proEtaleBaseChange f).op.obj W)
                    ((finiteCoefficientDirectImageMap f R).hom.app W r)) m
              have h := congrArg (fun t ↦ t.hom.app W)
                (finiteScalarRingMap_directImage f φ)
              exact congrArg (fun a : (finiteCoefficientRingSheaf X S).obj.obj
                ((Scheme.proEtaleBaseChange f).op.obj W) ↦ a •
                  (show M.val.obj ((Scheme.proEtaleBaseChange f).op.obj W) from m))
                (RingHom.congr_fun (congrArg RingCat.Hom.hom h) r) })
        (fun _ _ _ ↦ by ext m; rfl))) (by intro M N g; ext W m; rfl)

private theorem scalarDirectImageComparison_apply
    (M : FiniteCoefficientModules X S) (W : Y.ProEtᵒᵖ)
    (m : M.val.obj ((Scheme.proEtaleBaseChange f).op.obj W)) :
    ((scalarDirectImageComparison f φ).hom.app M).val.app W m = m := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarModuleAdjunction_normalized
    (C : Type (u + 1)) [Ring C] [Finite C] [TopologicalSpace C] [DiscreteTopology C] :
    ∃ adj : finiteCoefficientModulePullback f C ⊣ finiteScalarModuleDirectImage f C,
      ∀ (N : FiniteCoefficientModules Y C) (W : Y.ProEtᵒᵖ) (m : N.val.obj W),
        (adj.unit.app N).val.app W m = finiteScalarModuleUnitSection f C N W m := by
  obtain ⟨adj, h, _⟩ := finiteModuleAdjunction_existsUnique f C
  refine ⟨adj, ?_⟩
  intro N W m
  obtain ⟨g, hg, ht⟩ := h N ((finiteCoefficientModulePullback f C).obj N) (𝟙 _)
  have ht' := ht W m
  rw [Adjunction.homEquiv_unit] at ht'
  change (adj.unit.app N).val.app W m =
    g.val.app _ (finiteScalarModuleUnitSection f C N W m) at ht'
  exact ht'.trans (hg _ _)

@[irreducible] private noncomputable def scalarPullbackMate
    (adjR : finiteCoefficientModulePullback f R ⊣ finiteScalarModuleDirectImage f R)
    (adjS : finiteCoefficientModulePullback f S ⊣ finiteScalarModuleDirectImage f S) :
    finiteScalarRestriction φ Y ⋙ finiteCoefficientModulePullback f R ⟶
      finiteCoefficientModulePullback f S ⋙ finiteScalarRestriction φ X :=
  ((mateEquiv adjS adjR).symm
    (TwoSquare.mk _ _ _ _ (scalarDirectImageComparison f φ).hom)).natTrans

private theorem scalarPullbackMate_unit
    (adjR : finiteCoefficientModulePullback f R ⊣ finiteScalarModuleDirectImage f R)
    (adjS : finiteCoefficientModulePullback f S ⊣ finiteScalarModuleDirectImage f S)
    (N : FiniteCoefficientModules Y S) :
    (finiteScalarRestriction φ Y).map (adjS.unit.app N) ≫
      (scalarDirectImageComparison f φ).hom.app ((finiteCoefficientModulePullback f S).obj N) =
      adjR.unit.app ((finiteScalarRestriction φ Y).obj N) ≫
        (finiteScalarModuleDirectImage f R).map ((scalarPullbackMate f φ adjR adjS).app N) := by
  rw [scalarPullbackMate]
  exact unit_mateEquiv_symm adjS adjR
    (TwoSquare.mk _ _ _ _ (scalarDirectImageComparison f φ).hom) N

set_option maxHeartbeats 400000 in
-- The comparison proof synthesizes the transported module and sheaf instances.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite scalar restriction commutes with the specified pullback and direct image,
by the identity on underlying abelian sheaves, and preserves their actual unit.
The auxiliary e_R and e_S express the canonical identifications of the recorded
small-model module pullbacks with abelian inverse image. The first two clauses fix
both module adjunction units on the actual Kan-extension unit sections. The next two
clauses identify these sections with the abelian adjunction unit; thus the displayed
comparisons are identities in exactly the constructions of the node.

Source: Stacks Project, Tag 03D3, lemma-adjoint-push-pull-modules
(blueprint: lem-exc-proetale-finite-scalar-unit-comparison).
Proof:
1. By prop-weil-pbc-proetale-constant-ring-map, c_f is the adjunct of rho and is
   invertible for both finite rings. The coefficient square commutes: the adjuncts
   agree on constant sections by pointwise composition with φ. Every continuous
   function is constant on an open cover; glue and use sheafification to extend the
   equality. This also identifies inverse image of the restricted action, since
   inverse image preserves finite products (def-weil-proetale-inverse-image).
2. The module Kan-extension adjunction, transported to the original site and through
   c_f inverse, lifts the abelian adjunction of Stacks 03D3. Its unit is precisely
   finiteScalarModuleUnitSection. Forgetting modules identifies its pullback with
   abelian inverse image by the unique unit-preserving identification e_C. This is
   the transported action in prop-weil-pbc-proetale-constant-exact.
3. The coefficient square from step 1 makes identity on abelian inverse images
   R_X-linear, giving alpha, naturally and with identity inverse. For direct image,
   both sectionwise R_Y-actions factor through the same map rho^S φ_Y = f_*(φ_X) rho^R;
   identity on sections is linear and gives beta and its inverse. These are precisely
   restriction of scalars and linear morphisms in def-pc-sheaf-restrict-scalars and
   def-weil-sheaf-of-modules-category.
4. Under e_R and e_S, both normalized module units are the same abelian adjunction
   unit. Alpha and beta are identities on these underlying sheaves. The underlying
   map of the composite in the last clause is therefore that unit. Faithfulness of
   forgetting module structure gives the equation of module morphisms. Neither
   commutativity, flatness nor any geometric hypothesis is used. -/
theorem finiteScalarUnitComparison :
    ∃ (adjR : finiteCoefficientModulePullback f R ⊣ finiteScalarModuleDirectImage f R)
      (adjS : finiteCoefficientModulePullback f S ⊣ finiteScalarModuleDirectImage f S)
      (eR : finiteCoefficientModulePullback f R ⋙
          SheafOfModules.toSheaf (finiteCoefficientRingSheaf X R) ≅
        SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y R) ⋙
          Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1})
      (eS : finiteCoefficientModulePullback f S ⋙
          SheafOfModules.toSheaf (finiteCoefficientRingSheaf X S) ≅
        SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y S) ⋙
          Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1})
      (α : finiteCoefficientModulePullback f S ⋙ finiteScalarRestriction φ X ≅
        finiteScalarRestriction φ Y ⋙ finiteCoefficientModulePullback f R)
      (β : finiteScalarModuleDirectImage f S ⋙ finiteScalarRestriction φ Y ≅
        finiteScalarRestriction φ X ⋙ finiteScalarModuleDirectImage f R),
      (∀ (N : FiniteCoefficientModules Y R) (W : Y.ProEtᵒᵖ) (m : N.val.obj W),
        (adjR.unit.app N).val.app W m = finiteScalarModuleUnitSection f R N W m) ∧
      (∀ (N : FiniteCoefficientModules Y S) (W : Y.ProEtᵒᵖ) (m : N.val.obj W),
        (adjS.unit.app N).val.app W m = finiteScalarModuleUnitSection f S N W m) ∧
      (∀ (N : FiniteCoefficientModules Y R),
        (SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y R)).map (adjR.unit.app N) ≫
          (Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map (eR.hom.app N) =
        (Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
          ((SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y R)).obj N)) ∧
      (∀ (N : FiniteCoefficientModules Y S),
        (SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y S)).map (adjS.unit.app N) ≫
          (Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map (eS.hom.app N) =
        (Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
          ((SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y S)).obj N)) ∧
      (∀ (N : FiniteCoefficientModules Y S) (W : X.ProEtᵒᵖ)
        (m : ((finiteCoefficientModulePullback f S).obj N).val.obj W),
        (eR.hom.app ((finiteScalarRestriction φ Y).obj N)).hom.app W
          ((α.hom.app N).val.app W m) = (eS.hom.app N).hom.app W m) ∧
      (∀ (M : FiniteCoefficientModules X S) (W : Y.ProEtᵒᵖ)
        (m : M.val.obj ((Scheme.proEtaleBaseChange f).op.obj W)),
        (β.hom.app M).val.app W m = m) ∧
      ∀ N : FiniteCoefficientModules Y S,
        (finiteScalarRestriction φ Y).map (adjS.unit.app N) ≫
          β.hom.app ((finiteCoefficientModulePullback f S).obj N) ≫
          (finiteScalarModuleDirectImage f R).map (α.hom.app N) =
        adjR.unit.app ((finiteScalarRestriction φ Y).obj N) := by
  obtain ⟨adjR, hR⟩ := scalarModuleAdjunction_normalized f R
  obtain ⟨adjS, hS⟩ := scalarModuleAdjunction_normalized f S
  obtain ⟨eR, heR⟩ := finiteCoefficientModuleUnderlying_exists f R
  obtain ⟨eS, heS⟩ := finiteCoefficientModuleUnderlying_exists f S
  have huR (N : FiniteCoefficientModules Y R) :
      (SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y R)).map (adjR.unit.app N) ≫
        (Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map (eR.hom.app N) =
      (Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
        ((SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y R)).obj N) := by
    ext W m
    change (eR.hom.app N).hom.app ((Scheme.proEtaleBaseChange f).op.obj W)
      ((adjR.unit.app N).val.app W m) = _
    rw [hR]
    exact heR N W m
  have huS (N : FiniteCoefficientModules Y S) :
      (SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y S)).map (adjS.unit.app N) ≫
        (Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map (eS.hom.app N) =
      (Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
        ((SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y S)).obj N) := by
    ext W m
    change (eS.hom.app N).hom.app ((Scheme.proEtaleBaseChange f).op.obj W)
      ((adjS.unit.app N).val.app W m) = _
    rw [hS]
    exact heS N W m
  let β := scalarDirectImageComparison f φ
  let δ := scalarPullbackMate f φ adjR adjS
  have hd N : (finiteScalarRestriction φ Y).map (adjS.unit.app N) ≫
      β.hom.app ((finiteCoefficientModulePullback f S).obj N) =
      adjR.unit.app ((finiteScalarRestriction φ Y).obj N) ≫
        (finiteScalarModuleDirectImage f R).map (δ.app N) :=
    scalarPullbackMate_unit f φ adjR adjS N
  have heδ (N : FiniteCoefficientModules Y S) :
      (SheafOfModules.toSheaf (finiteCoefficientRingSheaf X R)).map (δ.app N) ≫
        eS.hom.app N = eR.hom.app ((finiteScalarRestriction φ Y).obj N) := by
    apply (cancel_epi (eR.inv.app ((finiteScalarRestriction φ Y).obj N))).1
    apply ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).injective
    ext W m
    change N.val.obj W at m
    have hr := congrArg (fun q ↦ q.hom.app W m)
      (huR ((finiteScalarRestriction φ Y).obj N))
    have hs := congrArg (fun q ↦ q.hom.app W m) (huS N)
    have hd' := congrArg (fun q ↦ q.val.app W m) (hd N)
    let V := (Scheme.proEtaleBaseChange f).op.obj W
    have hi : (eR.inv.app ((finiteScalarRestriction φ Y).obj N)).hom.app V
        (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
          ((SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y R)).obj
            ((finiteScalarRestriction φ Y).obj N))).hom.app W m) =
        (adjR.unit.app ((finiteScalarRestriction φ Y).obj N)).val.app W m := by
      erw [← hr]
      exact ConcreteCategory.congr_hom
        (congrArg (fun q ↦ q.hom.app V)
          (eR.hom_inv_id_app ((finiteScalarRestriction φ Y).obj N))) _
    change (eS.hom.app N).hom.app V ((δ.app N).val.app V
      ((eR.inv.app ((finiteScalarRestriction φ Y).obj N)).hom.app V _)) =
      (eR.hom.app ((finiteScalarRestriction φ Y).obj N)).hom.app V
        ((eR.inv.app ((finiteScalarRestriction φ Y).obj N)).hom.app V _)
    erw [hi]
    change (adjS.unit.app N).val.app W m =
      (δ.app N).val.app V
        ((adjR.unit.app ((finiteScalarRestriction φ Y).obj N)).val.app W m) at hd'
    exact (congrArg ((eS.hom.app N).hom.app V) hd'.symm).trans (hs.trans hr.symm)
  have hδ (N : FiniteCoefficientModules Y S) : IsIso (δ.app N) := by
    have : IsIso ((SheafOfModules.toSheaf (finiteCoefficientRingSheaf X R)).map
        (δ.app N)) := IsIso.of_isIso_fac_right
          (f := eS.hom.app N)
          (g := (SheafOfModules.toSheaf (finiteCoefficientRingSheaf X R)).map (δ.app N))
          (h := eR.hom.app ((finiteScalarRestriction φ Y).obj N)) (heδ N)
    exact isIso_of_reflects_iso _
      (SheafOfModules.toSheaf (finiteCoefficientRingSheaf X R))
  have (N : FiniteCoefficientModules Y S) : IsIso (δ.app N) := hδ N
  have : IsIso δ := NatIso.isIso_of_isIso_app δ
  let α := (asIso δ).symm
  refine ⟨adjR, adjS, eR, eS, α, β, hR, hS, huR, huS, ?_, ?_, ?_⟩
  · intro N W m
    have hh := heδ N
    have hh' := congrArg (fun q ↦ q.hom.app W ((α.hom.app N).val.app W m)) hh
    have hc : (δ.app N).val.app W ((α.hom.app N).val.app W m) = m :=
      congrArg (fun q ↦ q.val.app W m) ((asIso δ).inv_hom_id_app N)
    exact hh'.symm.trans (congrArg ((eS.hom.app N).hom.app W) hc)
  · exact scalarDirectImageComparison_apply f φ
  · intro N
    calc
      (finiteScalarRestriction φ Y).map (adjS.unit.app N) ≫
          β.hom.app ((finiteCoefficientModulePullback f S).obj N) ≫
          (finiteScalarModuleDirectImage f R).map (α.hom.app N) =
          (adjR.unit.app ((finiteScalarRestriction φ Y).obj N) ≫
            (finiteScalarModuleDirectImage f R).map (δ.app N)) ≫
            (finiteScalarModuleDirectImage f R).map (α.hom.app N) := by
              simpa only [Category.assoc] using
                congrArg (fun z ↦ z ≫ (finiteScalarModuleDirectImage f R).map
                  (α.hom.app N)) (hd N)
      _ = adjR.unit.app ((finiteScalarRestriction φ Y).obj N) ≫
          (finiteScalarModuleDirectImage f R).map (δ.app N ≫ α.hom.app N) := by
            rw [Functor.map_comp, Category.assoc]
      _ = adjR.unit.app ((finiteScalarRestriction φ Y).obj N) := by
            change adjR.unit.app _ ≫ (finiteScalarModuleDirectImage f R).map
              ((asIso δ).hom.app N ≫ (asIso δ).inv.app N) = _
            rw [Iso.hom_inv_id_app]
            simp

end AlgebraicGeometry.ProEtale
