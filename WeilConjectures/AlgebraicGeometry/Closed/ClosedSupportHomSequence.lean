/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.ConstructibleSheaf.Defs

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# The closed-support Hom sequence

The ordinary injective-sheaf exact sequence used in the derived closed-support comparison.
-/

@[expose] public section

attribute [local instance 200000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 200000] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The standard sheafification property, named before constructing the support maps.
Source: Stacks, Tag 00W1 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportEtaleHasSheafify (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance

attribute [local instance 200000] closedSupportEtaleHasSheafify

/-- The same weak sheafification instance, with its proof fixed once on the site.
Source: Stacks, Tag 00W1 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportEtaleHasWeakSheafify (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance

attribute [local instance 200000] closedSupportEtaleHasWeakSheafify

/-- Existence of the standard global-section adjunction, named once on the site.
Source: Stacks, Tag 009F (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportEtaleHasGlobalSections (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasGlobalSectionsFunctor T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance

attribute [local instance 200000] closedSupportEtaleHasGlobalSections

/-- The canonical abelian structure, with pointwise addition on sheaf morphisms exposed.
Source: Stacks, Tag 03DA (blueprint: new-lem-amb-closed-support-hom-sequence). -/
@[instance_reducible]
noncomputable def closedSupportEtaleAbelian (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Abelian (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  { (inferInstance : Abelian (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) with
    toPreadditive := @Preadditive.fullSubcategory _ _
      (CategoryTheory.functorCategoryPreadditive (C := T.Etaleᵒᵖ)
        (D := ModuleCat.{u + 1} A)) _ }

attribute [local instance 200000] closedSupportEtaleAbelian

/-- The existing linear structure on module sheaves, named for use in Hom functors.
Source: Stacks, Tag 03DA (blueprint: new-lem-amb-closed-support-hom-sequence). -/
@[instance_reducible]
noncomputable def closedSupportEtaleLinear (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Linear A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance

private lemma restriction_unit_formula
    {C D E : Type*} [Category C] [Category D] [Category E]
    (U : C ⥤ D) (L : D ⥤ C) (B : C ⥤ E) (G : D ⥤ E)
    (adj : U ⊣ L) (b : L ⋙ B ≅ G) {P : C} {PV : D} {M : E}
    (c : U.obj P ≅ PV) (ηT : M ⟶ B.obj P) (ηV : M ⟶ G.obj PV)
    (h : ηT ≫ B.map (adj.unit.app P ≫ L.map c.hom) ≫ b.hom.app PV = ηV)
    {J : C} (f : P ⟶ J) :
    ηT ≫ B.map f ≫ B.map (adj.unit.app J) ≫ b.hom.app (U.obj J) =
      ηV ≫ G.map (c.inv ≫ U.map f) := by
  have hb : ηT ≫ B.map (adj.unit.app P) ≫ b.hom.app (U.obj P) =
      ηV ≫ G.map c.inv := by
    apply (cancel_mono (G.map c.hom)).mp
    simp only [Category.assoc, ← G.map_comp, c.inv_hom_id, Functor.map_id,
      Category.comp_id]
    rw [← b.hom.naturality]
    dsimp only [Functor.comp_map]
    rw [← B.map_comp_assoc]
    exact h
  have hn : f ≫ adj.unit.app J = adj.unit.app P ≫ L.map (U.map f) :=
    adj.unit.naturality f
  rw [← B.map_comp_assoc, hn, B.map_comp, Category.assoc]
  have hbn : B.map (L.map (U.map f)) ≫ b.hom.app (U.obj J) =
      b.hom.app (U.obj P) ≫ G.map (U.map f) := b.hom.naturality (U.map f)
  rw [hbn, reassoc_of% hb, G.map_comp]

end AlgebraicGeometry.Etale

attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasWeakSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasGlobalSections
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleAbelian
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleLinear

namespace CategoryTheory
/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def adjunctionHomLinearEquiv
    (R : Type*) [Ring R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Linear R]
    (adj : F ⊣ G) (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) where
  __ := adj.homAddEquiv X Y
  map_smul' r f := by
    change adj.unit.app X ≫ G.map (r • f) = r • (adj.unit.app X ≫ G.map f)
    rw [Functor.map_smul, Linear.comp_smul]

end CategoryTheory

namespace AlgebraicGeometry.Etale
/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def rankOneSectionsEquiv (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) ≃ₗ[A]
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj J := by
  let adj := constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  have : ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (op (⊤_ T.Etale))).Linear A := adj.right_adjoint_linear
  let e : (((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) ≃ₗ[A]
      (ModuleCat.of A A ⟶ ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (op (⊤_ T.Etale))).obj J) :=
    CategoryTheory.adjunctionHomLinearEquiv A adj (ModuleCat.of A A) J
  exact (e.trans (ModuleCat.homLinearEquiv.trans
    (LinearMap.ringLmapEquivSelf A A _))).trans
      ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).app J).symm.toLinearEquiv

/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
lemma rankOneSectionsEquiv_naturality (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) {J J' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (k : J ⟶ J') (f : ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) :
    rankOneSectionsEquiv A T J' (f ≫ k) =
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).map k
        (rankOneSectionsEquiv A T J f) := by
  change (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).inv.app J'
      (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).homEquiv _ _ (f ≫ k)) (1 : A)) =
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).map k
      ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).inv.app J
        (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
          terminalIsTerminal).homEquiv _ _ f) (1 : A)))
  rw [Adjunction.homEquiv_naturality_right]
  exact congrArg (fun g ↦ g
    (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).homEquiv _ _ f) (1 : A)))
    ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.naturality k)

private lemma unit_app_upperStarConstantSheafIso (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T) (a : ModuleCat.{u + 1} A) :
    (constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).unit.app a ≫
      ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (op (⊤_ T.Etale))).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).unit.app _ ≫
          (lowerStar (ModuleCat.{u + 1} A) v).map
            ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).hom.app a)) ≫
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v).hom.app _ =
    (constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).unit.app a := by
  have := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).comp (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v)).ofNatIsoRight
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v))
    (constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal) a
  rw [Adjunction.homEquiv_unit] at this
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at this
  rw [← this, Scheme.upperStarConstantSheafIso]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v).hom.naturality]
  rfl

/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
lemma rankOneSections_restriction (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T)
    (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) :
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J
      (rankOneSectionsEquiv A T J f) =
    rankOneSectionsEquiv A V ((upperStar (ModuleCat.{u + 1} A) v).obj J)
      (((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
        (ModuleCat.of A A)).inv ≫ (upperStar (ModuleCat.{u + 1} A) v).map f) := by
  let P := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (ModuleCat.of A A)
  let U := upperStar (ModuleCat.{u + 1} A) v
  let B := (sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (op (⊤_ T.Etale))
  let C := (sheafSections V.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (op (⊤_ V.Etale))
  let b := lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v
  let c := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
    (ModuleCat.of A A)
  let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).unit
  let ηT := (constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).unit.app (ModuleCat.of A A)
  let ηV := (constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).unit.app (ModuleCat.of A A)
  have hmap : ηT ≫ B.map f ≫ B.map (η.app J) ≫ b.hom.app (U.obj J) =
      ηV ≫ C.map (c.inv ≫ U.map f) :=
    CategoryTheory.restriction_unit_formula U (lowerStar (ModuleCat.{u + 1} A) v) B C
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v) b c ηT ηV
        (unit_app_upperStarConstantSheafIso A v (ModuleCat.of A A)) f
  let eT := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal
  let eV := Sheaf.ΓNatIsoSheafSections V.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal
  have hr : (ηT ≫ B.map f ≫ eT.inv.app J) ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J =
      ηV ≫ C.map (c.inv ≫ U.map f) ≫ eV.inv.app (U.obj J) := by
    change (ηT ≫ B.map f ≫ eT.inv.app J) ≫
      (eT.hom.app J ≫ B.map (η.app J) ≫ b.hom.app (U.obj J) ≫
        eV.inv.app (U.obj J)) = _
    simp only [Category.assoc, eT.inv_hom_id_app_assoc]
    rw [reassoc_of% hmap]
  change ((ηT ≫ B.map f ≫ eT.inv.app J) ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) (1 : A) =
    (ηV ≫ C.map (c.inv ≫ U.map f) ≫ eV.inv.app (U.obj J)) (1 : A)
  exact congrArg (fun g ↦ g (1 : A)) hr

/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
private lemma linearHomShortComplex_shortExact (S : ShortComplex C) (hS : S.ShortExact)
    (J : C) [Injective J] : (linearHomShortComplex R S J).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro y
    constructor
    · intro h
      obtain ⟨x, hx⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel y h
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      change S.f ≫ S.g ≫ x = 0
      rw [← Category.assoc, S.zero, zero_comp]
  · intro x y hxy
    exact (cancel_epi S.g).1 hxy
  · intro z
    exact ⟨Injective.factorThru z S.f, Injective.comp_factorThru z S.f⟩

/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
private noncomputable def linearHomShortComplex (S : ShortComplex C) (J : C) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (((linearCoyoneda R C).map S.g.op).app J)
    (((linearCoyoneda R C).map S.f.op).app J) (by
      ext x
      change S.f ≫ S.g ≫ x = 0
      rw [← Category.assoc, S.zero, zero_comp])

end AlgebraicGeometry.Etale

namespace CategoryTheory
universe v u' w
variable {C : Type u'} [Category.{v} C] [Abelian C]
  (R : Type w) [Ring R] [Linear R C]
end CategoryTheory

namespace AlgebraicGeometry.Etale
/-- The closed constant sheaf from which supported Hom is taken.
Source: Stacks, Tag 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def closedSupportHomSource (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (lowerStar (ModuleCat.{u + 1} A) i).obj
    ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))

/-- The ordinary Hom functor used by the canonical closed-support sequence.
Source: Stacks, Tag 0A45 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def closedSupportHomFunctor (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  (linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
    (op (closedSupportHomSource A i))

/-- The closed-support Hom functor is additive.
Source: Stacks, Tag 0A45 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
instance closedSupportHomFunctor_additive (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) : (closedSupportHomFunctor A i).Additive := by
  dsimp only [closedSupportHomFunctor]
  infer_instance

/-- The canonical left map of the closed-support Hom sequence.
Source: Stacks, Tags 095L, 0A45
(blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def closedSupportHomToSections (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    closedSupportHomFunctor A i ⟶ Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) := by
  let g := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
      (ModuleCat.of A A)).hom
  exact
    { app J := ModuleCat.ofHom ((rankOneSectionsEquiv A T J).toLinearMap.comp
        (Linear.leftComp A J g))
      naturality J J' k := by
        ext f
        change rankOneSectionsEquiv A T J' (g ≫ f ≫ k) = _
        rw [← Category.assoc, rankOneSectionsEquiv_naturality]
        rfl }

/-- The exact sequence with its left map fixed as evaluation after the closed unit.
Source: Stacks, Tags 095L, 0A45
(blueprint: new-lem-amb-closed-support-hom-sequence).

Apply Hom into an injective sheaf to the open–closed short exact sequence. Evaluation at
one identifies the middle term with global sections. Extension-by-zero adjunction
identifies the last term with sections on the open, and the counit formula identifies
its map with restriction. The left map is the explicit `closedSupportHomToSections`,
so its normalization is retained instead of hidden by an existential choice. -/
theorem closedSupportHomSequenceNormalized (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (τ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hτ : ∀ J, τ.app J = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) :
    ∃ (hzero : ∀ J, (closedSupportHomToSections A i).app J ≫ τ.app J = 0),
      ∀ J, Injective J →
        (ShortComplex.mk ((closedSupportHomToSections A i).app J) (τ.app J)
          (hzero J)).ShortExact := by
  classical
  let P := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (ModuleCat.of A A)
  have hicomp : Set.range i.base = (Set.range v.base)ᶜ := by
    rw [hcomp, compl_compl]
  let S := openClosedShortComplex (ModuleCat.{u + 1} A) v i
    (disjoint_range_of_range_eq_compl v i hicomp) P
  have hS : S.ShortExact := shortExact_openClosedShortComplex
    (ModuleCat.{u + 1} A) v i P hicomp
  let c := (lowerStar (ModuleCat.{u + 1} A) i).mapIso
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app (ModuleCat.of A A))
  let g := S.g ≫ c.hom
  let α := closedSupportHomToSections A i
  let U := upperStar (ModuleCat.{u + 1} A) v
  let a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
  have : U.Linear A := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).left_adjoint_linear
  let d := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
    (ModuleCat.of A A)
  let e₃ (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (S.X₁ ⟶ J) ≃ₗ[A] (Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (U.obj J) :=
    (CategoryTheory.adjunctionHomLinearEquiv A a (U.obj P) J).trans
      ((Linear.homCongr A d (Iso.refl (U.obj J))).trans
        (rankOneSectionsEquiv A V (U.obj J)))
  have hβ (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (f : P ⟶ J) :
      τ.app J (rankOneSectionsEquiv A T J f) = e₃ J (S.f ≫ f) := by
    rw [hτ]
    erw [rankOneSections_restriction]
    dsimp only [e₃, LinearEquiv.trans_apply, Linear.homCongr_apply]
    apply congrArg (rankOneSectionsEquiv A V (U.obj J))
    change d.inv ≫ U.map f = d.inv ≫ a.homEquiv _ _ (a.counit.app P ≫ f)
    rw [Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_symm_id]
    erw [Equiv.apply_symm_apply, Category.id_comp]
  have hzero (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      α.app J ≫ τ.app J = 0 := by
    ext f
    change τ.app J (rankOneSectionsEquiv A T J (g ≫ f)) = 0
    rw [hβ]
    have hz : S.f ≫ g ≫ f = 0 := by
      dsimp only [g]
      rw [← Category.assoc, ← Category.assoc, S.zero, zero_comp, zero_comp]
    rw [hz, map_zero]
  refine ⟨hzero, ?_⟩
  intro J hJ
  let := hJ
  let e₁ := (Linear.homCongr A c (Iso.refl J)).toModuleIso
  let e₂ := (rankOneSectionsEquiv A T J).toModuleIso
  let e := ShortComplex.isoMk (S₁ := CategoryTheory.linearHomShortComplex A S J)
    (S₂ := ShortComplex.mk (α.app J) (τ.app J) (hzero J))
    e₁ e₂ (e₃ J).toModuleIso (by
      ext f
      change rankOneSectionsEquiv A T J (g ≫ ((c.inv ≫ f) ≫ 𝟙 J)) =
        rankOneSectionsEquiv A T J (S.g ≫ f)
      simp [g]) (by
      ext f
      exact hβ J f)
  exact ShortComplex.shortExact_of_iso e
    (CategoryTheory.linearHomShortComplex_shortExact A S hS J)

/-- The canonical support map followed by restriction is zero.
Source: Stacks, Tag 095L (blueprint: new-lem-amb-closed-support-hom-sequence).

Take the zero-composite proof from the canonical short exact sequence. Its witness is a
proof, so this exposes no new choice of map or object. -/
theorem closedSupportHomToSections_comp (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (τ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hτ : ∀ J, τ.app J = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) :
    ∀ J, (closedSupportHomToSections A i).app J ≫ τ.app J = 0 :=
  (closedSupportHomSequenceNormalized A i v hcomp τ hτ).choose

/-- Exactness on injectives, using the named canonical zero-composite proof.
Source: Stacks, Tag 095L (blueprint: new-lem-amb-closed-support-hom-sequence).

Apply exactness of the normalized sequence. Proof irrelevance identifies its witness of
the zero composite with the named witness, without changing either map. -/
theorem closedSupportHomSequence_shortExact (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (τ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hτ : ∀ J, τ.app J = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) :
    ∀ J, Injective J →
      (ShortComplex.mk ((closedSupportHomToSections A i).app J) (τ.app J)
        (closedSupportHomToSections_comp A i v hcomp τ hτ J)).ShortExact :=
  (closedSupportHomSequenceNormalized A i v hcomp τ hτ).choose_spec

end AlgebraicGeometry.Etale
