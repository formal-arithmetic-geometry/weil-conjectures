/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Etale-to-pro-etale comparison on geometric stalks

Source: Stacks Project, Pro-etale Cohomology, Tags 0GLZ and 0993; Sites, Tag 05V1
(blueprint: lem-cbc-proetale-comparison-stalk).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The canonical stalk comparison, expressed as a natural isomorphism normalized on
unit germs. This predicate merely spells out the conclusion for a coefficient category;
it introduces no chosen isomorphism or extra assumption on the inverse image.
Source: Stacks Project, Tags 0GLZ and 0993
(blueprint: lem-cbc-proetale-comparison-stalk). -/
def HasCanonicalProEtaleStalkComparison (T : Scheme.{u})
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u + 1, u + 1} A]
    [HasColimitsOfSize.{u, u} A]
    (L : Sheaf T.smallEtaleTopology A ⥤ Sheaf (ProEt.topology T) A)
    (η : 𝟭 (Sheaf T.smallEtaleTopology A) ⟶
      L ⋙ (toProEt T).sheafPushforwardContinuous A
        T.smallEtaleTopology (ProEt.topology T)) : Prop :=
  ∃ c : L ⋙ sheafToPresheaf (ProEt.topology T) A ⋙
      (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ A).obj
        (proEtaleGeometricNeighbourhoodForget t).op ⋙ colim ≅
      (pointSmallEtale t).sheafFiber,
    ∀ (H : Sheaf T.smallEtaleTopology A) (U : T.Etale)
      (x : (pointSmallEtale t).fiber.obj U),
      (η.app H).hom.app (op U) ≫
        colimit.ι (proEtaleGeometricStalkDiagram t (L.obj H))
          (op (StructuredArrow.mk (Y := (toProEt T).obj U) x)) ≫
        c.hom.app H = (pointSmallEtale t).toPresheafFiber U x H.obj

private theorem comparison_cover_lift
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {V : T.ProEt} (R : Sieve V) (hR : R ∈ ProEt.topology T V)
    (v : Spec (.of Ω) ⟶ V.left) :
    ∃ (W : T.ProEt) (g : W ⟶ V) (_ : R g) (w : Spec (.of Ω) ⟶ W.left),
      w ≫ g.left = v := by
  obtain ⟨S, hS, hSR⟩ := ProEt.mem_topology_iff.1 hR
  obtain ⟨ι, Z, f, rfl⟩ := S.exists_eq_ofArrows
  have hS' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage V.left := by
    simpa only [ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
      Functor.comp_obj, Functor.comp_map, ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, Comma.fst] using hS
  have hb := Precoverage.mem_coverings_of_isPullback (fun i ↦ (f i).left) hS' v
    (fun i ↦ pullback.snd (f i).left v) (fun i ↦ pullback.fst (f i).left v)
    (fun i ↦ (IsPullback.of_hasPullback (f i).left v).flip)
  obtain ⟨i, z, hz⟩ :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hb)).1
      (IsLocalRing.closedPoint Ω)
  have : WeaklyEtale (f i).left :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hS')).2 i
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale
    (pullback.snd (f i).left v) z
  refine ⟨Z i, f i, hSR _ _ ⟨i⟩, σ ≫ pullback.fst (f i).left v, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

private noncomputable def comparisonPoint
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) : (ProEt.topology T).Point.{u + 1} where
  fiber := (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t))) ⋙ uliftFunctor.{u + 1}
  isCofiltered := by
    have : IsCofiltered (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t))).Elements :=
      Functor.isCofiltered_elements _
    exact .of_equivalence
      (Functor.Elements.uliftEquivalence.{u + 1}
        (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t)))).symm
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR x := by
    obtain ⟨W, g, hg, w, hw⟩ := comparison_cover_lift R hR x.down.left
    refine ⟨W, g, hg, ULift.up (Over.homMk w ?_), ?_⟩
    · change w ≫ W.hom = t
      rw [← MorphismProperty.Over.w g, ← Category.assoc, hw]
      exact Over.w x.down
    · apply ULift.ext
      apply Over.OverMorphism.ext
      exact hw

private noncomputable def comparisonPointElements
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) :
    ProEtaleGeometricNeighbourhood t ≌ (comparisonPoint t).fiber.Elements where
  functor.obj n := ⟨n.right, ULift.up n.hom⟩
  functor.map f := ⟨f.right, congrArg ULift.up f.w⟩
  inverse.obj n := StructuredArrow.mk n.2.down
  inverse.map f := StructuredArrow.homMk f.1 (congrArg ULift.down f.2)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

private theorem comparison_coverPreserving (T : Scheme.{u}) :
    CoverPreserving T.smallEtaleTopology (ProEt.topology T) (toProEt T) := by
  rw [ProEt.topology_eq_restrictedTopology]
  exact MorphismProperty.Over.coverPreserving_changeProp T etale_le_weaklyEtale
    etaleTopology_le_proetaleTopology

private noncomputable def comparisonPointStalkIso
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (A : Type v) [Category.{w} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] :
    sheafToPresheaf (ProEt.topology T) A ⋙
      (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ A).obj
        (proEtaleGeometricNeighbourhoodForget t).op ⋙ colim ≅
      (comparisonPoint t).sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf (ProEt.topology T) A)
    (Functor.isoWhiskerLeft
      ((Functor.whiskeringLeft _ _ A).obj (CategoryOfElements.π
        (comparisonPoint t).fiber).op)
      (Functor.Final.colimIso (comparisonPointElements t).functor.op))

private theorem comparison_ulift_germ
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (A : Type v) [Category.{w} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] [HasColimitsOfSize.{u, u} A]
    (H : Sheaf T.smallEtaleTopology A) (U : T.Etale)
    (x : (pointSmallEtale t).fiber.obj U) :
    ((pointSmallEtale t).ulift.{u + 1}).toPresheafFiber U (ULift.up x) H.obj ≫
        ((pointSmallEtale t).uliftSheafFiberIso.{u + 1} A).hom.app H =
      (pointSmallEtale t).toPresheafFiber U x H.obj := by
  exact Functor.Final.ι_colimitIso_hom
    (Functor.Elements.uliftEquivalence.{u + 1} (pointSmallEtale t).fiber).functor.op
    ((CategoryOfElements.π (pointSmallEtale t).fiber).op ⋙ H.obj) (op ⟨U, ULift.up x⟩)

private theorem comparison_generic
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (A : Type v) [Category.{w} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] [HasColimitsOfSize.{u, u} A]
    [HasProducts.{u + 1} A]
    (L : Sheaf T.smallEtaleTopology A ⥤ Sheaf (ProEt.topology T) A)
    (adj : L ⊣ (toProEt T).sheafPushforwardContinuous A
      T.smallEtaleTopology (ProEt.topology T)) :
    HasCanonicalProEtaleStalkComparison T Ω t A L adj.unit := by
  let := adj.isRightAdjoint
  let Φ := comparisonPoint t
  let hF := comparison_coverPreserving T
  let a := (toProEt T).sheafAdjunctionContinuous A T.smallEtaleTopology (ProEt.topology T)
  let e := adj.leftAdjointUniq a
  have : InitiallySmall.{u + 1} ((toProEt T) ⋙ Φ.fiber).Elements := by
    change InitiallySmall.{u + 1} ((pointSmallEtale t).ulift.{u + 1}).fiber.Elements
    infer_instance
  let b := Φ.sheafFiberComapIso (toProEt T) hF A
  let hb : (Φ.comap (toProEt T) hF).sheafFiber ≅
      ((pointSmallEtale t).ulift.{u + 1}).sheafFiber (A := A) := Iso.refl _
  let c := Functor.isoWhiskerLeft L (comparisonPointStalkIso t A) ≪≫
    Functor.isoWhiskerRight e Φ.sheafFiber ≪≫ b.symm ≪≫ hb ≪≫
      (pointSmallEtale t).uliftSheafFiberIso.{u + 1} A
  refine ⟨c, ?_⟩
  intro H U x
  have hu : (adj.unit.app H).hom.app (op U) ≫
      (e.hom.app H).hom.app (op ((toProEt T).obj U)) =
      (a.unit.app H).hom.app (op U) := by
    exact NatTrans.congr_app (Sheaf.hom_ext_iff.1
      (Adjunction.unit_leftAdjointUniq_hom_app adj a H)) (op U)
  have hg := Φ.toPresheafFiber_sheafFiberComapIso_hom_app
    (toProEt T) hF A H U (ULift.up x)
  have hg' : (a.unit.app H).hom.app (op U) ≫
      Φ.toPresheafFiber ((toProEt T).obj U) (ULift.up x) (((toProEt T).sheafPullback A
        T.smallEtaleTopology (ProEt.topology T)).obj H).obj ≫
      b.inv.app H =
      (Φ.comap (toProEt T) hF).toPresheafFiber U (ULift.up x) H.obj := by
    rw [← Category.assoc, ← hg, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  simp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, hb, Iso.refl_hom, Category.id_comp]
  rw [comparisonPointStalkIso_germ_assoc]
  rw [show Φ.sheafFiber.map (e.hom.app H) =
      Φ.presheafFiber.map (e.hom.app H).hom from rfl]
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  rw [← Category.assoc, hu]
  calc
    _ = (Φ.comap (toProEt T) hF).toPresheafFiber U (ULift.up x) H.obj ≫
        ((pointSmallEtale t).uliftSheafFiberIso.{u + 1} A).hom.app H := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ ((pointSmallEtale t).uliftSheafFiberIso.{u + 1} A).hom.app H) hg'
    _ = _ := comparison_ulift_germ t A H U x

/-- Geometric stalks commute canonically with etale-to-pro-etale inverse image,
naturally for sets, abelian groups, and left modules over any fixed ring.
Source: Stacks Project, Tags 0GLZ, 0993, 05V1 and 00YR
(blueprint: lem-cbc-proetale-comparison-stalk).

Proof:
1. Geometric lifts define a point of the pro-etale site: its category of elements
   is equivalent to the cofiltered category of pointed weakly etale neighbourhoods.
   Given a covering sieve, choose a covering family and pull it back to Spec Ω.
   Joint surjectivity supplies a nonempty weakly etale member, which has a section
   over the algebraically closed field Ω. This gives the required lift to the sieve.
2. Restricting this point along toProEt gives the usual etale point, with its lift
   sets enlarged by ULift. The equivalences of neighbourhood categories induce
   natural isomorphisms on colimits, carrying each coprojection to its germ map.
3. Apply the general point-comap comparison (Sites, Tag 05V1). Its germ formula
   identifies an etale germ followed by the comparison with the inverse-image unit
   followed by the pro-etale germ. Transfer from the abstract left adjoint to the
   specified one by uniqueness of left adjoints; its unit equation gives exactly
   the normalization in the statement. Finally remove ULift using its colimit iso.
4. This argument works in any coefficient category with the required products and
   colimits. Specialize to sets, abelian groups and modules over any fixed ring.
   In the latter two categories the components are already additive or linear
   isomorphisms. No finite or commutative ring hypothesis is used. -/
theorem proEtale_comparison_stalk (T : Scheme.{u})
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    HasCanonicalProEtaleStalkComparison T Ω t (Type (u + 1))
      (Functor.sheafPullbackConstruction.sheafPullback (toProEt T)
        (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T))
      (proEtaleSiteComparison T).unit ∧
    HasCanonicalProEtaleStalkComparison T Ω t AddCommGrpCat.{u + 1}
      (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T)
      (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit ∧
    ∀ (Λ : Type (u + 1)) [Ring Λ],
      HasCanonicalProEtaleStalkComparison T Ω t (ModuleCat.{u + 1} Λ)
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
        (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) T).unit := by
  refine ⟨comparison_generic t (Type (u + 1)) _ (proEtaleSiteComparison T),
    comparison_generic t AddCommGrpCat.{u + 1} _
      (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T), ?_⟩
  intro Λ _
  exact comparison_generic t (ModuleCat.{u + 1} Λ) _
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) T)

set_option backward.isDefEq.respectTransparency false in
end AlgebraicGeometry.Scheme
