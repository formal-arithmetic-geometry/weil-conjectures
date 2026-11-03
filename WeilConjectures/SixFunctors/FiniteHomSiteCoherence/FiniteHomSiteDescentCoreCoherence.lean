/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus

/-! # Finite coefficient Hom coherence on the two actual sites

Small presentations are related to the actual small sites by explicit equivalences.
All functors below are normalized ringed derived pullbacks. In particular no scalar
functor, tensorator, associator, or Hom comparison is an unconstrained parameter.
Source: thm-coef-finite-hom, final evaluation and site-transport paragraph
(blueprint: lem-coef-finite-hom-site-descent-core-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxErrors 8
universe u w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
open CategoryTheory.RingedDerivedComparisons

namespace WeilConjectures
namespace FiniteHomSiteCoherence

private abbrev LocalStrong
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) :=
  letI := SA.monoidal
  letI := SB.monoidal
  {s : F.CoreMonoidal // ∀ P Q : A, s.μIso P Q = (μ.app (P, Q)).symm}

private theorem comparison_evaluation
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (K M : A) :
    SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ K M) (𝟙 _)) ≫
        SB.evaluation (F.obj K) (F.obj M) =
      μ.inv.app (HA.obj (op K, M), K) ≫ F.map (SA.evaluation K M) := by
  exact (scalarUncurry SB _ _ _ _).symm.trans
    (scalarBaseChangeHom_beta SA SB F μ K M)

private theorem comparison_composite_evaluation
    {A : Type a} {B : Type b} {C : Type c}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HC : Cᵒᵖ × C ⥤ C}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (F : A ⥤ B) (G : B ⥤ C)
    (μF : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (μG : SB.tensor ⋙ G ≅ G.prod G ⋙ SC.tensor) (K M : A) :
    SC.tensor.map (Prod.mkHom
        (G.map (coefficientBaseChangeHom SA SB F μF K M) ≫
          coefficientBaseChangeHom SB SC G μG (F.obj K) (F.obj M)) (𝟙 _)) ≫
        SC.evaluation (G.obj (F.obj K)) (G.obj (F.obj M)) =
      μG.inv.app (F.obj (HA.obj (op K, M)), F.obj K) ≫
        G.map (μF.inv.app (HA.obj (op K, M), K)) ≫
        G.map (F.map (SA.evaluation K M)) := by
  rw [← scalarUncurry, scalarUncurry_pre, scalarBaseChangeHom_beta]
  have hn := μG.inv.naturality
    (Prod.mkHom (coefficientBaseChangeHom SA SB F μF K M) (𝟙 (F.obj K)))
  simp only [Functor.comp_map, Functor.prod_map, G.map_id] at hn
  rw [← Category.assoc, hn, Category.assoc, ← G.map_comp,
    comparison_evaluation, G.map_comp]

/-- The canonical closed comparisons commute with a tensor-compatible square.
Only the tensor equation is needed; associativity and unit equations are separate.
Source: blueprint `lem-coef-monoidal-square-hom-transport`, evaluation transposition
(blueprint: lem-coef-right-closed-tensor-square).

Proof: uncurry both sides with the specified target adjunction, and precompose
with tensoring by the forward component on K. Naturality of the tensorators and
the counit identifies each composite comparison with the image of evaluation.
The tensor-square equation identifies their tensorators. Naturality of h at
evaluation identifies the remaining arrows. The inverse and forward components
on K cancel, and injectivity of the adjunction gives the assertion. -/
private theorem localTensorSquare
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    (μF : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (μG : SC.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (μU : SA.tensor ⋙ U ≅ U.prod U ⋙ SC.tensor)
    (μV : SB.tensor ⋙ V ≅ V.prod V ⋙ SD.tensor)
    (h : F ⋙ V ≅ U ⋙ G)
    (ht : ∀ K M : A,
      h.hom.app (SA.tensor.obj (K, M)) ≫ G.map (μU.hom.app (K, M)) ≫
          μG.hom.app (U.obj K, U.obj M) =
        V.map (μF.hom.app (K, M)) ≫ μV.hom.app (F.obj K, F.obj M) ≫
          SD.tensor.map (Prod.mkHom (h.hom.app K) (h.hom.app M)))
    (K M : A) :
    h.hom.app (HA.obj (op K, M)) ≫
        G.map (coefficientBaseChangeHom SA SC U μU K M) ≫
        coefficientBaseChangeHom SC SD G μG (U.obj K) (U.obj M) =
      V.map (coefficientBaseChangeHom SA SB F μF K M) ≫
        coefficientBaseChangeHom SB SD V μV (F.obj K) (F.obj M) ≫
        HD.map (Prod.mkHom (h.inv.app K).op (h.hom.app M)) := by
  apply (SD.transpose _ (G.obj (U.obj K)) (G.obj (U.obj M))).symm.injective
  rw [scalarUncurry_pre]
  rw [← Category.assoc (V.map (coefficientBaseChangeHom SA SB F μF K M))
    (coefficientBaseChangeHom SB SD V μV (F.obj K) (F.obj M))
    (HD.map (Prod.mkHom (h.inv.app K).op (h.hom.app M))), scalarUncurry_post]
  simp only [scalarUncurry]
  rw [comparison_composite_evaluation, comparison_composite_evaluation]
  let H := HA.obj (op K, M)
  have hi : SD.tensor.map (Prod.mkHom (h.hom.app H) (h.hom.app K)) ≫
        μG.inv.app (U.obj H, U.obj K) ≫ G.map (μU.inv.app (H, K)) =
      μV.inv.app (F.obj H, F.obj K) ≫ V.map (μF.inv.app (H, K)) ≫
        h.hom.app (SA.tensor.obj (H, K)) := by
    let a := V.mapIso (μF.app (H, K))
    let b := μV.app (F.obj H, F.obj K)
    let c := G.mapIso (μU.app (H, K))
    let d := μG.app (U.obj H, U.obj K)
    have he : h.hom.app (SA.tensor.obj (H, K)) ≫ c.hom ≫ d.hom =
        a.hom ≫ b.hom ≫ SD.tensor.map (Prod.mkHom (h.hom.app H) (h.hom.app K)) :=
      ht H K
    change _ ≫ d.inv ≫ c.inv = b.inv ≫ a.inv ≫ _
    apply (cancel_epi b.hom).1
    apply (cancel_epi a.hom).1
    simp only [Iso.hom_inv_id_assoc]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
      using congrArg (fun f ↦ f ≫ d.inv ≫ c.inv) he.symm
  let e := SD.tensor.mapIso (Iso.prod (Iso.refl (V.obj (F.obj H))) (h.app K))
  apply (cancel_epi e.hom).1
  change SD.tensor.map (Prod.mkHom (𝟙 _) (h.hom.app K)) ≫ _ =
    SD.tensor.map (Prod.mkHom (𝟙 _) (h.hom.app K)) ≫ _
  simp only [← Category.assoc, ← SD.tensor.map_comp]
  simp only [CategoryTheory.prod_comp, Category.id_comp,
    Iso.hom_inv_id_app]
  simp only [Category.assoc]
  have hid : Prod.mkHom (𝟙 ((F ⋙ V).obj H)) (𝟙 ((F ⋙ V).obj K)) =
      𝟙 ((F ⋙ V).obj H, (F ⋙ V).obj K) := rfl
  rw [hid]
  erw [SD.tensor.map_id, Category.id_comp]
  erw [Category.comp_id (h.hom.app K)]
  have hi' := congrArg (fun f ↦ f ≫ G.map (U.map (SA.evaluation K M))) hi
  have hn := h.hom.naturality (SA.evaluation K M)
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc] at hi'
  erw [← hn] at hi'
  exact hi'

/-- Identity of the underlying topos with the specified structural coefficient map.
The module direct image is scalar restriction, with its unchanged underlying sections.
Source: Stacks 03DA, 07A6
(blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
def scalar {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) where
  inverse := 𝟭 _
  direct := 𝟭 _
  adj := Adjunction.id
  leftExact := inferInstance
  ringMap := (sheafCompose J (CategoryTheory.forget CommRingCat)).map a
  ring_zero := by
    intro T z hz U t
    change (a.hom.app U).hom (z.hom.app U t) = 0
    have h := hz U t
    change z.hom.app U t = (0 : R.obj.obj U) at h
    exact (congrArg (a.hom.app U).hom h).trans (map_zero _)
  ring_one := by
    intro T z hz U t
    change (a.hom.app U).hom (z.hom.app U t) = 1
    have h := hz U t
    change z.hom.app U t = (1 : R.obj.obj U) at h
    exact (congrArg (a.hom.app U).hom h).trans (map_one _)
  ring_add := by
    intro T x y z hz U t
    change (a.hom.app U).hom (z.hom.app U t) =
      @Add.add (S.obj.obj U) inferInstance
        ((a.hom.app U).hom (x.hom.app U t)) ((a.hom.app U).hom (y.hom.app U t))
    have h := hz U t
    change z.hom.app U t =
      @Add.add (R.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t) at h
    exact (congrArg (a.hom.app U).hom h).trans (map_add _ _ _)
  ring_mul := by
    intro T x y z hz U t
    change (a.hom.app U).hom (z.hom.app U t) =
      @Mul.mul (S.obj.obj U) inferInstance
        ((a.hom.app U).hom (x.hom.app U t)) ((a.hom.app U).hom (y.hom.app U t))
    have h := hz U t
    change z.hom.app U t =
      @Mul.mul (R.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t) at h
    exact (congrArg (a.hom.app U).hom h).trans (map_mul _ _ _)
  modules := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
  additive := inferInstance
  underlying := Iso.refl _
  module_linear := by
    intro M T s x y z hz U t
    have h := hz U t
    change z.hom.app U t = @Add.add (M.val.obj U) inferInstance
      (@SMul.smul (S.obj.obj U) (M.val.obj U) inferInstance
        ((a.hom.app U).hom (s.hom.app U t)) (x.hom.app U t)) (y.hom.app U t) at h
    simp only [Adjunction.homEquiv, Adjunction.id]
    change z.hom.app U t = @Add.add (M.val.obj U) inferInstance
      (@SMul.smul (S.obj.obj U) (M.val.obj U) inferInstance
        ((a.hom.app U).hom (s.hom.app U t)) (x.hom.app U t)) (y.hom.app U t)
    exact h

/-- The canonical tensor comparison of a normalized ringed derived pullback.
Source: Stacks 07A4 (blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
abbrev tensor (s : System.{u, w}) {X Y : Site.{u, w}} (f : Morphism X Y) :=
  (s.lift f).edge.tensorComparison (s.lift f).tensorModelY (s.lift f).tensorModelX

/-- The specified Hom comparison: transpose of pullback of evaluation.
Source: Stacks 08J9 (blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
abbrev comparison (s : System.{u, w}) {X Y : Site.{u, w}}
    (f : Morphism X Y) (K M : Y.D) :=
  coefficientBaseChangeHom Y.closed X.closed (s.lift f).edge.left (tensor s f) K M

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory.{w} (RingedTensorModules.{u, u, u} J R)]

/-- The equations for one specified finite scalar map, including the evaluation formula.
These are equations in the ordinary module derived categories of this very site.
Source: thm-coef-finite-hom, final paragraph
(blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
def Laws (s : System.{u, w}) {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) : Prop :=
  let A := site J R
  let B := site J S
  let D := site J T
  let f := s.lift (X := B) (Y := A) (scalar a)
  let g := s.lift (X := D) (Y := B) (scalar b)
  let α := (scalarComposition J s a b).pullback.symm
  let ι := (scalarIdentity J s R).pullback
  CoefficientEvaluationCompatible A.closed B.closed f.edge.left
      (tensor s (X := B) (Y := A) (scalar a)) ∧
    (∀ K M : A.D,
      B.closed.tensor.map
          (Prod.mkHom (comparison s (X := B) (Y := A) (scalar a) K M) (𝟙 (f.edge.left.obj K))) ≫
          B.closed.evaluation (f.edge.left.obj K) (f.edge.left.obj M) =
        (tensor s (X := B) (Y := A) (scalar a)).inv.app
            ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, M), K) ≫
          f.edge.left.map (A.closed.evaluation K M)) ∧
    (∀ K M : A.D,
      g.edge.left.map (comparison s (X := B) (Y := A) (scalar a) K M) ≫
          comparison s (X := D) (Y := B) (scalar b) (f.edge.left.obj K) (f.edge.left.obj M) ≫
          (derivedInternalHomOfUniverses.{u, u, u, w} J T).map
            (Prod.mkHom (α.inv.app K).op (α.hom.app M)) =
        α.hom.app ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, M)) ≫
          comparison s (X := D) (Y := A) (scalar (a ≫ b)) K M) ∧
    (∀ K M : A.D,
      comparison s (X := A) (Y := A) (scalar (𝟙 R)) K M ≫
          (derivedInternalHomOfUniverses.{u, u, u, w} J R).map
            (Prod.mkHom (ι.inv.app K).op (ι.hom.app M)) =
        ι.hom.app ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op K, M)))

private theorem tensor_hom (s : System.{u, w}) {X Y : Site.{u, w}}
    (f : Morphism X Y) (U V : Y.D) :
    (tensor s f).hom.app (U, V) = ((s.lift f).tensor U V).hom :=
  ((s.lift f).tensor_canonical U V).symm

private def tensor_strong (s : System.{u, w}) {X Y : Site.{u, w}}
    (f : Morphism X Y) :
    LocalStrong Y.closed X.closed (s.lift f).edge.left (tensor s f) := by
  refine ⟨(s.lift f).monoidal, ?_⟩
  intro U V
  apply Iso.ext_inv
  exact (s.lift f).tensor_canonical U V

private theorem composition_tensor (s : System.{u, w}) {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    {θ : k.inverse ≅ g.inverse ⋙ f.inverse}
    (c : Composition (s.lift f) (s.lift g) (s.lift k) θ) (U V : Z.D) :
    (s.lift f).edge.left.map ((tensor s g).hom.app (U, V)) ≫
        (tensor s f).hom.app ((s.lift g).edge.left.obj U, (s.lift g).edge.left.obj V) ≫
        X.closed.tensor.map (Prod.mkHom (c.pullback.inv.app U) (c.pullback.inv.app V)) =
      c.pullback.inv.app (Z.closed.tensor.obj (U, V)) ≫ (tensor s k).hom.app (U, V) := by
  apply (cancel_epi (c.pullback.hom.app (Z.closed.tensor.obj (U, V)))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc, tensor_hom]
  rw [reassoc_of% c.tensor U V, ← X.closed.tensor.map_comp]
  simp only [Iso.symm_hom, prod_comp, Iso.hom_inv_id_app, Bifunctor.map_id]
  exact Category.comp_id _

private theorem scalar_laws (s : System.{u, w}) {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) : Laws J s a b := by
  dsimp only [Laws]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨scalarBaseChangeHom_naturality _ _ _ _, comparison_transpose _ _ _ _,
      comparison_composition _ _ _ _ (tensor_strong s _)⟩
  · intro K M
    rw [← scalarUncurry, scalarBaseChangeHom_beta]
    rfl
  · intro K M
    exact scalarBaseChangeHom_tower _ _ _ _ _ _ _ _ _
      (scalarComposition J s a b).pullback.symm
      (composition_tensor s (scalarComposition J s a b)) K M
  · intro K M
    apply scalarBaseChangeHom_identity
    intro U V
    let c := scalarIdentity J s R
    apply (cancel_mono
      ((site J R).closed.tensor.mapIso (Iso.prod (c.pullback.app U)
        (c.pullback.app V))).hom).1
    change (site J R).closed.tensor.map
        (Prod.mkHom (c.pullback.inv.app U) (c.pullback.inv.app V)) ≫
        (site J R).closed.tensor.map
          (Prod.mkHom (c.pullback.hom.app U) (c.pullback.hom.app V)) =
      (c.pullback.inv.app ((site J R).closed.tensor.obj (U, V)) ≫
        (tensor s (X := site J R) (Y := site J R) (scalar (𝟙 R))).hom.app (U, V)) ≫
          (site J R).closed.tensor.map
            (Prod.mkHom (c.pullback.hom.app U) (c.pullback.hom.app V))
    rw [Category.assoc, tensor_hom, c.tensor, Iso.inv_hom_id_app]
    rw [← (site J R).closed.tensor.map_comp]
    simp

private theorem square_law (s : System.{u, w}) {Y X Y' X' : Site.{u, w}}
    (f : Morphism X Y) (g : Morphism Y' Y)
    (j : Morphism X' X) (k : Morphism X' Y') (d : Morphism X' Y)
    (θ₁ : d.inverse ≅ f.inverse ⋙ j.inverse)
    (θ₂ : d.inverse ≅ g.inverse ⋙ k.inverse)
    (hd₁ : d.ringMap = θ₁.hom.app
      ((sheafCompose Y.J (CategoryTheory.forget CommRingCat.{u})).obj Y.A) ≫
        j.inverse.map f.ringMap ≫ j.ringMap)
    (hd₂ : d.ringMap = θ₂.hom.app
      ((sheafCompose Y.J (CategoryTheory.forget CommRingCat.{u})).obj Y.A) ≫
        k.inverse.map g.ringMap ≫ k.ringMap) :
    Square s f g j k d θ₁ θ₂ hd₁ hd₂ := by
  let c₁ := Classical.choice (s.composition j f d θ₁ hd₁)
  let c₂ := Classical.choice (s.composition k g d θ₂ hd₂)
  dsimp only [Square]
  apply localTensorSquare Y.closed X.closed Y'.closed X'.closed
    (s.lift f).edge.left (s.lift k).edge.left (s.lift g).edge.left (s.lift j).edge.left
    (tensor s f) (tensor s k) (tensor s g) (tensor s j)
    (c₁.pullback.symm ≪≫ c₂.pullback)
  intro U V
  apply (cancel_epi (c₁.pullback.hom.app (Y.closed.tensor.obj (U, V)))).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [tensor_hom s g U V,
    tensor_hom s k ((s.lift g).edge.left.obj U) ((s.lift g).edge.left.obj V),
    tensor_hom s f U V,
    tensor_hom s j ((s.lift f).edge.left.obj U) ((s.lift f).edge.left.obj V)]
  rw [c₂.tensor U V]
  rw [reassoc_of% c₁.tensor U V]
  simp only [← X'.closed.tensor.map_comp]
  congr 1
  congr 1
  apply Prod.ext <;> simp

/-- The induced topology on the chosen small presentation of the actual etale site.
Source: size convention (blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
abbrev etaleTopology {X : AlgebraicGeometry.Scheme.{u}}
    {E : Type (u + 1)} [SmallCategory E] (e : E ≌ X.Etale) :=
  e.functor.inducedTopology X.smallEtaleTopology

/-- The induced topology on the chosen small presentation of the actual pro-etale site.
Source: size convention (blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
abbrev proTopology {X : AlgebraicGeometry.Scheme.{u}}
    {P : Type (u + 1)} [SmallCategory P] (p : P ≌ X.ProEt) :=
  p.functor.inducedTopology (AlgebraicGeometry.Scheme.ProEt.topology X)

/-- The actual geometric inverse image, transported through the two site equivalences.
The middle functor is the left adjoint in `Scheme.proEtaleSiteComparison`.
Source: Stacks 099R, 00WX
(blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
def actualInverse {X : AlgebraicGeometry.Scheme.{u}}
    {E P : Type (u + 1)} [SmallCategory E] [SmallCategory P]
    (e : E ≌ X.Etale) (p : P ≌ X.ProEt) :
    Sheaf (etaleTopology e) (Type (u + 1)) ⥤
      Sheaf (proTopology p) (Type (u + 1)) := by
  letI : e.inverse.IsDenseSubsite X.smallEtaleTopology (etaleTopology e) := by
    change e.symm.functor.IsDenseSubsite X.smallEtaleTopology
      (e.symm.inverse.inducedTopology X.smallEtaleTopology)
    infer_instance
  letI : p.inverse.IsDenseSubsite (AlgebraicGeometry.Scheme.ProEt.topology X) (proTopology p) := by
    change p.symm.functor.IsDenseSubsite (AlgebraicGeometry.Scheme.ProEt.topology X)
      (p.symm.inverse.inducedTopology (AlgebraicGeometry.Scheme.ProEt.topology X))
    infer_instance
  exact (e.sheafCongr (etaleTopology e) X.smallEtaleTopology (Type (u + 1))).functor ⋙
    Functor.sheafPullbackConstruction.sheafPullback (AlgebraicGeometry.Scheme.toProEt X)
      (Type (u + 1)) X.smallEtaleTopology (AlgebraicGeometry.Scheme.ProEt.topology X) ⋙
    (p.sheafCongr (proTopology p) (AlgebraicGeometry.Scheme.ProEt.topology X)
      (Type (u + 1))).inverse

/-- The normalized ordinary derived category with the actual constant coefficient sheaf.
Source: Stacks 03DA (blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
abbrev constantSite {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : CommRingCat.{u})
    [HasDerivedCategory.{w}
      (RingedTensorModules.{u, u, u} J ((constantSheaf J CommRingCat.{u}).obj R))] :=
  site J ((constantSheaf J CommRingCat.{u}).obj R)

end FiniteHomSiteCoherence

open FiniteHomSiteCoherence AlgebraicGeometry

end WeilConjectures
