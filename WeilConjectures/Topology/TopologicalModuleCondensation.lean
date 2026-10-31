/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.Topology.ContinuousAbelianProfiniteSheaf
import WeilConjectures.Topology.ContinuousModulePresheafCoordinates
import WeilConjectures.CategoryTheory.SectionActionInternal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian

/-!
# Continuous-function condensation of topological modules

Source: blueprint main-20261015, `lem-sfb-subfield-flat.proof.md`, first two sentences
(blueprint: lem-sfb-topological-module-condensation).

The action is specified on the canonical images of presheaf pure tensors, without
identifying sections of the sheaf tensor with tensor products of sections.

## Main definitions

- `Profinite.continuousModuleTensorGenerator`: the canonical image of a presheaf pure tensor.

## Main statements

- `Profinite.topologicalModule_condensation`: the additive functor with all specified formulas.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

open scoped TensorProduct

namespace Profinite

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

private noncomputable def continuousCommRingPresheaf :
    Profinite.{u}ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj S := CommRingCat.of (ULift.{u + 1} C(S.unop, R))
  map f := CommRingCat.ofHom ((continuousCoefficientRingPresheaf R).map f).hom
  map_id _ := rfl
  map_comp _ _ := rfl

private noncomputable def continuousCommRingSheaf :
    Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  ⟨continuousCommRingPresheaf R, by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
    exact isSheaf_continuousCoefficientRingPresheaf R⟩

private theorem action_linear
    (X Y : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (a : continuousCoefficientRingObj R ⊗ X ⟶ X)
    (b : continuousCoefficientRingObj R ⊗ Y ⟶ Y) (f : X ⟶ Y)
    (β : (continuousCoefficientRingObj R).obj ⊗ X.obj ⟶ X.obj)
    (γ : (continuousCoefficientRingObj R).obj ⊗ Y.obj ⟶ Y.obj)
    (ha : Functor.LaxMonoidal.μ (sheafToPresheaf _ Ab.{u + 1})
      (continuousCoefficientRingObj R) X ≫ a.hom = β)
    (hb : Functor.LaxMonoidal.μ (sheafToPresheaf _ Ab.{u + 1})
      (continuousCoefficientRingObj R) Y ≫ b.hom = γ)
    (hf : β ≫ f.hom = (continuousCoefficientRingObj R).obj ◁ f.hom ≫ γ) :
    a ≫ f = continuousCoefficientRingObj R ◁ f ≫ b := by
  apply Sheaf.tensor_hom_ext
  change _ ≫ a.hom ≫ f.hom = _ ≫
    (sheafToPresheaf _ Ab.{u + 1}).map (_ ◁ f) ≫ b.hom
  rw [← Category.assoc, ha]
  erw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [hb]
  exact hf

/-- The canonical image of a pure tensor in the underlying presheaf of the sheaf tensor.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, continuous scalar action, and the
sheaf-tensor comparison of `sk-def-sfb-sheaf-tensor`
(blueprint: lem-sfb-topological-module-condensation). -/
noncomputable def continuousModuleTensorGenerator
    (F : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (S : Profinite.{u})
    (a : C(S, R)) (h : F.obj.obj (op S)) :
    ((continuousCoefficientRingObj R ⊗ F).obj.obj (op S)) :=
  (Functor.LaxMonoidal.μ
    (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (continuousCoefficientRingObj R) F).app (op S)
      (TensorProduct.tmul ℤ (ULift.up a) h)

private theorem modulePresheaf_isSheaf (M : TopModuleCat.{u} R)
    (P : PresheafOfModules.{u + 1} (continuousMapRingPresheafOfUniverse R))
    (e : ∀ S : Profinite.{u}, P.obj (op S) ≃+ C(S, M))
    (he : ∀ (S T : Profinite.{u}) (q : T ⟶ S) (x : P.obj (op S)),
      e T (P.map q.op x) = (e S x).comp q.hom.hom) :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) P.presheaf := by
  let t : P.presheaf ≅ continuousAbelianPresheaf.{u, u} M :=
    NatIso.ofComponents
      (fun S ↦ ((e S.unop).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro S T q
        ext x
        exact congrArg ULift.up (he S.unop T.unop q.unop x))
  exact (Presheaf.isSheaf_of_iso_iff t).2 (isSheaf_continuousAbelianPresheaf M)

private theorem moduleAction_exists
    (P : PresheafOfModules.{u + 1} (continuousMapRingPresheafOfUniverse R))
    (hP : Presheaf.IsSheaf (coherentTopology Profinite.{u}) P.presheaf)
    (β : (continuousMapRingPresheafOfUniverse R ⋙ forget₂ RingCat Ab) ⊗
      P.presheaf ⟶ P.presheaf)
    (hβ : ∀ (S : Profinite.{u})
      (a : (continuousMapRingPresheafOfUniverse R).obj (op S)) (x : P.obj (op S)),
      β.app (op S) (a ⊗ₜ[ℤ] x) = a • x) :
    ∃ m : ModObj (continuousCoefficientRingObj R)
        (⟨P.presheaf, hP⟩ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      Functor.LaxMonoidal.μ (sheafToPresheaf _ Ab.{u + 1})
        (continuousCoefficientRingObj R) _ ≫ m.smul.hom = β := by
  let J := coherentTopology Profinite.{u}
  let B := continuousCommRingSheaf R
  let Q : Sheaf J Ab.{u + 1} := ⟨P.presheaf, hP⟩
  have hu (U : Profinite.{u}ᵒᵖ) (n : ℤ) (x : Q.obj.obj U) :
      β.app U ((n • (1 : B.obj.obj U)) ⊗ₜ[ℤ] x) = n • x := by
    rw [hβ U.unop]
    exact smul_assoc n (1 : (continuousMapRingPresheafOfUniverse R).obj U) x |>.trans
      (by rw [one_smul])
  have ha (U : Profinite.{u}ᵒᵖ) (b c : B.obj.obj U) (x : Q.obj.obj U) :
      β.app U ((b * c) ⊗ₜ[ℤ] x) =
        β.app U (b ⊗ₜ[ℤ] β.app U (c ⊗ₜ[ℤ] x)) := by
    simp only [hβ U.unop]
    exact @mul_smul ((continuousMapRingPresheafOfUniverse R).obj U)
      (P.obj U) _ _ b c x
  obtain ⟨m, _, hn, _⟩ := (sfbSectionActionInternal.{u + 1, u, u + 1, u} J B).1 Q β hu ha
  exact ⟨m, hn⟩

private theorem moduleProduct
    (F : TopModuleCat.{u} R ⥤ Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (continuousCoefficientRingObj R))
    (e : ∀ (M : TopModuleCat.{u} R) (S : Profinite.{u}),
      (F.obj M).X.obj.obj (op S) ≃+ C(S, M))
    (hf : ∀ (M N : TopModuleCat.{u} R) (f : M ⟶ N) (S : Profinite.{u})
      (x : (F.obj M).X.obj.obj (op S)) (s : S),
      e N S ((F.map f).hom.hom.app (op S) x) s = f.hom (e M S x s))
    (I : Type u) [Finite I] (M : I → TopModuleCat.{u} R)
    (hL : IsLimit (Fan.mk (F.obj (TopModuleCat.of R (∀ i, M i))).X
      (fun i : I ↦ (F.map (TopModuleCat.ofHom (ContinuousLinearMap.proj i))).hom))) :
    ∃ p : F.obj (TopModuleCat.of R (∀ i, M i)) ≅ ∏ᶜ fun i ↦ F.obj (M i),
      (∀ i, p.hom ≫ Pi.π (fun i ↦ F.obj (M i)) i =
        F.map (TopModuleCat.ofHom (ContinuousLinearMap.proj i))) ∧
      (∀ (S : Profinite.{u})
        (x : (F.obj (TopModuleCat.of R (∀ i, M i))).X.obj.obj (op S)) (i : I) (s : S),
        e (M i) S ((p.hom ≫ Pi.π (fun i ↦ F.obj (M i)) i).hom.hom.app (op S) x) s =
          e (TopModuleCat.of R (∀ i, M i)) S x s i) ∧
      (∀ (S : Profinite.{u}) (x : (∏ᶜ fun i ↦ F.obj (M i)).X.obj.obj (op S))
        (i : I) (s : S),
        e (TopModuleCat.of R (∀ i, M i)) S (p.inv.hom.hom.app (op S) x) s i =
          e (M i) S ((Pi.π (fun i ↦ F.obj (M i)) i).hom.hom.app (op S) x) s) := by
  let π (i : I) : F.obj (TopModuleCat.of R (∀ i, M i)) ⟶ F.obj (M i) :=
    F.map (TopModuleCat.ofHom (ContinuousLinearMap.proj i))
  have hLim : IsLimit (Fan.mk (F.obj (TopModuleCat.of R (∀ i, M i))) π) :=
    isLimitOfIsLimitFanMkObj (Mod.forget (continuousCoefficientRingObj R))
      (fun i : I ↦ F.obj (M i)) π hL
  let p := hLim.conePointUniqueUpToIso (productIsProduct (fun i ↦ F.obj (M i)))
  have hp (i : I) : p.hom ≫ Pi.π (fun i ↦ F.obj (M i)) i = π i :=
    hLim.conePointUniqueUpToIso_hom_comp _ (Discrete.mk i)
  refine ⟨p, hp, ?_, ?_⟩
  · intro S x i s
    exact (congrArg (fun f ↦ e (M i) S (f.hom.hom.app (op S) x) s) (hp i)).trans
      (hf _ _ (TopModuleCat.ofHom (ContinuousLinearMap.proj i)) S x s)
  · intro S x i s
    have hi : p.inv ≫ π i = Pi.π (fun i ↦ F.obj (M i)) i :=
      hLim.conePointUniqueUpToIso_inv_comp _ (Discrete.mk i)
    exact (hf _ _ (TopModuleCat.ofHom (ContinuousLinearMap.proj i)) S
      (p.inv.hom.hom.app (op S) x) s).symm.trans
        (congrArg (fun f ↦ e (M i) S (f.hom.hom.app (op S) x) s) hi)

set_option backward.isDefEq.respectTransparency false in
/-- Continuous functions condense topological modules additively, with their specified
pointwise action, maps, finite-product comparison and regular-module normalization.
Source: blueprint main-20261015 `lem-sfb-subfield-flat.proof.md`, first two sentences
(blueprint: lem-sfb-topological-module-condensation).

Proof: (1) Form C(S,M) with pointwise addition and precomposition. A compatible family
on a finite jointly surjective profinite cover descends as a function. The coproduct of
that cover is compact and its target Hausdorff, so the surjection is a quotient map
(`lem-sfb-compact-hausdorff-surjection-quotient`); the descended function is continuous.
The empty space has exactly one section. No separation property of M is needed.
(2) Joint continuity of scalar multiplication makes (a,h) ↦ (s ↦ a(s) • h(s)) continuous.
Pointwise distributivity extends this bilinearly to the objectwise integer tensor;
precomposition commutes with this extension.
(3) The universal property of sheafification (`def-weil-pbc-sheafification`) gives the
unique action on the sheaf tensor (`sk-def-sfb-sheaf-tensor`). Strong monoidality sends
the pointwise unit and associativity equations to the internal module identities.
The ring-object normalization of `det-def-sfb-ring-object-sheaf` identifies the scalar
multiplication and unit with those of the given continuous coefficient ring object.
(4) Postcompose with continuous linear maps. Pointwise linearity gives action
compatibility before sheafification, hence after sheafification by uniqueness.
Evaluation verifies preservation of identities, compositions and sums.
(5) Continuous maps into a product are exactly tuples of continuous maps. These inverse
coordinate maps commute with restrictions and actions. Projections separate sections,
so their cone is a product also in internal modules, including the empty family.
(6) For M = R the section sheaf is the given scalar sheaf. Both its action and ring
multiplication extend the same pointwise presheaf multiplication, so uniqueness
identifies it with the regular module.
-/
theorem topologicalModule_condensation :
    ∃ (F : TopModuleCat.{u} R ⥤
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (continuousCoefficientRingObj R)),
    ∃ (e : ∀ (M : TopModuleCat.{u} R) (S : Profinite.{u}),
      (F.obj M).X.obj.obj (op S) ≃+ C(S, M)),
      F.Additive ∧
      (∀ (M : TopModuleCat.{u} R) (S T : Profinite.{u}) (q : T ⟶ S)
        (h : (F.obj M).X.obj.obj (op S)),
        e M T ((F.obj M).X.obj.map q.op h) = (e M S h).comp q.hom.hom) ∧
      (∀ (M : TopModuleCat.{u} R),
        (∀ (S : Profinite.{u}) (a : C(S, R)) (h : C(S, M)) (s : S),
          e M S ((ModObj.smul (M := continuousCoefficientRingObj R)
            (X := (F.obj M).X)).hom.app (op S)
              (continuousModuleTensorGenerator R (F.obj M).X S a ((e M S).symm h))) s =
                a s • h s) ∧
        (∀ (g : continuousCoefficientRingObj R ⊗ (F.obj M).X ⟶ (F.obj M).X),
          (∀ (S : Profinite.{u}) (a : C(S, R)) (h : C(S, M)) (s : S),
            e M S (g.hom.app (op S)
              (continuousModuleTensorGenerator R (F.obj M).X S a ((e M S).symm h))) s =
                a s • h s) →
          g = ModObj.smul (M := continuousCoefficientRingObj R) (X := (F.obj M).X))) ∧
      (∀ (M N : TopModuleCat.{u} R) (f : M ⟶ N) (S : Profinite.{u})
        (h : (F.obj M).X.obj.obj (op S)) (s : S),
        e N S ((F.map f).hom.hom.app (op S) h) s = f.hom (e M S h s)) ∧
      (∀ (I : Type u) [Finite I] (M : I → TopModuleCat.{u} R),
        ∃ (p : F.obj (TopModuleCat.of R (∀ i, M i)) ≅ ∏ᶜ fun i ↦ F.obj (M i)),
          (∀ i, p.hom ≫ Pi.π (fun i ↦ F.obj (M i)) i =
            F.map (TopModuleCat.ofHom (ContinuousLinearMap.proj i))) ∧
          (∀ (S : Profinite.{u})
            (h : (F.obj (TopModuleCat.of R (∀ i, M i))).X.obj.obj (op S)) (i : I) (s : S),
            e (M i) S (((p.hom ≫ Pi.π (fun i ↦ F.obj (M i)) i).hom.hom.app (op S)) h) s =
              e (TopModuleCat.of R (∀ i, M i)) S h s i) ∧
          (∀ (S : Profinite.{u}) (h : (∏ᶜ fun i ↦ F.obj (M i)).X.obj.obj (op S))
            (i : I) (s : S),
            e (TopModuleCat.of R (∀ i, M i)) S (p.inv.hom.hom.app (op S) h) s i =
              e (M i) S ((Pi.π (fun i ↦ F.obj (M i)) i).hom.hom.app (op S) h) s)) ∧
      (∃ (r : F.obj (TopModuleCat.of R R) ≅ Mod.regular (continuousCoefficientRingObj R)),
        ∀ (S : Profinite.{u}) (h : (F.obj (TopModuleCat.of R R)).X.obj.obj (op S)),
          (r.hom.hom.hom.app (op S) h).down = e (TopModuleCat.of R R) S h) := by
  classical
  let J := coherentTopology Profinite.{u}
  obtain ⟨P, e, β, hAdd, hres, hsmul, hβ, hβuniq, hunit, hassoc, hmap,
    hlinear, hprod, hempty, r, hr, hrβ⟩ := continuousModulePresheaf_coordinates R
  let : P.Additive := hAdd
  have hs (M : TopModuleCat.{u} R) : Presheaf.IsSheaf J (P.obj M).presheaf :=
    modulePresheaf_isSheaf R M (P.obj M) (e M) (hres M)
  let Q (M : TopModuleCat.{u} R) : Sheaf J Ab.{u + 1} := ⟨(P.obj M).presheaf, hs M⟩
  have hm (M : TopModuleCat.{u} R) :
      ∃ m : ModObj (continuousCoefficientRingObj R) (Q M),
        Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
          (continuousCoefficientRingObj R) (Q M) ≫ m.smul.hom = β M :=
    moduleAction_exists R (P.obj M) (hs M) (β M) (hβ M)
  choose m hn using hm
  let F : TopModuleCat.{u} R ⥤
      Mod (Sheaf J Ab.{u + 1}) (continuousCoefficientRingObj R) :=
    { obj := fun M ↦ { X := Q M, mod := m M }
      map := fun {M N} f ↦
        { hom := ⟨(PresheafOfModules.toPresheaf _).map (P.map f)⟩
          isModHom := ⟨by
            exact action_linear R _ _ _ _ _ _ _ (hn M) (hn N) (hlinear M N f)⟩ }
      map_id := by
        intro M
        apply Mod.hom_ext
        apply Sheaf.hom_ext
        change (PresheafOfModules.toPresheaf _).map (P.map (𝟙 M)) = 𝟙 _
        exact (congrArg (PresheafOfModules.toPresheaf _).map (P.map_id M)).trans
          ((PresheafOfModules.toPresheaf _).map_id _)
      map_comp := by
        intro M N K f g
        apply Mod.hom_ext
        apply Sheaf.hom_ext
        change (PresheafOfModules.toPresheaf _).map (P.map (f ≫ g)) = _
        rw [P.map_comp, Functor.map_comp]
        rfl }
  refine ⟨F, e, ?_, hres, ?_, hmap, ?_, ?_⟩
  · constructor
    intro M N f g
    apply Mod.hom_ext
    apply Sheaf.hom_ext
    change (PresheafOfModules.toPresheaf _).map (P.map (f + g)) = _
    rw [P.map_add, Functor.map_add]
    rfl
  · intro M
    constructor
    · intro S a h s
      change e M S (((m M).smul.hom.app (op S))
        ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
          (continuousCoefficientRingObj R) (Q M)).app (op S)
            (ULift.up a ⊗ₜ[ℤ] (e M S).symm h))) s = _
      have heq := ConcreteCategory.congr_hom (congr_app (hn M) (op S))
        (ULift.up a ⊗ₜ[ℤ] (e M S).symm h)
      change (m M).smul.hom.app (op S)
        ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
          (continuousCoefficientRingObj R) (Q M)).app (op S)
            (ULift.up a ⊗ₜ[ℤ] (e M S).symm h)) = _ at heq
      exact (congrArg (fun x : (P.obj M).obj (op S) ↦ e M S x s)
        (heq.trans (hβ M S (ULift.up a) ((e M S).symm h)))).trans
        ((hsmul M S a ((e M S).symm h) s).trans
          (congrArg (fun k : C(S, M) ↦ a s • k s) ((e M S).apply_symm_apply h)))
    · intro g hg
      apply Sheaf.tensor_hom_ext
      change Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
        (continuousCoefficientRingObj R) (Q M) ≫ g.hom =
        Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
          (continuousCoefficientRingObj R) (Q M) ≫ (m M).smul.hom
      rw [hn M]
      apply hβuniq M
      intro S a h
      apply (e M S).injective
      ext s
      have hh := hg S a.down (e M S h) s
      have ht : continuousModuleTensorGenerator R (F.obj M).X S a.down
          ((e M S).symm (e M S h)) =
          (Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
            (continuousCoefficientRingObj R) (Q M)).app (op S) (a ⊗ₜ[ℤ] h) :=
        congrArg (fun x ↦ (Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
          (continuousCoefficientRingObj R) (Q M)).app (op S) (a ⊗ₜ[ℤ] x))
          ((e M S).symm_apply_apply h)
      exact (congrArg (fun x ↦ e M S (g.hom.app (op S) x) s) ht).symm.trans
        (hh.trans (hsmul M S a.down h s).symm)
  · intro I _ M
    apply moduleProduct R F e hmap I M
    refine isLimitOfIsLimitFanMkObj (sheafToPresheaf J Ab.{u + 1})
      (fun i : I ↦ (F.obj (M i)).X)
      (fun i : I ↦ (F.map (TopModuleCat.ofHom (ContinuousLinearMap.proj i))).hom) ?_
    exact isLimitFanMkObjOfIsLimit (PresheafOfModules.toPresheaf _)
      (fun i : I ↦ P.obj (M i))
      (fun i : I ↦ P.map (TopModuleCat.ofHom (ContinuousLinearMap.proj i)))
      (hprod I M).choose_spec.2.2.2.2.some
  · let : MonObj (continuousCoefficientRingObj R).obj :=
      (continuousCoefficientRingPresheaf R).monObjCompForget₂
    let t : Q (TopModuleCat.of R R) ≅ continuousCoefficientRingObj R :=
      { hom := ⟨(PresheafOfModules.toPresheaf _).map r.hom⟩
        inv := ⟨(PresheafOfModules.toPresheaf _).map r.inv⟩
        hom_inv_id := by
          apply Sheaf.hom_ext
          exact (PresheafOfModules.toPresheaf _).mapIso r |>.hom_inv_id
        inv_hom_id := by
          apply Sheaf.hom_ext
          exact (PresheafOfModules.toPresheaf _).mapIso r |>.inv_hom_id }
    refine ⟨Mod.isoMk t ?_, hr⟩
    exact action_linear R _ _ _ _ _ _ _ (hn (TopModuleCat.of R R))
      (Sheaf.μ_comp_map_mul (continuousCoefficientRingObj R)) hrβ

end Profinite
