/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.ModuleCupResolutionFMap
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
import Sheaf.Paper.ModuleCupPullbackFlasqueComplexes
import all Sheaf.Paper.ModuleCupPairingExists

/-! # Pullback of augmented computing pairings

Source: Stacks Project, Tags 0FKS and 0FKU, functorial Godement resolutions
and the Alexander--Whitney tensor pairing.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Package an augmented flasque tensor-paired complex into computing resolutions. -/
private def computingPairing {X : Scheme.{v}} {F G : X.Modules} [MonoidalPreadditive X.Modules]
    (K L M : CochainComplex X.Modules ℤ)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶ K)
    (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶ L)
    (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶ M)
    (ha : QuasiIso a) (hb : QuasiIso b) (hc : QuasiIso c)
    (hK : K.IsStrictlyGE 0) (hL : L.IsStrictlyGE 0) (hM : M.IsStrictlyGE 0)
    (fK : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (K.X n)))
    (fL : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (L.X n)))
    (fM : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (M.X n)))
    (t : HomologicalComplex.tensorObj K L ⟶ M)
    (ht : ∀ (V : X.Opens)
      (x : Γ(((CochainComplex.singleFunctor X.Modules 0).obj F).X 0, V))
      (y : Γ(((CochainComplex.singleFunctor X.Modules 0).obj G).X 0, V)),
      (t.f 0).val.app (op V)
        ((HomologicalComplex.ιTensorObj K L 0 0 0 (by simp)).val.app (op V)
          (tmulSection ((a.f 0).val.app (op V) x) ((b.f 0).val.app (op V) y))) =
        (c.f 0).val.app (op V) (tmulSection x y)) :
    CupResolutionPairing F G := by
  have := ha
  have := hb
  have := hc
  have := hK
  have := hL
  have := hM
  have := natAugmentation_quasiIso a
  have := natAugmentation_quasiIso b
  have := natAugmentation_quasiIso c
  refine {
    left := computingFlasqueResolution _ (natAugmentation a) (fun n ↦ fK n)
    right := computingFlasqueResolution _ (natAugmentation b) (fun n ↦ fL n)
    target := computingFlasqueResolution _ (natAugmentation c) (fun n ↦ fM n)
    pair := tensorChainSectionPair K L M t
    restriction := ?_
    leibniz := ?_
    augmentation_pair := ?_ }
  · intro r s V W h x y
    change (M.X ((r + s : ℕ) : ℤ)).presheaf.map (homOfLE h).op
      (tensorChainSectionPair K L M t r s V x y) =
        tensorChainSectionPair K L M t r s W
          ((K.X (r : ℤ)).presheaf.map (homOfLE h).op x)
          ((L.X (s : ℤ)).presheaf.map (homOfLE h).op y)
    have hres := tensorSection_restriction
      (HomologicalComplex.ιTensorObj K L (r : ℤ) (s : ℤ) ((r + s : ℕ) : ℤ)
        (by simp) ≫ t.f _) V W h x y
    simpa only [tensorChainSectionPair_apply, Hom.comp_app,
      ConcreteCategory.comp_apply, app_val_apply] using hres
  · intro r s V x y
    have hs := tensorChain_leibniz K L M t (r : ℤ) (s : ℤ) V x y
    change (M.d ((r + s : ℕ) : ℤ) ((r + s + 1 : ℕ) : ℤ)).val.app (op V)
      (tensorChainSectionPair K L M t r s V x y) =
      (eqToHom (congrArg (fun n : ℕ ↦ M.X (n : ℤ))
        (show r + 1 + s = r + s + 1 by omega))).val.app (op V)
        (tensorChainSectionPair K L M t (r + 1) s V
          ((K.d (r : ℤ) ((r + 1 : ℕ) : ℤ)).val.app (op V) x) y) +
      (-1 : ℤ) ^ r •
        (eqToHom (congrArg (fun n : ℕ ↦ M.X (n : ℤ))
          (show r + (s + 1) = r + s + 1 by omega))).val.app (op V)
          (tensorChainSectionPair K L M t r (s + 1) V x
            ((L.d (s : ℤ) ((s + 1 : ℕ) : ℤ)).val.app (op V) y))
    rw [tensorChainSectionPair_transport K L M t (r + 1) s (r + s + 1) (by omega),
      tensorChainSectionPair_transport K L M t r (s + 1) (r + s + 1) (by omega),
      tensorChainSectionPair_apply]
    simp only [app_val_apply, Units.smul_def, Int.coe_negOnePow_natCast] at hs
    exact hs
  · intro V x y
    change tensorChainSectionPair K L M t 0 0 V
      (((natAugmentation a).f 0).val.app (op V) x)
      (((natAugmentation b).f 0).val.app (op V) y) =
      ((natAugmentation c).f 0).val.app (op V) (tmulSection x y)
    simp only [natAugmentation, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    rw [tensorChainSectionPair_apply]
    exact ht V x y


/-- Pullback admits simultaneous sheaf cochain maps of computing pairings over the
three coefficient f-maps, preserving the pairing before passing to cohomology.
Source: Stacks Project, Tag 0FKS, cohomology-lemma-godement-resolution;
Tag 0FKU, section-cup-product, naive products and Lemma 20.31.3.
(blueprint: lem-sc-module-cup-pullback-augmented-pairings).

Proof: take the concrete cosimplicial Godement models on X and X' for the three
coefficients. On an open V, send the coordinate indexed by f(x') through the
stalk map of the coefficient f-map to the coordinate indexed by x' over f-inverse V.
The germ unit commutes with these maps since both sides take the germ of the
image section. Stalk evaluation commutes since both sides evaluate that same
coordinate. Iteration therefore commutes with cofaces and codegeneracies and
gives maps of the augmented alternating complexes into the termwise pushforward.
For the tensor coefficient compose with the Godement map induced by the canonical
tensor-pullback comparison. Its normalization on section tensors and coordinatewise
tensoring imply compatibility with the Godement tensor pairing. The front and back
faces defining Alexander--Whitney commute with these maps, so the pairing equation
holds in every bidegree. Restrict to natural indices. Godement terms are flasque,
and their augmented stalk complexes contract by evaluation. Choose injective
comparisons over the three augmentations on each scheme; flasque acyclicity and
acyclic resolution comparison show that these compute cohomology. This constructs
D and E without imposing any cohomology-class equations. The augmentation equations
are the degree-zero germ equations. Taking sections and restricting along the
canonical equality f-inverse(top)=top gives the stated strict equation.
Empty schemes have empty stalk products, zero coefficients give zero products,
and degree zero uses the ordinary germ tensor equation. No exactness of tensor
pullback or flatness of the coefficients is required. -/
theorem moduleCup_pullback_augmented_pairings (X X' : Scheme.{v}) (f : X' ⟶ X)
    (F G : X.Modules) :
    ∃ (D : CupResolutionPairing F G)
      (E : CupResolutionPairing ((tensorPullback f).obj F) ((tensorPullback f).obj G))
      (l : D.left.K ⟶
        ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj E.left.K)
      (r : D.right.K ⟶
        ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj E.right.K)
      (t : D.target.K ⟶
        ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj E.target.K),
      (D.left.augmentation.f 0 ≫ l.f 0 =
        (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F ≫
          (pushforward f).map (E.left.augmentation.f 0)) ∧
      (D.right.augmentation.f 0 ≫ r.f 0 =
        (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G ≫
          (pushforward f).map (E.right.augmentation.f 0)) ∧
      (D.target.augmentation.f 0 ≫ t.f 0 =
        (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app (F ⊗ G) ≫
          (pushforward f).map ((Classical.choose (module_pullback_tensor f) F G).hom) ≫
          (pushforward f).map (E.target.augmentation.f 0)) ∧
      (∀ (p q : ℕ) (a : Γ(D.left.K.X p, ⊤)) (b : Γ(D.right.K.X q, ⊤)),
        (cupResolutionGlobalMap f t).f (p + q) (D.pair p q ⊤ a b) =
          E.pair p q ⊤ ((cupResolutionGlobalMap f l).f p a)
            ((cupResolutionGlobalMap f r).f q b)) := by
  let : MonoidalPreadditive X.Modules :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalPreadditive X'.Modules :=
    Classical.choice (SheafOfModules.tensorClosed X'.sheaf).1
  have h := moduleCup_pullback_flasque_complexes X X' f F G
  rcases h with ⟨K, L, M, a, b, c, h⟩
  rcases h with ⟨ha, hb, hc, hK, hL, hM, fK, fL, fM, u, hu, h⟩
  rcases h with ⟨K₁, L₁, M₁, a₁, b₁, c₁, h⟩
  rcases h with ⟨ha₁, hb₁, hc₁, hK₁, hL₁, hM₁, fK₁, fL₁, fM₁, u₁, hu₁,
    l, r, t, hl, hr, ht, hpair⟩
  let D := computingPairing K L M a b c ha hb hc hK hL hM fK fL fM u hu
  let E := computingPairing K₁ L₁ M₁ a₁ b₁ c₁ ha₁ hb₁ hc₁
    hK₁ hL₁ hM₁ fK₁ fL₁ fM₁ u₁ hu₁
  let ln : D.left.K ⟶
      ((pushforward f).mapHomologicalComplex (.up ℕ)).obj E.left.K :=
    HomologicalComplex.restrictionMap l ComplexShape.embeddingUpNat
  let rn : D.right.K ⟶
      ((pushforward f).mapHomologicalComplex (.up ℕ)).obj E.right.K :=
    HomologicalComplex.restrictionMap r ComplexShape.embeddingUpNat
  let tn : D.target.K ⟶
      ((pushforward f).mapHomologicalComplex (.up ℕ)).obj E.target.K :=
    HomologicalComplex.restrictionMap t ComplexShape.embeddingUpNat
  refine ⟨D, E, ln, rn, tn, ?_, ?_, ?_, ?_⟩
  · change (natAugmentation a).f 0 ≫ l.f 0 = _
    simpa only [D, E, computingPairing, computingFlasqueResolution,
      natAugmentation, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero] using hl
  · change (natAugmentation b).f 0 ≫ r.f 0 = _
    simpa only [D, E, computingPairing, computingFlasqueResolution,
      natAugmentation, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero] using hr
  · change (natAugmentation c).f 0 ≫ t.f 0 = _
    simpa only [D, E, computingPairing, computingFlasqueResolution,
      natAugmentation, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero] using ht
  · intro p q x y
    change (cupResolutionGlobalMap f tn).f (p + q)
      (tensorChainSectionPair K L M u p q ⊤ x y) =
      tensorChainSectionPair K₁ L₁ M₁ u₁ p q ⊤
        ((cupResolutionGlobalMap f ln).f p x) ((cupResolutionGlobalMap f rn).f q y)
    have hs := hpair p q ⊤ x y
    simp only [← tensorChainSectionPair_apply] at hs
    change (M₁.X ((p + q : ℕ) : ℤ)).presheaf.map
        (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : X.Opens)) ⟶ op (⊤ : X'.Opens))
        ((t.f ((p + q : ℕ) : ℤ)).val.app (op ⊤)
          (tensorChainSectionPair K L M u p q ⊤ x y)) =
      tensorChainSectionPair K₁ L₁ M₁ u₁ p q ⊤
        ((K₁.X (p : ℤ)).presheaf.map
          (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : X.Opens)) ⟶ op (⊤ : X'.Opens))
          ((l.f (p : ℤ)).val.app (op ⊤) x))
        ((L₁.X (q : ℤ)).presheaf.map
          (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : X.Opens)) ⟶ op (⊤ : X'.Opens))
          ((r.f (q : ℤ)).val.app (op ⊤) y))
    rw [hs]
    have hres := tensorSection_restriction
      (HomologicalComplex.ιTensorObj K₁ L₁ (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ)
        (by simp) ≫ u₁.f _) (f ⁻¹ᵁ ⊤) ⊤ (by simp)
      ((l.f (p : ℤ)).val.app (op ⊤) x) ((r.f (q : ℤ)).val.app (op ⊤) y)
    have he : (homOfLE (show (⊤ : X'.Opens) ≤ f ⁻¹ᵁ (⊤ : X.Opens) by simp)).op =
        (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : X.Opens)) ⟶ op (⊤ : X'.Opens)) :=
      Subsingleton.elim _ _
    simpa only [tensorChainSectionPair_apply, Hom.comp_app,
      ConcreteCategory.comp_apply, app_val_apply, he] using hres

end
end AlgebraicGeometry.Scheme.Modules
