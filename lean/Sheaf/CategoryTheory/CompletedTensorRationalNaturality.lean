/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.CategoryTheory.Products.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Naturality and rationalization of a completed tensor comparison

Source: Weil conjectures blueprint, main-20261015, `def-wf-tensor-product`, second
sentence (tensor Frobenius); the abstract reflector and rationalization argument
(blueprint: lem-sf-completed-tensor-rational-naturality).

## Main definitions and statements

- `restriction`: the restriction P of H.
- `tensor`: the completed bifunctor B.
- `comparison`: the given component d = c ; L(tau).
- `naturality_and_rationalization`: naturality and the unique localized isomorphism.

The full subcategory is Mathlib's `ObjectProperty.FullSubcategory`. The raw localization
uses the project's scalar-first tensor convention: `f/p^n` is `p⁻ⁿ ⊗ f`.
The object and fraction formulas for the supplied localized functors use heterogeneous
equality only to accommodate their specified, rather than definitional, object maps.
-/

@[expose] public section

universe r u v

open TensorProduct

namespace CategoryTheory.CompletedTensorComparison

variable {D : Type u} [Category.{v} D] (C : ObjectProperty D)
  (L : D ⥤ C.FullSubcategory) (H : D ≌ D)
  (hH : ∀ M : C.FullSubcategory, C (H.functor.obj M.obj))
  (T : D × D ⥤ D)

/-- The restriction P of H to the full subcategory.
Source: blueprint `def-wf-tensor-product`, tensor Frobenius
(blueprint: lem-sf-completed-tensor-rational-naturality). -/
def restriction : C.FullSubcategory ⥤ C.FullSubcategory :=
  C.lift (C.ι ⋙ H.functor) hH

/-- The completed bifunctor B(M,N) = L(T(M,N)).
Source: blueprint `def-wf-tensor-product`, tensor Frobenius
(blueprint: lem-sf-completed-tensor-rational-naturality). -/
def tensor : C.FullSubcategory × C.FullSubcategory ⥤ C.FullSubcategory :=
  (C.ι.prod C.ι) ⋙ T ⋙ L

/-- The specified component d = c ; L(tau), regarded in the full subcategory.
Source: blueprint `def-wf-tensor-product`, tensor Frobenius
(blueprint: lem-sf-completed-tensor-rational-naturality). -/
def comparison
    (c : ∀ X : D, H.functor.obj (C.ι.obj (L.obj X)) ≅ C.ι.obj (L.obj (H.functor.obj X)))
    (τ : T ⋙ H.functor ≅ (H.functor.prod H.functor) ⋙ T)
    (M N : C.FullSubcategory) :
    (restriction C H hH).obj ((tensor C L T).obj (M, N)) ≅
      (tensor C L T).obj ((restriction C H hH).obj M, (restriction C H hH).obj N) :=
  ObjectProperty.isoMk C
    (c (T.obj (M.obj, N.obj)) ≪≫ C.ι.mapIso (L.mapIso (τ.app (M.obj, N.obj))))

private theorem tensor_fraction (A : Type r) [CommRing A] (p : A)
    (V : Type v) [AddCommGroup V] [Module A V]
    (x : Localization.Away p ⊗[A] V) :
    ∃ (f : V) (n : ℕ), x =
      (IsLocalization.Away.invSelf (S := Localization.Away p) p ^ n) ⊗ₜ[A] f := by
  obtain ⟨⟨f, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers p)
    (TensorProduct.mk A (Localization.Away p) V 1) x
  obtain ⟨n, hn⟩ := s.property
  refine ⟨f, n, ?_⟩
  have hi : (IsLocalization.Away.invSelf (S := Localization.Away p) p ^ n) *
      algebraMap A (Localization.Away p) (p ^ n) = 1 := by
    rw [map_pow, ← mul_pow, mul_comm, IsLocalization.Away.mul_invSelf, one_pow]
  change (s : A) • x = 1 ⊗ₜ[A] f at hs
  rw [← hn, ← algebraMap_smul (Localization.Away p) (p ^ n) x] at hs
  have hh := congrArg
    (fun y ↦ (IsLocalization.Away.invSelf (S := Localization.Away p) p ^ n) • y) hs
  rw [smul_smul, hi, one_smul] at hh
  simpa only [TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    using hh

private theorem map_heq {E : Type u} [Category.{v} E]
    {F : Type u} [Category.{v} F]
    (J : E ⥤ F) {X Y X' Y' : E} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (J.map f) (J.map g) := by
  subst X'; subst Y'
  cases eq_of_heq h
  rfl

private theorem prod_heq {E : Type u} [Category.{v} E]
    {X Y X' Y' Z W Z' W' : E}
    (hx : X = X') (hy : Y = Y') (hz : Z = Z') (hw : W = W')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Z ⟶ W} {g' : Z' ⟶ W'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (Prod.mkHom f g) (Prod.mkHom f' g') := by
  subst X'; subst Y'; subst Z'; subst W'
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

/-- Unit normalization forces naturality and a unique rational tensor comparison.
Source: blueprint `def-wf-tensor-product`, second sentence (tensor Frobenius)
(blueprint: lem-sf-completed-tensor-rational-naturality).

Proof: (1) rewrite H(eta_X) as eta_(HX) ; c_X.inv. The reflector Hom bijection
then cancels H(eta_X) against any target in C; no global epimorphism is asserted.
(2) Precompose the two candidate naturality composites for c with H(eta_X).
Naturality of eta and the unit equations make them equal, so (1) cancels.
(3) Apply (2) to T(f,g), then functoriality of L and naturality of tau. This gives
simultaneous naturality of d = c ; L(tau).
(4) Use `IsLocalizedModule.isBaseChange` (lem-weil-pbc-localization-module-tensor)
and `LocalizedModule.Away` (def-weil-pbc-module-localization-away) on each Hom
module: every arrow is f/p^n, with equality tested after multiplication by some
power of p. Scalar-localization composition adds denominators.
(5) Define every component to be Q(d). For arbitrary fractions f/p^r and g/p^s,
the prescribed functor formulas reduce naturality to (3), divided by p^(r+s).
This proves an equality in localized Hom modules without cancelling p integrally.
(6) Functoriality of Q gives both inverse identities with Q(d.inv); naturality of
the inverse follows by composing the forward naturality equation with inverses.
Every localized object is an integral object, so the component formula also gives
uniqueness. No step requires torsion-free Hom modules. -/
theorem naturality_and_rationalization
    (A : Type r) [CommRing A] [Preadditive D] [Linear A D] (p : A)
    [L.Additive] [L.Linear A] [H.functor.Additive] [H.functor.Linear A]
    [(restriction C H hH).IsEquivalence]
    (η : 𝟭 D ⟶ L ⋙ C.ι)
    (hη : ∀ (X : D) (Y : C.FullSubcategory),
      Function.Bijective (fun f : C.ι.obj (L.obj X) ⟶ Y.obj ↦ η.app X ≫ f))
    (c : ∀ X : D, H.functor.obj (C.ι.obj (L.obj X)) ≅ C.ι.obj (L.obj (H.functor.obj X)))
    (hc : ∀ X : D, H.functor.map (η.app X) ≫ (c X).hom = η.app (H.functor.obj X))
    (hT : ∀ M M' N N' : D,
      ∃ t : (M ⟶ M') →ₗ[A] (N ⟶ N') →ₗ[A] (T.obj (M, N) ⟶ T.obj (M', N')),
        ∀ (f : M ⟶ M') (g : N ⟶ N'), t f g = T.map (Prod.mkHom f g))
    (τ : T ⋙ H.functor ≅ (H.functor.prod H.functor) ⋙ T)
    (Pbar : ScalarLocalization A C.FullSubcategory p ⥤
      ScalarLocalization A C.FullSubcategory p)
    (Bbar : ScalarLocalization A C.FullSubcategory p ×
      ScalarLocalization A C.FullSubcategory p ⥤ ScalarLocalization A C.FullSubcategory p)
    (hPobj : ∀ M : C.FullSubcategory,
      Pbar.obj ⟨M⟩ = ⟨(restriction C H hH).obj M⟩)
    (hBobj : ∀ M N : C.FullSubcategory,
      Bbar.obj (⟨M⟩, ⟨N⟩) = ⟨(tensor C L T).obj (M, N)⟩)
    (hPmap : ∀ (M M' : C.FullSubcategory) (f : M ⟶ M') (n : ℕ),
      HEq (Pbar.map ((IsLocalization.Away.invSelf (S := Localization.Away p) p ^ n) ⊗ₜ[A] f :
        ScalarLocalization.mk (R := A) (p := p) M ⟶ ScalarLocalization.mk M'))
        ((IsLocalization.Away.invSelf (S := Localization.Away p) p ^ n) ⊗ₜ[A]
          (restriction C H hH).map f))
    (hBmap : ∀ (M M' N N' : C.FullSubcategory) (f : M ⟶ M') (g : N ⟶ N') (n m : ℕ),
      HEq (Bbar.map (Prod.mkHom
        ((IsLocalization.Away.invSelf (S := Localization.Away p) p ^ n) ⊗ₜ[A] f :
          ScalarLocalization.mk (R := A) (p := p) M ⟶ ScalarLocalization.mk M')
        ((IsLocalization.Away.invSelf (S := Localization.Away p) p ^ m) ⊗ₜ[A] g :
          ScalarLocalization.mk (R := A) (p := p) N ⟶ ScalarLocalization.mk N')))
        ((IsLocalization.Away.invSelf (S := Localization.Away p) p ^ (n + m)) ⊗ₜ[A]
          (tensor C L T).map (Prod.mkHom f g))) :
    (∀ (X X' : D) (f : X ⟶ X'),
      H.functor.map (C.ι.map (L.map f)) ≫ (c X').hom =
        (c X).hom ≫ C.ι.map (L.map (H.functor.map f))) ∧
    (∀ (M M' N N' : C.FullSubcategory) (f : M ⟶ M') (g : N ⟶ N'),
      (restriction C H hH).map ((tensor C L T).map (Prod.mkHom f g)) ≫
          (comparison C L H hH T c τ M' N').hom =
        (comparison C L H hH T c τ M N).hom ≫
          (tensor C L T).map (Prod.mkHom
            ((restriction C H hH).map f) ((restriction C H hH).map g))) ∧
    ∃! μ : Bbar ⋙ Pbar ≅ (Pbar.prod Pbar) ⋙ Bbar,
      ∀ M N : C.FullSubcategory,
        HEq (μ.hom.app (⟨M⟩, ⟨N⟩))
          ((ScalarLocalization.localization A C.FullSubcategory p).map
            (comparison C L H hH T c τ M N).hom) ∧
        HEq (μ.inv.app (⟨M⟩, ⟨N⟩))
          ((ScalarLocalization.localization A C.FullSubcategory p).map
            (comparison C L H hH T c τ M N).inv) := by
  classical
  have _ := hT
  have hcancel (X : D) (Y : C.FullSubcategory)
      (a b : H.functor.obj (C.ι.obj (L.obj X)) ⟶ Y.obj)
      (h : H.functor.map (η.app X) ≫ a = H.functor.map (η.app X) ≫ b) : a = b := by
    apply (cancel_epi (c X).inv).1
    apply (hη (H.functor.obj X) Y).1
    simpa only [← hc X, Category.assoc, Iso.hom_inv_id_assoc] using h
  have hcn (X X' : D) (f : X ⟶ X') :
      H.functor.map (C.ι.map (L.map f)) ≫ (c X').hom =
        (c X).hom ≫ C.ι.map (L.map (H.functor.map f)) := by
    apply hcancel X (L.obj (H.functor.obj X'))
    calc
      _ = H.functor.map (η.app X ≫ C.ι.map (L.map f)) ≫ (c X').hom := by
        rw [H.functor.map_comp, Category.assoc]
      _ = H.functor.map (f ≫ η.app X') ≫ (c X').hom := by
        rw [show η.app X ≫ C.ι.map (L.map f) = f ≫ η.app X' from
          (η.naturality f).symm]
      _ = H.functor.map f ≫ η.app (H.functor.obj X') := by
        rw [H.functor.map_comp, Category.assoc, hc]
      _ = η.app (H.functor.obj X) ≫ C.ι.map (L.map (H.functor.map f)) :=
        η.naturality (H.functor.map f)
      _ = _ := by rw [← hc X, Category.assoc]
  have hdn (M M' N N' : C.FullSubcategory) (f : M ⟶ M') (g : N ⟶ N') :
      (restriction C H hH).map ((tensor C L T).map (Prod.mkHom f g)) ≫
          (comparison C L H hH T c τ M' N').hom =
        (comparison C L H hH T c τ M N).hom ≫
          (tensor C L T).map (Prod.mkHom
            ((restriction C H hH).map f) ((restriction C H hH).map g)) := by
    apply C.ι.map_injective
    change H.functor.map (C.ι.map (L.map (T.map (Prod.mkHom f.hom g.hom)))) ≫
        ((c _).hom ≫ C.ι.map (L.map (τ.hom.app (M'.obj, N'.obj)))) =
      ((c _).hom ≫ C.ι.map (L.map (τ.hom.app (M.obj, N.obj)))) ≫
        C.ι.map (L.map (T.map (Prod.mkHom (H.functor.map f.hom) (H.functor.map g.hom))))
    rw [← Category.assoc, hcn, Category.assoc, ← C.ι.map_comp, ← L.map_comp]
    have ht := τ.hom.naturality (Prod.mkHom f.hom g.hom)
    dsimp at ht
    rw [ht]
    rw [L.map_comp, C.ι.map_comp, Category.assoc]
  refine ⟨hcn, hdn, ?_⟩
  let Q := ScalarLocalization.localization A C.FullSubcategory p
  let P := restriction C H hH
  let B := tensor C L T
  let d := comparison C L H hH T c τ
  have hp (M N : C.FullSubcategory) :
      (Bbar ⋙ Pbar).obj (⟨M⟩, ⟨N⟩) = Q.obj (P.obj (B.obj (M, N))) :=
    (congrArg Pbar.obj (hBobj M N)).trans (hPobj (B.obj (M, N)))
  have hb (M N : C.FullSubcategory) :
      ((Pbar.prod Pbar) ⋙ Bbar).obj (⟨M⟩, ⟨N⟩) =
        Q.obj (B.obj (P.obj M, P.obj N)) := by
    change Bbar.obj (Pbar.obj ⟨M⟩, Pbar.obj ⟨N⟩) = _
    rw [hPobj M, hPobj N]
    exact hBobj _ _
  let e (M N : C.FullSubcategory) :=
    eqToIso (hp M N) ≪≫ Q.mapIso (d M N) ≪≫ (eqToIso (hb M N)).symm
  have eh (M N : C.FullSubcategory) :
      HEq (e M N).hom (Q.map (d M N).hom) := by
    simp only [e, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv,
      Functor.mapIso_hom, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl
  have ei (M N : C.FullSubcategory) :
      HEq (e M N).inv (Q.map (d M N).inv) := by
    simp only [e, Iso.trans_inv, eqToIso.hom, Iso.symm_inv, eqToIso.inv,
      Functor.mapIso_inv, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl
  have en (X Y : ScalarLocalization A C.FullSubcategory p ×
      ScalarLocalization A C.FullSubcategory p) (f : X ⟶ Y) :
      (Bbar ⋙ Pbar).map f ≫ (e Y.1.obj Y.2.obj).hom =
        (e X.1.obj X.2.obj).hom ≫ ((Pbar.prod Pbar) ⋙ Bbar).map f := by
    rcases X with ⟨⟨M⟩, ⟨N⟩⟩
    rcases Y with ⟨⟨M'⟩, ⟨N'⟩⟩
    rcases f with ⟨f, g⟩
    obtain ⟨f, n, rfl⟩ := tensor_fraction A p (M ⟶ M') f
    obtain ⟨g, m, rfl⟩ := tensor_fraction A p (N ⟶ N') g
    have hl := (map_heq Pbar (hBobj M N) (hBobj M' N')
      (hBmap M M' N N' f g n m)).trans (hPmap _ _ (B.map (Prod.mkHom f g)) (n + m))
    have hr := (map_heq Bbar
      (congrArg₂ Prod.mk (hPobj M) (hPobj N))
      (congrArg₂ Prod.mk (hPobj M') (hPobj N'))
      (prod_heq (hPobj M) (hPobj M') (hPobj N) (hPobj N')
        (hPmap M M' f n) (hPmap N N' g m))).trans
      (hBmap _ _ _ _ (P.map f) (P.map g) n m)
    have hleft := heq_comp (hp M N) (hp M' N') (hb M' N') hl (eh M' N')
    have hright := heq_comp (hp M N) (hb M N) (hb M' N') (eh M N) hr
    apply eq_of_heq
    refine hleft.trans (HEq.trans ?_ hright.symm)
    apply heq_of_eq
    change ScalarLocalization.composition A C.FullSubcategory p _ _ _
        (1 ⊗ₜ[A] (d M' N').hom)
        ((IsLocalization.Away.invSelf p ^ (n + m)) ⊗ₜ[A]
          P.map (B.map (Prod.mkHom f g))) =
      ScalarLocalization.composition A C.FullSubcategory p _ _ _
        ((IsLocalization.Away.invSelf p ^ (n + m)) ⊗ₜ[A]
          B.map (Prod.mkHom (P.map f) (P.map g))) (1 ⊗ₜ[A] (d M N).hom)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    rw [hdn M M' N N' f g]
  let μ : Bbar ⋙ Pbar ≅ (Pbar.prod Pbar) ⋙ Bbar :=
    NatIso.ofComponents (fun X ↦ e X.1.obj X.2.obj) (fun {X Y} f ↦ en X Y f)
  refine ⟨μ, fun M N ↦ ⟨eh M N, ei M N⟩, ?_⟩
  intro ν hν
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact eq_of_heq ((hν X.1.obj X.2.obj).1.trans (eh X.1.obj X.2.obj).symm)

end CategoryTheory.CompletedTensorComparison
