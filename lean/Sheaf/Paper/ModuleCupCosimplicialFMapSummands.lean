/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Paper.ModuleCupAWComponents

/-! # Cross-scheme naturality of front/back summands

This construction uses only paired cosimplicial objects and natural transformations to pushforward.
Source: Banerjee, arXiv:1004.1491, §1.1.4, front/back formula; Stacks, Tag 0FKU.
(blueprint: new-module-cup-cosimplicial-fmap-summands).
No Godement construction or resolution property enters the argument.
-/

@[expose] public section
universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private theorem app_inv_hom {X : Scheme.{v}} {M N : X.Modules} (e : M ≅ N)
    (V : X.Opens) (s : Γ(N, V)) : e.hom.app V (e.inv.app V s) = s := by
  have he := congrArg (fun z : N ⟶ N ↦ z.app V s) e.inv_hom_id
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app,
    ConcreteCategory.id_apply] using he

private def crossComponent (X X' : Scheme.{v}) (f : X' ⟶ X)
    (A : CosimplicialObject X.Modules) (A' : CosimplicialObject X'.Modules)
    (g : A ⟶ A' ⋙ pushforward f) (n : ℤ) :
    (moduleCup_cosimplicialComplex X A).X n ⟶
      (pushforward f).obj ((moduleCup_cosimplicialComplex X' A').X n) :=
  if hn : 0 ≤ n then
    (((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
      ComplexShape.embeddingUpNat (i := n.toNat) (Int.toNat_of_nonneg hn)).hom ≫
      g.app ⦋n.toNat⦌ ≫ (pushforward f).map
        ((((alternatingCofaceMapComplex X'.Modules).obj A').extendXIso
          ComplexShape.embeddingUpNat (i := n.toNat) (Int.toNat_of_nonneg hn)).inv)
  else 0

private theorem crossComponent_nat (X X' : Scheme.{v}) (f : X' ⟶ X)
    (A : CosimplicialObject X.Modules) (A' : CosimplicialObject X'.Modules)
    (g : A ⟶ A' ⋙ pushforward f) (n : ℕ) :
    crossComponent X X' f A A' g (n : ℤ) =
      (((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
        ComplexShape.embeddingUpNat (i := n) rfl).hom ≫ g.app ⦋n⦌ ≫
        (pushforward f).map
          ((((alternatingCofaceMapComplex X'.Modules).obj A').extendXIso
            ComplexShape.embeddingUpNat (i := n) rfl).inv) := by
  simp only [crossComponent, Nat.cast_nonneg, dif_pos, Int.toNat_natCast]

private theorem crossComponent_comm (X X' : Scheme.{v}) (f : X' ⟶ X)
    (A : CosimplicialObject X.Modules) (A' : CosimplicialObject X'.Modules)
    (g : A ⟶ A' ⋙ pushforward f) (n : ℤ) :
    crossComponent X X' f A A' g n ≫
        (pushforward f).map ((moduleCup_cosimplicialComplex X' A').d n (n + 1)) =
      (moduleCup_cosimplicialComplex X A).d n (n + 1) ≫
        crossComponent X X' f A A' g (n + 1) := by
  -- In nonnegative degrees, conjugate the alternating coface naturality equation.
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have he : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by simp
    rw [he, crossComponent_nat, crossComponent_nat]
    dsimp only [moduleCup_cosimplicialComplex] at *
    erw [HomologicalComplex.extend_d_eq _ _ (i := m) (j := m + 1) rfl rfl,
      HomologicalComplex.extend_d_eq _ _ (i := m) (j := m + 1) rfl rfl]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]
    have hd : g.app ⦋m⦌ ≫ (pushforward f).map
        (((alternatingCofaceMapComplex X'.Modules).obj A').d m (m + 1)) =
      (((alternatingCofaceMapComplex X.Modules).obj A).d m (m + 1)) ≫ g.app ⦋m + 1⦌ := by
      simp only [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
        CochainComplex.of_d]
      simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul,
        Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
        Preadditive.zsmul_comp]
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun z ↦ ((-1 : ℤ) ^ (i : ℕ)) • z) (g.naturality _).symm
    erw [Functor.map_comp, ← Category.assoc (g.app _) ((pushforward f).map _), hd]
    simp only [Category.assoc]
  -- Every negative source term is zero, including the boundary degree -1.
  · have hz : IsZero ((moduleCup_cosimplicialComplex X A).X n) := by
      apply HomologicalComplex.isZero_extend_X
      intro i hi
      change (i : ℤ) = n at hi
      omega
    exact hz.eq_of_src _ _

private def crossMap (X X' : Scheme.{v}) (f : X' ⟶ X)
    (A : CosimplicialObject X.Modules) (A' : CosimplicialObject X'.Modules)
    (g : A ⟶ A' ⋙ pushforward f) :
    moduleCup_cosimplicialComplex X A ⟶
      ((pushforward f).mapHomologicalComplex (.up ℤ)).obj
        (moduleCup_cosimplicialComplex X' A') :=
  CochainComplex.ofHom (crossComponent X X' f A A' g)
    (crossComponent_comm X X' f A A' g)

/-- Pushforward comparisons of paired cosimplicial objects induce comparisons of each
front/back summand after alternating cofaces and extension by zero.
Source: Banerjee, arXiv:1004.1491, §1.1.4, p. 16, front/back formula;
Stacks Project, Tag 0FKU, alternating coface complexes.
(blueprint: new-module-cup-cosimplicial-fmap-summands)
Proof: In natural degree n use the component of the given natural transformation.
Its naturality with each coface, summed with alternating signs, is the cochain
map equation because pushforward is additive. In integral degree n ≥ 0 conjugate
this component by the source extension identification and the pushforward of the
inverse target extension identification. In negative degrees use the zero map.
The extension differential formula verifies the map equation in nonnegative
adjacent degrees. For negative source degrees the source object is zero; for
nonadjacent degrees both differentials vanish. These maps give l,r,t and the
three component formulas. Unfold a front/back summand in bidegree (p,q).
The extension identifications cancel. Tensor morphisms send pure section tensors
to tensors of the two section images. Naturality of g and h moves their components
past the front inclusion [p] → [p+q] and back inclusion [q] → [p+q]. Apply hμ
in degree p+q. Naturality of the inverse extension identifications then yields
exactly the displayed section equality. In bidegree (0,0) both simplex maps
are identities; zero coefficients give zero tensors. No Godement models,
coefficient maps, augmentations, exactness or quasi-isomorphisms are assumed. -/
theorem moduleCup_cosimplicial_fmap_summands (X X' : Scheme.{v}) (f : X' ⟶ X)
    [MonoidalPreadditive X.Modules] [MonoidalPreadditive X'.Modules]
    (A B C : CosimplicialObject X.Modules) (A₁ B₁ C₁ : CosimplicialObject X'.Modules)
    (μ : moduleCup_cosimplicialTensor X A B ⟶ C)
    (μ₁ : moduleCup_cosimplicialTensor X' A₁ B₁ ⟶ C₁)
    (g : A ⟶ A₁ ⋙ pushforward f) (h : B ⟶ B₁ ⋙ pushforward f)
    (k : C ⟶ C₁ ⋙ pushforward f)
    (hμ : ∀ (n : SimplexCategory) (V : X.Opens)
      (x : Γ(A.obj n, V)) (y : Γ(B.obj n, V)),
      (k.app n).val.app (op V) ((μ.app n).val.app (op V) (tmulSection x y)) =
        (μ₁.app n).val.app (op (f ⁻¹ᵁ V))
          (tmulSection ((g.app n).val.app (op V) x) ((h.app n).val.app (op V) y))) :
        ∃ (l : moduleCup_cosimplicialComplex X A ⟶
            ((pushforward f).mapHomologicalComplex (.up ℤ)).obj
              (moduleCup_cosimplicialComplex X' A₁))
          (r : moduleCup_cosimplicialComplex X B ⟶
            ((pushforward f).mapHomologicalComplex (.up ℤ)).obj
              (moduleCup_cosimplicialComplex X' B₁))
          (t : moduleCup_cosimplicialComplex X C ⟶
            ((pushforward f).mapHomologicalComplex (.up ℤ)).obj
              (moduleCup_cosimplicialComplex X' C₁)),
          (∀ n : ℕ, l.f (n : ℤ) =
            (((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
              ComplexShape.embeddingUpNat (i := n) rfl).hom ≫ g.app ⦋n⦌ ≫
              (pushforward f).map
                ((((alternatingCofaceMapComplex X'.Modules).obj A₁).extendXIso
                  ComplexShape.embeddingUpNat (i := n) rfl).inv)) ∧
          (∀ n : ℕ, r.f (n : ℤ) =
            (((alternatingCofaceMapComplex X.Modules).obj B).extendXIso
              ComplexShape.embeddingUpNat (i := n) rfl).hom ≫ h.app ⦋n⦌ ≫
              (pushforward f).map
                ((((alternatingCofaceMapComplex X'.Modules).obj B₁).extendXIso
                  ComplexShape.embeddingUpNat (i := n) rfl).inv)) ∧
          (∀ n : ℕ, t.f (n : ℤ) =
            (((alternatingCofaceMapComplex X.Modules).obj C).extendXIso
              ComplexShape.embeddingUpNat (i := n) rfl).hom ≫ k.app ⦋n⦌ ≫
              (pushforward f).map
                ((((alternatingCofaceMapComplex X'.Modules).obj C₁).extendXIso
                  ComplexShape.embeddingUpNat (i := n) rfl).inv)) ∧
          ∀ (p q : ℕ) (V : X.Opens)
            (x : Γ((moduleCup_cosimplicialComplex X A).X (p : ℤ), V))
            (y : Γ((moduleCup_cosimplicialComplex X B).X (q : ℤ), V)),
            (t.f ((p + q : ℕ) : ℤ)).val.app (op V)
              ((moduleCup_awSummand X A B C μ (p : ℤ) (q : ℤ)
                ((p + q : ℕ) : ℤ) (by simp)).val.app (op V) (tmulSection x y)) =
            (moduleCup_awSummand X' A₁ B₁ C₁ μ₁ (p : ℤ) (q : ℤ)
              ((p + q : ℕ) : ℤ) (by simp)).val.app (op (f ⁻¹ᵁ V))
                (tmulSection ((l.f (p : ℤ)).val.app (op V) x)
                  ((r.f (q : ℤ)).val.app (op V) y)) := by
  refine ⟨crossMap X X' f A A₁ g, crossMap X X' f B B₁ h,
    crossMap X X' f C C₁ k, crossComponent_nat X X' f A A₁ g,
    crossComponent_nat X X' f B B₁ h, crossComponent_nat X X' f C C₁ k, ?_⟩
  intro p q V x y
  change (crossComponent X X' f C C₁ k ((p + q : ℕ) : ℤ)).val.app (op V)
    ((moduleCup_awSummand X A B C μ (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ)
      (by simp)).val.app (op V) (tmulSection x y)) =
    (moduleCup_awSummand X' A₁ B₁ C₁ μ₁ (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ)
      (by simp)).val.app (op (f ⁻¹ᵁ V))
        (tmulSection ((crossComponent X X' f A A₁ g (p : ℤ)).val.app (op V) x)
          ((crossComponent X X' f B B₁ h (q : ℤ)).val.app (op V) y))
  rw [crossComponent_nat, crossComponent_nat, crossComponent_nat]
  simp only [moduleCup_awSummand, Nat.cast_nonneg, dif_pos, Int.toNat_natCast]
  let eA := (((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
    ComplexShape.embeddingUpNat (i := p) rfl)
  let eB := (((alternatingCofaceMapComplex X.Modules).obj B).extendXIso
    ComplexShape.embeddingUpNat (i := q) rfl)
  let eC := (((alternatingCofaceMapComplex X.Modules).obj C).extendXIso
    ComplexShape.embeddingUpNat (i := p + q) rfl)
  let eA₁ := (((alternatingCofaceMapComplex X'.Modules).obj A₁).extendXIso
    ComplexShape.embeddingUpNat (i := p) rfl)
  let eB₁ := (((alternatingCofaceMapComplex X'.Modules).obj B₁).extendXIso
    ComplexShape.embeddingUpNat (i := q) rfl)
  let eC₁ := (((alternatingCofaceMapComplex X'.Modules).obj C₁).extendXIso
    ComplexShape.embeddingUpNat (i := p + q) rfl)
  let α := SimplexCategory.subinterval (n := p + q) 0 p (by omega)
  let δ := SimplexCategory.subinterval (n := p + q) p q (by omega)
  change (eC.hom ≫ k.app ⦋p + q⦌ ≫ (pushforward f).map eC₁.inv).app V
    (((eA.hom ⊗ₘ eB.hom) ≫ (A.map α ⊗ₘ B.map δ) ≫ μ.app ⦋p + q⦌ ≫ eC.inv).app V
      (tmulSection x y)) =
    ((eA₁.hom ⊗ₘ eB₁.hom) ≫ (A₁.map α ⊗ₘ B₁.map δ) ≫ μ₁.app ⦋p + q⦌ ≫ eC₁.inv).app
      (f ⁻¹ᵁ V) (tmulSection
        ((eA.hom ≫ g.app ⦋p⦌ ≫ (pushforward f).map eA₁.inv).app V x)
        ((eB.hom ≫ h.app ⦋q⦌ ≫ (pushforward f).map eB₁.inv).app V y))
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection]
  simp only [pushforward_map_app]
  erw [app_inv_hom eC V, app_inv_hom eA₁ (f ⁻¹ᵁ V), app_inv_hom eB₁ (f ⁻¹ᵁ V)]
  -- Evaluate naturality at the two front/back inclusions on the given sections.
  have hg := congrArg (fun z ↦ z.app V (eA.hom.app V x)) (g.naturality α)
  have hh := congrArg (fun z ↦ z.app V (eB.hom.app V y)) (h.naturality δ)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, Functor.comp_map,
    pushforward_map_app] at hg hh
  have hm := hμ ⦋p + q⦌ V ((A.map α).app V (eA.hom.app V x))
    ((B.map δ).app V (eB.hom.app V y))
  change eC₁.inv.app (f ⁻¹ᵁ V)
    ((k.app ⦋p + q⦌).app V ((μ.app ⦋p + q⦌).app V
      (tmulSection ((A.map α).app V (eA.hom.app V x))
        ((B.map δ).app V (eB.hom.app V y))))) = _
  erw [hm, hg, hh]
  rfl

end
end AlgebraicGeometry.Scheme.Modules
