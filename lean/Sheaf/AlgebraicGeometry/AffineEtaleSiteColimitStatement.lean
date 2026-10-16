/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.CategoryTheory.Sites.Continuous
public import Sheaf.CategoryTheory.FinitePrecoverage
public import Sheaf.CategoryTheory.ArrowsFunctor
import Sheaf.AlgebraicGeometry.AffineEtaleBaseChangeSystem
import Sheaf.AlgebraicGeometry.AffineEtaleDescentData
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.AffineEtaleFiniteColimitConstruction

/-! # Statements of the new targets (batch 2) about `AffineEtaleSiteColimit`

Kept in their own module so that `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`,
which the first task's targets use, is unchanged.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Stacks Project, Étale Cohomology, Lemma 0EYL, first paragraph (qcqs case);
Sites, Situation 0A34 and Lemma 09YL.
(blueprint: lem-weil-pbc-affine-etale-site-colimit).

The natural transformations `p` and `q` are the first projections of the base changes.
Their cartesian squares specify the base change functors without another definition.
The projection equations for `gamma` and `delta` specify the canonical comparisons.
The functor `F` is a strictification; `W` is its comparison from the category colimit.

Proof (the node's four steps):
1. Choose U, v, p, q, gamma and delta from
   lem-weil-pbc-affine-etale-base-change-system. Its pullback squares, projection
   equations, normalization, cocycles, covering and pullback preservation, continuity,
   and adjoints supply the first fifteen conjuncts.
2. Apply lem-weil-pbc-affine-etale-descent-data to those pullback squares, the delta
   projection equation and covering preservation. This gives object descent and the
   equivalence for finite covering families, including the empty family.
3. For map descent use thm-pd-spreading-out: convert the map using the q-pullback
   isomorphism, descend its composite with q, and lift to the stage pullback. Naturality
   of q, the delta projection equation and pullback uniqueness give the conjugation
   formula. For eventual equality, naturality of q gives equality after the limit first
   projection; descend this equality using exists_pullback_fst_comp_eq_of_isLimit.
   Naturality of p and pullback extensionality give equality at that stage. These
   étale maps from affine domains to quasi-separated bases are of finite presentation:
   étaleness gives local finite presentation, and
   lem-weil-pbc-qcqs-morphism-permanence supplies quasi-compactness and quasi-separatedness.
4. Strictify the coherent system and form its colimit as in
   lem-weil-pbc-affine-etale-finite-colimit-construction, using finite covering families
   (def-weil-pbc-finite-precoverage). Object and map descent and eventual equality make
   W an equivalence, while covering descent identifies the finite precoverages.
   The final criterion retains finiteness of the source presieve: an equivalence
   can map an infinite presieve to a finite one by identifying source objects. Reassemble
   these witnesses with the preceding nineteen conjuncts. -/
theorem exists_affineEtaleSite_colimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) :
    ∃ (U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
          (D.obj (op j)).FullAffineEtale)
      (v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale)
      (p : ∀ (i j : I) (h : i ≤ j),
        U i j h ⋙ fullAffineEtaleInclusion (D.obj (op j)) ⋙
          Etale.forget (D.obj (op j)) ⋙ Over.forget (D.obj (op j)) ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (q : ∀ i : I,
        v i ⋙ fullAffineEtaleInclusion c.pt ⋙ Etale.forget c.pt ⋙ Over.forget c.pt ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
        U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
      (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i),
      (∀ i : I, U i i le_rfl = 𝟭 _) ∧
      (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((p i j h).app A) ((U i j h).obj A).obj.hom
          A.obj.hom (D.map (homOfLE h).op)) ∧
      (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((q i).app A) ((v i).obj A).obj.hom A.obj.hom (c.π.app (op i))) ∧
      (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i i k le_rfl h) (Iso.refl (U i k h))) ∧
      (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i k k h le_rfl) (Iso.refl (U i k h))) ∧
      (∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i))) ∧
      (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        ((gamma i j k h h').hom.app A).hom.left ≫ (p i k (h.trans h')).app A =
          (p j k h').app ((U i j h).obj A) ≫ (p i j h).app A) ∧
      (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        ((delta i j h).hom.app A).hom.left ≫ (q i).app A =
          (q j).app ((U i j h).obj A) ≫ (p i j h).app A) ∧
      (∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l)
        (A : (D.obj (op i)).FullAffineEtale),
        (gamma j k l h' h'').hom.app ((U i j h).obj A) ≫
            (gamma i j l h (h'.trans h'')).hom.app A =
          (U k l h'').map ((gamma i j k h h').hom.app A) ≫
            (gamma i k l (h.trans h') h'').hom.app A) ∧
      (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        (v k).map ((gamma i j k h h').hom.app A) ≫
            (delta i k (h.trans h')).hom.app A =
          (delta j k h').hom.app ((U i j h).obj A) ≫ (delta i j h).hom.app A) ∧
      (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (U i j h) ∈ fullAffineEtalePrecoverage (D.obj (op j)) ((U i j h).obj A)) ∧
      (∀ (i j : I) (h : i ≤ j) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (U i j h)) ∧
      (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (v i) ∈ fullAffineEtalePrecoverage c.pt ((v i).obj A)) ∧
      (∀ (i : I) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (v i)) ∧
      (∃ (_ : ∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology (D.obj (op j))))
        (_ : ∀ i : I, (v i).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology c.pt)),
        (∀ (i j : I) (h : i ≤ j), ∃ L :
            Sheaf (fullAffineEtaleTopology (D.obj (op i))) (Type u) ⥤
              Sheaf (fullAffineEtaleTopology (D.obj (op j))) (Type u),
          Nonempty (L ⊣ (U i j h).sheafPushforwardContinuous (Type u)
            (fullAffineEtaleTopology (D.obj (op i)))
            (fullAffineEtaleTopology (D.obj (op j)))) ∧ PreservesFiniteLimits L) ∧
        (∀ i : I, ∃ L : Sheaf (fullAffineEtaleTopology (D.obj (op i))) (Type u) ⥤
            Sheaf (fullAffineEtaleTopology c.pt) (Type u),
          Nonempty (L ⊣ (v i).sheafPushforwardContinuous (Type u)
            (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology c.pt)) ∧
          PreservesFiniteLimits L)) ∧
      (∀ A : c.pt.FullAffineEtale,
        ∃ (i : I) (Ai : (D.obj (op i)).FullAffineEtale), Nonempty ((v i).obj Ai ≅ A)) ∧
      (∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale)
        (f : (v i).obj A ⟶ (v i).obj B),
        ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
          f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B) ∧
      (∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale) (f g : A ⟶ B),
        (v i).map f = (v i).map g →
          ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g) ∧
      (∀ (n : ℕ) (A : c.pt.FullAffineEtale) (B : Fin n → c.pt.FullAffineEtale)
        (f : ∀ a : Fin n, B a ⟶ A),
        Presieve.ofArrows B f ∈ fullAffineEtalePrecoverage c.pt A ↔
          ∃ (i : I) (Ai : (D.obj (op i)).FullAffineEtale)
            (Bi : Fin n → (D.obj (op i)).FullAffineEtale) (fi : ∀ a : Fin n, Bi a ⟶ Ai)
            (t : (v i).obj Ai ≅ A) (s : ∀ a : Fin n, (v i).obj (Bi a) ≅ B a),
            Presieve.ofArrows Bi fi ∈ fullAffineEtalePrecoverage (D.obj (op i)) Ai ∧
              ∀ a : Fin n, (v i).map (fi a) ≫ t.hom = (s a).hom ≫ f a) ∧
      ∃ (F : I ⥤ Cat.{u, u + 1}) (Q : ∀ i : I, Precoverage (F.obj i))
        (e : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ F.obj i)
        (v' : ∀ i : I, F.obj i ⥤ c.pt.FullAffineEtale)
        (theta : ∀ (i j : I) (h : i ≤ j),
          e i ⋙ (F.map (homOfLE h)).toFunctor ≅ U i j h ⋙ e j)
        (eta : ∀ i : I, e i ⋙ v' i ≅ v i),
        (∀ i : I, (e i).IsEquivalence) ∧
        (∃ (_ : ∀ i : I, (Q i).HasIsos)
          (_ : ∀ i : I, (Q i).IsStableUnderFiniteComposition)
          (_ : ∀ i : I, (Q i).IsStableUnderFiniteBaseChange)
          (_ : ∀ i : I, (Q i).HasPullbacks),
          (∀ (i : I) (A : F.obj i) (R : Presieve A), R ∈ Q i A → Finite R.uncurry) ∧
          (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
            R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A ↔
              R.map (e i) ∈ Q i ((e i).obj A)) ∧
          (∀ (i j : I) (h : i ≤ j) (A : F.obj i) (R : Presieve A), R ∈ Q i A →
            R.map (F.map (homOfLE h)).toFunctor ∈
              Q j ((F.map (homOfLE h)).toFunctor.obj A)) ∧
          (∀ (i j : I) (h : i ≤ j) (A B C : F.obj i) (f : B ⟶ A) (g : C ⟶ A),
            PreservesLimit (cospan f g) (F.map (homOfLE h)).toFunctor) ∧
          (∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor ⋙ v' j = v' i) ∧
          (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
            Arrow.mk ((v' j).map ((theta i j h).hom.app A) ≫
                (eta j).hom.app ((U i j h).obj A) ≫ (delta i j h).hom.app A) =
              Arrow.mk ((eta i).hom.app A)) ∧
          (∃ (_ : ∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor.IsContinuous
              (Q i).toGrothendieck (Q j).toGrothendieck)
            (_ : ∀ i : I, (v' i).IsContinuous (Q i).toGrothendieck
              (fullAffineEtaleTopology c.pt)),
            (∀ (i j : I) (h : i ≤ j), ∃ L : Sheaf (Q i).toGrothendieck (Type u) ⥤
                Sheaf (Q j).toGrothendieck (Type u),
              Nonempty (L ⊣ (F.map (homOfLE h)).toFunctor.sheafPushforwardContinuous
                (Type u) (Q i).toGrothendieck (Q j).toGrothendieck) ∧
                PreservesFiniteLimits L) ∧
            (∀ i : I, ∃ L : Sheaf (Q i).toGrothendieck (Type u) ⥤
                Sheaf (fullAffineEtaleTopology c.pt) (Type u),
              Nonempty (L ⊣ (v' i).sheafPushforwardContinuous (Type u)
                (Q i).toGrothendieck (fullAffineEtaleTopology c.pt)) ∧
                PreservesFiniteLimits L)) ∧
          ∃ (K : Cocone F) (W : K.pt ⥤ c.pt.FullAffineEtale) (P : Precoverage K.pt),
            Nonempty (IsColimit (Cat.objects.mapCocone K)) ∧
            Nonempty (IsColimit (Cat.arrows.mapCocone K)) ∧
            (∀ i : I, (K.ι.app i).toFunctor ⋙ W = v' i) ∧
            (∀ (A : K.pt) (R : Presieve A), R ∈ P A ↔
              ∃ (i : I) (Ai : F.obj i) (Ri : Presieve Ai)
                (h : (K.ι.app i).toFunctor.obj Ai = A),
                Ri ∈ Q i Ai ∧ h ▸ Ri.map (K.ι.app i).toFunctor = R) ∧
            (∃ (_ : P.HasIsos) (_ : P.IsStableUnderFiniteComposition)
              (_ : P.IsStableUnderFiniteBaseChange) (_ : P.HasPullbacks),
              W.IsEquivalence ∧ ∀ (A : K.pt) (R : Presieve A),
                R ∈ P A ↔ Finite R.uncurry ∧
                  R.map W ∈ fullAffineEtalePrecoverage c.pt (W.obj A))) := by
  obtain ⟨U, v, p, q, gamma, delta, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14⟩ := exists_affineEtale_baseChange_system D c hc
  obtain ⟨h15, h18⟩ := affineEtale_descent_data D c hc U v p q gamma delta
    h1 h2 h7 h10 h12
  have h16 : ∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale)
      (f : (v i).obj A ⟶ (v i).obj B),
      ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
        f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B := by
    intro i A B f
    have : IsAffine A.obj.left := A.property
    have : IsAffine B.obj.left := B.property
    have : QuasiCompact A.obj.hom :=
      @quasiCompact_of_compactSpace A.obj.left (D.obj (op i)) A.obj.hom
        inferInstance inferInstance
    have : QuasiSeparated A.obj.hom :=
      @QuasiSeparated.of_quasiSeparatedSpace A.obj.left (D.obj (op i)) A.obj.hom
        inferInstance
    have : QuasiCompact B.obj.hom :=
      @quasiCompact_of_compactSpace B.obj.left (D.obj (op i)) B.obj.hom
        inferInstance inferInstance
    have : QuasiSeparated B.obj.hom :=
      @QuasiSeparated.of_quasiSeparatedSpace B.obj.left (D.obj (op i)) B.obj.hom
        inferInstance
    let ψ := (h2 i A).isoPullback.inv ≫ f.hom.left ≫ (q i).app B
    have hψ : ψ ≫ B.obj.hom =
        pullback.fst A.obj.hom (c.π.app (op i)) ≫ A.obj.hom := by
      dsimp only [ψ]
      rw [Category.assoc, Category.assoc, (h2 i B).w,
        ← Category.assoc f.hom.left, MorphismProperty.Over.w f.hom, ← Category.assoc,
        (h2 i A).isoPullback_inv_snd, ← pullback.condition]
    obtain ⟨k, a, ψk, hψk, heq⟩ :=
      exists_pullback_hom_of_isLimit hc A.obj.hom B.obj.hom ψ hψ
    let j := k.unop
    let hij : i ≤ j := leOfHom a.unop
    change pullback A.obj.hom (D.map (homOfLE hij).op) ⟶ B.obj.left at ψk
    change ψk ≫ B.obj.hom =
      pullback.fst A.obj.hom (D.map (homOfLE hij).op) ≫ A.obj.hom at hψk
    let φ := (h1 i j hij A).isoPullback.hom ≫ ψk
    have hφ : φ ≫ B.obj.hom = ((U i j hij).obj A).obj.hom ≫
        D.map (homOfLE hij).op := by
      dsimp only [φ]
      rw [Category.assoc, hψk, ← Category.assoc,
        (h1 i j hij A).isoPullback_hom_fst, (h1 i j hij A).w]
    let g : (U i j hij).obj A ⟶ (U i j hij).obj B :=
      ObjectProperty.homMk (MorphismProperty.Over.homMk
        ((h1 i j hij B).lift φ ((U i j hij).obj A).obj.hom hφ)
        ((h1 i j hij B).lift_snd _ _ _))
    let b := pullback.map A.obj.hom (c.π.app (op i)) A.obj.hom
      (D.map (homOfLE hij).op) (𝟙 _) (c.π.app (op j)) (𝟙 _) (by simp) (by simp)
    have hb : b ≫ ψk = ψ := heq
    have hbridge : ((delta i j hij).hom.app A).hom.left ≫
        (h2 i A).isoPullback.hom ≫ b =
        (q j).app ((U i j hij).obj A) ≫ (h1 i j hij A).isoPullback.hom := by
      apply pullback.hom_ext
      · simp only [b, Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id,
          IsPullback.isoPullback_hom_fst]
        exact h7 i j hij A
      · simp only [b, Category.assoc, pullback.map, pullback.lift_snd,
          IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc]
        rw [← Category.assoc, MorphismProperty.Over.w ((delta i j hij).hom.app A).hom]
        exact (h2 j ((U i j hij).obj A)).w.symm
    have hg : g.hom.left ≫ (p i j hij).app B = φ :=
      (h1 i j hij B).lift_fst _ _ _
    have hqg := (q j).naturality g
    change ((v j).map g).hom.left ≫ (q j).app ((U i j hij).obj B) =
      (q j).app ((U i j hij).obj A) ≫ g.hom.left at hqg
    refine ⟨j, hij, g, ?_⟩
    apply (cancel_epi ((delta i j hij).hom.app A)).1
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    apply InducedCategory.hom_ext
    apply MorphismProperty.Over.Hom.ext
    apply (h2 i B).hom_ext
    · change (((delta i j hij).hom.app A).hom.left ≫ f.hom.left) ≫ (q i).app B =
        (((v j).map g).hom.left ≫ ((delta i j hij).hom.app B).hom.left) ≫ (q i).app B
      have hcalc := congrArg (· ≫ ψk) hbridge
      rw [Category.assoc, Category.assoc, hb] at hcalc
      have hleft : ((delta i j hij).hom.app A).hom.left ≫ f.hom.left ≫ (q i).app B =
          (q j).app ((U i j hij).obj A) ≫ φ := by
        simpa only [ψ, φ, Category.assoc, Iso.hom_inv_id_assoc] using hcalc
      rw [Category.assoc, Category.assoc, hleft, h7 i j hij B,
        ← Category.assoc ((v j).map g).hom.left, hqg, Category.assoc, hg]
    · exact (MorphismProperty.Over.w ((delta i j hij).hom.app A ≫ f).hom).trans
        (MorphismProperty.Over.w (((v j).map g ≫ (delta i j hij).hom.app B).hom)).symm
  have h17 : ∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale) (f g : A ⟶ B),
      (v i).map f = (v i).map g →
        ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g := by
    intro i A B f g heq
    have : IsAffine A.obj.left := A.property
    have : IsAffine B.obj.left := B.property
    have : QuasiCompact A.obj.hom :=
      @quasiCompact_of_compactSpace A.obj.left (D.obj (op i)) A.obj.hom
        inferInstance inferInstance
    have : QuasiSeparated A.obj.hom :=
      @QuasiSeparated.of_quasiSeparatedSpace A.obj.left (D.obj (op i)) A.obj.hom
        inferInstance
    have : QuasiCompact B.obj.hom :=
      @quasiCompact_of_compactSpace B.obj.left (D.obj (op i)) B.obj.hom
        inferInstance inferInstance
    have : QuasiSeparated B.obj.hom :=
      @QuasiSeparated.of_quasiSeparatedSpace B.obj.left (D.obj (op i)) B.obj.hom
        inferInstance
    have hqf := (q i).naturality f
    have hqg := (q i).naturality g
    change ((v i).map f).hom.left ≫ (q i).app B =
      (q i).app A ≫ f.hom.left at hqf
    change ((v i).map g).hom.left ≫ (q i).app B =
      (q i).app A ≫ g.hom.left at hqg
    have hlim : pullback.fst A.obj.hom (c.π.app (op i)) ≫ f.hom.left =
        pullback.fst A.obj.hom (c.π.app (op i)) ≫ g.hom.left := by
      rw [← (h2 i A).isoPullback_inv_fst_assoc,
        ← (h2 i A).isoPullback_inv_fst_assoc, ← hqf, ← hqg, heq]
    obtain ⟨j, a, ha⟩ := exists_pullback_fst_comp_eq_of_isLimit hc A.obj.hom B.obj.hom
      f.hom.left g.hom.left (MorphismProperty.Over.w f.hom)
      (MorphismProperty.Over.w g.hom) hlim
    let hij : i ≤ j.unop := leOfHom a.unop
    have ha' : a = (homOfLE hij).op := Subsingleton.elim _ _
    rw [ha'] at ha
    refine ⟨j.unop, hij, ?_⟩
    have hp : (p i j.unop hij).app A ≫ f.hom.left =
        (p i j.unop hij).app A ≫ g.hom.left := by
      simpa only [← Category.assoc, (h1 i j.unop hij A).isoPullback_hom_fst] using
        congrArg ((h1 i j.unop hij A).isoPullback.hom ≫ ·) ha
    apply InducedCategory.hom_ext
    apply MorphismProperty.Over.Hom.ext
    apply (h1 i j.unop hij B).hom_ext
    · have hpf := (p i j.unop hij).naturality f
      have hpg := (p i j.unop hij).naturality g
      change ((U i j.unop hij).map f).hom.left ≫ (p i j.unop hij).app B =
        (p i j.unop hij).app A ≫ f.hom.left at hpf
      change ((U i j.unop hij).map g).hom.left ≫ (p i j.unop hij).app B =
        (p i j.unop hij).app A ≫ g.hom.left at hpg
      exact hpf.trans (hp.trans hpg.symm)
    · exact (MorphismProperty.Over.w ((U i j.unop hij).map f).hom).trans
        (MorphismProperty.Over.w ((U i j.unop hij).map g).hom).symm
  refine ⟨U, v, p, q, gamma, delta, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, h17, h18, ?_⟩
  obtain ⟨F, Q, e, v', theta, eta, he, hcolimit, hstage⟩ :=
    exists_affineEtale_finite_colimit_construction D c U v gamma delta
      h0 h3 h4 h5 h8 h9 h10 h11 h12 h14 h15 h16 h17 h18
  obtain ⟨hQiso, hQcomp, hQbase, hQpull, hQfinite, hecover, hcover, hpull,
    hcompat, htheta, hexact⟩ := hstage
  refine ⟨F, Q, e, v', theta, eta, he, hQiso, hQcomp, hQbase, hQpull,
    hQfinite, hecover, hcover, hpull, hcompat, htheta, hexact, ?_⟩
  obtain ⟨K, W, P, hW, hobjects, harrows, hlegs, himages, hPiso, hPcomp,
    hPbase, hPpull, hreflect⟩ := hcolimit
  exact ⟨K, W, P, hobjects, harrows, hlegs, himages, hPiso, hPcomp,
    hPbase, hPpull, hW, hreflect⟩

end AlgebraicGeometry.Scheme

