/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Sheaf.CategoryTheory.SiteSystemStrictification
import Sheaf.AlgebraicGeometry.AffineEtaleBaseChangeSystem
import Sheaf.AlgebraicGeometry.AffineEtaleDescentData
import Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# The affine étale site of an inverse limit

Source: Stacks Project, Étale Cohomology, Lemma 0EYL (qcqs case), and Sites, Lemma 09YL
(blueprint: lem-weil-pbc-affine-etale-site-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Stacks Project, Étale Cohomology, Lemma 0EYL, first paragraph (qcqs case);
Sites, Situation 0A34 and Lemma 09YL.
(blueprint: lem-weil-pbc-affine-etale-site-colimit).

The natural transformations `p` and `q` are the first projections of the base changes.
Their cartesian squares specify the base change functors without another definition.
The projection equations for `gamma` and `delta` specify the canonical comparisons.
The functor `F` is a strictification; `W` is its comparison from the category colimit.

Proof (the node's eight steps):
1. Projections of the limiting cone are affine (lem-weil-pbc-limit-affine-transition).
   Thus the limit is qcqs. Affine étale objects over each qcqs base have finite presentation
   (lem-weil-pbc-qcqs-morphism-permanence). Pullback along an affine map preserves affine
   domains, and étaleness survives pullback (lem-weil-pbc-affine-morphism-permanence and
   lem-weil-pbc-etale-base-change-finite-limits).
2. Base change preserves finite jointly surjective étale coverings and their pullbacks
   (lem-weil-pbc-etale-base-change-continuous). Hence it is continuous on the affine sites.
3. Restriction from the small étale site is an equivalence
   (lem-weil-pbc-affine-etale-site-topos). Transport the small-site inverse image and its
   adjunction across these equivalences; its finite-limit preservation proves that each
   affine-site base change defines a morphism of sites
   (lem-weil-pbc-etale-inverse-image-algebraic-structures).
4. Cartesian-square pasting gives the canonical composition comparisons, compatible with
   the first projections (lem-weil-pbc-cartesian-square-pasting, def-pc-fibre-product).
   Uniqueness of maps of pullbacks gives normalization and the cocycle identities.
   Apply lem-weil-pbc-site-system-strictification to obtain F, Q, e, theta and v'.
5. Descend an affine étale object by thm-pd-spreading-out; its descended finite-presentation
   model becomes affine by lem-weil-pbc-limit-affine-stage and étale by
   lem-weil-pbc-descend-etale. The tail has the given base change as its limit by
   lem-weil-pbc-scheme-over-limit, and pullback pasting identifies its models.
6. Descend a map and eventual equality of maps by thm-pd-spreading-out (clauses 2 and 3).
   Directedness moves any finite collection to a common stage.
7. Descend the finitely many objects and maps of a standard cover using steps 5 and 6.
   Apply lem-weil-pbc-descend-surjective to their finite disjoint union. At a later stage
   the descended family is jointly surjective, hence is a standard étale cover
   (lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-etale-composition-cancellation).
   Conversely base change preserves these covers by step 2.
8. Apply lem-weil-pbc-colimit-of-sites to the strict system. Steps 5 and 6 make its
   comparison essentially surjective and fully faithful, hence an equivalence
   (def-weil-pbc-category-colimit). Step 7 identifies coverings in both directions. -/
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
          (_ : ∀ i : I, (Q i).IsStableUnderComposition)
          (_ : ∀ i : I, (Q i).IsStableUnderBaseChange)
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
            (∃ (_ : P.HasIsos) (_ : P.IsStableUnderComposition)
              (_ : P.IsStableUnderBaseChange) (_ : P.HasPullbacks),
              W.IsEquivalence ∧ ∀ (A : K.pt) (R : Presieve A),
                R ∈ P A ↔ R.map W ∈ fullAffineEtalePrecoverage c.pt (W.obj A))) := by
  obtain ⟨U, v, p, q, gamma, delta,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    exists_affineEtale_baseChange_system D c hc
  obtain ⟨h15, h18⟩ := affineEtale_descent_data D c hc U v p q gamma delta
    h1 h2 h7 h10 h12
  have h16 : (∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale)
        (f : (v i).obj A ⟶ (v i).obj B),
        ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
          f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B) := by
    intro i A B f
    have : IsAffine A.obj.left := A.property
    have : IsAffine B.obj.left := B.property
    have : QuasiCompact A.obj.hom :=
      quasiCompact_of_compactSpace (X := A.obj.left) (Y := D.obj (op i)) A.obj.hom
    have : QuasiCompact B.obj.hom :=
      quasiCompact_of_compactSpace (X := B.obj.left) (Y := D.obj (op i)) B.obj.hom
    have : QuasiSeparated A.obj.hom :=
      QuasiSeparated.of_quasiSeparatedSpace (X := A.obj.left) A.obj.hom
    have : QuasiSeparated B.obj.hom :=
      QuasiSeparated.of_quasiSeparatedSpace (X := B.obj.left) B.obj.hom
    let eA := (h2 i A).isoPullback
    let ψ := eA.inv ≫ f.hom.left ≫ (q i).app B
    have hψ : ψ ≫ B.obj.hom =
        pullback.fst A.obj.hom (c.π.app (op i)) ≫ A.obj.hom := by
      dsimp [ψ]
      rw [Category.assoc, Category.assoc, (h2 i B).w]
      have fw : f.hom.left ≫ ((v i).obj B).obj.hom = ((v i).obj A).obj.hom := by
        exact MorphismProperty.Over.w f.hom
      rw [← Category.assoc f.hom.left, fw]
      rw [← (h2 i A).isoPullback_hom_snd]
      dsimp [eA]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      exact pullback.condition.symm
    obtain ⟨j, a, ψj, hψj, hdesc⟩ := exists_pullback_hom_of_isLimit hc
      A.obj.hom B.obj.hom ψ hψ
    let h : i ≤ j.unop := leOfHom a.unop
    have ha : a = (homOfLE h).op := Subsingleton.elim _ _
    let eAj := (h1 i j.unop h A).isoPullback
    let gleft := (h1 i j.unop h B).lift (eAj.hom ≫ ψj)
      ((U i j.unop h).obj A).obj.hom (by
        rw [Category.assoc, hψj, ha, ← Category.assoc]
        dsimp [eAj]
        rw [IsPullback.isoPullback_hom_fst, (h1 i j.unop h A).w])
    let g : (U i j.unop h).obj A ⟶ (U i j.unop h).obj B :=
      ObjectProperty.homMk (MorphismProperty.Over.homMk gleft
        (by dsimp [gleft]; exact (h1 i j.unop h B).lift_snd _ _ _) (by trivial))
    refine ⟨j.unop, h, g, ?_⟩
    apply (cancel_epi ((delta i j.unop h).hom.app A)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    apply (h2 i B).hom_ext
    · change ((delta i j.unop h).hom.app A).hom.left ≫ f.hom.left ≫ (q i).app B =
        ((v j.unop).map g).hom.left ≫
          ((delta i j.unop h).hom.app B).hom.left ≫ (q i).app B
      rw [h7 i j.unop h B]
      have hqg := (q j.unop).naturality g
      change ((v j.unop).map g).hom.left ≫ (q j.unop).app ((U i j.unop h).obj B) =
        (q j.unop).app ((U i j.unop h).obj A) ≫ g.hom.left at hqg
      rw [reassoc_of% hqg]
      have gp : g.hom.left ≫ (p i j.unop h).app B = eAj.hom ≫ ψj := by
        dsimp [g, gleft]
        exact (h1 i j.unop h B).lift_fst _ _ _
      rw [gp]
      have hm : (q j.unop).app ((U i j.unop h).obj A) ≫ eAj.hom =
          ((delta i j.unop h).hom.app A).hom.left ≫ eA.hom ≫
            pullback.map A.obj.hom (c.π.app (op i)) A.obj.hom (D.map a)
              (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) := by
        apply pullback.hom_ext
        · rw [ha]
          change (q j.unop).app ((U i j.unop h).obj A) ≫ eAj.hom ≫
              pullback.fst _ _ =
            ((delta i j.unop h).hom.app A).hom.left ≫ eA.hom ≫
              (pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.fst _ _)
          rw [show pullback.map A.obj.hom (c.π.app (op i)) A.obj.hom
              (D.map (homOfLE h).op) (𝟙 _) (c.π.app j) (𝟙 _)
              (by simp) (by simp) ≫ pullback.fst _ _ =
              pullback.fst A.obj.hom (c.π.app (op i)) by simp]
          dsimp only [eA, eAj]
          rw [IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst]
          exact (h7 i j.unop h A).symm
        · rw [ha]
          simp only [Category.assoc, pullback.map, pullback.lift_snd,
            Category.comp_id]
          dsimp only [eA, eAj]
          rw [IsPullback.isoPullback_hom_snd_assoc, IsPullback.isoPullback_hom_snd]
          rw [reassoc_of% (MorphismProperty.Over.w ((delta i j.unop h).hom.app A).hom)]
          exact (h2 j.unop ((U i j.unop h).obj A)).w
      rw [reassoc_of% hm]
      have hd := congrArg
        (fun z ↦ ((delta i j.unop h).hom.app A).hom.left ≫ eA.hom ≫ z) hdesc
      simpa only [Category.assoc, ψ, Iso.hom_inv_id_assoc, Functor.id_obj,
        Functor.fromPUnit, Functor.comp_obj, fullAffineEtaleInclusion,
        ObjectProperty.ι_obj] using hd.symm
    · simp only [MorphismProperty.Over.w]
  have h17 : (∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale) (f g : A ⟶ B),
        (v i).map f = (v i).map g →
          ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g) := by
    intro i A B f g hfg
    have : IsAffine A.obj.left := A.property
    have : IsAffine B.obj.left := B.property
    have : QuasiCompact A.obj.hom :=
      quasiCompact_of_compactSpace (X := A.obj.left) (Y := D.obj (op i)) A.obj.hom
    have : QuasiCompact B.obj.hom :=
      quasiCompact_of_compactSpace (X := B.obj.left) (Y := D.obj (op i)) B.obj.hom
    have : QuasiSeparated A.obj.hom :=
      QuasiSeparated.of_quasiSeparatedSpace (X := A.obj.left) A.obj.hom
    have : QuasiSeparated B.obj.hom :=
      QuasiSeparated.of_quasiSeparatedSpace (X := B.obj.left) B.obj.hom
    have hqf := (q i).naturality f
    have hqg := (q i).naturality g
    change ((v i).map f).hom.left ≫ (q i).app B =
      (q i).app A ≫ f.hom.left at hqf
    change ((v i).map g).hom.left ≫ (q i).app B =
      (q i).app A ≫ g.hom.left at hqg
    have hqeq : (q i).app A ≫ f.hom.left = (q i).app A ≫ g.hom.left := by
      rw [← hqf, ← hqg, hfg]
    have hlim : pullback.fst A.obj.hom (c.π.app (op i)) ≫ f.hom.left =
        pullback.fst A.obj.hom (c.π.app (op i)) ≫ g.hom.left := by
      apply (cancel_epi (h2 i A).isoPullback.hom).mp
      simpa only [← Category.assoc, IsPullback.isoPullback_hom_fst] using hqeq
    obtain ⟨j, a, heq⟩ := exists_pullback_fst_comp_eq_of_isLimit hc
      A.obj.hom B.obj.hom f.hom.left g.hom.left f.hom.w g.hom.w hlim
    let h : i ≤ j.unop := leOfHom a.unop
    have ha : a = (homOfLE h).op := Subsingleton.elim _ _
    rw [ha] at heq
    refine ⟨j.unop, h, ?_⟩
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    apply (h1 i j.unop h B).hom_ext
    · have hpf := (p i j.unop h).naturality f
      have hpg := (p i j.unop h).naturality g
      change ((U i j.unop h).map f).hom.left ≫ (p i j.unop h).app B =
        (p i j.unop h).app A ≫ f.hom.left at hpf
      change ((U i j.unop h).map g).hom.left ≫ (p i j.unop h).app B =
        (p i j.unop h).app A ≫ g.hom.left at hpg
      rw [hpf, hpg]
      rw [← (h1 i j.unop h A).isoPullback_hom_fst]
      simpa only [Category.assoc] using
        congrArg (fun z ↦ (h1 i j.unop h A).isoPullback.hom ≫ z) heq
    · simp only [MorphismProperty.Over.w]
  obtain h19 := exists_affineEtale_colimit_presentation D c hc U v p q gamma delta
    h0 h3 h4 h5 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  exact ⟨U, v, p, q, gamma, delta, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩


end AlgebraicGeometry.Scheme
