# exists_site_system_strictification_data

## Reason

The old output asserted arbitrary indexed composition/base change while requiring every covering
presieve to be finite. The proved counterexample `site_system_strictification_data_refuted`
refutes precisely that output. Stacks 0A34 and 09YL use finite indexed covering families. Replace
only the two output axioms by their finite-index versions; retain every input and every other
output, including strict coefficients and equality in Arrow. The corrected theorem is proved
by an explicit pair-category construction, with no deferred proof or hollow definition.

The general colimit caller has the identical correction and retains its complete proof.
The affine colimit presentation previously used the false theorem and its refutation to derive
its entire result. Its only actual consumer is the affine-site-colimit package; that package's
only actual consumer needs object descent alone. Use `exists_affineEtale_baseChange_system`
and `affineEtale_descent_data` directly there, and withdraw both unused false formal packages.
Six other modules imported the package without referring to its declaration. Remove those
imports; each compiles without them. Keep the mathematical DAG nodes, but set their obsolete
Lean attachments to null. This is pruning below the blueprint unit, not a weaker replacement
for either removed declaration. No target signature or target-used definition changes.

Sources checked: Stacks https://stacks.math.columbia.edu/tag/004A,
https://stacks.math.columbia.edu/tag/0A34, https://stacks.math.columbia.edu/tag/09YL,
and https://stacks.math.columbia.edu/tag/0EYL (including the strictification comment).

## Old

`Sheaf.CategoryTheory.SiteSystemStrictificationData`:

```lean
theorem exists_site_system_strictification_data
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (C : I → Cat.{u, u}) (P : ∀ i : I, Precoverage (C i))
    [∀ i, (P i).HasIsos] [∀ i, (P i).IsStableUnderComposition]
    [∀ i, (P i).IsStableUnderBaseChange] [∀ i, (P i).HasPullbacks]
    (hfinite : ∀ (i : I) (X : C i) (R : Presieve X), R ∈ P i X → Finite R.uncurry)
    (U : ∀ (i j : I), i ≤ j → C i ⥤ C j)
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
      U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X)
    (hcover : ∀ (i j : I) (h : i ≤ j) (X : C i) (R : Presieve X),
      R ∈ P i X → R.map (U i j h) ∈ P j ((U i j h).obj X))
    (hpullback : ∀ (i j : I) (h : i ≤ j) (X Y Z : C i) (R : Presieve X),
      R ∈ P i X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (U i j h))
    [∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
      (P i).toGrothendieck (P j).toGrothendieck]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteLimits
      (sheafPullback (U i j h) (Type u) (P i).toGrothendieck (P j).toGrothendieck)]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteColimits
      (sheafPullback (U i j h) (Type u) (P i).toGrothendieck (P j).toGrothendieck)]
    (D : Type v) [Category.{w} D] (v : ∀ i : I, C i ⥤ D)
    (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
    (hdelta : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (X : C i),
      (v k).map ((gamma i j k h h').hom.app X) ≫
          (delta i k (h.trans h')).hom.app X =
        (delta j k h').hom.app ((U i j h).obj X) ≫ (delta i j h).hom.app X)
    :
    ∃ (F : I ⥤ Cat.{u, u}) (Q : ∀ i : I, Precoverage (F.obj i))
      (e : ∀ i : I, C i ⥤ F.obj i),
      (∀ i : I, (e i).IsEquivalence) ∧
      (∃ (_ : ∀ i, (Q i).HasIsos) (_ : ∀ i, (Q i).IsStableUnderComposition)
        (_ : ∀ i, (Q i).IsStableUnderBaseChange) (_ : ∀ i, (Q i).HasPullbacks),
        (∀ (i : I) (X : F.obj i) (R : Presieve X), R ∈ Q i X → Finite R.uncurry) ∧
        (∀ (i : I) (X : C i) (R : Presieve X),
          R ∈ P i X ↔ R.map (e i) ∈ Q i ((e i).obj X)) ∧
        (∀ (i : I) (X : F.obj i) (K : Type u) (A : K → F.obj i)
          (f : ∀ a : K, A a ⟶ X), Presieve.ofArrows A f ∈ Q i X →
          ∃ (Y : C i) (B : K → C i) (g : ∀ a : K, B a ⟶ Y)
            (t : (e i).obj Y ≅ X) (s : ∀ a : K, (e i).obj (B a) ≅ A a),
            Presieve.ofArrows B g ∈ P i Y ∧
              ∀ a : K, (e i).map (g a) ≫ t.hom = (s a).hom ≫ f a) ∧
        (∀ (i j : I) (h : i ≤ j) (X : F.obj i) (R : Presieve X), R ∈ Q i X →
          R.map (F.map (homOfLE h)).toFunctor ∈
            Q j ((F.map (homOfLE h)).toFunctor.obj X)) ∧
        (∀ (i j : I) (h : i ≤ j) (X Y Z : F.obj i) (R : Presieve X), R ∈ Q i X →
          ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
            PreservesLimit (cospan f g) (F.map (homOfLE h)).toFunctor) ∧
        ∃ (_ : ∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor.IsContinuous
            (Q i).toGrothendieck (Q j).toGrothendieck),
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteLimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteColimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          ∃ (theta : ∀ (i j : I) (h : i ≤ j),
              e i ⋙ (F.map (homOfLE h)).toFunctor ≅ U i j h ⋙ e j)
            (v' : ∀ i : I, F.obj i ⥤ D),
            (∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor ⋙ v' j = v' i) ∧
            (∀ i : I, e i ⋙ v' i = v i) ∧
            (∀ (i j : I) (h : i ≤ j) (X : C i),
              Arrow.mk ((v' j).map ((theta i j h).hom.app X)) =
                Arrow.mk ((delta i j h).inv.app X)))
```

`Sheaf.CategoryTheory.SiteSystemStrictification`:

```lean
theorem exists_site_system_strictification
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (C : I → Cat.{u, u}) (P : ∀ i : I, Precoverage (C i))
    [∀ i, (P i).HasIsos] [∀ i, (P i).IsStableUnderComposition]
    [∀ i, (P i).IsStableUnderBaseChange] [∀ i, (P i).HasPullbacks]
    (hfinite : ∀ (i : I) (X : C i) (R : Presieve X), R ∈ P i X → Finite R.uncurry)
    (U : ∀ (i j : I), i ≤ j → C i ⥤ C j)
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
      U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X)
    (hcover : ∀ (i j : I) (h : i ≤ j) (X : C i) (R : Presieve X),
      R ∈ P i X → R.map (U i j h) ∈ P j ((U i j h).obj X))
    (hpullback : ∀ (i j : I) (h : i ≤ j) (X Y Z : C i) (R : Presieve X),
      R ∈ P i X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (U i j h))
    [∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
      (P i).toGrothendieck (P j).toGrothendieck]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteLimits
      (sheafPullback (U i j h) (Type u) (P i).toGrothendieck (P j).toGrothendieck)]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteColimits
      (sheafPullback (U i j h) (Type u) (P i).toGrothendieck (P j).toGrothendieck)]
    (D : Type v) [Category.{w} D] (v : ∀ i : I, C i ⥤ D)
    (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
    (hdelta : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (X : C i),
      (v k).map ((gamma i j k h h').hom.app X) ≫
          (delta i k (h.trans h')).hom.app X =
        (delta j k h').hom.app ((U i j h).obj X) ≫ (delta i j h).hom.app X) :
    ∃ (F : I ⥤ Cat.{u, u}) (Q : ∀ i : I, Precoverage (F.obj i))
      (e : ∀ i : I, C i ⥤ F.obj i),
      (∀ i : I, (e i).IsEquivalence) ∧
      (∃ (_ : ∀ i, (Q i).HasIsos) (_ : ∀ i, (Q i).IsStableUnderComposition)
        (_ : ∀ i, (Q i).IsStableUnderBaseChange) (_ : ∀ i, (Q i).HasPullbacks),
        (∀ (i : I) (X : F.obj i) (R : Presieve X), R ∈ Q i X → Finite R.uncurry) ∧
        (∀ (i : I) (X : C i) (R : Presieve X),
          R ∈ P i X ↔ R.map (e i) ∈ Q i ((e i).obj X)) ∧
        (∀ (i : I) (X : F.obj i) (K : Type u) (A : K → F.obj i)
          (f : ∀ a : K, A a ⟶ X), Presieve.ofArrows A f ∈ Q i X →
          ∃ (Y : C i) (B : K → C i) (g : ∀ a : K, B a ⟶ Y)
            (t : (e i).obj Y ≅ X) (s : ∀ a : K, (e i).obj (B a) ≅ A a),
            Presieve.ofArrows B g ∈ P i Y ∧
              ∀ a : K, (e i).map (g a) ≫ t.hom = (s a).hom ≫ f a) ∧
        (∀ (i j : I) (h : i ≤ j) (X : F.obj i) (R : Presieve X), R ∈ Q i X →
          R.map (F.map (homOfLE h)).toFunctor ∈
            Q j ((F.map (homOfLE h)).toFunctor.obj X)) ∧
        (∀ (i j : I) (h : i ≤ j) (X Y Z : F.obj i) (R : Presieve X), R ∈ Q i X →
          ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
            PreservesLimit (cospan f g) (F.map (homOfLE h)).toFunctor) ∧
        ∃ (_ : ∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor.IsContinuous
            (Q i).toGrothendieck (Q j).toGrothendieck),
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteLimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteColimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          ∃ (theta : ∀ (i j : I) (h : i ≤ j),
              e i ⋙ (F.map (homOfLE h)).toFunctor ≅ U i j h ⋙ e j)
            (v' : ∀ i : I, F.obj i ⥤ D),
            (∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor ⋙ v' j = v' i) ∧
            (∀ i : I, e i ⋙ v' i = v i) ∧
            (∀ (i j : I) (h : i ≤ j) (X : C i),
              Arrow.mk ((v' j).map ((theta i j h).hom.app X)) =
                Arrow.mk ((delta i j h).inv.app X)) ∧
            ∃ (L : Cocone F) (V : L.pt ⥤ D),
              Nonempty (IsColimit (Cat.objects.mapCocone L)) ∧
              Nonempty (IsColimit (Cat.arrows.mapCocone L)) ∧
              ∀ i : I, (L.ι.app i).toFunctor ⋙ V = v' i)
```

`Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentation`:

```lean
theorem exists_affineEtale_colimit_presentation
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c)
    (U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
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
      (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)
    (h0 : (∀ i : I, U i i le_rfl = 𝟭 _))
    (h3 : (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i i k le_rfl h) (Iso.refl (U i k h))))
    (h4 : (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i k k h le_rfl) (Iso.refl (U i k h))))
    (h5 : (∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i))))
    (h8 : (∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l)
        (A : (D.obj (op i)).FullAffineEtale),
        (gamma j k l h' h'').hom.app ((U i j h).obj A) ≫
            (gamma i j l h (h'.trans h'')).hom.app A =
          (U k l h'').map ((gamma i j k h h').hom.app A) ≫
            (gamma i k l (h.trans h') h'').hom.app A))
    (h9 : (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        (v k).map ((gamma i j k h h').hom.app A) ≫
            (delta i k (h.trans h')).hom.app A =
          (delta j k h').hom.app ((U i j h).obj A) ≫ (delta i j h).hom.app A))
    (h10 : (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (U i j h) ∈ fullAffineEtalePrecoverage (D.obj (op j)) ((U i j h).obj A)))
    (h11 : (∀ (i j : I) (h : i ≤ j) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (U i j h)))
    (h12 : (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (v i) ∈ fullAffineEtalePrecoverage c.pt ((v i).obj A)))
    (h13 : (∀ (i : I) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (v i)))
    (h14 : (∃ (_ : ∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
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
          PreservesFiniteLimits L)))
    (h15 : (∀ A : c.pt.FullAffineEtale,
        ∃ (i : I) (Ai : (D.obj (op i)).FullAffineEtale), Nonempty ((v i).obj Ai ≅ A)))
    (h16 : (∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale)
        (f : (v i).obj A ⟶ (v i).obj B),
        ∃ (j : I) (h : i ≤ j) (g : (U i j h).obj A ⟶ (U i j h).obj B),
          f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B))
    (h17 : (∀ (i : I) (A B : (D.obj (op i)).FullAffineEtale) (f g : A ⟶ B),
        (v i).map f = (v i).map g →
          ∃ (j : I) (h : i ≤ j), (U i j h).map f = (U i j h).map g))
    (h18 : (∀ (n : ℕ) (A : c.pt.FullAffineEtale) (B : Fin n → c.pt.FullAffineEtale)
        (f : ∀ a : Fin n, B a ⟶ A),
        Presieve.ofArrows B f ∈ fullAffineEtalePrecoverage c.pt A ↔
          ∃ (i : I) (Ai : (D.obj (op i)).FullAffineEtale)
            (Bi : Fin n → (D.obj (op i)).FullAffineEtale) (fi : ∀ a : Fin n, Bi a ⟶ Ai)
            (t : (v i).obj Ai ≅ A) (s : ∀ a : Fin n, (v i).obj (Bi a) ≅ B a),
            Presieve.ofArrows Bi fi ∈ fullAffineEtalePrecoverage (D.obj (op i)) Ai ∧
              ∀ a : Fin n, (v i).map (fi a) ≫ t.hom = (s a).hom ≫ f a))
    :
      ∃ (F : I ⥤ Cat.{u, u + 1}) (Q : ∀ i : I, Precoverage (F.obj i))
        (e : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ F.obj i)
        (v' : ∀ i : I, F.obj i ⥤ c.pt.FullAffineEtale)
        (theta : ∀ (i j : I) (h : i ≤ j),
          e i ⋙ (F.map (homOfLE h)).toFunctor ≅ U i j h ⋙ e j)
        (eta : ∀ i : I, e i ⋙ v' i ≅ v i),
        (∀ i : I, (e i).IsEquivalence) ∧ (∃ (_ : ∀ i : I, (Q i).HasIsos)
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
                R ∈ P A ↔ R.map W ∈ fullAffineEtalePrecoverage c.pt (W.obj A)))
```

`Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`:

```lean
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
                R ∈ P A ↔ R.map W ∈ fullAffineEtalePrecoverage c.pt (W.obj A)))
```

## New

`Sheaf.CategoryTheory.SiteSystemStrictificationData`:

```lean
theorem exists_site_system_strictification_data
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (C : I → Cat.{u, u}) (P : ∀ i : I, Precoverage (C i))
    [∀ i, (P i).HasIsos] [∀ i, (P i).IsStableUnderComposition]
    [∀ i, (P i).IsStableUnderBaseChange] [∀ i, (P i).HasPullbacks]
    (hfinite : ∀ (i : I) (X : C i) (R : Presieve X), R ∈ P i X → Finite R.uncurry)
    (U : ∀ (i j : I), i ≤ j → C i ⥤ C j)
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
      U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X)
    (hcover : ∀ (i j : I) (h : i ≤ j) (X : C i) (R : Presieve X),
      R ∈ P i X → R.map (U i j h) ∈ P j ((U i j h).obj X))
    (hpullback : ∀ (i j : I) (h : i ≤ j) (X Y Z : C i) (R : Presieve X),
      R ∈ P i X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (U i j h))
    [∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
      (P i).toGrothendieck (P j).toGrothendieck]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteLimits
      (sheafPullback (U i j h) (Type u) (P i).toGrothendieck (P j).toGrothendieck)]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteColimits
      (sheafPullback (U i j h) (Type u) (P i).toGrothendieck (P j).toGrothendieck)]
    (D : Type v) [Category.{w} D] (v : ∀ i : I, C i ⥤ D)
    (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
    (hdelta : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (X : C i),
      (v k).map ((gamma i j k h h').hom.app X) ≫
          (delta i k (h.trans h')).hom.app X =
        (delta j k h').hom.app ((U i j h).obj X) ≫ (delta i j h).hom.app X)
    :
    ∃ (F : I ⥤ Cat.{u, u}) (Q : ∀ i : I, Precoverage (F.obj i))
      (e : ∀ i : I, C i ⥤ F.obj i),
      (∀ i : I, (e i).IsEquivalence) ∧
      (∃ (_ : ∀ i, (Q i).HasIsos) (_ : ∀ i, (Q i).IsStableUnderFiniteComposition)
        (_ : ∀ i, (Q i).IsStableUnderFiniteBaseChange) (_ : ∀ i, (Q i).HasPullbacks),
        (∀ (i : I) (X : F.obj i) (R : Presieve X), R ∈ Q i X → Finite R.uncurry) ∧
        (∀ (i : I) (X : C i) (R : Presieve X),
          R ∈ P i X ↔ R.map (e i) ∈ Q i ((e i).obj X)) ∧
        (∀ (i : I) (X : F.obj i) (K : Type u) (A : K → F.obj i)
          (f : ∀ a : K, A a ⟶ X), Presieve.ofArrows A f ∈ Q i X →
          ∃ (Y : C i) (B : K → C i) (g : ∀ a : K, B a ⟶ Y)
            (t : (e i).obj Y ≅ X) (s : ∀ a : K, (e i).obj (B a) ≅ A a),
            Presieve.ofArrows B g ∈ P i Y ∧
              ∀ a : K, (e i).map (g a) ≫ t.hom = (s a).hom ≫ f a) ∧
        (∀ (i j : I) (h : i ≤ j) (X : F.obj i) (R : Presieve X), R ∈ Q i X →
          R.map (F.map (homOfLE h)).toFunctor ∈
            Q j ((F.map (homOfLE h)).toFunctor.obj X)) ∧
        (∀ (i j : I) (h : i ≤ j) (X Y Z : F.obj i) (R : Presieve X), R ∈ Q i X →
          ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
            PreservesLimit (cospan f g) (F.map (homOfLE h)).toFunctor) ∧
        ∃ (_ : ∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor.IsContinuous
            (Q i).toGrothendieck (Q j).toGrothendieck),
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteLimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteColimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          ∃ (theta : ∀ (i j : I) (h : i ≤ j),
              e i ⋙ (F.map (homOfLE h)).toFunctor ≅ U i j h ⋙ e j)
            (v' : ∀ i : I, F.obj i ⥤ D),
            (∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor ⋙ v' j = v' i) ∧
            (∀ i : I, e i ⋙ v' i = v i) ∧
            (∀ (i j : I) (h : i ≤ j) (X : C i),
              Arrow.mk ((v' j).map ((theta i j h).hom.app X)) =
                Arrow.mk ((delta i j h).inv.app X)))
```

`Sheaf.CategoryTheory.SiteSystemStrictification`:

```lean
theorem exists_site_system_strictification
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (C : I → Cat.{u, u}) (P : ∀ i : I, Precoverage (C i))
    [∀ i, (P i).HasIsos] [∀ i, (P i).IsStableUnderComposition]
    [∀ i, (P i).IsStableUnderBaseChange] [∀ i, (P i).HasPullbacks]
    (hfinite : ∀ (i : I) (X : C i) (R : Presieve X), R ∈ P i X → Finite R.uncurry)
    (U : ∀ (i j : I), i ≤ j → C i ⥤ C j)
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
      U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X)
    (hcover : ∀ (i j : I) (h : i ≤ j) (X : C i) (R : Presieve X),
      R ∈ P i X → R.map (U i j h) ∈ P j ((U i j h).obj X))
    (hpullback : ∀ (i j : I) (h : i ≤ j) (X Y Z : C i) (R : Presieve X),
      R ∈ P i X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (U i j h))
    [∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
      (P i).toGrothendieck (P j).toGrothendieck]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteLimits
      (sheafPullback (U i j h) (Type u) (P i).toGrothendieck (P j).toGrothendieck)]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteColimits
      (sheafPullback (U i j h) (Type u) (P i).toGrothendieck (P j).toGrothendieck)]
    (D : Type v) [Category.{w} D] (v : ∀ i : I, C i ⥤ D)
    (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
    (hdelta : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (X : C i),
      (v k).map ((gamma i j k h h').hom.app X) ≫
          (delta i k (h.trans h')).hom.app X =
        (delta j k h').hom.app ((U i j h).obj X) ≫ (delta i j h).hom.app X) :
    ∃ (F : I ⥤ Cat.{u, u}) (Q : ∀ i : I, Precoverage (F.obj i))
      (e : ∀ i : I, C i ⥤ F.obj i),
      (∀ i : I, (e i).IsEquivalence) ∧
      (∃ (_ : ∀ i, (Q i).HasIsos) (_ : ∀ i, (Q i).IsStableUnderFiniteComposition)
        (_ : ∀ i, (Q i).IsStableUnderFiniteBaseChange) (_ : ∀ i, (Q i).HasPullbacks),
        (∀ (i : I) (X : F.obj i) (R : Presieve X), R ∈ Q i X → Finite R.uncurry) ∧
        (∀ (i : I) (X : C i) (R : Presieve X),
          R ∈ P i X ↔ R.map (e i) ∈ Q i ((e i).obj X)) ∧
        (∀ (i : I) (X : F.obj i) (K : Type u) (A : K → F.obj i)
          (f : ∀ a : K, A a ⟶ X), Presieve.ofArrows A f ∈ Q i X →
          ∃ (Y : C i) (B : K → C i) (g : ∀ a : K, B a ⟶ Y)
            (t : (e i).obj Y ≅ X) (s : ∀ a : K, (e i).obj (B a) ≅ A a),
            Presieve.ofArrows B g ∈ P i Y ∧
              ∀ a : K, (e i).map (g a) ≫ t.hom = (s a).hom ≫ f a) ∧
        (∀ (i j : I) (h : i ≤ j) (X : F.obj i) (R : Presieve X), R ∈ Q i X →
          R.map (F.map (homOfLE h)).toFunctor ∈
            Q j ((F.map (homOfLE h)).toFunctor.obj X)) ∧
        (∀ (i j : I) (h : i ≤ j) (X Y Z : F.obj i) (R : Presieve X), R ∈ Q i X →
          ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
            PreservesLimit (cospan f g) (F.map (homOfLE h)).toFunctor) ∧
        ∃ (_ : ∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor.IsContinuous
            (Q i).toGrothendieck (Q j).toGrothendieck),
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteLimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteColimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type u)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          ∃ (theta : ∀ (i j : I) (h : i ≤ j),
              e i ⋙ (F.map (homOfLE h)).toFunctor ≅ U i j h ⋙ e j)
            (v' : ∀ i : I, F.obj i ⥤ D),
            (∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor ⋙ v' j = v' i) ∧
            (∀ i : I, e i ⋙ v' i = v i) ∧
            (∀ (i j : I) (h : i ≤ j) (X : C i),
              Arrow.mk ((v' j).map ((theta i j h).hom.app X)) =
                Arrow.mk ((delta i j h).inv.app X)) ∧
            ∃ (L : Cocone F) (V : L.pt ⥤ D),
              Nonempty (IsColimit (Cat.objects.mapCocone L)) ∧
              Nonempty (IsColimit (Cat.arrows.mapCocone L)) ∧
              ∀ i : I, (L.ι.app i).toFunctor ⋙ V = v' i)
```

`Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentation` is withdrawn via `deleted.txt`; its module will contain no declarations.
No replacement theorem with a weaker conclusion is introduced.

`Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit` is withdrawn via `deleted.txt`; its module will contain no declarations.
No replacement theorem with a weaker conclusion is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SiteSystemStrictificationData | M4 | Two finite indexed output axioms; fully proved. |
| Sheaf.CategoryTheory.SiteSystemStrictification | unclaimed | Matching output correction; original colimit proof retained. |
| Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentation | unclaimed | False, unused formal attachment withdrawn. |
| Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit | unclaimed | False, unused formal attachment withdrawn. |
| Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleFamilyModels | unclaimed | Same signature; use coherent base change and object descent directly. |
| Sheaf.AlgebraicGeometry.EtaleSetEventualLocalStageMatching | unclaimed | Remove unused affine-site-colimit import; declaration unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSetFiniteLocalStageRepresentatives | unclaimed | Remove unused affine-site-colimit import; declaration unchanged. |
| Sheaf.AlgebraicGeometry.EtaleLimitScalarSectionContinuity | unclaimed | Remove unused affine-site-colimit import; declaration unchanged. |
| Sheaf.AlgebraicGeometry.EtaleLimitAffineDegreeZeroKernel | unclaimed | Remove unused affine-site-colimit import; declaration unchanged. |
| Sheaf.Paper.AffineOpenSectionsDescent | unclaimed | Remove unused affine-site-colimit import; declaration unchanged. |
| Sheaf.Paper.AffineOpenSectionsZeroDetection | unclaimed | Remove unused affine-site-colimit import; declaration unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleLimitDescentGeneral | unclaimed | Forced adaptation: replace withdrawn exists_affineEtaleSite_colimit with affineEtale_baseChangeSystem and affineEtale_descent_data; declaration unchanged. |

Claims were checked in the project snapshot; all adapted/withdrawn modules are unclaimed.
All live adapted modules compile individually against the sandbox dependencies.
The two withdrawn modules have no remaining importers after these changes.
The blueprint unit sk-thm-p1 has neither withdrawn node among its realized statement/steps.
Its statement and every realized step remain intact. The original counterexample modules
remain untouched and their negation remains true for the old, unrestricted assertion.

Second reading additionally removes the redundant direct proof imports listed in the report
from `EtaleLimitScalarSectionContinuity`, `EtaleLimitAffineDegreeZeroKernel`,
`AffineOpenSectionsDescent`, and `AffineOpenSectionsZeroDetection`, and the redundant public
`Mathlib.CategoryTheory.Limits.Preserves.Limits` import from the new `SiteSystemFiniteCoverings`.
All statement-level declarations of that Mathlib module remain available through its other
public imports. Every changed consumer is unclaimed and compiles with its identical signature.

## Status

landed 20261014T170739-L-2556489 2026-10-14 (merge of deliver/M4/Sheaf.CategoryTheory.SiteSystemStrictificationData)
