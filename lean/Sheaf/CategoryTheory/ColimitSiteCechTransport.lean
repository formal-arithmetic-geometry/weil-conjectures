module

public import Sheaf.CategoryTheory.ColimitSites
public import Sheaf.CategoryTheory.SiteCechComplex
import Sheaf.CategoryTheory.ColimitSiteCoveringConstructionParts

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem product_ext {C : Type u} [Category C] {T : Type u} {U : C}
    {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom)
    {p : ℕ} {t : Fin (p + 1) → T} {Z : C} (a b : Z ⟶ S.W p t)
    (h : ∀ k, a ≫ S.pr p t k = b ≫ S.pr p t k) : a = b := by
  obtain ⟨c, hc, hu⟩ := S.universal p t Z (fun k ↦ b ≫ S.pr p t k)
    (fun k ↦ by simp only [Category.assoc]; rw [S.comm])
  exact (hu a h).trans (hu b (fun _ ↦ rfl)).symm

private theorem mapped_product_universal {C D : Type u} [Category C] [Category D]
    {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom) (A : C ⥤ D)
    (hp : ∀ (t : T) (Z : C) (g : Z ⟶ U), PreservesLimit (cospan (hom t) g) A)
    (p : ℕ) (t : Fin (p + 1) → T) (Z : D)
    (a : ∀ k, Z ⟶ A.obj (f (t k)))
    (ha : ∀ k, a k ≫ A.map (hom (t k)) = a 0 ≫ A.map (hom (t 0))) :
    ∃! b : Z ⟶ A.obj (S.W p t), ∀ k, b ≫ A.map (S.pr p t k) = a k := by
  classical
  induction p generalizing Z with
  | zero =>
    have hi : IsIso (A.map (S.pr 0 t 0)) := by
      rw [S.pr_zero]
      infer_instance
    refine ⟨a 0 ≫ inv (A.map (S.pr 0 t 0)), ?_, ?_⟩
    · intro k
      fin_cases k
      simp
    · intro b hb
      apply (cancel_mono (A.map (S.pr 0 t 0))).mp
      simpa using hb 0
  | succ p ih =>
    let tail := t ∘ Fin.succ
    obtain ⟨b, hb, _⟩ := S.universal p tail (S.W (p + 1) t)
      (fun k ↦ S.pr (p + 1) t k.succ)
      (fun k ↦ (S.comm _ _ k.succ).trans (S.comm _ _ (Fin.succ 0)).symm)
    let g := S.pr p tail 0 ≫ hom (tail 0)
    have comm : S.pr (p + 1) t 0 ≫ hom (t 0) = b ≫ g := by
      dsimp [g, tail]
      rw [← Category.assoc, hb 0]
      exact (S.comm _ _ (Fin.succ 0)).symm
    have pb : IsPullback (S.pr (p + 1) t 0) b (hom (t 0)) g := by
      apply IsPullback.mk' comm
      · intro Y x y hx hy
        apply product_ext S x y
        intro k
        refine Fin.cases hx (fun k ↦ ?_) k
        rw [← hb k, ← Category.assoc, ← Category.assoc, hy]
      · intro Y x y hxy
        let ar : ∀ k : Fin (p + 1 + 1), Y ⟶ f (t k) :=
          Fin.cases x (fun k ↦ y ≫ S.pr p tail k)
        have har : ∀ k, ar k ≫ hom (t k) = ar 0 ≫ hom (t 0) := by
          intro k
          refine Fin.cases rfl (fun k ↦ ?_) k
          change (y ≫ S.pr p tail k) ≫ hom (tail k) = x ≫ hom (t 0)
          rw [Category.assoc, S.comm]
          exact hxy.symm
        obtain ⟨l, hl, _⟩ := S.universal (p + 1) t Y ar har
        refine ⟨l, hl 0, ?_⟩
        apply product_ext S (l ≫ b) y
        intro k
        rw [Category.assoc, hb k]
        exact hl k.succ
    have : PreservesLimit (cospan (hom (t 0)) g) A := hp (t 0) _ g
    have lim := isLimitPullbackConeMapOfIsLimit A comm pb.isLimit
    obtain ⟨d, hd, hud⟩ := ih tail Z (fun k ↦ a k.succ)
      (fun k ↦ (ha k.succ).trans (ha (Fin.succ 0)).symm)
    have had : a 0 ≫ A.map (hom (t 0)) = d ≫ A.map g := by
      dsimp [g]
      rw [A.map_comp, ← Category.assoc, hd 0]
      exact (ha (Fin.succ 0)).symm
    let l := PullbackCone.IsLimit.lift lim (a 0) d had
    have hl0 : l ≫ A.map (S.pr (p + 1) t 0) = a 0 :=
      PullbackCone.IsLimit.lift_fst lim _ _ _
    have hlb : l ≫ A.map b = d := PullbackCone.IsLimit.lift_snd lim _ _ _
    refine ⟨l, ?_, ?_⟩
    · intro k
      refine Fin.cases hl0 (fun k ↦ ?_) k
      rw [← hb k, A.map_comp, ← Category.assoc, hlb, hd k]
    · intro m hm
      apply PullbackCone.IsLimit.hom_ext lim
      · exact (hm 0).trans hl0.symm
      · exact (hud (m ≫ A.map b) (fun k ↦ by
          rw [Category.assoc, ← A.map_comp, hb k]
          exact hm k.succ)).trans hlb.symm

private theorem mapped_product_iso {C D : Type u} [Category C] [Category D]
    {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom) (A : C ⥤ D)
    (hp : ∀ (t : T) (Z : C) (g : Z ⟶ U), PreservesLimit (cospan (hom t) g) A)
    (S' : SiteCechComplex (fun t ↦ A.obj (f t)) (fun t ↦ A.map (hom t)))
    (p : ℕ) (t : Fin (p + 1) → T) :
    ∃ e : A.obj (S.W p t) ≅ S'.W p t,
      ∀ k, e.hom ≫ S'.pr p t k = A.map (S.pr p t k) := by
  have hc : ∀ k, A.map (S.pr p t k) ≫ A.map (hom (t k)) =
      A.map (S.pr p t 0) ≫ A.map (hom (t 0)) := by
    intro k
    simp only [← A.map_comp, S.comm]
  obtain ⟨a, ha, hua⟩ := S'.universal p t _ (fun k ↦ A.map (S.pr p t k)) hc
  obtain ⟨b, hb, hub⟩ := mapped_product_universal S A hp p t _
    (S'.pr p t) (S'.comm p t)
  have hab : a ≫ b = 𝟙 _ := by
    obtain ⟨c, hc, hu⟩ := mapped_product_universal S A hp p t _
      (fun k ↦ A.map (S.pr p t k)) hc
    apply (hu _ _).trans (hu _ _).symm
    · intro k
      rw [Category.assoc, hb, ha]
    · intro k
      simp
  have hba : b ≫ a = 𝟙 _ := by
    apply product_ext S'
    intro k
    rw [Category.assoc, ha, hb]
    simp
  exact ⟨⟨a, b, hab, hba⟩, ha⟩

-- The fixed interface includes sheaf coherence assumptions unused by product transport.
set_option linter.unusedVariables false in
/-- Transport the covering and all its chosen iterated products, with their projections.
Source: Stacks Project, Sites, proof of Tag 09YL (the Hom pullback calculation).
(blueprint: lem-weil-pbc-colimit-of-sites-cech-complex-transport).

Proof: `hcover` transports the stage covering, since the image of `ofArrows` is the
presieve of the image arrows. The equivalence `hQ`, with witness `i`, transports the
covering to the colimit site. Each resulting covering has chosen iterated products by
`SiteCechComplex.exists_of_covering`. At a stage, induct on the number of factors:
the one-factor case is the object itself, and the next product is a pullback of one
original covering arrow along the remaining product's map to the base. `hpullback`
preserves this pullback, so the image satisfies the same universal property. This
argument applies to any original choice `S`, by uniqueness of the universal product.
For the canonical functor to the colimit, lift a test object, its finitely many arrows,
and their compatibility equations to a common stage using the object and arrow set
colimits. There the image of the original product is a product by the stage argument.
Lift its unique mediating arrow to the colimit. Two mediating arrows become equal at a
later common stage by the equality criterion for filtered set colimits; this proves
uniqueness. Thus the canonical functor also preserves these products (the argument of
09YL). Finally the universal properties of the image product and the chosen target
product give inverse maps: their composites have the identity projections and hence
are identities. The forward map commutes with each projection by its construction.
There are no tuples when the covering index is empty, since every degree has at least
one factor; all assertions about those tuples are then vacuous.
-/
theorem colimitSite_cech_complex_transport
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Cat.{u, u}) (P : ∀ j, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderComposition]
    [∀ j, (P j).IsStableUnderBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteColimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange] [Q.HasPullbacks]
    (hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)
    [∀ j, (V.ι.app j).toFunctor.IsContinuous (P j).toGrothendieck Q.toGrothendieck]
    (G : ∀ j, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (θ : ∀ (j k : J) (a : j ⟶ k),
      (G j).obj ⟶ (F.map a).toFunctor.op ⋙ (G k).obj)
    (hθid : ∀ (j : J) (X : F.obj j),
      Arrow.mk ((θ j j (𝟙 j)).app (op X)) = Arrow.mk (𝟙 ((G j).obj.obj (op X))))
    (hθcomp : ∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l) (X : F.obj j),
      Arrow.mk ((θ j l (a ≫ b)).app (op X)) =
        Arrow.mk ((θ j k a).app (op X) ≫
          (θ k l b).app (op ((F.map a).toFunctor.obj X))))
    (H : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (E : ∀ j, H.obj j ≅
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (G j)) :
    let β := fun (j : J) (X : F.obj j) ↦
      (((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).unit.app (G j)).hom.app (op X)) ≫
        (E j).inv.hom.app (op ((V.ι.app j).toFunctor.obj X))
    (∀ (j k : J) (a : j ⟶ k) (X : F.obj j),
      Arrow.mk (β j X ≫ (H.map a).hom.app (op ((V.ι.app j).toFunctor.obj X))) =
        Arrow.mk ((θ j k a).app (op X) ≫ β k ((F.map a).toFunctor.obj X))) →
    ∀ (c : Cocone H), IsColimit c →
    ∀ (i : J) {T : Type u} [Finite T] {U : F.obj i}
      (f : T → F.obj i) (hom : ∀ t, f t ⟶ U),
      Presieve.ofArrows f hom ∈ P i U →
    ∀ S : SiteCechComplex f hom,
      (∀ a : Under i,
        Presieve.ofArrows (fun t ↦ (F.map a.hom).toFunctor.obj (f t))
          (fun t ↦ (F.map a.hom).toFunctor.map (hom t)) ∈
            P a.right ((F.map a.hom).toFunctor.obj U) ∧
        ∃ Sa : SiteCechComplex (fun t ↦ (F.map a.hom).toFunctor.obj (f t))
            (fun t ↦ (F.map a.hom).toFunctor.map (hom t)),
          ∀ (p : ℕ) (t : Fin (p + 1) → T),
            ∃ e : (F.map a.hom).toFunctor.obj (S.W p t) ≅ Sa.W p t,
              ∀ k, e.hom ≫ Sa.pr p t k = (F.map a.hom).toFunctor.map (S.pr p t k)) ∧
      (Presieve.ofArrows (fun t ↦ (V.ι.app i).toFunctor.obj (f t))
          (fun t ↦ (V.ι.app i).toFunctor.map (hom t)) ∈
            Q ((V.ι.app i).toFunctor.obj U) ∧
        ∃ Sc : SiteCechComplex (fun t ↦ (V.ι.app i).toFunctor.obj (f t))
            (fun t ↦ (V.ι.app i).toFunctor.map (hom t)),
          ∀ (p : ℕ) (t : Fin (p + 1) → T),
            ∃ e : (V.ι.app i).toFunctor.obj (S.W p t) ≅ Sc.W p t,
              ∀ k, e.hom ≫ Sc.pr p t k = (V.ι.app i).toFunctor.map (S.pr p t k)) := by
  dsimp
  intro hcompat c hc i T instT U f hom hcov S
  obtain ⟨hpres, _⟩ := colimit_site_covering_continuity J F P hfinite hcover hpullback
    V hobjects harrows Q hQ
  constructor
  · intro a
    have hcov' := hcover i a.right a.hom U _ hcov
    rw [Presieve.map_ofArrows] at hcov'
    obtain ⟨Sa⟩ := SiteCechComplex.exists_of_covering (P a.right) hcov'
    refine ⟨hcov', Sa, ?_⟩
    intro p t
    exact mapped_product_iso S (F.map a.hom).toFunctor
      (fun t Z g ↦ hpullback i a.right a.hom U (f t) Z _ hcov
        (hom t) g (Presieve.ofArrows.mk t)) Sa p t
  · have hcov' : (Presieve.ofArrows f hom).map (V.ι.app i).toFunctor ∈
        Q ((V.ι.app i).toFunctor.obj U) :=
      (hQ _ _).mpr ⟨i, U, Presieve.ofArrows f hom, rfl, hcov, rfl⟩
    rw [Presieve.map_ofArrows] at hcov'
    obtain ⟨Sc⟩ := SiteCechComplex.exists_of_covering Q hcov'
    refine ⟨hcov', Sc, ?_⟩
    intro p t
    exact mapped_product_iso S (V.ι.app i).toFunctor
      (fun t Z g ↦ hpres i U (f t) Z _ hcov (hom t) g (Presieve.ofArrows.mk t)) Sc p t

end CategoryTheory
