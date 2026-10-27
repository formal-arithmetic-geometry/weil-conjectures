module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Localized counit calculus for augmented arrows

Source: the completed-pullback invocation in the main-20261015 blueprint,
`lem-cbc-completed-extension-zero-comparison.proof.md`; the abstract calculation is
agent-written. Stacks, Derived Categories, Tag 06XN supplies computing counits in applications.
(blueprint: lem-cbc-localized-counit-augmentation-calculus)
-/

@[expose] public noncomputable section

universe uA vA wA uB vB wB uX vX

open CategoryTheory

namespace CategoryTheory.LocalizedCounitAugmentation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (G : HomotopyCategory A (ComplexShape.up ℤ) ⥤ HomotopyCategory B (ComplexShape.up ℤ))
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (τ : DerivedCategory.Qh ⋙ L ⟶ G ⋙ DerivedCategory.Qh)
  (P : HomotopyCategory A (ComplexShape.up ℤ) → Prop)
  (hτ : ∀ H, P H → IsIso (τ.app H))

/-- The specified augmentation `w`, using only the inverse of the counit at `S(X)`.
Source: completed-pullback invocation, main-20261015 blueprint, agent calculation.
(blueprint: lem-cbc-localized-counit-augmentation-calculus) -/
def augmentation {X : Type uX} [Category.{vX} X]
    (S R : X ⥤ HomotopyCategory A (ComplexShape.up ℤ)) (a : S ⟶ R)
    (hS : ∀ x, P (S.obj x)) (x : X) :
    (G ⋙ DerivedCategory.Qh).obj (S.obj x) ⟶ (DerivedCategory.Qh ⋙ L).obj (R.obj x) := by
  letI := hτ (S.obj x) (hS x)
  exact inv (τ.app (S.obj x)) ≫ L.map (DerivedCategory.Qh.map (a.app x))

/-- The specified isomorphism `χ_r = F(r)⁻¹ ≫ τ_H` for a given good resolution.
Source: completed-pullback invocation, main-20261015 blueprint, agent calculation.
The inverse is `τ_H⁻¹ ≫ F(r)`, since `Qh` inverts quasi-isomorphisms and `L` preserves
isomorphisms. No isomorphism condition is imposed on `G(r)` or on `τ` at the target.
(blueprint: lem-cbc-localized-counit-augmentation-calculus) -/
def resolutionIso {H K : HomotopyCategory A (ComplexShape.up ℤ)}
    (r : H ⟶ K) (hH : P H) (hr : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) r) :
    L.obj (DerivedCategory.Qh.obj K) ≅ DerivedCategory.Qh.obj (G.obj H) := by
  letI := hτ H hH
  letI : IsIso (DerivedCategory.Qh.map r) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) r hr
  exact (L.mapIso (asIso (DerivedCategory.Qh.map r))).symm ≪≫ asIso (τ.app H)

/-- The comparison `c_{s,r} = χ_r⁻¹ ≫ χ_s`, requiring no comparison arrow.
Source: completed-pullback invocation, main-20261015 blueprint, agent calculation.
(blueprint: lem-cbc-localized-counit-augmentation-calculus) -/
def comparison {H H' K : HomotopyCategory A (ComplexShape.up ℤ)}
    (r : H ⟶ K) (hH : P H) (hr : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) r)
    (s : H' ⟶ K) (hH' : P H') (hs : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s) :
    DerivedCategory.Qh.obj (G.obj H) ≅ DerivedCategory.Qh.obj (G.obj H') :=
  (resolutionIso G L τ P hτ r hH hr).symm ≪≫ resolutionIso G L τ P hτ s hH' hs

/-- The map computed in two specified resolutions is `χ_r⁻¹ ≫ D(f) ≫ χ_s`.
Source: completed-pullback invocation, main-20261015 blueprint, agent calculation.
(blueprint: lem-cbc-localized-counit-augmentation-calculus) -/
def computedMap {X : Type uX} [Category.{vX} X]
    (R : X ⥤ HomotopyCategory A (ComplexShape.up ℤ)) {x y : X} (f : x ⟶ y)
    {H H' : HomotopyCategory A (ComplexShape.up ℤ)}
    (r : H ⟶ R.obj x) (hH : P H) (hr : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) r)
    (s : H' ⟶ R.obj y) (hH' : P H') (hs : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s) :
    DerivedCategory.Qh.obj (G.obj H) ⟶ DerivedCategory.Qh.obj (G.obj H') :=
  (resolutionIso G L τ P hτ r hH hr).inv ≫
    L.map (DerivedCategory.Qh.map (R.map f)) ≫ (resolutionIso G L τ P hτ s hH' hs).hom

/-- Counit calculus for the actual augmentation and arbitrary given good resolutions.
Source: completed-pullback invocation, main-20261015 blueprint; abstract proof agent-written.
(blueprint: lem-cbc-localized-counit-augmentation-calculus)

Proof plan (the seven steps of the DAG node):
1. `Qh(r)` is invertible by the derived localization, so `F(r) = L(Qh(r))` is invertible.
   Together with invertibility of `τ_H`, this gives `χ_r` and its displayed inverse.
2. Naturality at `r` gives `χ_r ≫ T(r) = τ_R`; naturality at `a` and cancellation of
   `τ_S` give `w ≫ τ_R = T(a)`, hence the augmented resolution identity.
3. Cancel `χ_r ≫ χ_r⁻¹` to get augmentation compatibility, the cocycle, and identity.
4. If `h ≫ s = r`, functoriality gives `F(h) ≫ F(s) = F(r)`; naturality of `τ`
   then gives `χ_r ≫ T(h) = χ_s`, hence `T(h) = c_{s,r}`. No `h` is constructed.
5. Apply naturality of `a` and of `τ` at `S(f)`, cancel the invertible counits at
   `S(x), S(y)`, and obtain `w_x ≫ D(f) = B(f) ≫ w_y`.
6. Use `Localization.lift`, `fac`, `liftNatTrans`, and `liftNatTrans_app` from the
   localization universal-property dependency to descend this natural transformation.
   If `f ∈ W`, cancel `B(f)` and `D(f)` in Step 5 to obtain inverse naturality.
7. Express `D(f)` through `χ_r, χ_s`; cancel `χ_r⁻¹` against `χ_r` and use Step 5.
Only `F(r)` and the counits on good objects are inverted throughout. -/
theorem calculus {X : Type uX} [Category.{vX} X]
    (S R : X ⥤ HomotopyCategory A (ComplexShape.up ℤ)) (a : S ⟶ R)
    (hS : ∀ x, P (S.obj x)) :
    (∃ w : S ⋙ G ⋙ DerivedCategory.Qh ⟶ R ⋙ DerivedCategory.Qh ⋙ L,
      ∀ x, w.app x = augmentation G L τ P hτ S R a hS x) ∧
    (∀ (x : X) (H : HomotopyCategory A (ComplexShape.up ℤ)) (r : H ⟶ R.obj x)
      (hH : P H) (hr : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) r),
      (resolutionIso G L τ P hτ r hH hr).hom ≫ DerivedCategory.Qh.map (G.map r) =
        τ.app (R.obj x) ∧
      augmentation G L τ P hτ S R a hS x ≫ (resolutionIso G L τ P hτ r hH hr).hom ≫
        DerivedCategory.Qh.map (G.map r) = DerivedCategory.Qh.map (G.map (a.app x))) ∧
    (∀ (x : X) (H H' H'' : HomotopyCategory A (ComplexShape.up ℤ))
      (r : H ⟶ R.obj x) (hH : P H)
      (hr : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) r)
      (s : H' ⟶ R.obj x) (hH' : P H')
      (hs : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s)
      (t : H'' ⟶ R.obj x) (hH'' : P H'')
      (ht : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) t),
      (augmentation G L τ P hτ S R a hS x ≫ (resolutionIso G L τ P hτ r hH hr).hom ≫
        (comparison G L τ P hτ r hH hr s hH' hs).hom =
        augmentation G L τ P hτ S R a hS x ≫ (resolutionIso G L τ P hτ s hH' hs).hom) ∧
      (comparison G L τ P hτ r hH hr s hH' hs ≪≫
        comparison G L τ P hτ s hH' hs t hH'' ht =
        comparison G L τ P hτ r hH hr t hH'' ht) ∧
      (comparison G L τ P hτ r hH hr r hH hr = Iso.refl _) ∧
      (∀ h : H ⟶ H', h ≫ s = r → DerivedCategory.Qh.map (G.map h) =
        (comparison G L τ P hτ r hH hr s hH' hs).hom)) ∧
    (∀ (x y : X) (f : x ⟶ y),
      augmentation G L τ P hτ S R a hS x ≫ L.map (DerivedCategory.Qh.map (R.map f)) =
        DerivedCategory.Qh.map (G.map (S.map f)) ≫ augmentation G L τ P hτ S R a hS y) ∧
    (∀ (W : MorphismProperty X)
      (hB : W.IsInvertedBy (S ⋙ G ⋙ DerivedCategory.Qh))
      (hD : W.IsInvertedBy (R ⋙ DerivedCategory.Qh ⋙ L)),
      (∃ w : Localization.lift (S ⋙ G ⋙ DerivedCategory.Qh) hB W.Q ⟶
          Localization.lift (R ⋙ DerivedCategory.Qh ⋙ L) hD W.Q,
        ∀ x, w.app (W.Q.obj x) =
          (Localization.fac (S ⋙ G ⋙ DerivedCategory.Qh) hB W.Q).hom.app x ≫
          augmentation G L τ P hτ S R a hS x ≫
          (Localization.fac (R ⋙ DerivedCategory.Qh ⋙ L) hD W.Q).inv.app x) ∧
      (∀ (x y : X) (f : x ⟶ y) (hf : W f),
        @inv _ _ _ _ (DerivedCategory.Qh.map (G.map (S.map f))) (hB f hf) ≫
          augmentation G L τ P hτ S R a hS x =
        augmentation G L τ P hτ S R a hS y ≫
          @inv _ _ _ _ (L.map (DerivedCategory.Qh.map (R.map f))) (hD f hf))) ∧
    (∀ (x y : X) (f : x ⟶ y) (H H' : HomotopyCategory A (ComplexShape.up ℤ))
      (r : H ⟶ R.obj x) (hH : P H)
      (hr : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) r)
      (s : H' ⟶ R.obj y) (hH' : P H')
      (hs : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s),
      augmentation G L τ P hτ S R a hS x ≫ (resolutionIso G L τ P hτ r hH hr).hom ≫
        computedMap G L τ P hτ R f r hH hr s hH' hs =
      DerivedCategory.Qh.map (G.map (S.map f)) ≫ augmentation G L τ P hτ S R a hS y ≫
        (resolutionIso G L τ P hτ s hH' hs).hom) := by
  let e : S ⋙ DerivedCategory.Qh ⋙ L ≅ S ⋙ G ⋙ DerivedCategory.Qh :=
    NatIso.ofComponents (fun x ↦ by
      have := hτ (S.obj x) (hS x)
      exact asIso (τ.app (S.obj x))) (fun f ↦ by simpa using τ.naturality (S.map f))
  let w : S ⋙ G ⋙ DerivedCategory.Qh ⟶ R ⋙ DerivedCategory.Qh ⋙ L :=
    e.inv ≫ Functor.whiskerRight a (DerivedCategory.Qh ⋙ L)
  have hw (x : X) : w.app x = augmentation G L τ P hτ S R a hS x := by
    simp [w, e, augmentation]
  have hn (x y : X) (f : x ⟶ y) :
      augmentation G L τ P hτ S R a hS x ≫ L.map (DerivedCategory.Qh.map (R.map f)) =
        DerivedCategory.Qh.map (G.map (S.map f)) ≫
          augmentation G L τ P hτ S R a hS y := by
    simpa only [← hw, Functor.comp_map] using (w.naturality f).symm
  have hres {H K : HomotopyCategory A (ComplexShape.up ℤ)}
      (r : H ⟶ K) (hH : P H) (hr : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) r) :
      (resolutionIso G L τ P hτ r hH hr).hom ≫ DerivedCategory.Qh.map (G.map r) =
        τ.app K := by
    have := hτ H hH
    have : IsIso (DerivedCategory.Qh.map r) :=
      Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) r hr
    dsimp [resolutionIso]
    have hnτ := τ.naturality r
    simp only [Functor.comp_map] at hnτ
    rw [Category.assoc, ← hnτ]
    simp
  refine ⟨⟨w, hw⟩, ?_, ?_, hn, ?_, ?_⟩
  · intro x H r hH hr
    refine ⟨hres r hH hr, ?_⟩
    rw [hres r hH hr]
    have := hτ (S.obj x) (hS x)
    dsimp [augmentation]
    have hnτ := τ.naturality (a.app x)
    simp only [Functor.comp_map] at hnτ
    rw [Category.assoc, hnτ]
    simp
  · intro x H H' H'' r hH hr s hH' hs t hH'' ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [comparison]
    · ext
      simp [comparison]
    · ext
      simp [comparison]
    · intro h hh
      have := hτ H hH
      have := hτ H' hH'
      have : IsIso (DerivedCategory.Qh.map r) :=
        Localization.inverts DerivedCategory.Qh
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) r hr
      have : IsIso (DerivedCategory.Qh.map s) :=
        Localization.inverts DerivedCategory.Qh
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) s hs
      apply (cancel_epi (resolutionIso G L τ P hτ r hH hr).hom).1
      simp only [comparison, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
      dsimp [resolutionIso]
      have hnτ := τ.naturality h
      simp only [Functor.comp_map] at hnτ
      rw [Category.assoc, ← hnτ]
      have hcomp : L.map (DerivedCategory.Qh.map h) ≫ L.map (DerivedCategory.Qh.map s) =
          L.map (DerivedCategory.Qh.map r) := by
        rw [← L.map_comp, ← DerivedCategory.Qh.map_comp, hh]
      rw [← Category.assoc]
      congr 1
      rw [L.map_inv, L.map_inv, IsIso.inv_comp_eq, ← hcomp, Category.assoc]
      simp
  · intro W hB hD
    constructor
    · refine ⟨Localization.liftNatTrans W.Q W _ _ _ _ w, ?_⟩
      intro x
      simpa only [Localization.fac, hw] using
        Localization.liftNatTrans_app W.Q W _ _
          (Localization.lift (S ⋙ G ⋙ DerivedCategory.Qh) hB W.Q)
          (Localization.lift (R ⋙ DerivedCategory.Qh ⋙ L) hD W.Q) w x
    · intro x y f hf
      have : IsIso (DerivedCategory.Qh.map (G.map (S.map f))) := by
        simpa only [Functor.comp_map] using hB f hf
      have : IsIso (L.map (DerivedCategory.Qh.map (R.map f))) := by
        simpa only [Functor.comp_map] using hD f hf
      apply (cancel_epi (DerivedCategory.Qh.map (G.map (S.map f)))).1
      simp only [IsIso.hom_inv_id_assoc]
      rw [← Category.assoc, ← hn x y f]
      simp
  · intro x y f H H' r hH hr s hH' hs
    simp only [computedMap, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hn x y f, Category.assoc]

end CategoryTheory.LocalizedCounitAugmentation
