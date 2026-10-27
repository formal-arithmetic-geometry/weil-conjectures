module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Coset.Defs
import Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange

/-! # Semilinear induction of a scheme action along a subgroup

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X 2.3 Step 2,
printed p. 150, contracted products and diagram (2.b); Stacks Tags 01JB and 01JC.
(blueprint: lem-sfb-semilinear-coset-scheme)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Scalar-twisted induction, with its contracted-product mapping property and base change.

Source: ILO, Expose X 2.3 Step 2, printed p. 150, diagram (2.b), expanded into
left cosets; Stacks Tags 01JB and 01JC for scheme coproducts.
(blueprint: lem-sfb-semilinear-coset-scheme)

Proof:
1. Write g = s(c) eta(g), with eta(g) in Gamma. Put S_g = Spec(pi(g) inverse).
   Contravariance of Spec gives S_(gh) = S_g composed with S_h; each S_g fixes Spec e.
2. Form Y as the coproduct of copies of W (lem-weil-pbc-scheme-coproduct-family).
   On its c-th inclusion j_c set pY j_c = S_(s(c)) p, and set t_g = j_c d_(eta(g)).
   The action law gives the relation and the scalar formula for t_g. Coprojections
   are open immersions, disjoint and covering; their complements are open as well.
3. Define a_h j_c = t_(h s(c)). Then a_h t_g = t_(hg). Coproduct uniqueness
   proves the action laws and pY a_h = S_h pY.
4. Define f j_c = q. Gamma-invariance gives f t_g = q and f a_h = f.
   As every S_g fixes Spec e, the same coproduct test shows b f = r pY.
5. Any family b_g with b_(g gamma) = b_g d_gamma descends uniquely by its
   representative subfamily. Applied to two representative systems this gives
   inverse isomorphisms preserving t, pY, f and a by coproduct uniqueness.
6. The codiagonal Y to W expresses f as q after that codiagonal. Apply
   lem-weil-pbc-sets-etale-inverse-image-constant-base-change, then the canonical
   pullback reassociation, to identify Y times_B T with the coproduct of W times_B T.
   Its coprojections are exactly pullback.map applied to t_(s(c)).
7. The invariant endomorphisms induce the displayed pullback.map actions.
   Every point lies in a representative summand. If w' = d_gamma w, then
   s(b) gamma s(c) inverse carries t_(s(c))(w) to t_(s(b))(w'). A point in W_T
   gives a point in Y_T via t_1. No field-normality or scheme-finiteness is used. -/
theorem semilinear_coset_scheme
    (e K : Type u) [Field e] [Field K] [Algebra e K]
    (G : Type v) [Group G] [Finite G] (pi : G →* (K ≃ₐ[e] K)) (Gamma : Subgroup G)
    (W B : Scheme.{u}) (p : W ⟶ Spec (.of K)) (b : B ⟶ Spec (.of e))
    (d : Gamma →* Aut W)
    (hd : ∀ gamma : Gamma, (d gamma).hom ≫ p =
      p ≫ Spec.map (CommRingCat.ofHom (pi (gamma : G)⁻¹).toRingHom))
    (q : W ⟶ B)
    (hqbase : q ≫ b = p ≫ Spec.map (CommRingCat.ofHom (algebraMap e K)))
    (hq : ∀ gamma : Gamma, (d gamma).hom ≫ q = q)
    (s : G ⧸ Gamma → G)
    (hs : ∀ c : G ⧸ Gamma, Quotient.mk (QuotientGroup.leftRel Gamma) (s c) = c)
    (hsone : s (Quotient.mk (QuotientGroup.leftRel Gamma) (1 : G)) = 1) :
    ∃ (Y : Scheme.{u}) (pY : Y ⟶ Spec (.of K)) (t : G → (W ⟶ Y))
      (a : G →* Aut Y) (f : Y ⟶ B)
      (htf : ∀ g : G, t g ≫ f = q) (haf : ∀ h : G, (a h).hom ≫ f = f),
      Nonempty (IsColimit (Cofan.mk Y (fun c : G ⧸ Gamma ↦ t (s c)))) ∧
      (∀ c : G ⧸ Gamma, IsOpenImmersion (t (s c))) ∧
      (∀ c : G ⧸ Gamma, IsClopen (Set.range (t (s c)))) ∧
      (∀ c c' : G ⧸ Gamma, c ≠ c' →
        Disjoint (Set.range (t (s c))) (Set.range (t (s c')))) ∧
      (∀ y : Y, ∃ (c : G ⧸ Gamma) (w : W), t (s c) w = y) ∧
      (∀ (g : G) (gamma : Gamma), t (g * gamma) = (d gamma).hom ≫ t g) ∧
      (∀ g : G, t g ≫ pY =
        p ≫ Spec.map (CommRingCat.ofHom (pi g⁻¹).toRingHom)) ∧
      (∀ h g : G, t g ≫ (a h).hom = t (h * g)) ∧
      (∀ h : G, (a h).hom ≫ pY =
        pY ≫ Spec.map (CommRingCat.ofHom (pi h⁻¹).toRingHom)) ∧
      (f ≫ b = pY ≫ Spec.map (CommRingCat.ofHom (algebraMap e K))) ∧
      (∀ (Z : Scheme.{u}) (k : G → (W ⟶ Z)),
        (∀ (g : G) (gamma : Gamma), k (g * gamma) = (d gamma).hom ≫ k g) →
        ∃! l : Y ⟶ Z, ∀ g : G, t g ≫ l = k g) ∧
      (∀ (s' : G ⧸ Gamma → G),
        (∀ c : G ⧸ Gamma, Quotient.mk (QuotientGroup.leftRel Gamma) (s' c) = c) →
        s' (Quotient.mk (QuotientGroup.leftRel Gamma) (1 : G)) = 1 →
        ∀ (Y' : Scheme.{u}) (pY' : Y' ⟶ Spec (.of K)) (t' : G → (W ⟶ Y'))
          (a' : G →* Aut Y') (f' : Y' ⟶ B),
        Nonempty (IsColimit (Cofan.mk Y' (fun c : G ⧸ Gamma ↦ t' (s' c)))) →
        (∀ (g : G) (gamma : Gamma), t' (g * gamma) = (d gamma).hom ≫ t' g) →
        (∀ g : G, t' g ≫ pY' =
          p ≫ Spec.map (CommRingCat.ofHom (pi g⁻¹).toRingHom)) →
        (∀ h g : G, t' g ≫ (a' h).hom = t' (h * g)) →
        (∀ g : G, t' g ≫ f' = q) →
        ∃ phi : Y ≅ Y',
          (∀ g : G, t g ≫ phi.hom = t' g) ∧
          phi.hom ≫ pY' = pY ∧ phi.hom ≫ f' = f ∧
          ∀ h : G, (a h).hom ≫ phi.hom = phi.hom ≫ (a' h).hom) ∧
      (∀ (T : Scheme.{u}) (z : T ⟶ B),
        Nonempty (IsColimit (Cofan.mk (pullback f z) (fun c : G ⧸ Gamma ↦
          pullback.map q z f z (t (s c)) (𝟙 T) (𝟙 B)
            (by simpa only [Category.comp_id] using (htf (s c)).symm)
            (by simp only [Category.comp_id, Category.id_comp]))))) ∧
      (∀ (T : Scheme.{u}) (z : T ⟶ B),
        (Nonempty ↥(pullback q z) ∧
          ∀ x y : ↥(pullback q z), ∃ gamma : Gamma,
            pullback.map q z q z (d gamma).hom (𝟙 T) (𝟙 B)
              (by simpa only [Category.comp_id] using (hq gamma).symm)
              (by simp only [Category.comp_id, Category.id_comp]) x = y) →
        Nonempty ↥(pullback f z) ∧
          ∀ x y : ↥(pullback f z), ∃ h : G,
            pullback.map f z f z (a h).hom (𝟙 T) (𝟙 B)
              (by simpa only [Category.comp_id] using (haf h).symm)
              (by simp only [Category.comp_id, Category.id_comp]) x = y) := by
  sorry

end AlgebraicGeometry
