/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite
public import Sheaf.CategoryTheory.FinitePrecoverage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Category.Cat
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.Pullback
import Sheaf.AlgebraicGeometry.AffineEtaleFiniteColimitConstruction
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite affine étale colimit presentation

Source: Stacks Project, Étale Cohomology 0EYL; Sites 09YL.
(blueprint: lem-weil-pbc-affine-etale-colimit-presentation).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The raw labelled-pair construction does not reflect arbitrary finite coverings.
There are infinitely many distinct source labels over one identity arrow. Their presieve
is infinite, while its image is the singleton identity covering. -/
private theorem labelled_presieve_obstruction {C : Type u} [Category.{v} C]
    (A : C) (J : Precoverage C) [J.HasIsos] :
    let K := InducedCategory C (fun X : (Σ _ : ℕ, C) ↦ X.2)
    let W : K ⥤ C := inducedFunctor _
    ∃ (X : K) (R : Presieve X), ¬ Finite R.uncurry ∧ R.map W ∈ J (W.obj X) := by
  let K := InducedCategory C (fun X : (Σ _ : ℕ, C) ↦ X.2)
  let W : K ⥤ C := inducedFunctor _
  let X : K := ⟨0, A⟩
  let Y : ℕ → K := fun n ↦ ⟨n, A⟩
  let f : ∀ n, Y n ⟶ X := fun _ ↦ InducedCategory.homMk (𝟙 A)
  let R := Presieve.ofArrows Y f
  have hi : Function.Injective
      (fun n : ℕ ↦ (⟨⟨Y n, f n⟩, Presieve.ofArrows.mk n⟩ : R.uncurry)) := by
    intro n m h
    exact congrArg (fun t : R.uncurry ↦ t.val.1.1) h
  refine ⟨X, R, ?_, ?_⟩
  · intro h
    have : Finite ℕ := Finite.of_injective _ hi
    exact not_finite ℕ
  · have heq : R.map W = Presieve.singleton (𝟙 A) := by
      rw [Presieve.map_ofArrows]
      apply le_antisymm
      · rintro B g ⟨n⟩
        exact Presieve.singleton_self _
      · intro B g h
        cases h
        exact Presieve.ofArrows.mk 0
    rw [heq]
    exact Precoverage.mem_coverings_of_isIso (𝟙 A)

/-- No finite-cover precoverage on the raw labelled category can satisfy the
unrestricted reflection equivalence. The infinite presieve supplied above would be
a covering, contradicting the assumed finiteness of every covering presieve. -/
private theorem labelled_precoverage_no_reflection {C : Type u} [Category.{v} C]
    (A : C) (J : Precoverage C) [J.HasIsos] :
    let K := InducedCategory C (fun X : (Σ _ : ℕ, C) ↦ X.2)
    let W : K ⥤ C := inducedFunctor _
    ∀ (P : Precoverage K),
      (∀ (X : K) (R : Presieve X), R ∈ P X → Finite R.uncurry) →
      ¬ (∀ (X : K) (R : Presieve X), R ∈ P X ↔ R.map W ∈ J (W.obj X)) := by
  intro K W P hfinite hreflect
  obtain ⟨X, R, hinfinite, hcover⟩ := labelled_presieve_obstruction A J
  exact hinfinite (hfinite X R ((hreflect X R).mpr hcover))

/-- Reflection of arbitrary covers through a fully faithful functor forces finite
fibers on objects when every source covering presieve is finite. Apply reflection to
the family of all lifts of the identity at a fixed target object. -/
private theorem finite_fibers_of_finite_cover_reflection
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : C ⥤ D) [W.Full] [W.Faithful]
    (P : Precoverage C) (Q : Precoverage D) [Q.HasIsos]
    (hfinite : ∀ (A : C) (R : Presieve A), R ∈ P A → Finite R.uncurry)
    (hreflect : ∀ (A : C) (R : Presieve A), R.map W ∈ Q (W.obj A) → R ∈ P A)
    (A : C) : Finite {B : C // W.obj B = W.obj A} := by
  classical
  let E := {B : C // W.obj B = W.obj A}
  let B : E → C := fun b ↦ b.val
  let f : ∀ b, B b ⟶ A := fun b ↦ W.preimage (eqToHom b.property)
  let R := Presieve.ofArrows B f
  have hm : R.map W = Presieve.singleton (𝟙 (W.obj A)) := by
    rw [Presieve.map_ofArrows]
    apply le_antisymm
    · rintro Z g ⟨b⟩
      change Presieve.singleton (𝟙 (W.obj A)) (W.map (W.preimage (eqToHom b.property)))
      rw [W.map_preimage]
      have hid {X Y : D} (h : X = Y) :
          Presieve.singleton (𝟙 Y) (eqToHom h) := by
        subst Y
        exact Presieve.singleton_self _
      exact hid b.property
    · intro Z g hg
      cases hg
      have h := Presieve.ofArrows.mk (f := fun b ↦ W.map (f b)) (⟨A, rfl⟩ : E)
      simpa [f] using h
  have hR : Finite R.uncurry := hfinite A R (hreflect A R (hm ▸
    Precoverage.mem_coverings_of_isIso (J := Q) (𝟙 (W.obj A))))
  exact Finite.of_injective
    (fun b : E ↦ (⟨⟨B b, f b⟩, Presieve.ofArrows.mk b⟩ : R.uncurry)) (by
      intro b b' h
      apply Subtype.ext
      exact congrArg (fun t : R.uncurry ↦ t.val.1) h)


/-- A faithful functor with finite object fibers reflects finiteness of presieves.
Map the arrows of the presieve to their images. Each fiber injects into an object fiber:
faithfulness identifies arrows once their source objects agree. A map with finite fibers
and finite target has finite domain. -/
private theorem finite_presieve_of_finite_image
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : C ⥤ D) [W.Faithful]
    (hfib : ∀ Y : D, Finite {X : C // W.obj X = Y})
    (A : C) (R : Presieve A) (hR : Finite (R.map W).uncurry) : Finite R.uncurry := by
  classical
  let q : R.uncurry → (R.map W).uncurry := fun x ↦
    ⟨⟨W.obj x.val.1, W.map x.val.2⟩, Presieve.map_map x.property⟩
  by_contra hinf
  have : Infinite R.uncurry := not_finite_iff_infinite.mp hinf
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber q
  have : Finite (q ⁻¹' {y}) := by
    apply Finite.of_injective (fun x : q ⁻¹' {y} ↦
      (⟨x.val.val.1, congrArg (fun a : (R.map W).uncurry ↦ a.val.1) x.property⟩ :
        {X : C // W.obj X = y.val.1}))
    intro x x' h
    apply Subtype.ext
    apply Subtype.ext
    have hs : x.val.val.1 = x'.val.val.1 := congrArg Subtype.val h
    have hq : q x.val = q x'.val := x.property.trans x'.property.symm
    rcases x with ⟨⟨⟨B, f⟩, hf⟩, hx⟩
    rcases x' with ⟨⟨⟨B', f'⟩, hf'⟩, hx'⟩
    change B = B' at hs
    subst B'
    have hm : W.map f = W.map f' :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val hq)).2
    exact congrArg (Sigma.mk B) (W.map_injective hm)
  exact hy.false

/-- The unrestricted reflection criterion for the finite inverse-image precoverage
holds exactly when the fully faithful functor has finite object fibers. Necessity uses
all lifts of an identity; sufficiency uses finiteness of the image covering presieve. -/
private theorem finite_cover_reflection_iff_finite_fibers
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : C ⥤ D) [W.Full] [W.Faithful] (Q : Precoverage D) [Q.HasIsos]
    (hQfinite : ∀ (A : D) (R : Presieve A), R ∈ Q A → Finite R.uncurry) :
    (∀ (A : C) (R : Presieve A),
      R ∈ (Precoverage.finite C ⊓ Q.comap W) A ↔ R.map W ∈ Q (W.obj A)) ↔
      ∀ Y : D, Finite {X : C // W.obj X = Y} := by
  constructor
  · intro h Y
    by_cases hex : ∃ X : C, W.obj X = Y
    · obtain ⟨X, rfl⟩ := hex
      exact finite_fibers_of_finite_cover_reflection W
        (Precoverage.finite C ⊓ Q.comap W) Q
        (fun _ _ hR ↦ hR.1.to_subtype) (fun A R hR ↦ (h A R).mpr hR) X
    · have : IsEmpty {X : C // W.obj X = Y} := ⟨fun x ↦ hex ⟨x.val, x.property⟩⟩
      infer_instance
  · intro hfib A R
    constructor
    · exact fun hR ↦ hR.2
    · intro hR
      have := finite_presieve_of_finite_image W hfib A R (hQfinite _ _ hR)
      exact ⟨Set.toFinite _, hR⟩

/-- Source: Stacks Project, Categories 004A; Sites 0A34 and 09YL;
Étale Cohomology 0EYL, qcqs case.

Proof (steps 4 and 8 of lem-weil-pbc-affine-etale-site-colimit):
1. Strictify the coherent system using pairs (j,A) with j ≤ i at stage i. Morphisms
   are maps between their U-images in the affine site at i. The comparison functor to
   that site is an equivalence with quasi-inverse e_i. Transition fixes the pair and
   conjugates the image of a morphism by gamma. The gamma cocycle gives strict
   composition. Give the new category the precoverage detected by the equivalence.
   Its finite site axioms and finiteness follow from the finite étale precoverage.
2. Define v'_i(j,A) = v_j(A), conjugating morphisms by delta. The delta cocycle gives
   strict compatibility with transition, and normalization gives eta. The theta
   comparison satisfies the displayed Arrow equation. Equivalence transports all
   pullbacks, covering preservation, continuity, adjunctions, and finite-limit
   preservation. This construction uses Cat.{u, u + 1}: the original sites have
   object universe u + 1 and morphism universe u; coefficients remain Type u.
3. Form filtered colimits of the object and arrow sets. Source, target, identities
   and composition descend because any finite collection of data occurs at a common
   stage and any equality holds eventually. These operations give K; compatibility
   of v' gives W. The union of images of stage precoverages is P (09YL).
4. Object descent makes W essentially surjective. Map descent makes it full and
   eventual equality makes it faithful, after representing any two objects at a
   common stage. Thus W is an equivalence.
5. Images of stage covers cover by preservation. For reflection, represent the
   finite presieve at a stage. Descent of covers presents its W-image as a stage
   cover; map descent and eventual equality align these two finite presentations
   at a common later stage. Invariance under isomorphism then identifies the original
   presieve with an image of a stage cover. This proves the finite-presieve version and
   its site axioms; reflection for arbitrary presieves remains unproved.
(blueprint: lem-weil-pbc-affine-etale-colimit-presentation). -/
/- STATEMENT-DISPUTED: the node's labelled-pair construction does not satisfy the
last covering-reflection iff for arbitrary presieves. The proved finite construction
is `exists_affineEtale_finite_colimit_construction`. An infinite presieve on distinct
natural-number labels has singleton identity image; see `labelled_presieve_obstruction`.
Reflection with finite covers forces finite object fibers; see
`finite_fibers_of_finite_cover_reflection`; for finite target covers it is also sufficient,
as `finite_cover_reflection_iff_finite_fibers` proves. The full
existential is not refuted: a different presentation needs additional justification. -/
theorem exists_affineEtale_colimit_presentation_finite
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c)
    (U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
          (D.obj (op j)).FullAffineEtale)
      (v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale)
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
                R ∈ P A ↔ R.map W ∈ fullAffineEtalePrecoverage c.pt (W.obj A))) := by
  sorry

end AlgebraicGeometry.Scheme
