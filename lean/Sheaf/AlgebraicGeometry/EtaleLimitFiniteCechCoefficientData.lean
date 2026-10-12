/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Canonical coefficient maps on descended Čech complexes

Source: Stacks Project, Tags 01ZM, 07RP, 07RR and 09YP. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Fixed descended geometry gives a complex diagram and a compatible cocone.
Source: Stacks Project, Tag 09YP, proof of lemma-colimit, canonical maps in its
Čech comparison; Tag 09YQ for the étale realization.
(blueprint: lem-weil-pbc-etale-limit-finite-cech-coefficient-data).

Proof: Use the actual Čech complex at each stage as the object of A, and the
Čech complex with coefficients L.pt as the cocone point. Thus eA and eK are
identity isomorphisms. In each degree, use the product universal property to
prescribe the tuple component of A(a) by the adjunction unit, φ_a, and γ_a inverse,
conjugated by eNj at the source and target. Prescribe each cocone leg using the
unit, eG inverse, L.ι, and δ inverse, conjugated by eNj and eNlim. The projection
identities hNj and hNlim imply compatibility with every deletion-of-coordinate
map of the nerve, by uniqueness of product maps. The equations hγ and hδ imply
identity and composition of the geometric transport maps, by uniqueness of maps
into pullbacks. Naturality of the adjunction unit and of φ, eG, and L.ι now shows
that every tuple component commutes with each face map. Additivity yields
commutation with the alternating differential, giving complex morphisms. Product
extensionality, the coefficient identity/composition assumptions, unit coherence,
and pullback uniqueness prove A.map_id and A.map_comp. For the cocone equation
use hG and L.w, again checking each tuple component. These checks construct A
and cA and give exactly the two displayed equations. No finite-cover descent,
quasi-compactness, limit universal property, or colimit universal property is used.
The construction works for empty K, when every positive-length tuple index is
empty and each section product is the zero group. -/
theorem exists_etale_limit_finite_cech_coefficient_data
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G)
    (U : c.pt.Etale)
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (i₀ : I) (U₀ : (D.obj (op i₀)).Etale)
    (V₀ : K → (D.obj (op i₀)).Etale) (f₀ : ∀ k, V₀ k ⟶ U₀)
    (eU : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj U₀ ≅ U)
    (eV : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (V₀ k) ≅ V k)
    (he : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).map (f₀ k) ≫
        eU.hom = (eV k).hom ≫ f k) :
    let J := {j : I // i₀ ≤ j}
    let B := fun j : J ↦
      MorphismProperty.Over.pullback @Etale ⊤ (D.map (homOfLE j.property).op)
    let Blim := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))
    let Uj := fun j : J ↦ (B j).obj U₀
    let Vj := fun (j : J) (k : K) ↦ (B j).obj (V₀ k)
    let fj := fun (j : J) (k : K) ↦ (B j).map (f₀ k)
    let W₀ := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f₀ (t a))).left
    let pr₀ := fun (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)) ↦
      (Pi.π (fun a ↦ Over.mk (f₀ (t a))) a).left
    let Wj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦ (B j).obj (W₀ n t)
    let Wlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦ Blim.obj (W₀ n t)
    let Nj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (fj j (t a))).left
    let Nlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f (t a))).left
    let Pj := fun (j : J) (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ (F j.val).obj.obj (op (Nj j n t))
    let Plim := fun (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ L.pt.obj.obj (op (Nlim n t))
    ∀ (eNj : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        Wj j n t ≅ Nj j n t)
      (eNlim : ∀ (n : ℕ) (t : Fin (n + 1) → K), Wlim n t ≅ Nlim n t)
      (γ : ∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t) ≅ Wj k n t)
      (δ : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op j.val))).obj (Wj j n t) ≅ Wlim n t)
      (hNj : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNj j n t).hom ≫ (Pi.π (fun a ↦ Over.mk (fj j (t a))) a).left =
          (B j).map (pr₀ n t a))
      (hNlim : ∀ (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNlim n t).hom ≫ (Pi.π (fun a ↦ Over.mk (f (t a))) a).left =
          Blim.map (pr₀ n t a) ≫ (eV (t a)).hom)
      (hγ : ∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (γ j k a n t).hom.left ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE k.property).op) =
          pullback.fst (Wj j n t).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op))
      (hδ : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (δ j n t).hom.left ≫ pullback.fst (W₀ n t).hom (c.π.app (op i₀)) =
          pullback.fst (Wj j n t).hom (c.π.app (op j.val)) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op)),
      ∃ (A : J ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
      (eA : ∀ j : J, A.obj j ≅
        (cechComplexFunctor (fun k : K ↦ Over.mk (fj j k))).obj
          ((Over.forget (Uj j)).op ⋙ (F j.val).obj))
      (cA : Cocone A)
      (eK : cA.pt ≅ (cechComplexFunctor (fun k : K ↦ Over.mk (f k))).obj
        ((Over.forget U).op ⋙ L.pt.obj)),
      (∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (eA j).inv.f n ≫ (A.map a).f n ≫ (eA k).hom.f n ≫
            Pi.π (Pj k n) t ≫ (F k.val).obj.map (eNj k n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app
                (op (Wj j n t)) ≫
            (φ (show j.val ⟶ k.val from a)).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t))) ≫
            (F k.val).obj.map (γ j k a n t).inv.op) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (eA j).inv.f n ≫ (cA.ι.app j).f n ≫ eK.hom.f n ≫
            Pi.π (Plim n) t ≫ L.pt.obj.map (eNlim n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Wj j n t)) ≫
            (eG j.val).inv.hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            (L.ι.app j.val).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            L.pt.obj.map (δ j n t).inv.op) := by sorry

end AlgebraicGeometry.Etale
