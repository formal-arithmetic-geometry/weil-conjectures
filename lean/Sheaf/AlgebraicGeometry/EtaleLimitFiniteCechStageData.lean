/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent
import Sheaf.AlgebraicGeometry.DescendSurjective

set_option linter.unusedVariables false

/-! # Canonical descended finite Čech comparison

Source: Stacks Project, Tags 09YN, 09YP and 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Descend a finite covering and construct its canonical complex diagram and cocone.
Source: Stacks Project, Limits, Tags 01ZM (spreading out), 07RP (étaleness), 07RR
(surjectivity); Étale Cohomology, Tag 09YQ; Sites, Tag 09YN; Cohomology on Sites,
Tag 09YP, proof of lemma-colimit.
(blueprint: lem-weil-pbc-etale-limit-finite-cech-stage-data).

Proof: The qcqs étale objects U and V_k have finite presentation over the qcqs base.
Spread out these objects and the finite family of arrows. Descend étaleness using 07RP.
Apply 07RR to the finite disjoint union of the covering arrows to make the family
jointly surjective at a common stage i₀. Choose the resulting U₀, V₀, f₀ and their
base-change isomorphisms eU, eV; their arrow equation is part of descent. All later
families are the actual pullbacks B_j(U₀), B_j(V₀), B_j(f₀), hence remain covering.
The products W₀ over U₀ pull back to the products over Uj and U. Their isomorphisms
are the unique maps preserving each projection, as required by the eNj and eNlim
equations. Pullback pasting constructs γ and δ; their first-projection equations
uniquely prescribe them, since their other projection is fixed in the étale category.
In degree n define A_j to be the product of the sections F_j on the stage nerve.
For every arrow a, prescribe its tuple component by the unit for D(a.op), followed
by φ_a and the inverse of γ. Define the cocone tuple component by the unit for π_j,
then eG_j inverse, L.ι_j, and the inverse of δ. These are precisely the last two
equations. Naturality of the units and the coefficient maps with respect to every
nerve projection commutes with the face maps, hence with the alternating differential.
The coefficient identity and composition equations, pullback uniqueness, and hG
then prove the functor and cocone laws. Take eA and eK to be the resulting complex
identifications. No section-continuity isomorphism or colimit universal property is
asserted here; these belong to the separate colimit theorem. Empty K gives empty
products of section groups; the same formulas define zero complexes. -/
theorem exists_etale_limit_finite_cech_stage_data
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
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
    (L : Cocone G) (hL : IsColimit L)
    (U : c.pt.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (hV : ∀ k, CompactSpace (V k).left ∧ QuasiSeparatedSpace (V k).left)
    (hf : Sieve.ofArrows V f ∈ c.pt.smallEtaleTopology U) :
    ∃ (i₀ : I) (U₀ : (D.obj (op i₀)).Etale)
    (V₀ : K → (D.obj (op i₀)).Etale) (f₀ : ∀ k, V₀ k ⟶ U₀)
    (eU : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj U₀ ≅ U)
    (eV : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (V₀ k) ≅ V k),
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
    ∃ (A : J ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
      (eA : ∀ j : J, A.obj j ≅
        (cechComplexFunctor (fun k : K ↦ Over.mk (fj j k))).obj
          ((Over.forget (Uj j)).op ⋙ (F j.val).obj))
      (cA : Cocone A)
      (eK : cA.pt ≅ (cechComplexFunctor (fun k : K ↦ Over.mk (f k))).obj
        ((Over.forget U).op ⋙ L.pt.obj))
      (eNj : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        Wj j n t ≅ Nj j n t)
      (eNlim : ∀ (n : ℕ) (t : Fin (n + 1) → K), Wlim n t ≅ Nlim n t)
      (γ : ∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t) ≅ Wj k n t)
      (δ : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op j.val))).obj (Wj j n t) ≅ Wlim n t),
      (CompactSpace U₀.left ∧ QuasiSeparatedSpace U₀.left) ∧
      (∀ k, CompactSpace (V₀ k).left ∧ QuasiSeparatedSpace (V₀ k).left) ∧
      (∀ k, Blim.map (f₀ k) ≫ eU.hom = (eV k).hom ≫ f k) ∧
      (∀ j : J, Sieve.ofArrows (Vj j) (fj j) ∈
        (D.obj (op j.val)).smallEtaleTopology (Uj j)) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNj j n t).hom ≫ (Pi.π (fun a ↦ Over.mk (fj j (t a))) a).left =
          (B j).map (pr₀ n t a)) ∧
      (∀ (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNlim n t).hom ≫ (Pi.π (fun a ↦ Over.mk (f (t a))) a).left =
          Blim.map (pr₀ n t a) ≫ (eV (t a)).hom) ∧
      (∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (γ j k a n t).hom.left ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE k.property).op) =
          pullback.fst (Wj j n t).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op)) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (δ j n t).hom.left ≫ pullback.fst (W₀ n t).hom (c.π.app (op i₀)) =
          pullback.fst (Wj j n t).hom (c.π.app (op j.val)) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op)) ∧
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
