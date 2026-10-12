/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.AlgebraicGeometry.DescendSurjective
import Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Descent of a finite qcqs étale covering

Source: Stacks Project, Tags 01ZM, 07RP, 07RR and 09YP. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Descend just the finite geometric covering, with its arrow equations.
Source: Stacks Project, Tags 01ZM, 07RP, 07RR and 09YQ.
(blueprint: lem-weil-pbc-etale-limit-finite-cover-descent).

Proof: The limit base is qcqs by affine-limit permanence. The qcqs sources of the
étale structure maps give quasi-compact and quasi-separated structure maps, hence
finite presentation. Use 01ZM(1) to spread out U and each V_k. Each model is qcqs
because it is of finite presentation over a qcqs stage. Apply 07RP to its structure
map to make it étale. Choose a common upper bound of these finitely many stages,
retaining the isomorphisms to U and V_k by pullback composition. Use 01ZM(2) for
the arrows, and take another common upper bound; this gives the displayed arrow
identities with the same object isomorphisms. The finite disjoint union of the
arrows is locally finitely presented and has qcqs source and target. Its limit
base change is surjective because the original family covers. Apply 07RR to
make it surjective at one later stage. This is a covering at that stage. Every
subsequent family is its actual base change, hence is covering. All models
remain qcqs under these affine base changes. For empty K the union is the empty
scheme: 07RR makes the target empty at a stage, so the empty family covers.
No sheaves, nerve products, or complex maps are involved. -/
theorem exists_etale_limit_finite_cover_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
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
    (CompactSpace U₀.left ∧ QuasiSeparatedSpace U₀.left) ∧
    (∀ k, CompactSpace (V₀ k).left ∧ QuasiSeparatedSpace (V₀ k).left) ∧
    (∀ k, Blim.map (f₀ k) ≫ eU.hom = (eV k).hom ≫ f k) ∧
    (∀ j : J, Sieve.ofArrows (Vj j) (fj j) ∈
        (D.obj (op j.val)).smallEtaleTopology (Uj j)) := by sorry

end AlgebraicGeometry.Etale
