/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseRationalScalarFiberMaps
import WeilConjectures.CategoryTheory.PoincareDuality.LisseCoefficientRetractDescent
import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientRestrictionRetracts
import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientRestrictionHomSpan

/-!
# Endomorphisms of geometric fibres under coefficient extension

Source: Deligne, Weil II (1.1.1) b)-d), pp. 146-147.
(blueprint: lem-pod-lisse-coefficient-fiber-endomorphisms).
-/

@[expose] public section

universe d
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {Ω : Type d} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (K : Type (d + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

/-- Extension from the least coefficient field detects and uniquely extends natural
endomorphisms of the geometric fibre with algebraically closed coefficients.

Source: Deligne, Weil II (1.1.1) b)-d), pp. 146-147 (restriction and extension of
coefficients); Stacks Project, Algebra, `lemma-separable-algebraic-diagonal`, finite
separable case (the diagonal summand of the scalar tensor product).
(blueprint: lem-pod-lisse-coefficient-fiber-endomorphisms).

Proof: write B for the least coefficient field, fix a finite coefficient field E, and
let T = P(B-to-E). Every rational E-sheaf is a retract of T(A) for some rational
B-sheaf A, namely the E-extension of its restriction to B, split by the separability
idempotent of E tensor_B E (lem-pod-lisse-coefficient-restriction-retracts). For
rational B-sheaves A and A', J_E sends every morphism T(A) to T(A') into the K-span of
the maps J_E(T(g)), g : A to A': coefficient Hom base change gives the E-span before
fibres, and the pure-tensor formula hmap makes the fibre functor E-linear on Hom
(lem-pod-lisse-coefficient-restriction-hom-span). The generic retract-and-span descent
(lem-pod-lisse-coefficient-retract-descent) then gives the bijection: a transformation
on T followed by J_E is natural on the K-span of image maps by linearity; its extension
at an object X is the sandwich of the given component at the chosen A_X between the
fibre maps of the retract inclusion and projection; naturality for these sandwiches
proves naturality and restriction, and the retract identities prove uniqueness. For
E=B and for zero objects the same argument applies without change. -/
theorem lisseCoefficientFiberEndomorphisms_whisker_bijective
    (S : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      LisseRationalSheaf l E₀.val Y ⥤ ModuleCat.{d + 1} E₀.val)
    (hS : ∀ (E₀ : Padic.FiniteCoefficientFields l K)
      (F : LisseRationalSheaf l E₀.val Y), (S E₀).obj F = lisseRationalFiber l E₀.val Y y F)
    (hmap : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      IsLisseRationalFiberFunctor Y y l E₀.val (S E₀) (hS E₀)) :
    let P := (lisseCoefficientDiagramData l Y K).diagram
    let J := fun E₀ : Padic.FiniteCoefficientFields l K ↦
      (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor ⋙
        S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K)
    ∀ E₀ : Padic.FiniteCoefficientFields l K,
      Function.Bijective (fun u : J E₀ ⟶ J E₀ ↦
        Functor.whiskerLeft (P.map (homOfLE
          (show Padic.finiteCoefficientBase l K ≤ E₀ from
            show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)).toLoc).toFunctor u) := by
  dsimp only
  intro E₀
  apply CategoryTheory.bijective_whiskerLeft_of_span_retract
    (T := ((lisseCoefficientDiagramData l Y K).diagram.map (homOfLE
      (show Padic.finiteCoefficientBase l K ≤ E₀ from
        show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)).toLoc).toFunctor)
    (F := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor ⋙
      S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K))
  · exact lisseCoefficientRestriction_retracts l Y K E₀
  · exact lisseCoefficientRestriction_hom_span l Y K y S hS hmap E₀

end AlgebraicGeometry.Scheme
