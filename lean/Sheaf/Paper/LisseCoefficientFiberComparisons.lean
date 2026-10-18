/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.LisseRationalScalarFiberMaps
import Sheaf.Paper.LisseCoefficientFiberEndomorphisms
import Sheaf.Paper.LisseFiberCoherenceNormalization

/-!
# Coherent scalar comparisons for geometric fibres

Source: Deligne, Weil II (1.1.1) b)-d), pp. 146-147.
(blueprint: lem-pod-lisse-coefficient-fiber-comparisons).
-/

@[expose] public section

universe d
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {Ω : Type d} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (K : Type (d + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

/-- Transport a rational coefficient comparison to the recorded pseudofunctor categories.
Source: Weil II (1.1.1) d)
(blueprint: lem-pod-lisse-coefficient-fiber-comparisons). -/
noncomputable def lisseCoefficientFiberRawComparison
    (S : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      LisseRationalSheaf l E₀.val Y ⥤ ModuleCat.{d + 1} E₀.val)
    (E₀ L₀ : Padic.FiniteCoefficientFields l K) (f : E₀ ⟶ L₀)
    (e : S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K) ≅
      lisseRationalScalarExtension l E₀.val Y L₀.val
          (IntermediateField.inclusion (leOfHom f)) ⋙ S L₀ ⋙
        ModuleCat.extendScalars (algebraMap L₀.val K)) :
    let P := (lisseCoefficientDiagramData l Y K).diagram
    let J := fun E₀ : Padic.FiniteCoefficientFields l K ↦
      (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor ⋙
        S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K)
    J E₀ ≅ (P.map f.toLoc).toFunctor ⋙ J L₀ := by
  let D := lisseCoefficientDiagramData l Y K
  let P := D.diagram
  let T := (eqToHom (D.obj_eq E₀)).toFunctor
  let U := (eqToHom (D.obj_eq E₀).symm).toFunctor
  let V := (eqToHom (D.obj_eq L₀)).toFunctor
  let Q := lisseRationalScalarExtension l E₀.val Y L₀.val
    (IntermediateField.inclusion (leOfHom f))
  let R := (P.map f.toLoc).toFunctor
  let H := S L₀ ⋙ ModuleCat.extendScalars (algebraMap L₀.val K)
  have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
  have he := D.map_eq E₀ L₀ (leOfHom f)
  rw [hf] at he
  have h : U ⋙ R ⋙ V = Q := congrArg Cat.Hom.toFunctor he
  let cancel (C D : Cat.{d + 1, d + 2}) (h : C = D) :
      (eqToHom h).toFunctor ⋙ (eqToHom h.symm).toFunctor ≅ 𝟭 C := by
    cases h
    exact Functor.leftUnitor _
  let a : T ⋙ Q ≅ R ⋙ V :=
    Functor.isoWhiskerLeft T (eqToIso h.symm) ≪≫
      (Functor.associator T U (R ⋙ V)).symm ≪≫
        Functor.isoWhiskerRight (cancel _ _ (D.obj_eq E₀)) (R ⋙ V) ≪≫
          Functor.leftUnitor _
  exact Functor.isoWhiskerLeft T e ≪≫
    (Functor.associator T Q H).symm ≪≫ Functor.isoWhiskerRight a H ≪≫
      Functor.associator R V H

/-- Scalar extension of the rational geometric fibres gives coherent transition
isomorphisms over the finite coefficient fields.

Source: Weil II (1.1.1) b)-d), especially the iterated-extension comparison (d)(i),
pp. 146-147; finite-level stalk comparison and adic reconstruction.
(blueprint: lem-pod-lisse-coefficient-fiber-comparisons).

Proof: let B be the least coefficient field. First observe that restriction along
B-to-E induces a bijection on K-linear natural endomorphisms of the geometric fibre
functors after extension to K. To see this, restrict an E-sheaf to B using any finite
integral lattice, and apply the given endomorphism to that restriction. Multiplications
by elements of E are rational B-sheaf morphisms, so naturality makes the endomorphism
commute with them. The E-to-K eigensummand of K tensor_B E is cut out by the separability
idempotent (all coefficient extensions have characteristic zero). The endomorphism
therefore preserves this summand, which is the required E-fibre. This defines its
extension. Conversely the E-sheaf is a retract of the scalar extension of its
B-restriction, by that same idempotent. Naturality with the inclusion and projection of
the retract proves uniqueness, independence of the lattice and functoriality. The
argument also applies to natural isomorphisms by extending the inverse. The pure-tensor
formula supplies all the asserted identifications with the prescribed functors.

The supplied comparisons are already transported to the functors J. Choose
a comparison b_E from J_B to P(B-to-E) followed by J_E. For E-to-L, require its desired
comparison, after whiskering by P(B-to-E), to equal b_E inverse followed by b_L and
P's composition constraint. A supplied comparison for E-to-L reduces this
lifting problem to the bijection on natural endomorphisms just proved. Lift the inverse
as well; injectivity proves that both lifts are inverse. This gives e_f. Whiskering is
also injective on comparisons with an iterated scalar extension, since postcomposing
with a supplied comparison reduces this to endomorphisms. Whisker the proposed identity
and composition equations by P(B-to-E). Substitute the defining equations for e. Cancel
the adjacent b's. The identity equation is then P's unit law; the composition equation
is its associativity pentagon. Injectivity gives the two equations below. This
normalization uses the actual recorded constraints of P and does not assume that their
components are the canonical tensor maps. -/
theorem lisseCoefficientFiberComparisons_exists
    (S : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      LisseRationalSheaf l E₀.val Y ⥤ ModuleCat.{d + 1} E₀.val)
    (hS : ∀ (E₀ : Padic.FiniteCoefficientFields l K)
      (F : LisseRationalSheaf l E₀.val Y), (S E₀).obj F = lisseRationalFiber l E₀.val Y y F)
    (hmap : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      IsLisseRationalFiberFunctor Y y l E₀.val (S E₀) (hS E₀))
    (hcomparison :
      let P := (lisseCoefficientDiagramData l Y K).diagram
      let J := fun E₀ : Padic.FiniteCoefficientFields l K ↦
        (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor ⋙
          S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K)
      ∀ (E₀ L₀ : Padic.FiniteCoefficientFields l K) (f : E₀ ⟶ L₀),
        J E₀ ≅ (P.map f.toLoc).toFunctor ⋙ J L₀) :
    let P := (lisseCoefficientDiagramData l Y K).diagram
    let J := fun E₀ : Padic.FiniteCoefficientFields l K ↦
      (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor ⋙
        S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K)
    ∃ e : ∀ {E₀ L₀ : Padic.FiniteCoefficientFields l K} (f : E₀ ⟶ L₀),
        J E₀ ≅ (P.map f.toLoc).toFunctor ⋙ J L₀,
      (∀ (E₀ : Padic.FiniteCoefficientFields l K) (X : P.obj ⟨E₀⟩),
        (e (𝟙 E₀)).hom.app X ≫
          (J E₀).map ((P.mapId ⟨E₀⟩).hom.toNatTrans.app X) = 𝟙 _) ∧
      (∀ {E₀ L₀ M₀ : Padic.FiniteCoefficientFields l K}
        (f : E₀ ⟶ L₀) (g : L₀ ⟶ M₀) (X : P.obj ⟨E₀⟩),
        (e (f ≫ g)).hom.app X ≫
            (J M₀).map ((P.mapComp f.toLoc g.toLoc).hom.toNatTrans.app X) =
          (e f).hom.app X ≫ (e g).hom.app ((P.map f.toLoc).toFunctor.obj X)) := by
  exact CategoryTheory.Pseudofunctor.coherentFiberComparisons_of_endWhisker
    (Padic.finiteCoefficientBase l K)
    (fun E₀ ↦ show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)
    _ _ (fun {_ _} f ↦ hcomparison _ _ f)
    (lisseCoefficientFiberEndomorphisms_whisker_bijective l Y y K S hS hmap)

end AlgebraicGeometry.Scheme
