/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentHom
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf
public import
  WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFiniteModelProofAPISupplement
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexColimit

/-!
# Finite descent of coefficient morphisms over any allowed base field

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-reduction-finite-coefficients/sec-descent-to-a-finite-coefficient-field/
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-hom.md, clauses (1)--(3),
with the Q30 any-field scope repair of 2026-11-02
(blueprint: det-lem-coefficient-finite-descent-hom).

The old positive-characteristic theorem and the canonical maps it defines remain
available. This statement includes characteristic zero and uses those same maps,
coefficient rings, ordinary derived categories, and bounded constructible objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-- The natural derived scalar adjunctions, uniformly bounded-below coefficient
complex colimit, and finite descent of every shifted morphism, over any field
whose characteristic differs from the coefficient prime.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-reduction-finite-coefficients/sec-descent-to-a-finite-coefficient-field/
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-hom.md (1)--(3) and its
.proof.md, with the node's Q30 scope repair of 2026-11-02
(blueprint: det-lem-coefficient-finite-descent-hom).

Proof, following the five current DAG steps:
1. A field is Noetherian, including in characteristic zero. A finite type scheme
   over it is Noetherian by lem-weil-pbc-finite-type-over-noetherian. Finite
   subextensions form a set directed by composita
   (def-weil-finite-subextension-directed-set).
2. Apply lem-weil-pbc-condensed-flat-coefficient-calculus to X. Exact extension
   is left adjoint to exact restriction on the ordinary derived categories, and
   the recorded derived extension is termwise tensor. Evaluate the adjunctions
   on C and D_F[r], also over the algebraic closure. The tensor multiplication,
   unit and shift comparisons identify their transitions with coefficient
   inclusions. Adjunction naturality gives the two displayed transition identities.
3. By sk-prop-sfb-qlbar-colimit-x the algebraic-closure coefficient ring is the
   filtered colimit of finite fields. The tail above E is cofinal by composita.
   Tensor preserves this colimit by the coefficient calculus. Apply this termwise
   to every bounded representative K of D to obtain the specified colimiting
   coefficientComplexCocone. A zero term below a stays zero after scalar extension
   and restriction, so every stage has the same lower bound a.
4. Apply sk-lem-constructible-ext-continuity (1) in its any-field setting to C,
   this coefficient diagram, and r. Its complexes have the common lower bound
   just established; its first-argument hypothesis holds for every bounded
   constructible object over E. This gives the restricted-target Hom colimit
   bijection.
5. Identify that comparison using the natural adjunctions of step 2 and the
   actual colimit of step 3. It is the specified scalar-extension map on Hom.
   Elements of a filtered colimit have finite-stage representatives and two
   representatives agree precisely when they agree at a common later stage.
   The final two conjuncts express exactly its surjectivity and injectivity.
-/
theorem coefficient_finite_descent_hom_of_char_ne
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (_hchar : ringChar k ≠ ℓ)
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (C D : BoundedConstructible (padicSubfieldRingObj X ℓ E)) (r : ℤ) :
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      Function.Bijective (finiteCoefficientDerivedHomEquiv X ℓ h C.obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧))) ∧
    Function.Bijective (finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj
      (((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧)) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : F ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedHomEquiv X ℓ (h.trans j) C.obj _
          (coefficientDescentHomTransition X ℓ h j C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionTransition X ℓ h j D.obj r) ∧
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj _
          (coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionToAlgCl X ℓ h D.obj r) ∧
    (∀ (K : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)) ℤ)
      (_e : DerivedCategory.Q.obj K ≅ D.obj) (a b : ℤ)
      (_hK : ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)),
      IsFiltered (AsSmall.{u + 1} (Under E)) ∧
        Nonempty (IsColimit (coefficientComplexCocone X ℓ K (coefficientDescentFields ℓ E)
          (fun i ↦ leOfHom (ULift.down i).hom) (fun i ↦ leOfHom (ULift.down i).hom))) ∧
        ∀ (i : AsSmall.{u + 1} (Under E)) (n : ℤ), n < a →
          IsZero (((coefficientComplexDiagram X ℓ K (coefficientDescentFields ℓ E)
            (fun j ↦ leOfHom (ULift.down j).hom)
            (fun j ↦ leOfHom (ULift.down j).hom)).obj i).X n)) ∧
    (∀ f : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C.obj ⟶
        ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧,
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
        (g : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
          ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
        coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r g = f) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : E ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧)
      (g : (derivedExtendScalarsSubfield X ℓ j).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ j).obj D.obj)⟦r⟧),
      coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f =
        coefficientDescentHomToAlgCl X ℓ j C.obj D.obj r g →
      ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (hF : F ≤ H) (hG : G ≤ H),
        coefficientDescentHomTransition X ℓ h hF C.obj D.obj r f =
          coefficientDescentHomTransition X ℓ j hG C.obj D.obj r g) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F h
    exact (finiteCoefficientDerivedHomEquiv X ℓ h C.obj _).bijective
  · exact (finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj _).bijective
  · intro F G h j f
    exact adjunction_comparison_naturality
      (finiteCoefficientDerivedAdjunction X ℓ h)
      (derivedExtendScalarsSubfield X ℓ j)
      (finiteCoefficientDerivedAdjunction X ℓ (h.trans j))
      (condensedCoefficientCompIso X ℓ h j) C.obj _ _ f _
  · intro F h f
    exact adjunction_comparison_naturality
      (finiteCoefficientDerivedAdjunction X ℓ h)
      (derivedExtendScalarsToPadicAlgCl X ℓ F)
      (finiteCoefficientDerivedAlgClAdjunction X ℓ E)
      (derivedExtendScalarsCompIso X ℓ h) C.obj _ _ f _
  · intro K e a b hK
    let : (coefficientDescentFields ℓ E).Final := by
      dsimp [coefficientDescentFields]
      infer_instance
    refine ⟨?_, ?_, ?_⟩
    · exact IsFiltered.of_equivalence (AsSmall.equiv (C := Under E))
    · exact nonempty_isColimit_coefficientComplexCocone X ℓ K
        (coefficientDescentFields ℓ E) _ _
    · intro i n hn
      exact (Mod.comap (padicSubfieldRingObjMap X ℓ
        (leOfHom (ULift.down i).hom))).map_isZero
          ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ
            (leOfHom (ULift.down i).hom))).map_isZero (hK n (Or.inl hn)))
  · intro f
    have : (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated :=
      finiteBoundedTriangulated X ℓ E
    let D' : BoundedConstructible (padicSubfieldRingObj X ℓ E) :=
      ⟨D.obj⟦r⟧, (boundedConstructible (padicSubfieldRingObj X ℓ E)).le_shift r _ D.property⟩
    let f' := f ≫ ((derivedExtendScalarsToPadicAlgCl X ℓ E).commShiftIso r).inv.app D.obj
    obtain ⟨F, h, j, g, hg⟩ := constructibleCocone_homSurj X ℓ E E C D'
      (ObjectProperty.homMk f')
    let g' := g.hom ≫ ((derivedExtendScalarsSubfield X ℓ h).commShiftIso r).hom.app D.obj
    refine ⟨F, h, g', ?_⟩
    have hh := congrArg (·.hom) hg
    dsimp only [constructibleCocone] at hh
    simp only [ObjectProperty.FullSubcategory.comp_hom, tensorComp_inv, tensorComp_hom,
      constructibleToPadicAlgCl_map_hom] at hh
    have : NatTrans.CommShift (derivedExtendScalarsCompIso X ℓ h).hom ℤ :=
      tensorCompShift X ℓ h
    have hc := NatTrans.shift_app_comm (derivedExtendScalarsCompIso X ℓ h).hom r D.obj
    simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hc
    change f' = (derivedExtendScalarsCompIso X ℓ h).inv.app C.obj ≫
      (derivedExtendScalarsToPadicAlgCl X ℓ F).map g.hom ≫
        (derivedExtendScalarsCompIso X ℓ h).hom.app (D.obj⟦r⟧) at hh
    dsimp only [g', coefficientDescentHomToAlgCl, coefficientDescentDerivedHomMap]
    simp only [Functor.map_comp, Category.assoc]
    rw [hc]
    rw [← Category.assoc, ← Category.assoc]
    rw [← Category.assoc] at hh
    rw [← hh]
    simp only [f', Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id f
  · intro F G h j f g heq
    let H := IsFiltered.max F G
    have hF : F ≤ H := leOfHom (IsFiltered.leftToMax F G)
    have hG : G ≤ H := leOfHom (IsFiltered.rightToMax F G)
    refine ⟨H, hF, hG, ?_⟩
    apply descentHomToAlgCl_injective X ℓ (h.trans hF) C.obj D.obj r
    rw [descentHomToAlgCl_transition, descentHomToAlgCl_transition]
    exact heq

end AlgebraicGeometry.ProEtale
