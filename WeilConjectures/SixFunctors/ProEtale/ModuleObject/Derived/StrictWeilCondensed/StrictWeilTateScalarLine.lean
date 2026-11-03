/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedDerivedTensorComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # The signed Tate scalar line and its Frobenius square

Source: latest blueprint, Tate compatibility, scalar extension paragraph.
(blueprint: lem-wf-tate-scalar-line)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
open PurityTransport

/-- The specified exact pullback/scalar comparison, shared by the line statement
and the strict-pair functor. This is the canonical composite, with no witness chosen.
Source: Tate compatibility, coefficient square (blueprint: lem-wf-tate-scalar-line). -/
def tateScalarComparison (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (g : X ≅ X)
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    finiteCoefficientDerivedExtension X ell h ⋙ action ((Coefficient.rational F).obj ell) g ≅
      action ((Coefficient.rational E).obj ell) g ⋙
        finiteCoefficientDerivedExtension X ell h :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory ((Coefficient.rational F).obj ell) g.hom).symm
    ≪≫ (derivedUpperStarExtendScalarsIso (Profinite.padicSubfieldRingObjMap ell h) g.hom).symm
    ≪≫ Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory ((Coefficient.rational E).obj ell) g.hom) _


/-- The canonical finite scalar/Frobenius comparison is monoidal for a strong
monoidal structure on the prescribed derived extension, and the signed Tate line
has an equivariant scalar comparison.
Source: latest blueprint, lem-wf-tate-twist-compatibility.proof.md, the equality
F_X(m)=F_X tensor E_X(m) with its Weil structure (blueprint: lem-wf-tate-scalar-line).
Proof: use the ordinary balanced scalar tensor comparison, normalized on pure
tensors, and derive it on flat-term K-flat representatives. Tensor products of
these representatives remain K-flat, so the unit and associativity identities
on pure tensors descend to a strong monoidal structure on the existing derived
extension functor. The balanced pullback/scalar comparison commutes with these
tensorators on representatives. The exact-pullback identification is monoidal
for the transported action structure, so their composite c is monoidal.
On the compatible primitive-root cover, send a tensor a tensor (e x) to e(ax).
Its inverse sends e y to y tensor e. Rescaling e multiplies both formulas by the
same unit, hence these maps glue. Root pullback and coefficient inclusions commute,
which gives the displayed Frobenius square in degree one. Unit normalization gives
degree zero; tensor compatibility gives positive powers by induction; evaluation
and the invertibility of the line give negative powers. The canonical signed-line
identification and the degree-zero derived comparison transport this equality to
the actual tateDatum used here. No root frame is fixed globally. -/
theorem tate_scalar_line (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (g : X ≅ X)
    [∀ x : X, Invertible (ell : X.residueField x)]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) (m : ℤ) :
    let B := finiteCoefficientDerivedExtension X ell h
    let cEF := tateScalarComparison ell g h
    ∃ hB : B.Monoidal, letI := hB
      NatTrans.IsMonoidal cEF.hom ∧
      ∃ b : B.obj (derivedTateLine ell (.rational E) X m) ≅
          derivedTateLine ell (.rational F) X m,
        (action ((Coefficient.rational F).obj ell) g).map b.hom ≫
            (tateDatum ell (.rational F) g m).hom =
          cEF.hom.app (derivedTateLine ell (.rational E) X m) ≫
            B.map (tateDatum ell (.rational E) g m).hom ≫ b.hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
