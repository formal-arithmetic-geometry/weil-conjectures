/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.KInjectiveBridge
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# The natural RHom comparison and its roof normalization

Source: Stacks Tags 06XR and 070I (blueprint: lem-sc-p1-rhom-hom-derived-roof).
-/

@[expose] public section

universe w w₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

/-- The natural RHom comparison with its cocycle roof formula, before shift compatibility.
Source: Stacks Project, Tags 06XR (part 1) and 070I
(blueprint: lem-sc-p1-rhom-hom-derived-roof).

Proof: represent a bounded below derived object by a bounded below complex of injectives.
Cocycles from M to its degree n terms are degree n Hom-complex cocycles from M[0].
The boundary subgroup consists precisely of null-homotopic maps, so taking the quotient
identifies H^n(Hom(M,I)) with homotopy-category maps M[0] to I[n]. Bounded below
injective complexes and their shifts are K-injective. The K-injective localization
bijection identifies these maps with derived-category maps. Postcompose with the inverse
of the resolution map to obtain the stated roof. All operations preserve addition.
The derived unit on an injective complex is invertible and identifies the source with
H^n(RHom(M,Q(I))). Extend the comparison along a representing isomorphism to every
object of D+. For a derived morphism between two such objects, the K-injective
localization bijection gives a lift between resolutions, unique up to homotopy.
Applying Hom(M,-) to the lift and passing to cohomology yields naturality, since the
lift commutes with the resolution maps in the derived category. Taking the identity
morphism with two resolutions proves independence of the resolution and hence the
formula for every r, not only the resolution used to construct the comparison. -/
theorem exists_rhom_hom_derived_roof
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w₂} AddCommGrpCat.{v}] (M : C) :
    let V := preadditiveCoyoneda.obj (op M)
    let RV := V.rightDerivedFunctorPlus
    let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
    let S := (DerivedCategory.singleFunctor C 0).obj M
    ∃ ψ : ∀ (X : DerivedCategory.Plus C) (n : ℤ),
        (H n).obj (RV.obj X) ≃+ (S ⟶ X.obj⟦n⟧),
      (∀ (X Y : DerivedCategory.Plus C) (g : X ⟶ Y) (n : ℤ)
          (a : (H n).obj (RV.obj X)),
        ψ Y n ((H n).map (RV.map g) a) =
          ψ X n a ≫ ((DerivedCategory.Plus.ι (C := C)).map g)⟦n⟧') ∧
      (∀ (K : CochainComplex.Plus C) (r : CochainComplex.KInjectiveResolutionChoice K.obj)
          (hb : CochainComplex.plus C r.complex)
          (_hi : ∀ k : ℤ, Injective (r.complex.X k)) (n : ℤ)
          (f : M ⟶ r.complex.X n) (hf : f ≫ r.complex.d n (n + 1) = 0),
        let I : CochainComplex.Plus C := ⟨r.complex, hb⟩
        letI := r.quasiIso
        let e : (DerivedCategory.Plus.Q (C := C)).obj K ≅
            (DerivedCategory.Plus.Q (C := C)).obj I :=
          (DerivedCategory.Plus.ι (C := C)).preimageIso
            ((DerivedCategory.quotientCompQhIso C).symm.app K.obj ≪≫
              asIso (DerivedCategory.Q.map r.map) ≪≫
              (DerivedCategory.quotientCompQhIso C).app r.complex)
        let J := V.rightDerivedComplexWithResolution K r
        let a := J.homologyπ n ((J.sc n).abCyclesIso.inv
          ⟨f, by
            change f ≫ r.complex.d n ((ComplexShape.up ℤ).next n) = 0
            rw [CochainComplex.next]
            exact hf⟩)
        let b := (DerivedCategory.Plus.homologyFunctorObjQIso
          (V.mapCochainComplexPlus.obj I) n).inv a
        let η := V.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj I)
        ψ ((DerivedCategory.Plus.Q (C := C)).obj K) n
            ((H n).map (RV.map e.inv)
              ((H n).map η b)) =
          ShiftedHom.map (Cocycle.equivHomShift.symm
              (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)) DerivedCategory.Q ≫
            (CategoryTheory.inv (DerivedCategory.Q.map r.map))⟦n⟧' ≫
            ((DerivedCategory.quotientCompQhIso C).hom.app K.obj)⟦n⟧') := by
  sorry

end CategoryTheory.Functor
