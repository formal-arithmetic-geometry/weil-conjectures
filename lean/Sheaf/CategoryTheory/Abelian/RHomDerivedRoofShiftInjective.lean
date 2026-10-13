/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.CategoryTheory.KInjectiveBridge
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Shift compatibility on an injective cocycle

Source: Stacks Tags 06XR, 070I and 05TE
(blueprint: lem-sc-p1-rhom-hom-derived-roof-shift-injective-cocycle).
-/

@[expose] public section

universe w w₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

/-- The unit-shift equation for the class constructed from one injective cocycle.
Source: Stacks Project, Tags 06XR (1), 070I and 05TE, as expanded in the parent
node's first proof step
(blueprint: lem-sc-p1-rhom-hom-derived-roof-shift-injective-cocycle).

Proof: I and K = I[1] are bounded below complexes of injectives and hence are
K-injective. Use their identity K-injective resolutions in hroof. If α is the
complex comparison K.obj ≅ I.obj[1], the given cocycle f corresponds, via α and
the degreewise shift isomorphism, to a cocycle f' : M ⟶ I.obj.X (n+1).
The class b in the statement is the class of f on K, carried through the derived
unit and the canonical quotient shift comparison e. The commShift property of
the derived unit identifies its image under the displayed homology shiftMap
with the class of f' on I, carried through the derived unit. The homology shift
isomorphism sends f to f' without a sign: the shift is in the target complex,
and the source is M concentrated in degree zero. Apply hroof for the identity
resolutions of I and K to these two classes. Naturality along e gives the roof
formula for the class b at X[1]. The resulting derived morphisms agree after
postcomposition with the inclusion shift comparison and shift addition:
shifting a morphism has unsigned components, and (I[1])[n] and I[n+1] both have
differential (-1)^(n+1)d_I. The quotient comparisons in the roof formula commute
with shifts. Thus both sides are the localized morphism of the same cocycle f',
with the same quotient comparison appended. This argument concerns one cocycle;
surjectivity onto cohomology and transport to arbitrary derived objects are
proved separately in the importing parent module. -/
theorem rhom_hom_derived_roof_shift_injective_cocycle
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w₂} AddCommGrpCat.{v}] (M : C) :
    let V := preadditiveCoyoneda.obj (op M)
    let RV := V.rightDerivedFunctorPlus
    let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
    let S := (DerivedCategory.singleFunctor C 0).obj M
    ∀ (ψ : ∀ (X : DerivedCategory.Plus C) (n : ℤ),
        (H n).obj (RV.obj X) ≃+ (S ⟶ X.obj⟦n⟧))
      (hnat : (∀ (X Y : DerivedCategory.Plus C) (g : X ⟶ Y) (n : ℤ)
          (a : (H n).obj (RV.obj X)),
        ψ Y n ((H n).map (RV.map g) a) =
          ψ X n a ≫ ((DerivedCategory.Plus.ι (C := C)).map g)⟦n⟧'))
      (hroof : (∀ (K : CochainComplex.Plus C) (r : CochainComplex.KInjectiveResolutionChoice K.obj)
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
            ((DerivedCategory.quotientCompQhIso C).hom.app K.obj)⟦n⟧')),
    ∀ (I : CochainComplex.Plus C) (_hi : ∀ k : ℤ, Injective (I.obj.X k)),
      let X := (DerivedCategory.Plus.Q (C := C)).obj I
      let K := I⟦(1 : ℤ)⟧
      ∀ (n : ℤ) (f : M ⟶ K.obj.X n)
        (hf : f ≫ K.obj.d n ((ComplexShape.up ℤ).next n) = 0),
      let J := V.mapCochainComplexPlus.obj K
      let a := J.obj.homologyπ n ((J.obj.sc n).abCyclesIso.inv ⟨f, hf⟩)
      let η := V.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj K)
      let q : (HomotopyCategory.Plus.quotient C).obj K ≅
          ((HomotopyCategory.Plus.quotient C).obj I)⟦(1 : ℤ)⟧ :=
        (HomotopyCategory.Plus.ι C).preimageIso
          ((HomotopyCategory.quotient C (.up ℤ)).mapIso
              (((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).app I) ≪≫
            ((HomotopyCategory.quotient C (.up ℤ)).commShiftIso (1 : ℤ)).app I.obj ≪≫
            ((HomotopyCategory.Plus.ι C).commShiftIso (1 : ℤ)).symm.app
              ((HomotopyCategory.Plus.quotient C).obj I))
      let e := (DerivedCategory.Plus.Qh (C := C)).mapIso q ≪≫
        ((DerivedCategory.Plus.Qh (C := C)).commShiftIso (1 : ℤ)).app
          ((HomotopyCategory.Plus.quotient C).obj I)
      let b := (H n).map (RV.map e.hom)
        ((H n).map η ((DerivedCategory.Plus.homologyFunctorObjQIso J n).inv a))
      ψ X (n + 1)
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).shiftMap
            (((RV ⋙ DerivedCategory.Plus.ι).commShiftIso (1 : ℤ)).hom.app X)
            n (n + 1) (by omega) b) =
        ψ (X⟦(1 : ℤ)⟧) n b ≫
          (((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).hom.app X)⟦n⟧' ≫
          (shiftFunctorAdd' (DerivedCategory C) 1 n (n + 1) (by omega)).inv.app X.obj := by
  sorry

end CategoryTheory.Functor
