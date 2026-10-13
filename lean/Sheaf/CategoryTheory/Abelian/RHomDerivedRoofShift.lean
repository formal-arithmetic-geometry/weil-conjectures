/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.Abelian.RHomDerivedRoof

/-!
# Shift compatibility of the roof-normalized RHom comparison

Source: Stacks Tags 06XR, 070I and 05TE
(blueprint: lem-sc-p1-rhom-hom-derived-roof-shift).
-/

@[expose] public section

universe w w₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

/-- A natural RHom comparison normalized by the roof formula commutes with a unit shift.
Source: Stacks Project, Tags 06XR (part 1), 070I and 05TE
(blueprint: lem-sc-p1-rhom-hom-derived-roof-shift).

Proof: choose a bounded below injective representative I for X. Its shift I[1] is
again bounded below and degreewise injective, so it can be used to calculate RHom of
X[1]. The derived-functor shift comparison is computed by the termwise identity
Hom(M,I[1]) = Hom(M,I)[1], with the canonical shift comparisons. Every cohomology
class is represented by a cocycle f : M to I^(n+1), because cycles surject onto
cohomology and the derived unit on I is invertible. The homology shift comparison
sends this cocycle in degree n of Hom(M,I[1]) to the same cocycle in degree n+1 of
Hom(M,I). Apply hroof to both of these classes. Their localized morphisms agree
after the shift-addition isomorphism: shifting a morphism has unsigned components,
and (I[1])[n] and I[n+1] have the same differential, (-1)^(n+1) times d_I.
The canonical unit and quotient comparisons commute with these shifts, so the
resulting equality is exactly the displayed one for Q(I). Finally transport along
the representing isomorphism Q(I) to X using hnat and naturality of the two shift
comparisons. This proves the equality for every X, n and b; no triangle or boundary
map is used. -/
theorem rhom_hom_derived_roof_shift
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
    ∀ (X : DerivedCategory.Plus C) (n : ℤ)
        (b : (H n).obj (RV.obj (X⟦(1 : ℤ)⟧))),
      ψ X (n + 1)
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} 0).shiftMap
            (((RV ⋙ DerivedCategory.Plus.ι).commShiftIso (1 : ℤ)).hom.app X)
            n (n + 1) (by omega) b) =
        ψ (X⟦(1 : ℤ)⟧) n b ≫
          (((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).hom.app X)⟦n⟧' ≫
          (shiftFunctorAdd' (DerivedCategory C) 1 n (n + 1) (by omega)).inv.app X.obj := by
  sorry

end CategoryTheory.Functor
