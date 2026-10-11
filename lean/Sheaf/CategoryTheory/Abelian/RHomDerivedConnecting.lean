/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.KInjectiveBridge
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Derived Hom and connecting morphisms

Source: Stacks Project, Derived Categories, Tags 06XR (part 1), 070I and 05TE
(blueprint: lem-sc-p1-rhom-hom-derived-connecting).
-/

@[expose] public section

universe w w₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

/-- Cohomology of derived `Hom(M,-)` is naturally derived-category Hom, with the cocycle
roof formula for every bounded below injective resolution, compatibly with boundaries.
Source: Stacks Project, Tags 06XR (part 1), 070I and 05TE
(blueprint: lem-sc-p1-rhom-hom-derived-connecting).

Proof, Step 1: a cocycle `f : M ⟶ I.X n` is a map `M[0] ⟶ I[n]`; boundaries are exactly
null-homotopic maps. A bounded below injective complex is K-injective by
`lem-weil-pbc-bounded-below-injectives-kinjective`. Thus
`lem-weil-pbc-kinjective-hom-derived` identifies its homotopy Hom with derived Hom.
Compose with the inverse of the resolution quasi-isomorphism to obtain the roof formula.
Step 2: K-injectivity makes lifts of derived morphisms unique up to homotopy. Applying
`Hom(M,-)` to such lifts gives naturality, and applying this to the identity with two
resolutions gives independence of the choice (`def-sp-kinjective-bridge`).
Step 3: the right derived functor is triangulated
(`lem-weil-pbc-derived-direct-image-triangulated`). Its connecting morphism is shifted
cohomology of the third triangle map (`lem-sf-derived-homology-long-exact`). Naturality
for that third map, together with the unsigned shift of cocycles, identifies this with
postcomposition by the shifted boundary (`lem-sp-long-exact-of-triangle`).
The explicit shift comparisons below retain the cone convention and introduce no extra sign.
The resolution formula quantifies over every choice, so its left side uses the single
choice-independent total derived functor, rather than a separately chosen comparison. -/
theorem exists_rhom_hom_derived_connecting
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w₂} AddCommGrpCat.{v}] (M : C) :
    let V := preadditiveCoyoneda.obj (op M)
    let RV := V.rightDerivedFunctorPlus
    let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
    let S := (DerivedCategory.singleFunctor C 0).obj M
    let Φ := preadditiveCoyoneda.obj (op S)
    letI := Functor.ShiftSequence.tautological Φ ℤ
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
            ((DerivedCategory.quotientCompQhIso C).hom.app K.obj)⟦n⟧') ∧
      (∀ (T : Triangle (DerivedCategory.Plus C)) (_hT : T ∈ distTriang _) (n : ℤ)
          (a : (H n).obj (RV.obj T.obj₃)),
        ψ T.obj₁ (n + 1)
            (DerivedCategory.HomologySequence.δ
              ((RV ⋙ DerivedCategory.Plus.ι).mapTriangle.obj T) n (n + 1) rfl a) =
          Φ.homologySequenceδ ((DerivedCategory.Plus.ι (C := C)).mapTriangle.obj T)
            n (n + 1) rfl (ψ T.obj₃ n a)) := by
  sorry

end CategoryTheory.Functor
