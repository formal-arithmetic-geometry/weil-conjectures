/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback

/-!
# Derived pullback on ringed topoi

Source: Stacks Project, Cohomology on Sites, Tag 06YY, lemma-derived-base-change
(blueprint: lem-weil-pbc-ringed-topoi-derived-pullback).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- A morphism of ringed topoi admits an exact derived pullback computed on
K-flat complexes with flat terms.  The functor `uStar` is the module-sheaf
pullback `M ↦ S ⊗_{u⁻¹R} u⁻¹M` attached to the morphism of ringed topoi.
Source: Stacks Project, Tag 06YY (blueprint: lem-weil-pbc-ringed-topoi-derived-pullback).
The proof first makes termwise pullback an exact functor on homotopy categories.
It then proves that pullback preserves quasi-isomorphisms between K-flat
complexes with flat terms, using exactness of inverse image and change of rings.
The resolving-class left-derived-functor theorem gives `LF`, its canonical
transformation `epsilon`, and the isomorphism on every such complex.  Finally,
for a resolution `p`, define `alpha p` as the inverse of `LF.map (Q p)` followed
by `epsilon`. Naturality follows from the resolution square and naturality of
`epsilon`. For resolutions p, q of the same object put C(q,p) = alpha(p) inverse
followed by alpha(q); cancellation proves the identity and composition laws,
and a chain map a with a followed by q = p induces exactly C(q,p).
-/
theorem ringedTopoiDerivedPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))] :
    ∃ (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤
        DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
      (epsilon : DerivedCategory.Qh ⋙ LF ⟶
        uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor epsilon
        (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)) ∧
      (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
      (∀ {P Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ} (s : P ⟶ Q),
        P.IsKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        Q.IsKFlat → (∀ n : ℤ, (Q.X n).IsFlat) → QuasiIso s →
          QuasiIso ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) ∧
      (∀ (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ),
        P.IsKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
          IsIso (epsilon.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ∧
      ∃ (alpha : ∀ {A P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
        (p : P ⟶ A), P.IsKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
          QuasiIso p → (LF.obj (DerivedCategory.Q.obj A) ≅
            DerivedCategory.Q.obj
              ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))),
        (∀ {A P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ} (p : P ⟶ A)
          (hp : P.IsKFlat) (hf : ∀ n : ℤ, (P.X n).IsFlat) [hq : QuasiIso p],
          (alpha p hp hf hq).hom = inv (LF.map (DerivedCategory.Q.map p)) ≫
            epsilon.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ∧
        (∀ {A A' P P' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
          (p : P ⟶ A) (p' : P' ⟶ A') (a : P ⟶ P') (b : A ⟶ A')
          (hp : P.IsKFlat) (hf : ∀ n : ℤ, (P.X n).IsFlat) (hq : QuasiIso p)
          (hp' : P'.IsKFlat) (hf' : ∀ n : ℤ, (P'.X n).IsFlat) (hq' : QuasiIso p'),
          p ≫ b = a ≫ p' →
          LF.map (DerivedCategory.Q.map b) ≫ (alpha p' hp' hf' hq').hom =
            (alpha p hp hf hq).hom ≫ DerivedCategory.Q.map
              ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map a)) ∧
        (∀ {A P P' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
          (p : P ⟶ A) (p' : P' ⟶ A) (a : P ⟶ P')
          (hp : P.IsKFlat) (hf : ∀ n : ℤ, (P.X n).IsFlat) (hq : QuasiIso p)
          (hp' : P'.IsKFlat) (hf' : ∀ n : ℤ, (P'.X n).IsFlat) (hq' : QuasiIso p'),
          a ≫ p' = p →
          (alpha p hp hf hq).inv ≫ (alpha p' hp' hf' hq').hom =
            DerivedCategory.Q.map
              ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map a)) ∧
        (∀ {A P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ} (p : P ⟶ A)
          (hp : P.IsKFlat) (hf : ∀ n : ℤ, (P.X n).IsFlat) (hq : QuasiIso p),
          (alpha p hp hf hq).inv ≫ (alpha p hp hf hq).hom = 𝟙 _) ∧
        (∀ {A P P' P'' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
          (p : P ⟶ A) (p' : P' ⟶ A) (p'' : P'' ⟶ A)
          (hp : P.IsKFlat) (hf : ∀ n : ℤ, (P.X n).IsFlat) (hq : QuasiIso p)
          (hp' : P'.IsKFlat) (hf' : ∀ n : ℤ, (P'.X n).IsFlat) (hq' : QuasiIso p')
          (hp'' : P''.IsKFlat) (hf'' : ∀ n : ℤ, (P''.X n).IsFlat) (hq'' : QuasiIso p''),
          ((alpha p hp hf hq).inv ≫ (alpha p' hp' hf' hq').hom) ≫
              ((alpha p' hp' hf' hq').inv ≫ (alpha p'' hp'' hf'' hq'').hom) =
            (alpha p hp hf hq).inv ≫ (alpha p'' hp'' hf'' hq'').hom) := by
  sorry

end SheafOfModules
