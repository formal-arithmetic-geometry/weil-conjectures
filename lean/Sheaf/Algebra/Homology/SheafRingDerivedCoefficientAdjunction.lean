/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Paper.PbcCompletedPullbackActual

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
/-!
# The normalized derived coefficient adjunction on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 07A6; Derived Categories,
Tags 0FND and 09T5; Modules on Sites, Tags 03D7 and 03DA
(blueprint: lem-pur-sheaf-ring-derived-coefficient-adjunction).

The left derived pair is the pair supplied by derived change of rings. We quantify over
its presentation rather than choosing a second derived functor. The localization used below
is `Qh`, so the comparison is literally its universal counit. A complex is inserted by the
homotopy quotient. The ordinary adjunction is fixed by its sectionwise tensor formula;
its termwise adjunction therefore names exactly the maps in the normalization clauses.
-/

@[expose] public section

set_option autoImplicit false

universe w r u v

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {O O' : Sheaf J CommRingCat.{r}}

/-- Restriction is exact and derived change of rings is its left adjoint, normalized by
`x ↦ x ⊗ 1` and `x ⊗ a ↦ a g(x)`. The tensor convention in the existing change-of-rings
construction writes the scalar first, so these are `1 ⊗ x` and `a ⊗ x` in Lean.

`E`, `h`, and the map equation specify precisely the ordinary change-of-rings functor
of `derivedChangeOfRingsIndependentCoefficients`; they impose no flatness assumption.
`LF` and `ε` specify its universal left derived pair, with the same homotopy localization.
The isomorphism assertion supplies `c_P`; the unit equation is written after applying
restriction to `c_P`. The inverse Hom equivalence is the transpose clause. The last
identity is the counit formula whenever the localized `g` is invertible, equivalently
when `g` is a quasi-isomorphism. Quantifying over homotopy maps includes every chain map.

Source: Stacks Project, Tags 07A6, 0FND, 09T5, 03D7 and 03DA
(blueprint: lem-pur-sheaf-ring-derived-coefficient-adjunction).

Proof:
1. The ringed-topos module adjunction on the identity topos gives the ordinary adjunction.
Its balanced sectionwise formulas descend through module sheafification; its unit sends
`x` to `1 ⊗ x`, and its inverse Hom map sends `a ⊗ x` to `a g(x)`.
2. Restriction preserves underlying abelian sheaves. Kernels are sectionwise and cokernels
are sheafified sectionwise cokernels, so it preserves finite limits and finite colimits.
3. Exact-functor derived factorization identifies its derived functor with termwise
restriction. Derived change of rings and flat-term K-flat resolutions supply the universal
left derived pair and its invertible comparison on K-flat representatives.
4. Apply the derived-adjoint-functors theorem to the ordinary pair, obtaining the natural
Hom bijections for these derived functors.
5. In the pre-derived fraction formula use identity denominators and the ordinary unit at
`P`. The right comparison is the exact-functor factorization and the left comparison is
`ε_P`. The termwise adjunct is the identity, giving the displayed unit normalization.
6. Use the same fraction formula with `g` to get the transpose identity. Naturality gives
`LF(q)` followed by the derived counit equal to `ε_P` followed by the localized termwise
transpose. If `g` is a quasi-isomorphism, invert `LF(q)` to obtain the counit formula.
No boundedness or flatness of the ring map occurs in these steps. -/
theorem sheafRingDerivedCoefficientAdjunction (φ : O ⟶ O')
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))] :
    ∃ (_ : PreservesFiniteLimits (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)))
      (_ : PreservesFiniteColimits (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ))),
    ∀ (E : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤
        SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))
      (h : ∀ M, E.obj M = changeOfRings φ M),
      (∀ {M N} (f : M ⟶ N), E.map f =
        eqToHom (h M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h N).symm) →
      ∀ [E.Additive], ∃ a : E ⊣ restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ),
        (∀ (M : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))
          (N : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))
          (f : changeOfRings φ M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U),
          (a.homEquiv M N (eqToHom (h M) ≫ f)).val.app U x =
            f.val.app U
              ((CategoryTheory.toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
                ((1 : O'.obj.obj U) ⊗ₜ[O.obj.obj U, (φ.hom.app U).hom] x))) ∧
        ∀ (LF : DerivedCategory (SheafOfModules.{r}
            (derivedChangeRingIndependentCoefficients J O)) ⥤
            DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O')))
          (ε : DerivedCategory.Qh ⋙ LF ⟶
            E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
          LF.IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso (SheafOfModules.{r}
              (derivedChangeRingIndependentCoefficients J O)) (ComplexShape.up ℤ)) →
          ∃ d : LF ⊣ (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategory,
            ∀ (P : CochainComplex (SheafOfModules.{r}
                (derivedChangeRingIndependentCoefficients J O)) ℤ),
              CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := O) P →
              (∀ i : ℤ, IsFlatOnSite (R := O) (P.X i)) →
              IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) ∧
              (d.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
                  (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategory.map
                    (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
                  (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategoryFactorsh.hom.app
                    ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj
                      ((HomotopyCategory.quotient _ _).obj P)) =
                DerivedCategory.Qh.map
                  ((a.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
                    ((HomotopyCategory.quotient _ _).obj P))) ∧
              ∀ (H : HomotopyCategory (SheafOfModules.{r}
                  (derivedChangeRingIndependentCoefficients J O')) (ComplexShape.up ℤ))
                (g : (HomotopyCategory.quotient _ _).obj P ⟶
                  ((restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapHomotopyCategory (ComplexShape.up ℤ)).obj H),
                (d.homEquiv _ _).symm
                    (DerivedCategory.Qh.map g ≫
                      (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategoryFactorsh.inv.app H) =
                  ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
                    DerivedCategory.Qh.map
                      (((a.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv _ _).symm g) ∧
                ∀ [IsIso (DerivedCategory.Qh.map g)],
                  d.counit.app (DerivedCategory.Qh.obj H) =
                    inv (LF.map (DerivedCategory.Qh.map g ≫
                      (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategoryFactorsh.inv.app H)) ≫
                    ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
                    DerivedCategory.Qh.map
                      (((a.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv _ _).symm g) := by
  sorry

end SheafOfModules
