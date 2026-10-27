/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.CategoryTheory.CochainUniversalCounitTransport
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent

/-! # A cochain presentation of independent-universe derived ringed pullback

This interface keeps the semilinear construction's instances private. In particular,
`import all` of an immediate consumer does not expose those implementation instances.
Source: Stacks Tag 06YY and the homotopy-to-cochain universal counit transport.
(blueprint: lem-pur-ringed-pullback-cochain-presentation)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe uC vC uD vD r w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {R : Sheaf JC CommRingCat.{r}} {S RI : Sheaf JD CommRingCat.{r}}

/-- The cochain counit for derived ringed pullback is universal and invertible on
flat-term K-flat representatives, with site and coefficient universes independent.

Source: Stacks Tag 06YY, via the independent-universe ringed derived pullback theorem,
and the universal cochain counit transport.
(blueprint: lem-pur-ringed-pullback-cochain-presentation)

Proof: apply the ringed derived pullback theorem to the specified algebraic inverse
image and scalar-extension presentation. Its universal homotopy counit is invertible
on the flat-term K-flat resolving class. Transport universality along the homotopy
quotient and its comparison with cochain localization. The componentwise transport
criterion preserves invertibility on precisely the same representatives. -/
theorem ringedPullbackCochainPresentation
    (uInv : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
    (uPush : Sheaf JD (Type r) ⥤ Sheaf JC (Type r))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{r} ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    (hobj : ∀ M : SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
      (a : M ⟶ N), uStar.map a =
        eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
          eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{r}
          ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))] :
    ∃ (F : DerivedCategory (SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
        DerivedCategory (SheafOfModules.{r}
          ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
      (ε : DerivedCategory.Q (C := SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⋙ F ⟶
        uStar.mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q (C := SheafOfModules.{r}
          ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))),
      F.IsRightKanExtension ε ∧
        ∀ P : CochainComplex (SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ,
          P.IsKFlatIndependentCoefficients →
          (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
          IsIso (ε.app P) := by
  obtain ⟨F, ε, hF, _, _, hε, _⟩ :=
    ringedTopoiDerivedPullbackIndependent uInv uPush adj I c uStar hobj hmap
  let := hF
  let := Functor.IsLeftDerivedFunctor.isRightKanExtension F ε
    (HomotopyCategory.quasiIso
      (SheafOfModules.{r} ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ))
  obtain ⟨hkan, hiso⟩ := cochainUniversalCounitTransport uStar F ε
  refine ⟨F, derivedCochainCounit uStar F ε, hkan, ?_⟩
  intro P hp hf
  exact (hiso P).2 (hε P hp hf)

end SheafOfModules
