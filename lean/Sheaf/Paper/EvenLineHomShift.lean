/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
public import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Even line twists and the signed source shift of internal Hom

Source: Stacks Project, Cohomology on Sites, Sections 0A8X and 08J7, Tag 08JC;
Weil blueprint main-20261015, thm-sf-dual-perfect, proof Step 4
(blueprint: lem-sf-even-line-hom-shift).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.SignedRingedHom

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{u} (Modules J R)]

/-- The coefficient evaluation transpose a_(K,B), including the canonical
associativity, Koszul braiding and unit constraints. Its definition uses the
unique representative-normalized adjunction, so no comparison map is an input.
Source: blueprint thm-sf-dual-perfect, proof Step 4; Stacks 08J9
(blueprint: lem-sf-even-line-hom-shift). -/
noncomputable def lineComparison (K B : D J R) :
    ((hom J R K).obj (𝟙_ (D J R))) ⊗ B ⟶ (hom J R K).obj B :=
  (adjunction J R K).homEquiv _ B
    ((α_ ((hom J R K).obj (𝟙_ (D J R))) B K).hom ≫
      ((hom J R K).obj (𝟙_ (D J R))) ◁ (β_ B K).hom ≫
      (α_ ((hom J R K).obj (𝟙_ (D J R))) K B).inv ≫
      ((adjunction J R K).counit.app (𝟙_ (D J R))) ▷ B ≫ (λ_ B).hom)

/-- The canonical line comparison commutes with the signed first-variable Hom
shift when the line shift r is even. The coefficient unit is R in degree zero;
the sheaf T is inserted by the ordinary degree-zero functor. There is no
boundedness or perfectness assumption on K.

Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08J7, Tag 08JC;
blueprint main-20261015, thm-sf-dual-perfect, proof Step 4 (agent expansion)
(blueprint: lem-sf-even-line-hom-shift).

Proof:
1. Use def-pc-kflat-complex and lem-pc-kflat-resolution to choose K-flat tensor
   representatives, and def-pur-derived-internal-hom to choose a K-injective
   Hom target. The tensor differential is d_F tensor 1 + (-1)^p 1 tensor d_G,
   and the Hom differential is d_B f - (-1)^n f d_A. The normalized adjunction
   represents lineComparison by the ordinary evaluation transpose.
2. The mate defining sourceShift reindexes j=i+s in the product Hom complex.
   In Hom degree n its coefficient is (-1)^(s*n), up to a sign depending only
   on s. Substitution in the Hom differential proves the chain-map identity;
   reindexing backwards gives its inverse. This also proves target naturality.
3. On a homogeneous tensor f tensor t the two paths use the same evaluation
   and totalization signs. The remaining ratio is (-1)^(s*r), which is 1
   since r is even. The tensor shift inserted on the right is the ordinary
   first-factor total-tensor shift. Hence the two chain maps agree. Multiplying
   both sourceShift components by the same shift-only sign changes both paths
   by that sign and preserves the equation.
4. The representative-normalized adjunction, Hom localization and natural
   tensor shift comparisons descend this equality to D(R), independently of
   the resolutions. This works for arbitrary K and every integer s. -/
theorem even_line_hom_shift
    (T : Modules J R)
    (hT : ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        Nonempty ((SheafOfModules.overFunctor
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) V).obj T ≅
          SheafOfModules.unit
            (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V)))
    (r s : ℤ) (hr : Even r) (K : D J R) :
    lineComparison J R (K⟦s⟧)
        (((DerivedCategory.singleFunctor (Modules J R) 0).obj T)⟦r⟧) ≫
      (sourceShift J R K s).hom.app
        (((DerivedCategory.singleFunctor (Modules J R) 0).obj T)⟦r⟧) =
    ((sourceShift J R K s).hom.app (𝟙_ (D J R))) ▷
        (((DerivedCategory.singleFunctor (Modules J R) 0).obj T)⟦r⟧) ≫
      (((curriedTensor (D J R)).flip.obj
        (((DerivedCategory.singleFunctor (Modules J R) 0).obj T)⟦r⟧)).commShiftIso
          (-s)).hom.app ((hom J R K).obj (𝟙_ (D J R))) ≫
      (lineComparison J R K
        (((DerivedCategory.singleFunctor (Modules J R) 0).obj T)⟦r⟧))⟦-s⟧' := by
  sorry

/-- The same square for every shift-only sign normalization, encoded by a unit
ε of the integers (hence either +1 or -1). The same ε is used for both targets.
Source: blueprint thm-sf-dual-perfect, proof Step 4, signed comparison expansion
(blueprint: lem-sf-even-line-hom-shift).
Proof: apply even_line_hom_shift. Tensoring and composition are additive, so
multiplying each of its two sourceShift components by ε multiplies both paths
by ε. The ordinary first-factor shift comparison and the evaluation transpose
are unchanged. This proves invariance under every coherent shift-only sign. -/
theorem even_line_hom_shift_normalization
    (T : Modules J R)
    (hT : ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        Nonempty ((SheafOfModules.overFunctor
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) V).obj T ≅
          SheafOfModules.unit
            (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V)))
    (r s : ℤ) (hr : Even r) (K : D J R) (ε : ℤˣ) :
    lineComparison J R (K⟦s⟧)
        (((DerivedCategory.singleFunctor (Modules J R) 0).obj T)⟦r⟧) ≫
      (ε • (sourceShift J R K s).hom.app
        (((DerivedCategory.singleFunctor (Modules J R) 0).obj T)⟦r⟧)) =
    (ε • (sourceShift J R K s).hom.app (𝟙_ (D J R))) ▷
        (((DerivedCategory.singleFunctor (Modules J R) 0).obj T)⟦r⟧) ≫
      (((curriedTensor (D J R)).flip.obj
        (((DerivedCategory.singleFunctor (Modules J R) 0).obj T)⟦r⟧)).commShiftIso
          (-s)).hom.app ((hom J R K).obj (𝟙_ (D J R))) ≫
      (lineComparison J R K
        (((DerivedCategory.singleFunctor (Modules J R) 0).obj T)⟦r⟧))⟦-s⟧' := by
  sorry

end CategoryTheory.SignedRingedHom
