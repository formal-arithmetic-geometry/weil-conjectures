/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictEtaleSystemInterfaces
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.StrictEtaleEvaluationExistence
import WeilConjectures.AlgebraicGeometry.EtaleBrownLevelRealization
import WeilConjectures.AlgebraicGeometry.EtaleBrownImageRealization
import WeilConjectures.AlgebraicGeometry.ProperDerivedDirectImageCoproducts

/-! # Proper coproducts in the constant ring-sheaf coefficient presentation

Source: Stacks 0F0D; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- The proper finite-coefficient coproduct theorem is unchanged by the normalized
ringed-site presentation of a quotient coefficient level and the chosen derived models.
Source: Stacks 0F0D; Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-proper-coproducts).

Proof: construct strict derived evaluation packages at V and T for the arbitrary
parameter t (strictEtaleEvaluation_exists) and their normalized Brown level
realizations; the derived level functors of these realizations are equivalences.
The normalized Brown image realization of A and D gives a natural isomorphism between
D.direct followed by the target level equivalence and the source level equivalence
followed by the usual total right derived direct image along g. The quotient ring is
finite, so proper_rightDerivedLowerStar_preservesCoproducts shows that this derived
direct image preserves coproducts indexed by I; so does the composite with the source
equivalence. Transport along the natural isomorphism, then reflect through the target
equivalence. This includes the empty coproduct. -/
theorem etaleCoefficientProper_coproducts
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V T : Scheme.{u}} (g : V ⟶ T) [IsProper g]
    [IsLocallyNoetherian V] [CompactSpace V]
    [IsLocallyNoetherian T] [CompactSpace T]
    (A : StrictEtaleOrdinaryImage O t g) (n : ℕ)
    [Finite (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1))]
    (D : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) D.direct := by
  obtain ⟨PV⟩ := strictEtaleEvaluation_exists V O t
  obtain ⟨PT⟩ := strictEtaleEvaluation_exists T O t
  obtain ⟨RV⟩ := etaleBrownLevelRealization_exists O t V PV
  obtain ⟨RT⟩ := etaleBrownLevelRealization_exists O t T PT
  obtain ⟨e⟩ := etaleBrownImageRealization_exists O t g n A D RV RT
  have : (RV.derived n).IsEquivalence := RV.val.equivalence n
  have : (RT.derived n).IsEquivalence := RT.val.equivalence n
  have : PreservesColimitsOfShape (Discrete I)
      ((Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        g).rightDerivedFunctor) :=
    (Etale.proper_rightDerivedLowerStar_preservesCoproducts
      (strictEtaleBrownRing O t n) g).1 I
  have : PreservesColimitsOfShape (Discrete I)
      (RV.derived n ⋙ (Etale.lowerStar
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).rightDerivedFunctor) :=
    inferInstance
  have : PreservesColimitsOfShape (Discrete I) (D.direct ⋙ RT.derived n) :=
    preservesColimitsOfShape_of_natIso e.right.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves D.direct (RT.derived n)

end AlgebraicGeometry
