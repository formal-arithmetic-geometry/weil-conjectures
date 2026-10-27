/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleBrownProjectionRealization

/-! # The normalized proper Brown scalar transport square

Source: Zheng, Constructions 4.1 and 5.14--5.15 and Lemma 5.16;
Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- The normalized realization square for a chosen proper scalar projection.
Source: Zheng, Lemma 5.16; Stacks 03CY, 06YY and 07A4.
(blueprint: lem-pur-etale-brown-proper-scalar-square).

The proof is the mate-pasting calculation on cochain representatives. The
ordinary restriction comparison is sectionwise the identity, its derived square
is fixed by localization, and the scalar unit equation identifies the two
transposes. -/
theorem etaleBrownProperScalarSquare
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) [IsProper g]
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    {m n : ℕ} (h : m ≤ n) [Finite (strictEtaleBrownRing O t n)]
    (p : (PV.scalar h).derived ⋙ (B.level m).direct ≅
      (B.level n).direct ⋙ (PW.scalar h).derived)
    (hp : p.inv = (mateEquiv (B.level n).adjunction (B.level m).adjunction
      (.mk _ _ _ _ (B.derivedTensor h).hom)).natTrans) :
    ∀ P : DerivedCategory (strictEtaleLevel V O t n),
      (RW.derived m).map (p.inv.app P) ≫
          (rg m).right.hom.app ((PV.scalar h).derived.obj P) ≫
          (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))
            g).rightDerivedFunctor.map ((RV.scalar h).hom.app P) =
        (RW.scalar h).hom.app ((B.level n).direct.obj P) ≫
          (Etale.scalarExtension (strictEtaleBrownRingMap O t h) W).map
            ((rg n).right.hom.app P) ≫
          (Etale.scalarMate (strictEtaleBrownRingMap O t h) g).app
            ((RV.derived n).obj P) := by
  sorry

end AlgebraicGeometry
