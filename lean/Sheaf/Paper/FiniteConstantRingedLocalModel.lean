module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleOperations

/-!
# Finite constant models in the ringed-site presentation

Source: blueprint latest, sec-proetale-coefficients/sk-def-sfb-constructible,
clause (1): scalar extensions of finitely presented modules on pro-etale charts
(blueprint: sk-def-sfb-constructible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- The ringed-site formulation of a finite constant scalar local model. The finite
presentation is over the scalar ring, before extension to the coefficient sheaf;
its matrix cannot have arbitrary coefficient-sheaf sections as entries.
Source: blueprint latest, sk-def-sfb-constructible, clause (1)
(blueprint: sk-def-sfb-constructible). -/
def HasFiniteConstantRingedLocalModel (X : Scheme.{u}) (A : Type u) [CommRing A]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : proEtaleConstantRing X A ⟶ R) (F : proEtaleRingModules X R) : Prop :=
  ∃ S : Sieve (⊤_ X.ProEt), S ∈ ProEt.topology X (⊤_ X.ProEt) ∧
    ∀ (V : X.ProEt) (f : V ⟶ ⊤_ X.ProEt), S f →
      ∃ N : ModuleCat.{u + 1} (ULift.{u + 1} A),
        Module.FinitePresentation (ULift.{u + 1} A) N ∧
        Nonempty ((SheafOfModules.overFunctor _ V).obj F ≅
          (SheafOfModules.overFunctor _ V).obj
            (SheafOfModules.changeOfRings.{u, u + 1, u + 1} a
              (proEtaleConstantModuleSheaf X A N)))

end AlgebraicGeometry.ProEtale
