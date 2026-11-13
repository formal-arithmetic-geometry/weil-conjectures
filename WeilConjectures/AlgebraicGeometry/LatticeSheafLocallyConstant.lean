/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeSheafBasic
import WeilConjectures.AlgebraicGeometry.LatticeClassDescent
import WeilConjectures.AlgebraicGeometry.LatticeCosetLocalSurjectivity
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.NumberTheory.Padics.CoefficientExtension
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.Topology.ContinuousMap.Algebra
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Coset.Defs
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.CompactOpen
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples

/-!
# Local constancy of the sheaf of integral lattices

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 6.8.4(6).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The presheaf of integral lattice classes is a sheaf, locally the constant sheaf of
cosets `g GL_n(A)`, with the specified map `g ↦ (g A^n, α_g)`. -/
theorem integralLatticeSheaf_locallyConstant (X : Scheme.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    [L.IsFiniteLocallyFree] :
    ∃ (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
      (c : ∀ U : X.ProEt,
        IntegralLatticePair (integralLatticeCoefficientMap X l E) L U → F.obj.obj (op U)),
      IsLatticeClassPresentation (integralLatticeCoefficientMap X l E) L F c ∧
      ∀ (U : X.ProEt) (n : ℕ)
        (e : L.over U ≅ latticeFreeSheaf X
          (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) U n),
        ∃ k : (constantSheaf ((Scheme.ProEt.topology X).over U) (Type (u + 2))).obj
          (ULift.{u + 2} (integralMatrixCosets (latticeCoefficientIntegers l E) n)) ≅ F.over U,
          ∀ (g : Matrix.GeneralLinearGroup (Fin n)
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
            (P : IntegralLatticePair (integralLatticeCoefficientMap X l E) L U),
            k.hom.hom.app (op (Over.mk (𝟙 U)))
              (((toSheafify ((Scheme.ProEt.topology X).over U)
                ((Functor.const (Over U)ᵒᵖ).obj
                  (ULift.{u + 2} (integralMatrixCosets
                    (latticeCoefficientIntegers l E) n)))).app (op (Over.mk (𝟙 U))))
                (ULift.up (Quotient.mk _ g))) = c U P ↔
              ∀ T : (Over U)ᵒᵖ, Set.image (e.hom.val.app T) (P.image T) =
                matrixLatticeImage X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))
                  (latticeCoefficientIntegers l E) U n g T := by
  obtain ⟨F, c, hc⟩ := exists_latticeClassPresentation X l E L
  refine ⟨F, c, hc, ?_⟩
  intro U n e
  let K := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  let A := latticeCoefficientIntegers l E
  have hs := latticeCosetMap_locallySurjective X l E L F c hc U n e
  let := latticeCosetSheafMap_isIso X K A L F c hc U n e hs
  refine ⟨asIso (latticeCosetSheafMap X K A L F c hc U n e), ?_⟩
  intro g P
  exact latticeCosetSheafMap_normalization X K A L F c hc U n e g P

end AlgebraicGeometry.ProEtale
