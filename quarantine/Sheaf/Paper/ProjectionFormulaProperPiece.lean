/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.Paper.ProEtaleProjectionFormulaArrows
import Sheaf.Paper.ProjectionFormulaTotalization
import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses

/-!
# The proper compactification piece of the perfect projection formula

Source: proper base change, lemma 1270
(blueprint: lemma-weil-pbc-projection-formula-proper-piece).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The projection mate for p and j_!E is invertible with precisely the specified
finite-total inverse. Both composites are stated, so the inverse is identified.
Source: proper base change, lemma 1270
(blueprint: lemma-weil-pbc-projection-formula-proper-piece).
Proof: use the chosen compactification d, with quasi-compact open d.i and proper d.g.
Put A = j_!E using exact extension by zero on the ringed pro-etale sites. The package
P gives degreewise retracts of finite free sheaves, and hb gives finite support.
Apply lemma-weil-pbc-projection-formula-totalization with h = p and its object E = A.
The two signed-total chain maps have inverse composites, and their localizations are
exactly the counit mate pi and the finite-total rho of definition 1264. Transport
through the canonical mixed-tensor and K-injective representative comparisons.
This gives both asserted identities with the displayed source and target. There is
no boundedness hypothesis on E and no comparison with condensed-module coefficients. -/
theorem proEtaleProjectionFormula_properPiece
    {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f) [QuasiCompact d.i]
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology d.Z) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (cp : (proEtaleSheafInverseImage d.g CommRingCat.{u + 1}).obj RY ≅ RZ)
    (cj : (proEtaleSheafInverseImage d.i CommRingCat.{u + 1}).obj RZ ≅ RX)
    (a : ProEtaleTensorModel Y RY) (b : ProEtaleTensorModel d.Z RZ)
    (E : DerivedCategory (proEtaleRingModules X RX))
    (K : CochainComplex (proEtaleRingModules d.Z RZ) ℤ) (hK : K.IsKInjective)
    (rep : (proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E ≅ DerivedCategory.Q.obj K)
    (F : CochainComplex (proEtaleRingModules Y RY) ℤ)
    (P : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY) F)
    (hb : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) :
    derivedProjectionFormulaMate (proEtaleRingDerivedPullback d.g RY RZ cp)
        (proEtaleRingDerivedDirectImage d.g RY RZ cp)
        (proEtaleRingDerivedAdjunction d.g RY RZ cp) a.tensor b.tensor
        (proEtaleCanonicalTensorComparison d.g RY RZ cp a b)
        ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) (DerivedCategory.Q.obj F) ≫
      proEtalePerfectProjectionInverse d.g RY RZ cp a b
        ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) K hK rep F P hb =
      𝟙 (a.tensor.obj ((proEtaleRingCompactSupportImage d RY RZ RX cp cj).obj E,
        DerivedCategory.Q.obj F)) ∧
    proEtalePerfectProjectionInverse d.g RY RZ cp a b
        ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) K hK rep F P hb ≫
      derivedProjectionFormulaMate (proEtaleRingDerivedPullback d.g RY RZ cp)
        (proEtaleRingDerivedDirectImage d.g RY RZ cp)
        (proEtaleRingDerivedAdjunction d.g RY RZ cp) a.tensor b.tensor
        (proEtaleCanonicalTensorComparison d.g RY RZ cp a b)
        ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) (DerivedCategory.Q.obj F) =
      𝟙 ((proEtaleRingDerivedDirectImage d.g RY RZ cp).obj
        (b.tensor.obj ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E,
          (proEtaleRingDerivedPullback d.g RY RZ cp).obj (DerivedCategory.Q.obj F)))) := sorry

end AlgebraicGeometry.Scheme
