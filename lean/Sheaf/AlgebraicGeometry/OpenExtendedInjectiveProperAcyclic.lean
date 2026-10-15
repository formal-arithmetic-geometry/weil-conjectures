/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.TorsionAssembly
import Sheaf.AlgebraicGeometry.GeometricStalkCohomology
import Sheaf.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange

/-!
# Acyclicity of open extensions in proper commutative squares

Source: Stacks Project, More on Etale Cohomology, Tag 0F7B,
`lemma-shriek-proper-and-open`, proof of case (b), specialized to open immersions.
(blueprint: lem-cbc-open-extended-injective-proper-acyclic)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- In a commutative square with open horizontal maps and proper vertical maps,
the extension by zero of an injective etale module sheaf is acyclic for the
right vertical direct image. No Cartesian hypothesis is required.

Source: Stacks Project, Tag 0F7B, proof of case (b), injective acyclicity claim.
(blueprint: lem-cbc-open-extended-injective-proper-acyclic)

Proof:
1. Put F = k_! J. Finiteness of the coefficient ring gives a positive integer
annihilating every module section. Thus the underlying abelian sheaf is torsion.
The module/abelian derived-direct-image comparison reduces vanishing to abelian sheaves
(lem-weil-pbc-module-abelian-derived-direct-image-comparison).
2. Form V = B ×_D C. The induced map t : A → V is open. The map s : V → C is proper
by proper base change, and s t = r is proper. Properness over a separated target makes
t proper, and a proper immersion is closed. Hence A is a clopen component of V
(def-pc-fibre-product, lem-weil-pbc-proper-base-change,
lem-weil-pbc-proper-over-separated, lem-weil-pbc-proper-immersion-closed).
3. Under the clopen product equivalence, t_! J corresponds naturally to (J, 0),
by the extension-by-zero adjunction, its stalk formulas, and geometric-stalk conservativity.
Retain the coefficient actions to obtain the module version of the equivalence.
A monomorphism is componentwise; extend its A-component using injectivity of J and use
the zero map on the other component. Thus t_! J is injective
(lem-weil-pbc-etale-sheaf-clopen-product, lem-weil-pbc-extension-by-zero-adjunction,
lem-weil-pbc-extension-by-zero-stalks, lemma-weil-pbc-geometric-stalk-conservative).
4. The single complex t_! J in degree zero is a bounded below complex of injectives.
It computes R s_* and stays concentrated in degree zero after applying s_*, so its
positive higher direct images vanish. The module/abelian comparison gives the same
abelian vanishing (lem-weil-pbc-right-derived-plus-injective).
5. Proper base change on the square defining V identifies the restriction to C of
R^q p_* F with R^q s_* t_! J. Extension-by-zero base change supplies the coefficient
identification. Step 4 therefore makes all geometric stalks over C zero
(lemma-weil-pbc-torsion-assembly,
sbc-prop-extension-by-zero-and-arbitrary-base-change, lem-kun-stalks-of-cohomology).
6. At a geometric point outside C, the base change of A is empty by commutativity.
The base change of F is consequently zero, by extension-by-zero base change and the
empty cover. Proper base change identifies the stalk of R^q p_* F with a higher
direct image of zero, hence zero by the zero injective complex
(lemma-weil-pbc-torsion-assembly, lem-weil-pbc-right-derived-plus-injective).
7. All geometric stalks vanish. Geometric-stalk conservativity gives zero for the
abelian higher direct image; the module/abelian comparison then gives zero for the
module higher direct image (lemma-weil-pbc-geometric-stalk-conservative,
lem-weil-pbc-module-abelian-derived-direct-image-comparison). -/
theorem isZero_higherDirectImage_openImmersionLowerShriek_injective
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
    (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (hcomm : k ≫ p = r ≫ i)
    (J : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J]
    (q : ℤ) (hq : 0 < q) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj J)))) := by
  sorry

end AlgebraicGeometry.Etale
