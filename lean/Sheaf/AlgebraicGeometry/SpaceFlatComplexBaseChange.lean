/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange
public import Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexTensorInheritance

/-! # Arbitrary base change for relatively flat complexes on algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tag 0A1K (lemma-base-change-tensor),
including the precise arrow in the proof
(blueprint: lem-sfb-space-flat-complex-base-change).

The exchange is the adjoint of the pulled counit. The coefficient comparison uses
ordinary termwise pullback of the bounded-above relatively flat complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
  [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
  [HasDerivedCategory.{w} X'.SmallModules] [HasDerivedCategory.{w} Y'.SmallModules]

/-- Exchange followed by derived tensor pullback and the ordinary-coefficient comparison.
The comparison on G is the counit of the total left derived tensor pullback, so no
invertibility of that coefficient comparison is built into the definition.
Source: Stacks, Tag 0A1K (blueprint: lem-sfb-space-flat-complex-base-change). -/
def moduleRelativelyFlatBaseChangeMap
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (h : X' ⟶ X)
    (w : h ≫ f = f' ≫ g) (E : X.DerivedModules) (G : CochainComplex X.Modules ℤ) :
    (derivedTensorPullback g).obj ((derivedDirectImage f).obj
        (X.derivedDualityModel.closed.tensor.obj
          (E, DerivedCategory.Q.obj ((smallModuleComplex X).obj G)))) ⟶
      (derivedDirectImage f').obj (X'.derivedDualityModel.closed.tensor.obj
        ((derivedTensorPullback h).obj E,
          DerivedCategory.Q.obj ((smallOrdinaryPullbackComplex h).obj G))) :=
  moduleDerivedExchange f f' g h w
      (X.derivedDualityModel.closed.tensor.obj
        (E, DerivedCategory.Q.obj ((smallModuleComplex X).obj G))) ≫
    (derivedDirectImage f').map
      ((moduleDerivedPullbackTensor h).hom.app
          (E, DerivedCategory.Q.obj ((smallModuleComplex X).obj G)) ≫
        X'.derivedDualityModel.closed.tensor.map
          (Prod.mkHom (𝟙 ((derivedTensorPullback h).obj E))
            (moduleOriginalPullbackCounit h G)))

/-- Arbitrary base change for tensor with a bounded-above relatively flat complex.
Source: Stacks, spaces-perfect.tex, Tag 0A1K, statement and precise arrow in its proof
(blueprint: lem-sfb-space-flat-complex-base-change).

Proof, following the four steps of the recorded DAG:
1. Quasi-coherent kernels and cokernels make the cohomology of G quasi-coherent.
   Ordinary module pullback preserves quasi-coherence termwise. Derived pullback
   and derived tensor preserve quasi-coherent cohomology. Thus both coefficient
   objects belong to D_QCoh (lem-sfb-space-qcoh-kernels-colimits,
   lem-sfb-space-module-pullback-quasicoherent,
   lem-sfb-space-derived-qcoh-pullback-tensor).
2. At a geometric stalk use the rings R, A, B and C of
   lem-sfb-space-geometric-stalk-tensor-calculus. The stalk complex M of G is
   bounded above and R-flat termwise, hence K-flat over R by
   lem-pc-module-bounded-flat-kflat. Write D = A tensor_R B. Flatness of D to C
   identifies H^i(M tensor_R B) tensor_D C with the cohomology after tensoring
   with C. The chain isomorphism to M tensor_A C sends (m tensor b) tensor c
   to m tensor bc; its inverse inserts one. This is exactly the stalk map
   for the derived-to-ordinary coefficient counit. It is invertible; the
   coefficient counit itself need not be invertible.
3. Apply lem-sfb-space-single-complex-tensor-inheritance to this coefficient
   map and arbitrary E in D_QCoh. Step 2 checks its stalk condition, giving
   the same condition after tensoring with E, without a bound on E.
4. Apply lem-sfb-space-single-complex-base-change to the resulting pair.
   Step 1 supplies quasi-coherence and step 3 its stalk condition. The qcqs
   hypothesis supplies the remaining input. Its exchange is the adjoint of
   the same pulled counit; the coefficient map is derived tensor pullback
   followed by identity tensor the coefficient counit. Their composite is
   precisely moduleRelativelyFlatBaseChangeMap, proving its invertibility. -/
theorem moduleRelativelyFlatBaseChange_isIso
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (h : X' ⟶ X)
    (sq : IsPullback h f' f g)
    (hqc : MapIsQuasiCompact f.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (E : X.DerivedModules) (hE : X.derivedQCohProperty E)
    (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (G.X i))
    (hGqc : ∀ i : ℤ, SheafOfModules.IsQuasicoherent (G.X i))
    (hGflat : ∀ i : ℤ, ModuleIsFlatOver f (G.X i)) :
    IsIso (moduleRelativelyFlatBaseChangeMap f f' g h sq.w E G) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
