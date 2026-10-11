/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule
public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Quasi-coherence of derived Hom from a finite pushforward algebra

Source: Stacks Project, Duality for Schemes, Tag 0AX2, with Tags 0AUC, 0AUP and 0A6H
(blueprint: lem-sc-finite-pushforward-derived-hom-qcoherent).
-/

@[expose] public section

universe u w wB

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- For a finite morphism of Noetherian schemes, `B = f_* 𝒪_X` is pseudo-coherent.
Derived internal Hom from `B` sends bounded-below quasi-coherent complexes to
bounded-below quasi-coherent complexes of `B`-modules. Forgetting the algebra action
still gives a bounded-below quasi-coherent complex on `Y`. The equality identifying `B`
includes its algebra structure, namely the structure map `f.c`, not just its module.

Source: Stacks Project, Duality for Schemes, Tag 0AX2, with Tags 0AUC, 0AUP and 0A6H
(blueprint: lem-sc-finite-pushforward-derived-hom-qcoherent).

Proof:
1. Finite pushforward of the structure sheaf is coherent and quasi-coherent on the
   Noetherian target (`lem-weil-pbc-finite-pushforward-coherent`). Coherent modules on a
   Noetherian scheme are pseudo-coherent (`lem-sc-coherent-pseudo-coherent`), using
   `def-pur-pseudo-coherent-complex` for the degree-zero complex of `B`.
2. Apply `lem-sc-pseudo-coherent-rhom-qcoherent` to `B` and `K`. The functor
   `derivedRHomAlgebraModule` (`def-pc-derived-rhom-algebra-module`) supplies the natural
   algebra action; `sheafAlgebraDerivedQCohProperty`
   (`def-pc-derived-category-qcoh-algebra`) expresses the asserted membership in
   `D⁺_QCoh(B)`. Local boundedness becomes global using a finite affine cover of `Y`.
3. Restriction of scalars is exact and leaves underlying cohomology sheaves unchanged.
   By `def-pc-derived-category-qcoh-algebra`, quasi-coherent `B`-modules have
   quasi-coherent underlying `𝒪_Y`-modules. The same lower bound therefore applies after
   forgetting the action. `derivedRHomAlgebraModule_underlying` identifies this forgotten
   object with `derivedInternalHom` (`def-pur-derived-internal-hom`). -/
theorem finite_pushforward_derivedHom_qcoherent {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [IsNoetherian X] [IsNoetherian Y]
    (B : Y.CommAlgebraSheaf)
    (hBf : B = Under.mk (⟨f.c⟩ : Y.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [HasDerivedCategory.{wB} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj
        B.right))]
    (K : schemeDerivedQCohCategory Y) (hK : ∃ n : ℤ, K.obj.IsGE n) :
    ∃ hB : B.toModule.IsQuasicoherent,
      Scheme.IsPseudoCoherent Y
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj B.toModule) ∧
      sheafAlgebraDerivedQCohProperty Y B hB
        ((derivedRHomAlgebraModule Y B hB).obj K.obj) ∧
      schemeDerivedQCohProperty Y
        ((SheafOfModules.restrictScalars.{u}
          ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).map
            B.hom)).mapDerivedCategory.obj
              ((derivedRHomAlgebraModule Y B hB).obj K.obj)) ∧
      ∃ n : ℤ,
        ((SheafOfModules.restrictScalars.{u}
          ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).map
            B.hom)).mapDerivedCategory.obj
              ((derivedRHomAlgebraModule Y B hB).obj K.obj)).IsGE n := by
  sorry

end AlgebraicGeometry
