/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import Sheaf.Paper.ModuleObjects
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints
import Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion
import Sheaf.CategoryTheory.SheafTensor

/-!
# Pullback transport preserves K-flat module complexes

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-prop-sfb-module-derived-factorization/lem-sfb-module-mapmod-pullback-kflat.md`,
node lem-sfb-module-mapmod-pullback-kflat (blueprint: lem-sfb-module-mapmod-pullback-kflat).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open CategoryTheory.MonObj
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale

@[expose] public section

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-prop-sfb-module-derived-factorization/lem-sfb-module-mapmod-pullback-kflat.md`,
node lem-sfb-module-mapmod-pullback-kflat (blueprint: lem-sfb-module-mapmod-pullback-kflat).
For a K-flat complex of modules over the coefficient ring on `Y`, transport along
strong monoidal abelian-sheaf pullback is K-flat over the pulled-back ring on `X`.

Proof of the node:
1. Put `R = Λ_Y` and `S = f^* R`. By `sk-def-sfb-sheaf-tensor` and
   `lem-pe-internal-section-tensor-comparison`, the equivalences `E_R` and `E_S`
   identify internal and sectionwise module tensors and their direct-sum total
   complexes, and preserve and reflect K-flatness. Thus `E_R P` is K-flat.
2. Use `def-weil-proetale-inverse-image` for the geometric inverse image `u⁻¹`
   and `def-sfb-finite-upper-star-monoidal` for its tensor comparison. The action
   formula of `sk-def-sfb-transport` identifies `E_S (mapMod(f^*) P)` with
   `u⁻¹ (E_R P)`: on pure tensors the action is the inverse image of the original
   bilinear action. Units, products, underlying sheaves, maps and differentials
   agree, so this identifies the full termwise complexes over `S_sec = u⁻¹ R_sec`.
3. For any topos point `p` on `X`, form `q = u ∘ p` using
   `def-trf-geometric-morphism`. The forward implication of
   `lem-sfb-ringed-site-kflat-stalk-criterion` makes `(E_R P)_q` K-flat.
   The identification in step 2 gives the same stalk complex and the same stalk
   ring at `p`, since both actions and differentials are obtained by `p⁻¹ u⁻¹`.
4. Choose the conservative family of `lem-sfb-proetale-enough-points` on `X`.
   Step 3 and the converse of `lem-sfb-ringed-site-kflat-stalk-criterion` make
   `E_S (mapMod(f^*) P)` K-flat. Reflect through `E_S` by
   `lem-pe-internal-section-tensor-comparison`. This tests every acyclic module
   complex on `X`, without flat-term or boundedness assumptions.

Here upstream `kFlat` is preservation of quasi-isomorphisms by both total-tensor
functors, as in `CochainComplex.kFlat_iff_preservesQuasiIso`; its binary tensor
maps are `HomologicalComplex.tensorHom`, the same test used by the recorded
`CochainComplex.IsKFlatForTotalTensor`.
-/
theorem preservesKFlatComplexes_mapMod_upperStar_statement :
    ∀ {P : CochainComplex
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ},
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
          ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomologicalComplex
            (.up ℤ)).obj P) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

end
