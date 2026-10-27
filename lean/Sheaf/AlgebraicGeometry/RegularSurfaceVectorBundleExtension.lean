/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-!
# Vector bundles extend across codimension two on a regular surface

Source: Stacks Project, Divisors, Tags 0EBJ and 0B3N; the finite locally free form
used in Alper--Halpern-Leistner--Heinloth, Section 2, Claim 2
(blueprint: lem-sfb-regular-surface-vector-bundle-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction and actual direct image give inverse equivalences of the full categories
of finite locally free modules across a codimension-two complement on a regular surface.
The unit and counit are those of the canonical open restriction adjunction, and morphism
extension is expressed using the actual restriction map on Hom sets.

Source: Stacks Project, Divisors, Tags 0EBJ and 0B3N
(blueprint: lem-sfb-regular-surface-vector-bundle-extension).

Proof:
1. The open subscheme is regular and locally Noetherian, since its local rings agree
   with those of X. Its dimension is at most that of X: closure in X embeds strict
   chains of irreducible closed subsets of the open subscheme into such chains in X.
   Restricting local trivializations preserves finite local freeness.
2. Finite locally free modules are quasi-coherent of finite type, hence coherent by
   pqf-lem-coherent-ft-locnoeth. On X and U, the criterion
   lem-sfb-regular-surface-reflexive-locally-free (Tag 0B3N) identifies these modules
   with coherent reflexive modules, retaining all module morphisms.
3. By clause (1) of rem-pc-regular-normal, X is normal. Apply
   lem-sfb-normal-reflexive-open-equivalence (Tag 0EBJ) using integrality, local
   Noetherianity and the omitted-point dimension bound. Direct image of a bundle
   is coherent reflexive, its counit is invertible, and the unit on a bundle on X
   is invertible. Tag 0B3N makes the actual direct image finite locally free.
   These functors therefore induce inverse equivalences of the full bundle categories.
4. For a map a between restricted bundles E and F, extend it by the composite
   of the unit of E, the direct image of a, and the inverse unit of F. The adjunction
   identities give its restriction a. Naturality of the unit forces this formula
   for any extension, proving uniqueness, also for direct-image extensions.
-/
theorem regularSurfaceVectorBundleExtension
    (X U : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (hregular : IsRegularScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (j : U ⟶ X) [IsOpenImmersion j]
    (hcodim : ∀ x : X, x ∉ Set.range j → 2 ≤ ringKrullDim (X.presheaf.stalk x)) :
    (∀ E : X.Modules, E.IsFiniteLocallyFree →
      ((restrictFunctor j).obj E).IsFiniteLocallyFree ∧
        IsIso ((restrictAdjunction j).unit.app E)) ∧
    (∀ V : U.Modules, V.IsFiniteLocallyFree →
      ((pushforward j).obj V).IsFiniteLocallyFree ∧
        IsIso ((restrictAdjunction j).counit.app V)) ∧
    (∀ (E F : X.Modules), E.IsFiniteLocallyFree → F.IsFiniteLocallyFree →
      ∀ a : (restrictFunctor j).obj E ⟶ (restrictFunctor j).obj F,
        ∃! b : E ⟶ F, (restrictFunctor j).map b = a) ∧
    (∃ e : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory ≌
        (SheafOfModules.isFiniteLocallyFree U.ringCatSheaf).FullSubcategory,
      Nonempty (e.functor ⋙
          (SheafOfModules.isFiniteLocallyFree U.ringCatSheaf).ι ≅
        (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι ⋙
          restrictFunctor j) ∧
      Nonempty (e.inverse ⋙
          (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι ≅
        (SheafOfModules.isFiniteLocallyFree U.ringCatSheaf).ι ⋙
          pushforward j)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
