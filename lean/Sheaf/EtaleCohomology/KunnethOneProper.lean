/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import Sheaf.AlgebraicGeometry.ProperStability
import Sheaf.EtaleCohomology.SepClosedFieldVanishing
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.LerayBounded
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import Sheaf.AlgebraicGeometry.IntegralProperProjectionFormula
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow
import Sheaf.AlgebraicGeometry.KunnethGlobalSections
import Sheaf.AlgebraicGeometry.KunnethMapAgrees
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Künneth formula with one proper factor

Source: Stacks Project, Tag 0F14, part (1), and Tag 0F1E
(blueprint: lem-kun-0f14a).

The canonical Künneth morphism for integer coefficients is an isomorphism when the
first factor is proper and its bounded-below complex has torsion cohomology.
Integer coefficients use modules over the universe lift of `ℤ`; this is the category
of abelian groups with their unique integer action. The map is stated on `Spec k`,
whose étale topos over a separably closed field is the point topos. Exact global
sections and the canonical tensor and Leray identifications give the displayed
map of derived global sections in the node.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry
open Scheme
namespace Etale

/--
Source: Stacks Project, Tag 0F14, part (1), and Tag 0F1E
(blueprint: lem-kun-0f14a).

For a separably closed field, a proper first factor and a qcqs second factor,
the canonical `kunnethMap` for bounded-below integer-coefficient complexes is an
isomorphism when the first complex has torsion cohomology. The source of this
map is `RaX_* E ⊗ᴸ RaY_* K` on `Spec k`; its target is the derived direct image
of the external tensor product. The tensor-compatible point-topos equivalence
identifies this very map with the node's global-sections Künneth morphism.

Proof, following the seven steps of the node:
1. Exact inverse image commutes with cohomology
   (`prop-weil-pbc-inverse-image-exact`, `lem-weil-pbc-exact-functor-complex-cohomology`).
   Both pullbacks stay bounded below, and the pullback of `E` has torsion cohomology
   (`lem-weil-pbc-inverse-image-torsion`). The second projection is proper
   (`lem-kun-proper-stability`).
2. Every étale scheme over the separably closed point is a disjoint union of points
   (`lem-kun-0ezp`). Sheaf gluing identifies sections and constant sheaves as exact
   inverse tensor equivalences. These descend to derived categories and identify
   each object on the point with its constant derived global sections.
3. Leray (`lem-kun-leray-bdd`) and the direct-image lower-bound estimate
   (`lem-kun-tensor-t-est`) make `A = RΓ(X,E)` bounded below. Proper base change
   (`thm-weil-pbc-bounded-below`) and `lem-kun-pullback-constant` identify
   `Rpr₂_* pr₁⁻¹E` with the constant complex `A` on `Y`.
4. The integer proper projection formula (`lem-kun-0f0f`) identifies the direct image
   of the external tensor product with `Rpr₂_* pr₁⁻¹E ⊗ᴸ K`.
5. The canonical unbounded Leray composition
   (`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, with
   `def-weil-size-convention`) identifies global sections on the product with
   global sections of that direct image on `Y`; on K-injective representatives
   this is the equality of sections of the composite direct image.
6. Substitute the constant complex `A`, use signed tensor symmetry
   (`lem-kun-tensor-sym`), apply the qcqs constant-complex projection formula
   (`lem-kun-0f0e`), and use symmetry once more. This constructs an isomorphism
   `theta` from global sections of the external product to `A ⊗ᴸ RΓ(Y,K)`.
7. The compatibility equation in clause (a) of `lem-kun-kunneth-map-agrees` says
   `theta ∘ kappa = id` for the adjoint-of-counits map of `def-kun-kunneth-map`.
   Since each factor of `theta` is invertible, `kappa = theta⁻¹`. The exact point
   equivalence reflects isomorphisms, yielding `IsIso` of the specified map.
-/
theorem isIso_kunneth_one_proper
    (k : Type u) [Field k] [IsSepClosed k]
    (X Y : Scheme.{u})
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsProper aX] [QuasiCompact aY] [QuasiSeparated aY]
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
    (hE : DerivedCategory.torsionCohomology (ULift.{u + 1} ℤ) X
      (DerivedCategory.Plus.ι.obj E))
    (K : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))) :
    IsIso (kunnethMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (pullback.fst aX aY) (pullback.snd aX aY) aX aY
      ((pullback.fst aX aY) ≫ aX) rfl (pullback.condition (f := aX) (g := aY)).symm
      (DerivedCategory.Plus.ι.obj E) (DerivedCategory.Plus.ι.obj K)) := by
  sorry

end Etale
end AlgebraicGeometry
