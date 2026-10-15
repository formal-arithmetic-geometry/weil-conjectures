/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ZetaSeries
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Sheaf.AlgebraicGeometry.GeometricStalkColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.EtaleCohomology.EtaleSectionZeroOpen

/-! # A sheaf supported in low dimension is a filtered union

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-sc-support-dimension-union`.
(blueprint: lem-sc-support-dimension-union)

The index category is the full poset of closed subsets of dimension at most `a`.
The parameters `D`, `c`, `hz`, and `hk` specify the support kernels by their universal
properties, including their inclusions into `N`. Naturality and monicity then force
exactly the canonical transition maps. No choice of a kernel model is imposed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Let `B` be finite type over a field `K`, and let `N` be a torsion étale sheaf whose
geometric stalks vanish above transcendence degree `a`.  For a filtered diagram of
the kernels of restriction away from closed subsets of dimension at most `a`, the
canonical map from its colimit to `N` is an isomorphism.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-sc-support-dimension-union.md`;
Stacks Project, Étale Cohomology, Tags 04FR, 03PT, and 03PU.

Proof:
1. The empty closed subset has dimension bottom. Finite unions preserve the dimension
   bound: an irreducible closed subset of a union lies in one member. Thus the index
   poset is small, nonempty and directed (`def-kun-topological-krull-dimension`,
   `def-weil-irreducible-components`).
2. On an open immersion, inverse image is restriction, by its adjunction to direct
   image. Its unit on sections is restriction to the open complement. Its kernel
   therefore consists of sections zero there. Inclusion of closed subsets gives
   inclusions of these kernels (`def-weil-pbc-direct-image`,
   `def-weil-pbc-inverse-image`, `def-weil-pbc-etale-site`).
3. Represent a geometric germ on a pointed affine étale neighbourhood. Restrict it
   over an affine chart of `B`. The resulting map of affine schemes is quasi-compact,
   so its source is finite type over `K` (`lemma-weil-pbc-affine-neighbourhood-cofinal`,
   `def-weil-finite-type-morphism`, `lem-kun-etale-lfp`).
4. The section has a largest zero open (`lem-sc-etale-section-zero-open`). Its closed
   complement `S` has finitely many irreducible components, since the neighbourhood
   is Noetherian (`lem-weil-pbc-finite-type-over-noetherian`,
   `lem-sc-noetherian-closed-subset-finite-components`). Each component has a generic
   point by `lem-weil-pbc-scheme-sober`; the empty case has no components.
5. Each image generic point has nonzero geometric germ, so its residue field has
   transcendence degree at most `a`. Its closure has dimension at most `a` by
   `lem-sc-closed-irreducible-dimension-trdeg`. Continuity places the image of the
   corresponding component in that closure. The finite union `Z` of these closures
   has dimension at most `a` and contains the image of `S`.
6. The section is zero over the complement of `Z`, by
   `lem-sc-etale-section-zero-open`, so belongs to the support kernel at `Z`.
   Hence the kernel stalks exhaust every geometric stalk of `N`.
7. Stalks preserve these colimits (`lem-kun-stalks-commute-colimits`) and kernel
   inclusions (`prop-weil-pbc-geometric-stalks-exact`). The resulting stalk map is
   injective because each stage embeds, and surjective by step 6. Apply
   `lemma-weil-pbc-geometric-stalk-conservative`. Torsion remains a hypothesis
   although this argument does not use it.

(blueprint: lem-sc-support-dimension-union)
-/
theorem support_dimension_union
    {K : Type u} [Field K] {B : Scheme.{u}}
    (p : B ⟶ Spec (.of K)) [LocallyOfFiniteType p] [QuasiCompact p]
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ℕ) (hN : CategoryTheory.Sheaf.IsTorsion N)
    (hvanish : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) <
          @Algebra.trdeg K _ _ _ ((p.residueFieldAlgebraMap (s default)).toAlgebra) →
        IsZero (((Scheme.pointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj N))
    (D : {Z : TopologicalSpace.Closeds B //
      topologicalKrullDim ↥(Z : Set B) ≤ (a : WithBot ℕ∞)} ⥤
        Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (c : D ⟶ (Functor.const _).obj N)
    (hz : ∀ Z, c.app Z ≫
      (Etale.upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1})
        (Scheme.Opens.ι ⟨(Z.val : Set B)ᶜ, Z.val.isClosed.isOpen_compl⟩)).unit.app N = 0)
    (hk : ∀ Z, IsLimit (KernelFork.ofι (c.app Z) (hz Z))) :
    IsIso ((colimit.isColimit D).desc (Cocone.mk N c)) := by
  sorry

end AlgebraicGeometry
