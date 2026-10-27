/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.MarkedIdealOrder
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Topology.Sheaves.Sheafify

/-! # A twisted boundary-ideal quotient at a closed point

Source: Stacks Project, Tag 0B5P, proof, first paragraph; Tag 01CA.
(blueprint: lem-trf-closed-point-twisted-ideal-quotient)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules.ClosedPointTwist

/-- The reduced ideal of the boundary of U. Source: Stacks 0B5P, proof.
(blueprint: lem-trf-closed-point-twisted-ideal-quotient). -/
noncomputable def boundary {X : Scheme.{u}} (U : X.Opens) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩

/-- The reduced ideal of the boundary together with x. Source: Stacks 0B5P, proof.
(blueprint: lem-trf-closed-point-twisted-ideal-quotient). -/
noncomputable def boundaryPoint {X : Scheme.{u}} (U : X.Opens) (x : X)
    (hx : IsClosed ({x} : Set X)) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨(U : Set X)ᶜ ∪ {x}, U.isOpen.isClosed_compl.union hx⟩

/-- The canonical inclusion J into I. Source: Stacks 0B5P, proof.
(blueprint: lem-trf-closed-point-twisted-ideal-quotient). -/
noncomputable def inclusion {X : Scheme.{u}} (U : X.Opens) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    (boundaryPoint U x hx).toModules ⟶ (boundary U).toModules :=
  Scheme.IdealSheafData.toModulesOfLE
    (Scheme.IdealSheafData.vanishingIdeal_antimono Set.subset_union_left)

/-- The sheafified sectionwise quotient I/J. Source: Stacks 0B5P, proof.
(blueprint: lem-trf-closed-point-twisted-ideal-quotient). -/
noncomputable def quotient {X : Scheme.{u}} (U : X.Opens) (x : X)
    (hx : IsClosed ({x} : Set X)) : X.Modules := cokernel (inclusion U x hx)

/-- The local tensor power of e, without extending e outside U. Source: Stacks 01CA.
(blueprint: lem-trf-closed-point-twisted-ideal-quotient). -/
noncomputable def powerSection {X : Scheme.{u}} {L : X.Modules} {U : X.Opens}
    (e : Γ(L, U)) : (n : ℕ) → Γ(L.tensorPow n, U)
  | 0 => unitSectionsEquiv U 1
  | n + 1 => tmulSection e (powerSection e n)

/-- The canonical twisted quotient arrow. Source: Stacks 0B5P, proof.
(blueprint: lem-trf-closed-point-twisted-ideal-quotient). -/
noncomputable def projection {X : Scheme.{u}} (U : X.Opens) (x : X)
    (hx : IsClosed ({x} : Set X)) (M : X.Modules) :
    (boundary U).toModules ⊗ M ⟶ quotient U x hx ⊗ M :=
  cokernel.π (inclusion U x hx) ▷ M

/-- Multiplication from the twisted ideal into M. Source: Stacks 0B5P, proof.
(blueprint: lem-trf-closed-point-twisted-ideal-quotient). -/
noncomputable def multiplication {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) :
    (boundary U).toModules ⊗ M ⟶ M :=
  (boundary U).toModulesι ▷ M ≫ (λ_ M).hom

/-- The residue-fibre relations m_x M_x. Source: Stacks 0B5P, proof.
(blueprint: lem-trf-closed-point-twisted-ideal-quotient). -/
noncomputable def fibreRelations {X : Scheme.{u}} (x : X) (M : X.Modules) :
    Submodule (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  IsLocalRing.maximalIdeal (X.presheaf.stalk x) • ⊤

/-- The complete twisted quotient construction, with its canonical residue identification.
Source: Stacks 0B5P, first paragraph of the proof, and 01CA.
(blueprint: lem-trf-closed-point-twisted-ideal-quotient).

Proof:
1. The reduced-induced-closed-subscheme theorem gives the residue-vanishing ideals,
   quasi-coherence and J subset I. On opens inside U, I is the whole ring; on opens
   avoiding x the two ideals coincide.
2. Represent stalk elements by germs on neighbourhoods inside U. Membership in J is
   exactly residue zero at x, so J_x is m_x and I_x is O_x. The module-stalk-exact
   theorem identifies the quotient stalk and shows that Q vanishes away from x.
3. On each rank-one chart, tensoring by the power of its generator identifies F tensor
   L^n with F: send a tensor (b f^n) to ba, with inverse a to a tensor f^n. Balancing and
   sheafification give mutually inverse maps, compatible with restrictions.
4. These coordinates identify the twisted sequence with J to I to Q and multiplication
   with I into O. Stalkwise exactness proves the short exact sequence and injectivity.
5. Glue the image of e^n on U with zero on X minus {x}. They agree on the overlap,
   because Q tensor L^n is zero there, and these two opens cover X.
6. At x, multiplication identifies the image of the twisted J with m_x M_x. Exactness
   gives the linear quotient identification, characterized below on every representative.
   The germ of the glued section maps to the class of e_x^n. Its generator coordinate
   is residue(1) = 1, hence is nonzero in the residue field.
-/
theorem closedPoint_twisted_ideal_quotient
    (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X))
    (U : X.affineOpens) (hxU : x ∈ U.1)
    (L : X.Modules) [L.IsInvertible] (e : Γ(L, U.1)) (he : IsFreeGenerator e) :
    (boundary U.1).toModules.IsQuasicoherent ∧
    (boundaryPoint U.1 x hx).toModules.IsQuasicoherent ∧
    boundaryPoint U.1 x hx ≤ boundary U.1 ∧
    (∀ (W : X.Opens), W ≤ U.1 → (boundary U.1).idealOfOpens W = ⊤) ∧
    (∀ (W : X.Opens), x ∉ W →
      (boundary U.1).idealOfOpens W = (boundaryPoint U.1 x hx).idealOfOpens W) ∧
    HilbertSamuel.stalkIdeal (boundary U.1) x = ⊤ ∧
    HilbertSamuel.stalkIdeal (boundaryPoint U.1 x hx) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
    (∀ (n : ℕ), 1 ≤ n →
      (∃ h : (inclusion U.1 x hx ▷ L.tensorPow n) ≫
          projection U.1 x hx (L.tensorPow n) = 0,
        (ShortComplex.mk (inclusion U.1 x hx ▷ L.tensorPow n)
          (projection U.1 x hx (L.tensorPow n)) h).ShortExact) ∧
      (∀ W : X.Opens, Function.Injective ((multiplication U.1 (L.tensorPow n)).app W)) ∧
      ∃ (q : Γ(quotient U.1 x hx ⊗ L.tensorPow n, ⊤)),
        (∃ t : Γ((boundary U.1).toModules ⊗ L.tensorPow n, U.1),
          (multiplication U.1 (L.tensorPow n)).app U.1 t = powerSection e n ∧
          (quotient U.1 x hx ⊗ L.tensorPow n).presheaf.map
            (homOfLE (le_top : U.1 ≤ ⊤)).op q =
              (projection U.1 x hx (L.tensorPow n)).app U.1 t) ∧
        (∀ (W : X.Opens), x ∉ W →
          (quotient U.1 x hx ⊗ L.tensorPow n).presheaf.map
            (homOfLE (le_top : W ≤ ⊤)).op q = 0) ∧
        ∃ θ : (quotient U.1 x hx ⊗ L.tensorPow n).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
            ((L.tensorPow n).presheaf.stalk x ⧸ fibreRelations x (L.tensorPow n)),
          (∀ v : ((boundary U.1).toModules ⊗ L.tensorPow n).presheaf.stalk x,
            θ ((projection U.1 x hx (L.tensorPow n)).stalkLinearMap x v) =
            (fibreRelations x (L.tensorPow n)).mkQ
              ((multiplication U.1 (L.tensorPow n)).stalkLinearMap x v)) ∧
          θ ((quotient U.1 x hx ⊗ L.tensorPow n).presheaf.germ ⊤ x (by trivial) q) =
            (fibreRelations x (L.tensorPow n)).mkQ
              ((L.tensorPow n).presheaf.germ U.1 x hxU (powerSection e n)) ∧
          ∃ c : ((L.tensorPow n).presheaf.stalk x ⧸ fibreRelations x (L.tensorPow n)) ≃+
              X.residueField x,
            (∀ r : X.presheaf.stalk x,
              c ((fibreRelations x (L.tensorPow n)).mkQ
                (r • (L.tensorPow n).presheaf.germ U.1 x hxU (powerSection e n))) =
                  X.residue x r) ∧
            c (θ ((quotient U.1 x hx ⊗ L.tensorPow n).presheaf.germ
              ⊤ x (by trivial) q)) = 1 ∧
            θ ((quotient U.1 x hx ⊗ L.tensorPow n).presheaf.germ
              ⊤ x (by trivial) q) ≠ 0) := by
  sorry

end AlgebraicGeometry.Scheme.Modules.ClosedPointTwist
