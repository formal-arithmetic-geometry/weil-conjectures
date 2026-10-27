/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.MarkedIdealOrder
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.TraceFormula.NodalSubcurveBoundary
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # Scalar gluing in a nodal cluster ideal

Source: Stacks Project, curves.tex, Tag 0CBW; varieties.tex, Tag 0C3V;
algebra.tex, Tag 00MC. Agent-written ideal-twist consequence supporting
Franciosi--Tenni, Lemma 3.6(i), p. 241
(blueprint: lem-sfb-nodal-ideal-scalar-gluing).

The two branch rings are expressed canonically as the quotients of the completed
local ring by the two completed component ideals. Thus the pair (f,0) belongs to
J exactly when an element r of J has r-s in the first component ideal and r in
the second. This retains membership in the equal-constant subring, without choosing
coordinates or an embedding into a product of power series rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.NodalIdealScalarGluing

/-- Inclusion of the existing reduced component, without normalizing it.
Source: Stacks 0CBW, reduced components
(blueprint: lem-sfb-nodal-ideal-scalar-gluing). -/
def componentι {X : Scheme.{u}} (C : irreducibleComponents X) :
    X.reducedNormalizationComponent C ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩).subschemeι

/-- The usual ideal-twist inclusion, from ideal inclusion and the tensor unitor.
Source: Stacks 0CBW, ideal-twist assembly
(blueprint: lem-sfb-nodal-ideal-scalar-gluing). -/
def twistι {X : Scheme.{u}} (I : X.IdealSheafData) (L : X.Modules) :
    I.toModules ⊗ L ⟶ L :=
  I.toModulesι ▷ L ≫ (λ_ L).hom

/-- Regard an ideal-twist section as a section of the line bundle.
Source: Stacks 0CBW, ideal-twist assembly
(blueprint: lem-sfb-nodal-ideal-scalar-gluing). -/
def ambientSection {X : Scheme.{u}} (I : X.IdealSheafData) (L : X.Modules)
    (s : Γ(I.toModules ⊗ L, ⊤)) : Γ(L, ⊤) :=
  (twistι I L).app ⊤ s

/-- Extend the existing stalk ideal along the actual completion map.
Source: Stacks 00MC and 0CBW, J = I times the completed local ring
(blueprint: lem-sfb-nodal-ideal-scalar-gluing). -/
def completedIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    Ideal (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x)) :=
  (HilbertSamuel.stalkIdeal I x).map (algebraMap _ _)

/-- Completed germ in an arbitrary stalk frame of the line bundle.
Source: Stacks 0CBW, completed framed germ
(blueprint: lem-sfb-nodal-ideal-scalar-gluing). -/
def completedValue {X : Scheme.{u}} (I : X.IdealSheafData) (L : X.Modules)
    (s : Γ(I.toModules ⊗ L, ⊤)) (x : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj L ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x) :
    AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
  algebraMap _ _ (e (L.presheaf.Γgerm x (ambientSection I L s)))

/-- Failure of membership of the one-branch pair (z mod P,0 mod Q) in the image of J.
The witness must be in J itself, so the equal-constant subring condition is retained.
Source: Stacks 0CBW, agent ideal-twist scalar calculation
(blueprint: lem-sfb-nodal-ideal-scalar-gluing). -/
def Constrained {R : Type u} [CommRing R] (J P Q : Ideal R) (z : R) : Prop :=
  ¬ ∃ r ∈ J, r - z ∈ P ∧ r ∈ Q

/-- The constrained-node test in the canonical completed component quotients.
At a node joining distinct components these quotients are precisely the two branch rings.
Source: Stacks 0CBW and 0C3V
(blueprint: lem-sfb-nodal-ideal-scalar-gluing). -/
def constrainedAt {X : Scheme.{u}} (I : X.IdealSheafData) (L : X.Modules)
    (s : Γ(I.toModules ⊗ L, ⊤)) (x : X) (C D : irreducibleComponents X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj L ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x) : Prop :=
  Constrained (completedIdeal I x) (completedIdeal (componentι C).ker x)
    (completedIdeal (componentι D).ker x) (completedValue I L s x e)

/-- Componentwise scalar multiples glue exactly across the constrained nodes.
The submodule W and its coefficient map are uniquely specified by their displayed
membership and graph formulas; no auxiliary subspace or arbitrary map is assumed.
Source: Stacks 0CBW, 0C3V and 00MC; agent coefficient-space consequence supporting
Franciosi--Tenni, Lemma 3.6(i), p. 241
(blueprint: lem-sfb-nodal-ideal-scalar-gluing).

Proof plan:
1. Projective-implies-proper and nodal-completed-normalization-model give the
   Noetherian curve setup. Closed-component-stalk-calculus and module-stalk-exact
   embed F = I tensor L in the finite product of component line bundles: the
   component prime ideals intersect in zero because X is reduced.
2. Nodal-subcurve-boundary and split-node-component-normalization show that
   intersections of distinct components are closed nodes. At a one-component
   point, including a self-node, the product stalk is the original local ring;
   any scalar multiple already lies in the ideal.
3. Local-completion-faithfully-flat, flat-tensor-exact and faithfully-flat-
   universally-injective reflect membership in the full ideal after completion.
   Split-node-component-normalization identifies the two completed component
   quotients with k[[u]] and k[[v]]. The completed pair lifts precisely when it
   belongs to J, which is the witness condition in Constrained.
4. For s = (f,g) in J, (af,bg) = b(f,g) + (a-b)(f,0).
   If (f,0) belongs to J any a,b work; otherwise the invertibility of every
   nonzero scalar implies that membership is equivalent to a = b.
5. The criterion makes each component tuple locally lift to F. Stalk exactness
   gives local lifts; injectivity into the component product makes them agree
   on overlaps, and the sheaf axiom gives a unique global section.
6. Generic nonvanishing makes the coefficients unique and their assignment
   linear. The component-product injection makes the coefficient map injective.
7. Changing the frame multiplies by a unit, preserving ideal membership.
   Swapping branches replaces (f,0) by s-(f,0). Under any k-compatible nodal
   presentation the two completed component ideals are minimal primes, hence
   go to (v) and (u) in some order (split-node component normalization); with
   the swap invariance the intrinsic test is the presented test "(f,0) in J"
   for the branch rings k[[u]] = R/(v) and k[[v]] = R/(u), for every
   presentation. Self-nodes contribute no equality
   between distinct coefficients. Nothing required connectedness or a reduced,
   Cartier, nonempty, or smooth-supported cluster.
-/
theorem nodal_ideal_scalar_gluing
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [IsHProjective p]
    [Nonempty X] [IsReduced X] (hpure : X.IsPureDimension 1)
    (hnodal : ∀ x : X, IsClosed ({x} : Set X) → x ∉ p.smoothLocus →
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}),
        ∀ a : k, e (algebraMap _ _
          (X.presheaf.Γgerm x (Scheme.Modules.scalarMap p ⊤ a))) =
            Ideal.Quotient.mk _ (MvPowerSeries.C a))
    (L : X.Modules) [L.IsInvertible] (T : Scheme.{u}) (i : T ⟶ X)
    [IsClosedImmersion i] (hdimT : topologicalKrullDim T ≤ 0)
    (s : Scheme.Modules.scalarObj p (i.ker.toModules ⊗ L) (op ⊤))
    (hs : ∀ (C : irreducibleComponents X) (ξ : X), IsGenericPoint ξ C.val →
      L.presheaf.Γgerm ξ (ambientSection i.ker L s) ≠ 0) :
    (∃ W : Submodule k (Scheme.Modules.scalarObj p (i.ker.toModules ⊗ L) (op ⊤)),
      (∀ t, t ∈ W ↔ ∀ C : irreducibleComponents X, ∃ a : k,
        Scheme.Modules.tensorPullbackTopSection (componentι C) L (ambientSection i.ker L t) =
          (Scheme.Modules.scalarMap (componentι C ≫ p) ⊤ a) •
            Scheme.Modules.tensorPullbackTopSection (componentι C) L
              (ambientSection i.ker L s)) ∧
      ∃ c : W →ₗ[k] (irreducibleComponents X → k),
        (∀ (t : W) (C : irreducibleComponents X),
          Scheme.Modules.tensorPullbackTopSection (componentι C) L
              (ambientSection i.ker L t.val) =
            (Scheme.Modules.scalarMap (componentι C ≫ p) ⊤ (c t C)) •
              Scheme.Modules.tensorPullbackTopSection (componentι C) L
                (ambientSection i.ker L s)) ∧
        Function.Injective c ∧
        (∀ a : irreducibleComponents X → k, a ∈ LinearMap.range c ↔
          ∀ x : X, IsClosed ({x} : Set X) → x ∉ p.smoothLocus →
            ∀ C D : irreducibleComponents X, C ≠ D → x ∈ C.val → x ∈ D.val →
              ∀ e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj L ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x,
                constrainedAt i.ker L s x C D e → a C = a D)) ∧
    (∀ x : X, IsClosed ({x} : Set X) → x ∉ p.smoothLocus →
      ∀ C D : irreducibleComponents X, C ≠ D → x ∈ C.val → x ∈ D.val →
        ∀ e e' : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj L ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x,
          (constrainedAt i.ker L s x C D e ↔ constrainedAt i.ker L s x D C e')) ∧
    (∀ x : X, IsClosed ({x} : Set X) → x ∉ p.smoothLocus →
      ∀ C D : irreducibleComponents X, C ≠ D → x ∈ C.val → x ∈ D.val →
      ∀ (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj L ≃ₗ[X.presheaf.stalk x]
          X.presheaf.stalk x)
        (ρ : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})),
      (∀ a : k, ρ (algebraMap _ _
          (X.presheaf.Γgerm x (Scheme.Modules.scalarMap p ⊤ a))) =
            Ideal.Quotient.mk _ (MvPowerSeries.C a)) →
        (constrainedAt i.ker L s x C D e ↔
          Constrained ((completedIdeal i.ker x).map ρ.toRingHom)
            (Ideal.span {Ideal.Quotient.mk (Ideal.span
              {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
              (MvPowerSeries.X 1)})
            (Ideal.span {Ideal.Quotient.mk (Ideal.span
              {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
              (MvPowerSeries.X 0)})
            (ρ (completedValue i.ker L s x e)))) := by
  sorry

end AlgebraicGeometry.NodalIdealScalarGluing
