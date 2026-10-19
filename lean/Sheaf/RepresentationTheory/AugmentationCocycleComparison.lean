/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker Q67
-/
module

public import Sheaf.RepresentationTheory.CompletedAugmentationAlgebra
public import Sheaf.RepresentationTheory.DiscreteContinuousCohomology
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Topology.Algebra.Group.Basic
import WeilConjectures.Topology.ContinuousOpenNormalStabilizer
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# Continuous cocycles and the completed augmentation resolution

Source: ILO, Expose XVII, 1.2.1–1.2.3, pp. 259–260; Stacks Project, Tag 0DVG.
The general continuous-cocycle comparison and its sign are the DAG's explicit refinement.
(blueprint: lem-per-augmentation-cocycle-comparison).
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace Rep

variable {Λ : Type v} [CommRing Λ] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Continuous one-cocycles, using the discrete coefficient topology.
Source: Stacks 0DVG (blueprint: lem-per-augmentation-cocycle-comparison).
Local constancy is equivalent to continuity to a discrete module. -/
def discreteContinuousCocycles₁ (M : DiscreteContinuousRep.{v, u, w} Λ G) :
    Submodule Λ (LocallyConstant G M.obj.V) :=
  LinearMap.ker (LinearMap.pi (fun p : G × G ↦
    (M.obj.ρ p.1).comp (LocallyConstant.evalₗ Λ p.2) -
      LocallyConstant.evalₗ Λ (p.1 * p.2) + LocallyConstant.evalₗ Λ p.1))

/-- The positive degree-zero inhomogeneous differential, m ↦ (g ↦ gm-m).
Source: Stacks 0DVG (blueprint: lem-per-augmentation-cocycle-comparison). -/
def discreteContinuousD₀ (M : DiscreteContinuousRep.{v, u, w} Λ G) :
    M.obj.V →ₗ[Λ] (G → M.obj.V) :=
  LinearMap.pi (fun g ↦ M.obj.ρ g - LinearMap.id)

/-- Coboundaries inside continuous cocycles, with the positive differential.
Source: Stacks 0DVG (blueprint: lem-per-augmentation-cocycle-comparison). -/
def discreteContinuousCoboundaries₁ (M : DiscreteContinuousRep.{v, u, w} Λ G) :
    Submodule Λ (discreteContinuousCocycles₁ M) :=
  (LinearMap.range (discreteContinuousD₀ M)).comap
    ((LocallyConstant.coeFnₗ Λ).comp (discreteContinuousCocycles₁ M).subtype)

/-- Degree-one continuous cohomology in the inhomogeneous model specified in the node.
Source: Stacks 0DVG (blueprint: lem-per-augmentation-cocycle-comparison). -/
abbrev discreteContinuousH₁ (M : DiscreteContinuousRep.{v, u, w} Λ G) :=
  (discreteContinuousCocycles₁ M) ⧸ discreteContinuousCoboundaries₁ M

end Rep

namespace Rep.CompletedAugmentation

variable (Λ : Type v) [CommRing Λ] [Finite Λ] (G : Type u) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G]

/-- Forget a Λ-linear map to its underlying function.
Source: ILO XVII 1.2.1 (blueprint: lem-per-augmentation-cocycle-comparison). -/
def homFunctions (M : DiscreteContinuousRep.{v, u, w} Λ G) :
    (Ideal Λ G →ₗ[Λ] M.obj.V) →ₗ[Λ] (Ideal Λ G → M.obj.V) :=
  LinearMap.pi (fun x ↦ LinearMap.applyₗ (R := Λ) (M₂ := M.obj.V) x)

/-- Algebraic A-linear maps, expressed inside Λ-linear maps using the canonical A-action.
Source: ILO XVII 1.2.1–1.2.2 (blueprint: lem-per-augmentation-cocycle-comparison). -/
def algebraicHom (M : DiscreteContinuousRep.{v, u, w} Λ G) :
    Submodule Λ (Ideal Λ G →ₗ[Λ] M.obj.V) :=
  LinearMap.ker (LinearMap.pi (fun p : Algebra Λ G × Ideal Λ G ↦
    LinearMap.applyₗ (R := Λ) (M₂ := M.obj.V) (p.1 • p.2) -
      (action Λ G M p.1).comp (LinearMap.applyₗ (R := Λ) (M₂ := M.obj.V) p.2)))

/-- Continuous A-linear maps. Membership in the range of locally constant functions
means exactly continuity to the discrete coefficient module.
Source: ILO XVII 1.2.1 (blueprint: lem-per-augmentation-cocycle-comparison). -/
def continuousHom (M : DiscreteContinuousRep.{v, u, w} Λ G) :
    Submodule Λ (Ideal Λ G →ₗ[Λ] M.obj.V) :=
  algebraicHom Λ G M ⊓
    (LinearMap.range (LocallyConstant.coeFnₗ Λ :
      LocallyConstant (Ideal Λ G) M.obj.V →ₗ[Λ] (Ideal Λ G → M.obj.V))).comap
        (homFunctions Λ G M)

/-- The restriction map m ↦ (x ↦ xm) in function coordinates.
Source: ILO XVII 1.2.2 (blueprint: lem-per-augmentation-cocycle-comparison). -/
def principalFunctions (M : DiscreteContinuousRep.{v, u, w} Λ G) :
    M.obj.V →ₗ[Λ] (Ideal Λ G → M.obj.V) :=
  LinearMap.pi (fun x ↦ action Λ G M x.val)

/-- The principal submodule in continuous Hom: exactly the maps x ↦ xm.
Source: ILO XVII 1.2.2 (blueprint: lem-per-augmentation-cocycle-comparison). -/
def principalContinuous (M : DiscreteContinuousRep.{v, u, w} Λ G) :
    Submodule Λ (continuousHom Λ G M) :=
  (LinearMap.range (principalFunctions Λ G M)).comap
    ((homFunctions Λ G M).comp (continuousHom Λ G M).subtype)

/-- The principal submodule in algebraic Hom, defining the algebraic cokernel.
Source: ILO XVII 1.2.2 (blueprint: lem-per-augmentation-cocycle-comparison). -/
def principalAlgebraic (M : DiscreteContinuousRep.{v, u, w} Λ G) :
    Submodule Λ (algebraicHom Λ G M) :=
  (LinearMap.range (principalFunctions Λ G M)).comap
    ((homFunctions Λ G M).comp (algebraicHom Λ G M).subtype)

/-- Degree one is naturally the quotient of continuous augmentation-ideal functionals
by the principal maps. The equivalence B identifies the published derived
invariants with the continuous cocycle model, naturally on coefficient maps.
The unique functional sends g-1 to c(g); this fixes the positive
bar-resolution comparison. The last clause uses the same comparison after dropping
continuity when I is topologically free on 1-σ, and records f(1-σ)=-c(σ).

Source: ILO XVII 1.2.1–1.2.3, pp. 259–260; Stacks 0DVG; the general profinite
comparison is the agent refinement in the DAG
(blueprint: lem-per-augmentation-cocycle-comparison).

Proof:
1. A continuous discrete-valued map on G factors through a finite quotient, by
lem-exc-coinduced-functions-open-stabilizer. A finite subset of M lies in the finite
Λ-span of finitely many finite G-orbits. Intersect their open stabilizers and normal
cores to find one open normal U acting trivially on this finite stable span.
2. The canonical completed action uses the U-coordinate of a; passing to a common
refinement proves independence, all action laws, and continuity of the orbit maps.
Equivariant Λ-linear maps commute with this finite-sum action.
3. For a continuous cocycle c, choose one such quotient Q=G/U that also carries c.
It descends to a cocycle with values in the finite stable span of its image; c(1)=0.
4. Set L(sum b_q q)=sum b_q c(q). The cocycle identity gives
L(qx)=q L(x)+ε(x)c(q), so L restricted to the augmentation ideal is Q-linear.
Compose with the projection I -> I_Q to obtain continuous A-linear f_c with
f_c(g-1)=c(g).
5. The Λ-span of g-1 is dense in I: refine finitely many coordinates by their
intersection V and lift the coefficients of the V-coordinate using representatives.
Their sum is zero, so the lift is a sum of b_g(g-1). Continuous maps to discrete M
are determined on this dense span. This proves uniqueness, independence and linearity.
6. Conversely c_f(g)=f(g-1) is continuous and satisfies the cocycle relation, since
gh-1=(g-1)+g(h-1). These operations are inverse. The continuous principal map x↦xm
corresponds to g↦gm-m, so they carry exactly the boundary submodules to each other.
7. By def-exc-continuous-cohomology and continuousCochains_derived_invariants,
identify derived invariants with the continuous inhomogeneous cochain homology.
Evaluate degree-zero cochains at the empty tuple and degree-one cochains at g.
The module-category kernel/image description of homology gives the equivalence B.
These evaluations commute with coefficient maps, proving the first naturality clause.
The differentials are d⁰m(g)=gm-m and
d¹c(g,h)=gc(h)-c(gh)+c(g). Thus degree one is the displayed cocycle quotient.
Postcomposition by any coefficient morphism commutes with f_c by uniqueness on g-1.
8. For lem-sfb-bar-resolution-cochains the signed differential is d₁[g]=g-1 and
d₂[g|h]=g[h]-[gh]+[g]. Send B₀ to A by the group-ring map and [g] to g-1 in I.
The augmentations commute and g(h-1)-(gh-1)+(g-1)=0. Together with zero higher
maps this is the comparison to [I -> A]. Precomposition is exactly f↦(g↦f(g-1)),
so the degree-one comparison is the stated one, with no sign change or claim of
projectivity for arbitrary I.
9. If θ(a)=a(1-σ) is a topological A-linear isomorphism, every algebraic f satisfies
(fθ)(a)=a f(1-σ). The orbit map is continuous; compose with continuous θ⁻¹.
Thus all algebraic maps are continuous and the two quotients identify by inclusion.
10. Since 1-σ=-(σ-1), f_c(1-σ)=-f_c(σ-1)=-c(σ), including on coboundaries. -/
theorem exists_augmentation_cocycle_comparison :
    ∃ B : ∀ M : DiscreteContinuousRep.{v, u, max u w} Λ G,
        ((discreteContinuousCohomologyFunctor.{u, v, w} G Λ 1).obj M) ≃ₗ[Λ]
          discreteContinuousH₁ M,
    ∃ E : ∀ M : DiscreteContinuousRep.{v, u, max u w} Λ G,
        discreteContinuousH₁ M ≃ₗ[Λ]
          ((continuousHom Λ G M) ⧸ principalContinuous Λ G M),
      (∀ (M N : DiscreteContinuousRep.{v, u, max u w} Λ G) (a : M ⟶ N)
        (c : discreteContinuousCocycles₁ M),
        ∃ d : discreteContinuousCocycles₁ N,
          (∀ g : G, d.val g = a.hom.hom (c.val g)) ∧
          B N (((discreteContinuousCohomologyFunctor.{u, v, w} G Λ 1).map a).hom
            ((B M).symm (Submodule.Quotient.mk c))) = Submodule.Quotient.mk d) ∧
      (∀ (M : DiscreteContinuousRep.{v, u, max u w} Λ G)
        (c : discreteContinuousCocycles₁ M),
        ∃ f : continuousHom Λ G M,
          (∀ g : G, f.val (difference Λ G g) = c.val g) ∧
          (∀ f' : continuousHom Λ G M,
            (∀ g : G, f'.val (difference Λ G g) = c.val g) → f' = f) ∧
          E M (Submodule.Quotient.mk c) = Submodule.Quotient.mk f) ∧
      (∀ (M N : DiscreteContinuousRep.{v, u, max u w} Λ G) (a : M ⟶ N)
        (c : discreteContinuousCocycles₁ M) (f : continuousHom Λ G M),
        E M (Submodule.Quotient.mk c) = Submodule.Quotient.mk f →
        ∃ (d : discreteContinuousCocycles₁ N) (h : continuousHom Λ G N),
          (∀ g : G, d.val g = a.hom.hom (c.val g)) ∧
          (∀ x : Ideal Λ G, h.val x = a.hom.hom (f.val x)) ∧
          E N (Submodule.Quotient.mk d) = Submodule.Quotient.mk h) ∧
      (∀ (σ : G), closure (Subgroup.zpowers σ : Set G) = Set.univ →
        ∀ θ : Algebra Λ G ≃ₗ[Algebra Λ G] Ideal Λ G,
          (∀ a : Algebra Λ G, (θ a).val = a * (1 - groupElement Λ G σ)) →
          Continuous θ → Continuous θ.symm →
          ∀ M : DiscreteContinuousRep.{v, u, max u w} Λ G,
            (∀ f : algebraicHom Λ G M, @Continuous (Ideal Λ G) M.obj.V
              (idealTopology Λ G) ⊥ f.val) ∧
            ∃ Ealg : discreteContinuousH₁ M ≃ₗ[Λ]
                ((algebraicHom Λ G M) ⧸ principalAlgebraic Λ G M),
              (∀ (c : discreteContinuousCocycles₁ M) (f : continuousHom Λ G M),
                E M (Submodule.Quotient.mk c) = Submodule.Quotient.mk f →
                Ealg (Submodule.Quotient.mk c) =
                  Submodule.Quotient.mk (⟨f.val, f.property.1⟩ : algebraicHom Λ G M)) ∧
              (∀ (c : discreteContinuousCocycles₁ M) (f : continuousHom Λ G M),
                (∀ g : G, f.val (difference Λ G g) = c.val g) →
                f.val (-difference Λ G σ) = -c.val σ)) := by
  sorry

end Rep.CompletedAugmentation
