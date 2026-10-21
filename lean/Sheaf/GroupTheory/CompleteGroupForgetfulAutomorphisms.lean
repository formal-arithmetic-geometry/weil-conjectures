/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.GroupTheory.OpenOrbitFunctor
public import Sheaf.CategoryTheory.Galois.AutProfinite
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Topology.Compactness.Compact

/-! # Reconstructing a complete group from its discrete actions

Source: Bhatt--Scholze, Proposition 7.1.5 and Example 7.1.6, printed pp. 63--64.
(blueprint: lem-sfb-complete-group-forgetful-automorphisms)
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory

namespace TopologicalGroup

/-- A Hausdorff group with an open-subgroup identity basis, compact or complete for the
infimum of its left and right uniformities, is recovered from its open-orbit forgetful functor.
Restriction identifies the automorphisms of all discrete continuous actions with these orbit
automorphisms, with the pointwise topology of `CategoryTheory.SetFunctorAut.functorTopology`.
The component formulas specify translation by the given element, and the formula for `r`
specifies actual restriction along `openOrbitInclusion`, rather than an arbitrary isomorphism.

Source: Bhatt--Scholze, Proposition 7.1.5 and Example 7.1.6, printed pp. 63--64.
(blueprint: lem-sfb-complete-group-forgetful-automorphisms)

Proof:
1. The induced category has all equivariant maps and the open subgroups form a set
   (`def-nagata-category`). Its automorphisms are natural families of coset bijections.
2. Translation defines a homomorphism; equivariance proves naturality. Evaluation conditions
   prove that multiplication and inversion on natural automorphisms are continuous.
3. Stabilizers of cosets are conjugate open subgroups. Evaluation fibres are clopen; the
   subgroup basis and Hausdorffness give injectivity and continuity of the inverse.
4. For finitely many coordinates a_j U_j, intersect a_j U_j a_j inverse. Naturality for
   hV -> h a_j U_j realizes all coordinates by a representative of alpha_V(V).
5. Direct the finite tagged coordinate sets by inclusion and choose simultaneous realizers.
   Each coordinate is eventually alpha(x). Its prescribed-value fibre is a closed coset.
6. Include both U and alpha_U inverse(U) among the coordinates. The two equations force
   both g_F inverse * g_F' and g_F * g_F' inverse into U, giving a two-sided Cauchy net.
7. Completeness gives a limit; closedness of every prescribed-value fibre gives translation
   by this limit on every coordinate.
8. Alternatively compactness realizes all coordinates by the finite intersection property
   (`lem-sfb-compact-closed-finite-intersection`, Mathlib `CompactSpace.iInter_nonempty`).
9. Thus translation is bijective, multiplicative and continuous with continuous inverse.
10. For any discrete action and s, the stabilizer U_s is open and h U_s -> h s is equivariant.
    Naturality forces any extension of an orbit automorphism to act by the same g everywhere;
    translation gives this unique extension, and restriction respects multiplication.
11. Restriction is continuous by orbit evaluation. Extension is continuous since evaluation
    at s factors through evaluation at U_s followed by the map h U_s -> h s of discrete sets.
-/
theorem completeGroup_forgetful_automorphisms
    (G : Type u) [Group G] [TopologicalSpace G] [T2Space G] [NonarchimedeanGroup G]
    (hG : CompactSpace G ∨
      @CompleteSpace G
        (IsTopologicalGroup.leftUniformSpace G ⊓ IsTopologicalGroup.rightUniformSpace G)) :
    ∃ e : G ≃ₜ* Aut (openOrbitForget G),
      (∀ (g : G) (U : OpenOrbitCategory G) (x : G ⧸ U.toSubgroup),
        ((e g).hom.app U) x = g • x) ∧
      ∃ r : Aut (discreteActionForget G) ≃ₜ* Aut (openOrbitForget G),
        (∀ α : Aut (discreteActionForget G),
          r α = (((Functor.whiskeringLeft (OpenOrbitCategory G)
            (DiscreteContAction TopCat.{u} G) (Type u)).obj
              (openOrbitInclusion G)).mapAut (discreteActionForget G) α)) ∧
        (∀ (g : G) (S : DiscreteContAction TopCat.{u} G)
            (x : (discreteActionForget G).obj S),
          ((r.symm (e g)).hom.app S) x = (S.obj.obj.ρ g).hom x) := by
  sorry

end TopologicalGroup
