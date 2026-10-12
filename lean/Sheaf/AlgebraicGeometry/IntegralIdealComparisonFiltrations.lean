/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.CategoryTheory.Subobject.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # Comparing an integral ideal with a module of generic rank one

Source: Stacks Project, Cohomology of Schemes, Tags 01YF and 01YH.
(blueprint: lem-pc-v3-integral-ideal-comparison-filtrations)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- An ideal and a coherent module of generic rank one have a common submodule whose
 two cokernels admit integral-ideal filtrations on strictly smaller closed supports.
 The zero ideal is recorded separately. This statement involves no cohomology property.

Source: Stacks Project, Cohomology of Schemes, Tag 01YH, proof of
`lemma-property-irreducible`, and Tag 01YF, `lemma-coherent-filter`.
(blueprint: lem-pc-v3-integral-ideal-comparison-filtrations)

Proof: A quasi-coherent ideal on the Noetherian integral W is coherent, as is its
closed pushforward. If the ideal is zero, so is that pushforward. Otherwise use the
coherent generic-point inclusion lemma to embed the pushforward of a nonzero ideal J
on W into G, isomorphically near its generic point. The generic stalk is a line, so
exactly one summand is required. Intersect J with I; the intersection J ∩ I is
quasi-coherent and nonzero because each affine section ring is a domain. Put
K = i_*(J ∩ I), and take its inclusions into G and i_* I. Their cokernels Q₁ and Q₂
are coherent, supported inside i(W), and have zero generic stalk: at the generic
point the maps are isomorphisms of one-dimensional residue-field modules. Their
supports are therefore closed proper subsets of i(W). Apply the coherent
integral-ideal filtration theorem to each cokernel. Stalk exactness puts every
filtration factor's support inside the support of the cokernel. A nonzero ideal on
an integral scheme has full support, so each factor's integral closed image is
strictly contained in i(W). Cokernel exactness yields the two short exact sequences.
The zero cokernel has the empty filtration. No properness or finiteness assumption
is used in this argument. -/
theorem exists_integral_ideal_comparison_filtrations (X W : Scheme.{u})
    [IsNoetherian X] (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (G : X.Modules) (hGcoh : RingedSpace.IsCoherent X.toRingedSpace G)
    (hGsupp : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base)
    (hGann : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint W))),
      ∀ v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G, a • v = 0)
    (hGrank : ∃ inst : Module (X.residueField (i.base (genericPoint W)))
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G),
      (∀ (a : X.presheaf.stalk (i.base (genericPoint W)))
        (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).obj G),
        a • v = (X.residue (i.base (genericPoint W))) a • v) ∧
      Module.finrank (X.residueField (i.base (genericPoint W)))
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G)
        = 1)
    (I : W.IdealSheafData) :
    IsZero ((pushforward i).obj I.toModules) ∨
      ∃ (K Q₁ Q₂ : X.Modules) (a : K ⟶ G) (b : G ⟶ Q₁) (hab : a ≫ b = 0),
        (ShortComplex.mk a b hab).ShortExact ∧
        ∃ (d : K ⟶ (pushforward i).obj I.toModules)
          (e : (pushforward i).obj I.toModules ⟶ Q₂) (hde : d ≫ e = 0),
          (ShortComplex.mk d e hde).ShortExact ∧
          ∀ Q : X.Modules, Q = Q₁ ∨ Q = Q₂ →
            ∃ (m : ℕ) (c : Fin (m + 1) → Subobject Q) (hc : Monotone c),
              c 0 = ⊥ ∧ c (Fin.last m) = ⊤ ∧
              ∀ k : Fin m, ∃ (W' : Scheme.{u}) (j : W' ⟶ X),
                IsClosedImmersion j ∧ IsIntegral W' ∧
                ∃ J : W'.IdealSheafData, Set.range j.base ⊂ Set.range i.base ∧
                  Nonempty (cokernel (Subobject.ofLE (c k.castSucc) (c k.succ)
                    (hc k.castSucc_le_succ)) ≅ (pushforward j).obj J.toModules) := by sorry

end AlgebraicGeometry.Scheme.Modules
