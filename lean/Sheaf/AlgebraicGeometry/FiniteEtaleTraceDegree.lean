/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.AlgebraicGeometry.FiniteEtaleTrace
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Degree and trace of a finite étale cover

Source: Stacks Project, Section 03SH, after Definition 03SE
(blueprint: lem-weil-pbc-finite-etale-trace-degree).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- (blueprint: lem-weil-pbc-finite-etale-trace-degree)
A finite étale morphism over a connected scheme has constant degree; its geometric fibres
have that cardinality, and restriction followed by trace is multiplication by the degree. Source:
Stacks Project, Section 03SH, after Definition 03SE (blueprint:
lem-weil-pbc-finite-etale-trace-degree).

Proof (the node's eight steps):
1. Finiteness and étaleness give finiteness, flatness, and local finite presentation
   (def-weil-pbc-scheme-conventions, def-weil-etale-morphism), which is finite local
   freeness (def-pc-finite-locally-free; Stacks 02KB).
2. The fibre degree is locally constant by
   lem-weil-pbc-finite-locally-free-degree-locally-constant (Stacks 04MH). Choose a point
   of the nonempty connected base; its degree d has a nonempty clopen level set, whose
   clopen complement must be empty (def-weil-connected-scheme). This proves (a).
3. Work in an affine chart about the image of a geometric point. The fibre rings are
   A tensor kappa(x) and A tensor Omega (lem-weil-pbc-open-fibre-product and
   lem-weil-pbc-fibre-product-affine-spectra). A basis remains a basis on field extension,
   so the geometric fibre has dimension d (def-weil-geometric-point).
4. By lem-galois-geometric-fibre, that fibre is a finite coproduct of copies of Spec Omega.
   Its global sections are Omega to the power of the number of copies, so the dimension
   in step 3 forces that number to be d. Its underlying space has exactly d points: (b).
5. Use lem-weil-pbc-finite-etale-etale-local-split (Stacks 04HN) at each base point.
   A geometric point above the distinguished point counts the local summands, using
   (b) and Cartesian pasting (def-pc-fibre-product). Hence there are d summands.
   Gluing along these disjoint opens gives a coproduct of d copies of the neighbourhood
   (lem-weil-pbc-scheme-coproduct-copies).
6. Under lem-weil-pbc-etale-inverse-image-restriction, restriction on a site object W
   is restriction along W times_X Y to W. Cartesian pasting identifies this projection
   with the corresponding projection after localisation. The trace commutes with the
   same localisation by lem-weil-pbc-finite-etale-trace-exists, property (1).
7. The sheaf condition identifies sections over the split cover with the d-fold product
   (def-weil-pbc-abelian-etale-sheaves). Restriction is the diagonal, and trace is the
   sum by lem-weil-pbc-finite-etale-trace-exists, property (2). Their composite is d times
   the identity; this also holds for the empty family, whose sections are zero.
8. Pull back the jointly surjective splitting neighbourhoods to each site object
   (lem-weil-pbc-etale-covering-base-change). The difference between the composite and
   d times the identity restricts to zero on this covering by steps 6 and 7. Sheaf
   separatedness makes the difference zero globally, proving (c).
-/
theorem exists_finiteEtaleTrace_degree
    {X Y : Scheme.{u}} [ConnectedSpace X] (f : Y ⟶ X) [IsFinite f] [Etale f] :
    ∃ d : ℕ, ∃ (_ : f.IsFiniteLocallyFreeOfDegree d),
      (∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ X),
        Finite ↥(pullback f x : Scheme.{u}) ∧
          Nat.card ↥(pullback f x : Scheme.{u}) = d ∧
          Nonempty (Over.mk (pullback.snd f x) ≅
            Over.mk (Sigma.desc fun _ : Fin d ↦ 𝟙 (Spec (.of Ω))))) ∧
      ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        finiteEtaleRestriction f F ≫ finiteEtaleTrace f F = d • 𝟙 F := by
  sorry

end AlgebraicGeometry.Etale
