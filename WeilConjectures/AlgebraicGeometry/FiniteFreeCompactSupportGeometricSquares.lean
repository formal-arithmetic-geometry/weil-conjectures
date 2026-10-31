/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompactSupportData

/-! # Canonical finite-free compact-support squares

Source: current blueprint sk-thm-purity-transport, Steps 1, 3 and 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry
open WeilConjectures.FiniteFreeCoefficients
namespace AlgebraicGeometry.FiniteFreeCompactSupport

/-- The scalar square for the two geometric comparisons on bounded origins.
This assertion concerns only their equations; it imposes no constructibility
condition and asserts no existence of an origin or of a scalar origin.
Source: current blueprint sk-thm-purity-transport, Steps 1, 3 and 4; node
lem-pur-finite-free-compact-composition, proof Steps 2--5
(blueprint: lem-pur-finite-free-compact-geometric-squares).

Proof: choose a compatible compactification tower. On the etale site, proper
composition is scalar-mate composition and open composition follows by taking
the open-unit transpose. The middle square is the scalar inverse-exchange
mate identity for the normalized proper/open interchange. Pasting gives the
composition square in the tower. For a proper refinement, apply the specified
proper/open coefficient-refinement square, then proper direct image and its
scalar composition identity. Invert the two refinement isomorphisms. Compare
arbitrary compactifications with the tower by common refinements and cancel
adjacent inverse comparisons; this is etaleCompactScalarComposition in the
canonical D-plus normalization used by etaleComposition. For the pro-etale
site apply the mixed scalar/site pasting identity and the normalized site
squares for the compositor and refinement. Cancel the invertible A-site
comparison and scalar/site balancing. Finally conjugate the input using alpha
and beta: coefficient-map naturality moves the input maps across the scalar
square, and naturality of the canonical geometric comparisons makes the two
conjugations identical. Full faithfulness is used only for bounded etale
origins when changing their presentation. This gives both equations for every
retained witness, including identity witnesses. -/
theorem finiteFree_geometric_squares
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hφ : letI := φ.toAlgebra; Module.Finite A B ∧ Module.Free A B)
    (pro : Bool) {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    {K : Sites.D pro A X}
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (α : (realization pro A X).obj L.obj ≅ K)
    (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (β : (realization pro B X).obj N.obj ≅ (Sites.scalar pro φ X).obj K) :
    (Sites.scalar pro φ Z).map (composition pro A c d e L α) ≫
        coefficientMap pro φ e K =
      coefficientMap pro φ d ((support pro A c).obj K) ≫
        (support pro B d).map (coefficientMap pro φ c K) ≫
          composition pro B c d e N β ∧
    ∀ (c' : Compactification f) (r : c'.Refinement c),
      (Sites.scalar pro φ Y).map (refinement pro A r L α) ≫
          coefficientMap pro φ c K =
        coefficientMap pro φ c' K ≫ refinement pro B r N β := by sorry

end AlgebraicGeometry.FiniteFreeCompactSupport
