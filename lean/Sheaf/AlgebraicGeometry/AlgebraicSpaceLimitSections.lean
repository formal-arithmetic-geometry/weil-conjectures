module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGlobalFunctions
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Global functions on affine inverse limits of qcqs algebraic spaces

Source: Stacks Project, Spaces Limits, Tag 07SI (lemma-descend-section), in
Situation 084R (situation-descent), specialized to the structure sheaf
(blueprint: lem-sfb-space-limit-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pullback identifies the filtered ring colimit with global functions on the specified
fppf-sheaf limit. Every function descends and equal pullbacks become equal at a later stage.
Source: Stacks Project, Spaces Limits, Tag 07SI, Situation 084R
(blueprint: lem-sfb-space-limit-sections).

Proof:
1. Choose an index 0 and pass to its directed tail. A compatible family extends uniquely
   to the whole system by choosing common upper bounds; this preserves both universal
   properties. Choose one affine etale surjective atlas U_0 -> X_0, using
   lem-trf-space-qc-finite-affine-atlas-refinement, including the empty-space case.
   Its overlap R_0 is a scheme by lem-trf-space-fibre-products-etale-covers and is qcqs
   by lem-sfb-space-qcqs-source-products and lem-weil-pbc-affine-scheme-qcqs.
2. Put U_i = X_i times_{X_0} U_0 and R_i = X_i times_{X_0} R_0. Affine locality
   (lem-sfb-space-affine-locality) makes these schemes with affine transitions; U_i is
   affine and R_i is qcqs. The scheme theorem lem-weil-pbc-limit-affine-transition
   supplies their limits U and R. The atlases U_i -> X_i remain etale surjective.
3. Test on every S-scheme T. The given sheaf-limit universal property identifies
   U = X times_{X_0} U_0, R = X times_{X_0} R_0 and R = U times_X U. Thus U -> X
   is an etale surjective atlas. This uses the assumed limit, not any space-limit theorem.
4. The small etale structure-sheaf axiom identifies global functions on each X_i with
   the equalizer of functions on U_i and R_i, and likewise on X with U and R. Matching
   sections glue on every etale scheme test; uniqueness makes the gluing compatible
   with all arrows. These are ring equalizers and commute with transition pullbacks.
5. Scheme continuity (lem-weil-pbc-limit-global-sections-colimit) represents a function
   on U at a stage U_i. Its overlap defect vanishes on R, hence vanishes on some R_j.
   The equalizer descends it to X_j; injectivity of restriction to U proves that its
   pullback is the original function on X.
6. If two functions at X_i agree on X, their difference restricts to zero on U.
   Scheme continuity makes it zero on some U_j, j >= i. Injectivity of restriction
   from X_j proves eventual equality. Distinct initial indices have a common upper bound.
7. Given compatible ring maps from the stage rings to any ring B, define their extension
   using representatives from step 5. Step 6 proves independence. Common upper bounds
   prove preservation of sums and products, and representatives of 0 and 1 give a unital
   map. Representation proves uniqueness. This is the ring-colimit universal property
   of def-weil-pbc-category-colimit, so the actual canonical map is an isomorphism.
   Cofinality of the tail restores the original index set. -/
theorem globalFunctions_affine_limit
    {S : Scheme.{u}} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ AlgebraicSpace S) (c : Cone D)
    (hc : IsLimit ((ObjectProperty.ι (IsAlgebraicSpace (S := S))).mapCone c))
    (hqc : ∀ i : Iᵒᵖ, ∃ (U : Over S) (a : yoneda.obj U ⟶ (D.obj i).obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : ∀ i : Iᵒᵖ, IsAbsolutelyQuasiSeparated (D.obj i))
    (haff : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), MapIsAffine (D.map f)) :
    IsIso (colimit.desc (D.op ⋙ globalFunctions) (globalFunctions.mapCocone c.op)) ∧
      (∀ a : c.pt.globalFunctionRing,
        ∃ (i : Iᵒᵖ) (aᵢ : (D.obj i).globalFunctionRing),
          globalFunctionMap (c.π.app i) aᵢ = a) ∧
      ∀ (i : Iᵒᵖ) (a b : (D.obj i).globalFunctionRing),
        globalFunctionMap (c.π.app i) a = globalFunctionMap (c.π.app i) b →
          ∃ (j : Iᵒᵖ) (hij : i.unop ≤ j.unop),
            globalFunctionMap (D.map (homOfLE hij).op) a =
              globalFunctionMap (D.map (homOfLE hij).op) b := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
