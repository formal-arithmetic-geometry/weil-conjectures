module

public import Sheaf.AlgebraicGeometry.TopologicalFormalOpenData
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.FormalAffinePrincipalRefinement
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Open gluing for Noetherian adic formal schemes and ideals

Source: Stacks Project, Tags 0AHY and 01JA, locally topologically ringed spaces
and open gluing (blueprint: lem-per-adic-formal-open-gluing).

The glued underlying ringed space is Mathlib's actual gluing construction.
The theorem supplies its formal section topologies and states descent, uniqueness,
and compatibility with open restriction and refinement, including coherent ideals.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalOpen

/-- Finite Noetherian adic formal gluing, including the empty family and nonaffine overlaps.
Source: Stacks Tags 0AHY, 01JA and 00AL
(blueprint: lem-per-adic-formal-open-gluing).

Proof plan:
1. Form the quotient of the disjoint union by the given transition relation. Diagonal,
   inverse and triple-overlap identities make it an equivalence relation. Its final topology
   makes each piece an open subspace, with exactly the prescribed intersections. This is the
   existing ringed-space gluing construction; no overlap is assumed affine.
2. Glue the sheaves of topological rings by matching tuples with their product-subspace
   topology (lem-per-topological-ring-sheaf-open-descent). Their underlying ring sheaf is the
   existing glued sheaf. Stalks identify with the local stalks of the pieces.
3. Transport the finite formal affine covers of the pieces into the gluing. Their union is
   finite; all complete coordinate rings and quotient-limit sheaves are unchanged
   (def-per-adic-formal-geometry). For an empty family the quotient is empty, its only section
   ring has one element, and the empty atlas is permitted.
4. Glue compatible point maps and section maps to an arbitrary adic formal target. Section
   maps into matching tuples are continuous because all their coordinates are. Stalk maps
   are local because they are the given local maps on pieces. Equality can be checked on
   the cover, giving uniqueness of morphisms and unique isomorphisms between realizations.
5. Define the ideal on each open to consist of the sections whose restrictions belong to
   every piece ideal. Restriction, addition and multiplication preserve this condition;
   the sheaf axiom proves locality. Compatibility recovers each given ideal, and any other
   ideal with those restrictions has the same membership condition, hence is equal.
6. Local finite generators prove coherence. Openness and the condition that ideal powers
   define the topology are local on formal affine charts, so descend by the same argument.
   No uniform exponent on arbitrary opens is asserted.
7. Restrict the quotient, matching tuples, section maps and ideal-membership formula to any
   open. Principal formal opens have Noetherian complete coordinate rings by
   lem-per-formal-affine-principal-refinement and lem-weil-pbc-module-completion-complete.
   Noetherianity selects finitely many principal opens in each original chart
   (def-weil-pbc-noetherian-ring), so every restricted open remains in the finite convention.
8. Repeat on a refined cover. The original object satisfies the refined gluing conditions;
   unique gluing of maps identifies the two objects and their morphisms canonically, and
   equality uniqueness of ideal subsheaves identifies the ideals. A common refinement
   gives the same comparison by uniqueness. `StableDescent` states descent on every open
   and every cover of it, hence includes the restriction and refinement comparisons.
-/
theorem adicFormal_open_gluing (D : GlueData.{u}) :
    ∃ τ : SectionTopology D.data.toGlueData.glued,
      Realizes D D.data.toGlueData.glued τ D.data.toGlueData.ι ∧
      CoverDescent τ D.data.U D.pieceTopology D.data.toGlueData.ι ∧
      StableDescent D.data.toGlueData.glued τ ∧
      ∀ (X : RingedSpace.{u}) (σ : SectionTopology X)
        (v : ∀ i : D.data.J, D.data.U i ⟶ X), Realizes D X σ v →
        ∃! e : D.data.toGlueData.glued ≅ X,
          IsMorphism τ σ e.hom ∧ IsMorphism σ τ e.inv ∧
            ∀ i : D.data.J, D.data.toGlueData.ι i ≫ e.hom = v i := by
  sorry

end AlgebraicGeometry.FormalOpen
