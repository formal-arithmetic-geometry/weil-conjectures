module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration
import WeilConjectures.AlgebraicGeometry.CoherentSerreVanishing
import WeilConjectures.Algebra.Homology.ModuleStalkExact

/-! # Eventual first-jet interpolation on an ample smooth curve

Source: Stacks Project, Coherent, Tag 02O1; Properties, Tag 01Q3 (1) to (7);
Cohomology, Tag 01DZ. The prescribed-jet deduction is the agent argument in
`lem-sfb-separating-pair-open`, steps 4--5.
(blueprint: lem-sfb-ample-curve-first-jet-interpolation)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSectionAdjunction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000 in
-- The explicit unit composite elaborates the tensor pullback and its inverse-image top.
/-- High powers of an ample invertible module interpolate all first jets on a fixed finite
set of rational closed points of a smooth proper integral curve. The chosen point `x : T`
expresses nonemptiness. The closed subset `T`, together with its finiteness and closed-point
condition, is the set of marked points; distinctness is intrinsic to a subset. Over the
algebraically closed field every such closed point is rational.

The first-jet subscheme is `V(vanishingIdeal T ^ 2)`. Its stalk-map kernels are the squares
of the ambient maximal ideals, so its local rings are the specified quotients. A component
frame is an equivalence from `R_y / m_y²` to `L_y / m_y² L_y`, linear over `R_y`; this is
equivalently a basis of rank one over `R_y / m_y²`. Its inverse computes coefficients.
The final two clauses express simple vanishing and nonvanishing without choosing a lift
of a component frame to the local ring.

Source: Stacks Project, Coherent, Tag 02O1; Properties, Tag 01Q3 (1) to (7);
Cohomology, Tag 01DZ; Algebra, Tag 00PD.
(blueprint: lem-sfb-ample-curve-first-jet-interpolation)

Proof:
1. The field is Noetherian. Finite type over it makes D Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Its structure module is coherent by
   pqf-lem-coherent-ft-locnoeth. The closed-immersion ideal is quasi-coherent by
   def-sbc-closed-immersion-ideal-sheaf and coherent by clause (2) of
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth.
2. Integrality gives connectedness and nonemptiness. Smoothness and dimension one give
   regular local domains by lem-sc-smooth-regular. Lemma lem-sc-point-cartier makes each
   marked maximal ideal principal and nonzero. Apply
   lem-weil-pbc-dvr-unit-times-uniformizer-power; cancellation shows uniqueness of the
   exponent, since otherwise a unit belongs to the maximal ideal. The square of the
   reduced ideal has stalk m_y² at y in T and the unit ideal off T. Thus its subscheme
   has support T, the stated quotient local rings, and is finite over the field.
3. Apply lem-weil-pbc-coherent-twist-global-generation to the structure module, identifying
   its tensor with A^n with A^n. This gives one global-generation bound for all large n.
4. Apply lem-weil-pbc-coherent-serre-vanishing to the fixed coherent ideal of Z. Take the
   maximum of its bound, the preceding bound, and 1. Then H¹(I_Z tensor A^n) vanishes
   for every n at least that maximum.
5. In local frames, ideal multiplication and tensor restriction are the sequence
   0 -> m_y² -> R_y -> R_y/m_y² -> 0 at a marked point, and
   0 -> O -> O -> 0 -> 0 elsewhere. Changes of frame multiply by a unit, so the maps
   glue; lem-weil-pbc-module-stalk-exact gives the short exact sequence
   0 -> I_Z tensor A^n -> A^n -> i_*(i^* A^n) -> 0.
6. The long exact sequence of pqf-def-cohomology and the preceding H¹ vanishing make
   global restriction surjective. Direct image has the same global sections as on Z.
7. The finite support is discrete. For each given component frame take coefficient
   u modulo m_x² at x and coefficient 1 at every other marked point. Glue these
   sections over the disjoint singleton components, and lift by the surjection.
8. A component frame lifts to a local frame since a unit modulo m_y² lifts to a unit
   in R_y. At x the lifted coefficient is u + c u² = u(1+cu), which belongs to
   m_x minus m_x²: cancellation would otherwise make u a unit. At every other point
   the coefficient is 1 modulo m_y² and therefore a unit. These assertions are
   unchanged by multiplying a frame by a unit. -/
theorem exists_ample_curve_first_jet_interpolation
    (k : Type u) [Field k] [IsAlgClosed k]
    (D : Scheme.{u}) [D.Over (Spec (.of k))]
    [Smooth (D ↘ Spec (.of k))] [IsProper (D ↘ Spec (.of k))] [IsIntegral D]
    (hdim : topologicalKrullDim D = 1)
    (A : D.Modules) [A.IsInvertible] (hA : IsAmple D A)
    (T : TopologicalSpace.Closeds D) (hT : (T : Set D).Finite)
    (hclosed : ∀ y : T, IsClosed ({y.val} : Set D)) (x : T) :
    (∀ y : T, IsDiscreteValuationRing (D.presheaf.stalk y.val)) ∧
    (Scheme.IdealSheafData.vanishingIdeal T ^ 2).support = T ∧
    IsFinite ((Scheme.IdealSheafData.vanishingIdeal T ^ 2).subschemeι ≫
      (D ↘ Spec (.of k))) ∧
    (∀ z : (Scheme.IdealSheafData.vanishingIdeal T ^ 2).subscheme,
      RingHom.ker ((Scheme.IdealSheafData.vanishingIdeal T ^ 2).subschemeι.stalkMap z).hom =
        IsLocalRing.maximalIdeal (D.presheaf.stalk
          ((Scheme.IdealSheafData.vanishingIdeal T ^ 2).subschemeι z)) ^ 2) ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      Nonempty (SheafOfModules.GeneratingSections (A.tensorPow n)) ∧
      IsZero ((RingedSpace.moduleCohomology D.toRingedSpace 1).obj
        (tensorObj (Scheme.IdealSheafData.vanishingIdeal T ^ 2).toModules (A.tensorPow n))) ∧
      Function.Surjective
        (((tensorPullbackSectionAdjunction
          (Scheme.IdealSheafData.vanishingIdeal T ^ 2).subschemeι).unit.app
            (A.tensorPow n)).app ⊤ ≫
          ((tensorPullback (Scheme.IdealSheafData.vanishingIdeal T ^ 2).subschemeι).obj
            (A.tensorPow n)).presheaf.map
              (homOfLE
                (Scheme.IdealSheafData.vanishingIdeal T ^ 2).subschemeι.preimage_top.ge).op :
          Γ(A.tensorPow n, ⊤) ⟶
            Γ((tensorPullback (Scheme.IdealSheafData.vanishingIdeal T ^ 2).subschemeι).obj
              (A.tensorPow n), ⊤)) ∧
      ∀ (e : ∀ y : T,
        ((D.presheaf.stalk y.val) ⧸ IsLocalRing.maximalIdeal (D.presheaf.stalk y.val) ^ 2)
          ≃ₗ[D.presheaf.stalk y.val]
        (↑(TopCat.Presheaf.stalk (A.tensorPow n).val.presheaf y.val) ⧸
          (IsLocalRing.maximalIdeal (D.presheaf.stalk y.val) ^ 2 •
            (⊤ : Submodule (D.presheaf.stalk y.val)
              ↑(TopCat.Presheaf.stalk (A.tensorPow n).val.presheaf y.val)))))
        (v : D.presheaf.stalk x.val),
        IsLocalRing.maximalIdeal (D.presheaf.stalk x.val) = Ideal.span {v} →
        ∃ a : Γ(A.tensorPow n, ⊤),
          (e x).symm (Submodule.Quotient.mk
            ((TopCat.Presheaf.germ (A.tensorPow n).val.presheaf ⊤ x.val trivial) a)) =
              Ideal.Quotient.mk _ v ∧
          (∀ y : T, y ≠ x →
            (e y).symm (Submodule.Quotient.mk
              ((TopCat.Presheaf.germ (A.tensorPow n).val.presheaf ⊤ y.val trivial) a)) = 1) ∧
          (TopCat.Presheaf.germ (A.tensorPow n).val.presheaf ⊤ x.val trivial) a ∈
            IsLocalRing.maximalIdeal (D.presheaf.stalk x.val) •
              (⊤ : Submodule (D.presheaf.stalk x.val)
                ↑(TopCat.Presheaf.stalk (A.tensorPow n).val.presheaf x.val)) ∧
          (TopCat.Presheaf.germ (A.tensorPow n).val.presheaf ⊤ x.val trivial) a ∉
            IsLocalRing.maximalIdeal (D.presheaf.stalk x.val) ^ 2 •
              (⊤ : Submodule (D.presheaf.stalk x.val)
                ↑(TopCat.Presheaf.stalk (A.tensorPow n).val.presheaf x.val)) ∧
          ∀ y : T, y ≠ x → y.val ∈ nonvanishingLocus (A.tensorPow n) a := by
  sorry

end AlgebraicGeometry.Scheme.Modules
