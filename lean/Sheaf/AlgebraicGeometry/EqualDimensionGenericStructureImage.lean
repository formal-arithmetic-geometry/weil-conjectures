module

public import Sheaf.TraceFormula.LocalDimensionFormula
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Sheaf.TraceFormula.FiniteResiduePointClosedInFibre
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOpenRestriction

/-!
# Generic structure-sheaf image in equal dimension

Source: Stacks Project, Tags 0A21, 02NW, 01Y6, and the generic-image paragraph of
Tag 0BET (blueprint: lem-sfb-equal-dimension-generic-structure-image).

The field module below bundles the already recorded canonical function-field algebra.
The isomorphism in the statement is fixed on every section germ, not chosen freely.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The source function field as a module over the target function field, through the
actual generic stalk pullback `f.dominantFunctionFieldAlgebra`.
Source: Stacks Project, Tags 01RW and 0BET
(blueprint: lem-sfb-equal-dimension-generic-structure-image). -/
def Scheme.Hom.dominantFunctionFieldModule
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : ModuleCat.{u} Y.functionField :=
  @ModuleCat.of Y.functionField _ X.functionField _ f.dominantFunctionFieldAlgebra.toModule

/-- A proper dominant map of equal-dimensional integral finite-type schemes is finite
on a nonempty open, has no positive higher structure-sheaf images there, and its canonical
generic direct-image stalk is the source function field with the actual pullback action.
Source: Stacks Project, Tags 0A21, 02NW, 01Y6 and the generic-image paragraph of Tag 0BET
(blueprint: lem-sfb-equal-dimension-generic-structure-image).

Proof:
1. Put K = k(Y), L = k(X), with the algebra of def-sfb-dominant-function-field-map.
   The generic local rings are their residue fields by
   lem-sc-integral-function-field-affine-fraction. Apply
   lem-sc-closed-irreducible-dimension-trdeg to X and Y and then
   lem-kun-transcendence-degree-tower: g = g + trdeg_K L. Since g is finite,
   trdeg_K L = 0, so L/K is algebraic.
2. Choose affine neighborhoods of the two generic points with the source inside the
   inverse image of the target. Properness gives local finite type; by
   lem-weil-pbc-lft-affine-pairs the source ring has finitely many algebra generators.
   The compatible generic germs identify the two function fields with fraction fields
   by lem-sc-integral-function-field-affine-fraction. Thus these generators also generate
   L as a field over K. They are algebraic by Step 1, so
   lem-weil-pbc-algebraic-generators-finite-extension makes L/K finite, including no generators.
3. By lem-trf-finite-residue-point-closed-in-fibre the source generic point is closed in
   the generic fibre. The fibre topology is the subspace topology by def-pc-scheme-fibre.
   Every point of X specializes from its generic point, so this closed point is the
   whole generic fibre.
4. A field and its spectrum are Noetherian. By lem-weil-pbc-finite-type-over-noetherian,
   X and Y are Noetherian, and lem-weil-pbc-locally-noetherian-quasi-separated and
   lem-weil-pbc-qcqs-morphism-permanence give quasi-separatedness of f. Properness gives
   quasi-compactness and local finite type. The generic fibre is a singleton by Step 3;
   lem-weil-pbc-generic-finite-morphism-open-neighborhood gives a nonempty finite open.
5. A finite map is affine and the structure sheaf is quasi-coherent (pqf-def-coherent).
   Apply lem-weil-pbc-affine-morphism-cohomology-edge on this open, and
   lem-pc-higher-direct-image-open-restriction, to obtain positive higher-image vanishing.
6. For every neighborhood W of the source generic point, properness makes f(X minus W)
   closed. By Step 3 it avoids the target generic point. Its complement V is therefore
   a target generic neighborhood with inverse image contained in W. Such inverse images
   refine every neighborhood of the source generic point.
7. Send a direct-image germ to its source generic germ (def-weil-pbc-module-stalk).
   Step 6 gives surjectivity by restricting representatives, and injectivity by shrinking
   wherever a representative with zero germ vanishes. This gives the canonical bijection.
8. Scalar multiplication is the sectionwise product through f-sharp
   (def-pc-module-pullback). Taking germs gives exactly f-star on function fields
   (def-sfb-dominant-function-field-map), so this bijection is K-linear. Transport a
   basis to obtain the equality of finite dimensions and hence the extension degree. -/
theorem Scheme.Hom.equalDimension_generic_structure_image
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] [IsDominant f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (g : ℕ) (hX : topologicalKrullDim X = (g : WithBot ℕ∞))
    (hY : topologicalKrullDim Y = (g : WithBot ℕ∞)) :
    FiniteDimensional Y.functionField f.dominantFunctionFieldModule ∧
      (∃ U : Y.Opens, Nonempty U ∧ IsFinite (f ∣_ U) ∧
        ∀ i : ℤ, 0 < i → IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
          ((schemeModuleHigherDirectImage f i).obj (Scheme.Modules.unit X)))) ∧
      (∃ e : ((Scheme.Modules.pushforward f).obj
          (Scheme.Modules.unit X)).presheaf.stalk (genericPoint Y) ≃ₗ[Y.functionField]
            f.dominantFunctionFieldModule,
        ∀ (V : Y.Opens) (hηY : genericPoint Y ∈ V)
          (hηX : genericPoint X ∈ f ⁻¹ᵁ V) (s : Γ(X, f ⁻¹ᵁ V)),
          e (((Scheme.Modules.pushforward f).obj (Scheme.Modules.unit X)).presheaf.germ
            V (genericPoint Y) hηY s) =
              X.presheaf.germ (f ⁻¹ᵁ V) (genericPoint X) hηX s) ∧
      Module.finrank Y.functionField
          (((Scheme.Modules.pushforward f).obj (Scheme.Modules.unit X)).presheaf.stalk
            (genericPoint Y)) =
        Module.finrank Y.functionField f.dominantFunctionFieldModule := by
  sorry

end AlgebraicGeometry
