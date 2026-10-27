/-
Copyright (c) 2026 SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
import WeilConjectures.AlgebraicGeometry.FiniteAffineFibreSections
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Constant Hilbert polynomial and finite locally free families

Source: Stacks Project, Tags 02LS, 02KB, 08AE and 0B3J.
(blueprint: lem-sfb-constant-hilbert-finite-locally-free)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- For a flat finitely presented closed family in projective space, constant fibre
Hilbert polynomial `d` characterizes finite local freeness of degree `d`, equivalently
finiteness with structure-sheaf pushforward locally free of rank `d`. Degree zero means
empty source, also over the empty base. The polynomial predicate is applied to identity
base change and the zero ideal, so its closed family is canonically the original family.
Source: Stacks Project, Tags 02LS, 02KB, 08AE and 0B3J.
(blueprint: lem-sfb-constant-hilbert-finite-locally-free)

Proof:
1. The embedding makes the structure morphism projective and proper. Identify each
   residue fibre's projective embedding with Proj of the polynomial ring by
   lem-nagata-affine-proj-scalar-extension and lem-weil-pbc-polynomial-scalar-extension.
   The field coordinate/Euler polynomial theorem and Hilbert dimension theorem identify
   its eventual Euler polynomial with the geometric coordinate Hilbert polynomial;
   both are zero for an empty fibre.
2. A nonempty fibre with constant polynomial has dimension zero by
   lem-sfb-projective-hilbert-polynomial-dimension, and is locally Noetherian and
   quasi-compact by lem-sfb-projective-field-coordinate-euler-polynomial. The
   zero-dimensional discrete-topology lemma makes its point set finite. For `d = 0`,
   every fibre is empty since a nonempty fibre has nonzero Hilbert polynomial.
3. The fibre projection identifies these point sets with the set-theoretic fibres.
   pqf-lem-locqf-fibre-discrete gives local quasi-finiteness. Properness and
   pqf-lem-proper-lqf-finite give finiteness over the unrestricted base.
4. Apply lem-sfb-coherent-zero-dimensional-support to the structure sheaf of each
   nonempty fibre. Higher cohomology vanishes, so evaluating its Euler polynomial at
   zero gives dimension of global sections equal to `d`. Empty fibres have zero sections.
   Together with flatness and local finite presentation this is the recorded definition
   of finite locally free degree. lem-pc-flf-properties gives the pushforward rank.
5. Conversely, finite local freeness gives finiteness and fibre section dimension `d`.
   pqf-lem-finite-qf and pqf-lem-qf-finitefibres give finite fibres; the finite-fibre
   criterion makes them discrete. Their topological Krull dimension is zero when
   nonempty, so the Hilbert dimension theorem makes the polynomial constant.
6. The same coherent-support vanishing at twist zero identifies that constant with `d`.
   On empty fibres the dimension condition forces `d = 0` and the polynomial is zero.
7. Conversely to the pushforward description, on an affine trivializing open the finite
   algebra is free of rank `d`. lem-pc-finite-affine-fibre-sections identifies its fibre
   sections with its tensor product with the residue field, of dimension `d`.
8. An empty base forces empty source, and all pointwise rank conditions are vacuous.
   For `d = 0`, all fibres are empty, hence the source is empty. Conversely the empty
   source has zero polynomial and finite flat finitely presented structure morphism;
   its pushforward is the zero module, free of rank zero.
-/
theorem constant_hilbertPolynomial_iff_finiteLocallyFree
    {Z T : Scheme.{u}} (n d : ℕ)
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) [IsClosedImmersion i]
    [Flat (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T))]
    [LocallyOfFinitePresentation (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T))]
    [QuasiCompact (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T))]
    [QuasiSeparated (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T))] :
    (HasProjectiveFibreHilbertPolynomial
      (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T)) i (Over.mk (𝟙 T)) ⊥
        (Polynomial.C (d : ℚ)) ↔
      (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T)).IsFiniteLocallyFreeOfDegree d) ∧
    ((i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T)).IsFiniteLocallyFreeOfDegree d ↔
      IsFinite (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T)) ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pushforward
            (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T))).obj
              (SheafOfModules.unit Z.ringCatSheaf)) d) ∧
    (d = 0 →
      ((i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T)).IsFiniteLocallyFreeOfDegree d ↔
        IsEmpty Z)) := by
  sorry

end AlgebraicGeometry
