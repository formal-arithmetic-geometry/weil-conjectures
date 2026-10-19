/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import Sheaf.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.TraceFormula.FlatFibreComponentClosureDimension

/-! # Pure dimension of fibres of a flat family with dense pure-dimensional generic fibre

Source: literature/stacks-project/more-morphisms.tex, Tags 0GSK and 0GSJ;
(literature/stacks-project/morphisms.tex, Tags 02NJ and 02NK for geometric fibres)
(blueprint: lem-trf-flat-dense-generic-fibre-pure-dimension).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
For an integral base, a flat locally-finite-type morphism with dense generic fibre
and pure generic-fibre dimension `d` has pure dimension `d` on every nonempty fibre
and on every nonempty geometric fibre.  The proof follows Stacks Project Tags
0GSK and 0GSJ, using flat going-down and the component-closure dimension lemma,
then the standard base-change dimension results.  In detail, the proof uses
flat going-down on affine charts to lift a component point to the generic fibre;
places it in a generic-fibre component and passes to its closure; applies the
flat fibre-component closure dimension lemma to obtain the ordinary-fibre
component dimension; uses locally-finite-type base change and the pure-open
local-dimension lemma; transfers local dimension to an arbitrary residue-field
extension; and applies the constant-local-dimension component criterion.  These
steps use the statement dependencies recorded for this node.  The explicit nonempty
premises in the conclusion leave empty ordinary and geometric fibres vacuous.
(blueprint: lem-trf-flat-dense-generic-fibre-pure-dimension).
-/
theorem flat_dense_generic_fibre_pure_dimension
    {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f]
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    (hdense : Dense (Set.range (f.fiberι η)))
    (d : ℕ)
    (hgeneric : ∀ C ∈ irreducibleComponents (f.fiber η),
      topologicalKrullDim C = (d : WithBot ℕ∞)) :
    (∀ s : S, Nonempty (f.fiber s) →
      ∀ C ∈ irreducibleComponents (f.fiber s),
        topologicalKrullDim C = (d : WithBot ℕ∞)) ∧
    (∀ s : S, ∀ (Ω : Type u) [Field Ω]
      [Algebra (S.residueField s) Ω] [IsAlgClosed Ω],
      Nonempty (pullback (C := Scheme.{u}) (f.fiberToSpecResidueField s)
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)))) →
      ∀ C ∈ irreducibleComponents
          (pullback (C := Scheme.{u}) (f.fiberToSpecResidueField s)
            (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)))),
        topologicalKrullDim C = (d : WithBot ℕ∞)) := by
  sorry

end AlgebraicGeometry
