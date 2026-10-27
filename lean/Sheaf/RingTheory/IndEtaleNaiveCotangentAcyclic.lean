/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.EtaleRingMapConormalCriterion
import Mathlib.RingTheory.Kaehler.Polynomial
import Sheaf.RingTheory.PresentationsHomotopyEquivalent
import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Acyclicity of the naive cotangent complex of an ind-etale algebra

Source: Stacks Project, Algebra, Tags 07BQ and 00U1; More on Algebra,
lemma-henselization-NL, first paragraph
(blueprint: lem-sfb-ind-etale-naive-cotangent-acyclic).

`Generators.self R S` is the canonical presentation `R[S] → S`. Its Mathlib
cotangent differential has target `S ⊗[R[S]] Ω[R[S]/R]`, with the canonical
basis `Generators.cotangentSpaceBasis` identifying it with the free module on
all elements of `S`. Its formula on a conormal class is `1 ⊗ dg`.

The cone of this differential between degree-zero single complexes is the
same two-term complex in cohomological degrees `-1,0`, under the canonical
biproduct-with-zero identifications. This uses Mathlib's existing cone and
canonical presentation, with no new cotangent-complex definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Algebra

/-- The canonical naive cotangent differential of an ind-etale algebra is an
isomorphism, its cohomology in degrees minus one and zero vanishes, and its
image in the derived category is isomorphic to zero.
Source: Stacks Project, Algebra, Tags 07BQ and 00U1; More on Algebra,
lemma-henselization-NL, first paragraph
(blueprint: lem-sfb-ind-etale-naive-cotangent-acyclic).

Proof for stage 3:
1. By def-weil-pbc-ind-etale-algebra choose a small filtered presentation by
finitely presented etale algebras. At each stage choose a finite polynomial
presentation, using def-weil-pbc-finitely-presented-algebra. The differential
of this presentation is invertible by
lem-weil-pbc-etale-ring-map-conormal-criterion.
2. Identify the free differential modules and their differential formulas by
lem-weil-pbc-polynomial-ring-kahler-basis-any-variables. Apply
lem-weil-pbc-nl-presentations-homotopy-equivalent to compare each finite
presentation with the canonical presentation on all elements. If d is the
finite-presentation differential and delta the canonical differential, the
homotopies give s = phi_1 d^{-1} psi_0 + h', with s delta = 1 and delta s = 1.
Thus every canonical stage differential is invertible.
3. Use lem-sfb-filtered-colimit-naive-cotangent-comparison and the degreewise
colimit of the stage complexes as R-modules. The inverses of the stage
differentials commute with every transition map: multiply the chain-map
identity on both sides by the inverse differentials. The colimit universal
property (def-weil-pbc-category-colimit) therefore gives an inverse to its
differential. No flatness or exactness hypothesis is introduced here.
4. The colimit comparison is a quasi-isomorphism, so the canonical complex
has vanishing kernel and cokernel. Thus its S-linear differential is
bijective, hence an isomorphism; its inverse is S-linear by uniqueness of
preimages. The cone of the degree-zero single map represents exactly this
two-term complex, so its homology in degrees minus one and zero is zero.
All its other cohomology objects vanish because the other terms vanish.
Consequently its map to zero is a quasi-isomorphism and is inverted by
DerivedCategory.Q, as in def-weil-abstract-derived-category. The hypothesis
on ind-etaleness uses the recorded canonical universe transport; transporting
the polynomial presentation along the ULift equivalences changes none of
these module or cohomology calculations. -/
theorem indEtale_naiveCotangent_acyclic
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} S)]
    (h : RingHom.IndEtaleAcrossUniverses (algebraMap R S)) :
    Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone
      ((HomologicalComplex.single (ModuleCat.{max u v} S) (.up ℤ) 0).map
        (ModuleCat.ofHom (Generators.self R S).toExtension.cotangentComplex))) ≅ 0) ∧
    IsIso (ModuleCat.ofHom (Generators.self R S).toExtension.cotangentComplex) ∧
    IsZero ((CochainComplex.mappingCone
      ((HomologicalComplex.single (ModuleCat.{max u v} S) (.up ℤ) 0).map
        (ModuleCat.ofHom (Generators.self R S).toExtension.cotangentComplex))).homology (-1)) ∧
    IsZero ((CochainComplex.mappingCone
      ((HomologicalComplex.single (ModuleCat.{max u v} S) (.up ℤ) 0).map
        (ModuleCat.ofHom (Generators.self R S).toExtension.cotangentComplex))).homology 0) := by
  sorry

end Algebra
