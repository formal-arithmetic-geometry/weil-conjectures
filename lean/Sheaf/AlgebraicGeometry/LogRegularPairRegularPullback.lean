/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.FSStrictLogMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber

import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.RingTheory.Flat.Stability
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.TraceFormula.LogRegularDivisorialStructure

/-!
# Regular pullback of a divisorial log regular pair

Source: ILO, Exposé VI 1.1--1.4, printed p.69, and VII 3.2, printed p.82;
Stacks Project, Tags 031E and 00ON
(blueprint: lem-per-log-regular-pair-regular-pullback).

The boundary is the complement of `U`. Its inverse image is the complement of
`g ⁻¹ᵁ U`. Strictness uses the recorded canonical characteristic-map criterion
for being the associated inverse-image log structure. Both divisorial
identifications commute with the structural maps, so neither identification
nor the inverse-image log structure is replaced by an arbitrary abstract object.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Regular pullback preserves divisorial fs log regular pairs, with the associated
inverse-image log structure and its structural divisorial identification.
Source: ILO VI 1.1--1.4, VII 3.2; Stacks 031E and 00ON
(blueprint: lem-per-log-regular-pair-regular-pullback).

Proof:
1. Pull back the monoid sheaf of the divisorial structure on X to a prelog
sheaf H on Y. On each etale V, form the actual pushout of H(V) with the units
of Gamma(V,O) over the elements of H(V) mapping to units. Sheafify this
commutative-monoid presheaf. The prelog-pushout log-axiom and hom-extension
lemmas identify the resulting log structure N with the associated log structure:
a compatible map to any log structure extends uniquely by [m,u] mapping to i(m)u.
Use lem-trf-commutative-monoid-sheafification,
lem-trf-prelog-pushout-log-axiom and lem-trf-prelog-pushout-hom-extension.
2. At a geometric y, the strict-local map A to C is flat local between
Noetherian local rings and has regular closed fibre F, by
lem-per-regular-geometric-stalk-map. Inverse-image and sheafification stalk
formulas give N_y = M_x plus_{A units} C units. For the pushout formula,
represent its finitely many germs, inverses and congruence relations on a
common pointed etale neighbourhood. Locality reflects units, so precisely the
A-unit elements become C-units. Use the inverse-image-stalk-germ and
sets-sheafification-geometric-stalk lemmas.
3. Pull back an fs chart Q on an etale W over X to Y times_X W. The latter
is etale over Y by lem-weil-pbc-etale-base-change-finite-limits. At every stalk,
(Q plus_E A units) plus_{A units} C units = Q plus_E C units,
via [[q,a],c] mapping to [q,h(a)c] and inverse [q,c] mapping to [[q,1],c].
Locality identifies E with the inverse image of C-units. Thus these are fs
charts for N; no finite-presentation hypothesis on g is needed.
4. Choose a sharp chart P at x by lem-trf-log-regular-sharp-chart. Then
M_x = P plus A units and N_y = P plus C units, so the canonical map on
characteristics is an isomorphism. This gives the graph-normalized strictness
of the resulting log morphism. The nonunit ideal I in A extends to J = IC
in C. Log regularity on X gives regularity of A/I and dim A = dim(A/I) + rank P.
5. By lem-weil-pbc-flat-module-quotient-flat, A/I to C/J is flat local, with
closed fibre F. The rings are Noetherian local. Apply
lem-weil-pbc-flat-over-regular-with-regular-fibre to obtain regularity of C/J.
6. The flat local dimension formula lem-weil-pbc-flat-height-formula gives
both dim C = dim A + dim F and dim(C/J) = dim(A/I) + dim F.
Substitution gives dim C = dim(C/J) + rank P, hence log regularity of N.
7. The characteristic calculation identifies the triviality locus with g inverse U.
Apply lem-trf-log-regular-divisorial-structure: this open is dense and N is
canonically its divisorial log structure via the structural map. Consequently
its closed complement is nowhere dense and the pulled-back pair satisfies the
recorded divisorial-pair predicate. The construction identifies the source
log structure with its divisorial presheaf in the same structural manner.
For empty Y all stalk conditions are vacuous and its empty open is dense.
For empty boundary P is trivial, the log structures are the units, and this
argument is ordinary regular ascent. Neither case is excluded. -/
theorem logRegularPair_regularPullback
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (g : Y ⟶ X) [Flat g]
    (hg : ∀ (x : X) (K : Type u) [Field K] [Algebra (X.residueField x) K]
      [Module.Finite (X.residueField x) K],
      IsRegularScheme (pullback (g.fiberToSpecResidueField x)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)))))
    (U : X.Opens) (hU : DenseRange U.ι)
    (hpair : IsDivisorialFineSaturatedLogRegularPair X U.toScheme U.ι hU) :
    ∃ hV : DenseRange (g ⁻¹ᵁ U).ι,
      IsDivisorialFineSaturatedLogRegularPair Y (g ⁻¹ᵁ U).toScheme (g ⁻¹ᵁ U).ι hV ∧
        ∃ (MX : EtaleLogStructure X) (MY : EtaleLogStructure Y)
          (fsX : MX.IsFineSaturated) (fsY : MY.IsFineSaturated)
          (eX : MX.monoidSheaf.obj ≅ divisorialLogPresheaf U.ι)
          (eY : MY.monoidSheaf.obj ≅ divisorialLogPresheaf (g ⁻¹ᵁ U).ι)
          (f : EtaleLogHom ⟨Y, inferInstance, MY, fsY⟩ ⟨X, inferInstance, MX, fsX⟩),
          eX.hom ≫ divisorialStructuralMap U.ι = MX.alpha ∧
          eY.hom ≫ divisorialStructuralMap (g ⁻¹ᵁ U).ι = MY.alpha ∧
          f.base = g ∧ f.IsStrict ∧
          (FineSaturatedLogScheme.mk Y inferInstance MY fsY).IsLogRegular ∧
          MY.trivialityLocus = (g ⁻¹ᵁ U : Set Y) := by
  sorry

end AlgebraicGeometry
