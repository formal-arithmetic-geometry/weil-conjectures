module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.FieldSpecializationTrdegDrop
import Sheaf.AlgebraicGeometry.StackPointTopology
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite

/-! # Étale charts of discrete Deligne--Mumford stacks over fields

Source: Stacks Project, Morphisms of Algebraic Stacks, Tag 06UC,
`lemma-locally-quasi-finite-over-field`, specialized to étale scheme charts
(blueprint: lem-sfb-dm-field-etale-chart-quasifinite).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Every étale scheme chart of a locally finite type DM stack over a field with discrete
point space is locally quasi-finite over that field. The chart need not be surjective.
The map `f` specifies the field structure of `Z` over `S`; `e` identifies `p` with the
composite of the chart and this specified structure map. The intrinsic local finite type
predicate uses étale atlases of scheme base changes, equivalently smooth charts for DM
stacks. The point topology is the existing smooth-atlas topology.

Source: Stacks Project, Tag 06UC, proof specialized to étale scheme charts
(blueprint: lem-sfb-dm-field-etale-chart-quasifinite).

Proof:
1. The chart is smooth and locally of finite type by
   lem-sfb-stack-chartwise-smooth-etale-calculus. By lem-sfb-stack-finite-type-calculus,
   its composite `p.left` is locally of finite type. The relation `R = A ×_Z A` is an
   algebraic space with étale projections by lem-sfb-dm-etale-atlas-calculus. These
   constructions do not require surjectivity of the chart.
2. If `p.left` were not locally quasi-finite,
   lem-sfb-field-nonquasifinite-specialization would give distinct specializations
   `x` to `x'`. By lem-sfb-field-specialization-trdeg-drop their residue transcendence
   degrees strictly decrease. Continuity from lem-sfb-stack-point-topology and
   discreteness of the point space of `Z` imply that their image classes coincide.
3. The two residue-field representatives become isomorphic over a common field
   extension. Their maps and that isomorphism give an object of `R`, hence a point `r`
   whose two projections are `x` and `x'` (Stacks 04XH and the defining triples in
   def-sfb-stable-pointed-moduli-groupoids).
4. By lem-a1-space-affine-etale-cover choose an étale scheme chart `W` of `R` and a
   point above `r`. Both projections of `R` are locally quasi-finite by
   lem-a1-etale-space-locally-quasi-finite. Apply
   lem-sfb-space-quasifinite-trdeg-comparison to each projection using this same
   chart and point. The residue transcendence degrees at `x` and `x'` are equal.
5. This contradicts the strict decrease in step 2. Therefore `p.left` is locally
   quasi-finite. This argument includes the empty chart, where the conclusion is vacuous.
-/
theorem dm_field_etale_chart_isLocallyQuasiFinite
    {S : Scheme.{u}} (k : Type u) [Field k] (s : Spec (.of k) ⟶ S)
    (Z : BasedCategory.{v, w} (Over S))
    (f : BasedFunctor Z (discreteModuli (yoneda.obj (Over.mk s))))
    (hZ : IsDeligneMumfordModuliStack Z) (hft : IsLocallyFiniteTypeModuliMap f)
    [DiscreteTopology (ModuliPoints Z)]
    (A : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj A)) Z)
    (ha : IsEtaleModuliMap a) (p : A ⟶ Over.mk s)
    (e : ModuliTwoIso (a.comp f) (discreteModuliMap (yoneda.map p))) :
    Scheme.Hom.IsLocallyQuasiFinite p.left := by
  sorry

end CategoryTheory
