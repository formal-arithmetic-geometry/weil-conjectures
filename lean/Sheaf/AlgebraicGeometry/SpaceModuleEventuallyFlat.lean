/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.AffineChartRelativeFlatCriterion
import WeilConjectures.AlgebraicGeometry.AffineFlatModuleDescent

/-! # Eventual relative flatness of finitely presented algebraic-space modules

Source: Stacks Project, Limits of Spaces, Tag 08K0, lemma-descend-flat, in Situation
084W; Morphisms of Spaces, Tag 05VW (base change of module flatness)
(blueprint: lem-sfb-space-module-eventually-flat).

The bases are schemes over Spec Z. The displayed presheaf pullback squares specify
all base changes by their universal properties. Relative flatness is expressed on
all etale scheme charts, equivalently by the geometric-stalk condition for these
quasi-coherent modules. No transition is required to be surjective or flat.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finitely presented quasi-coherent module that becomes flat over the affine
limit base is relatively flat over every sufficiently late base.

Source: Stacks, Limits of Spaces, Tag 08K0 (lemma-descend-flat), module assertion in
Situation 084W, with affine bases and finitely presented source; Morphisms of Spaces,
Tag 05VW (blueprint: lem-sfb-space-module-eventually-flat).

Proof:
1. Quasi-compactness of f0 and affineness of its target make X0 quasi-compact.
   By lem-trf-space-qc-finite-affine-atlas-refinement choose an affine surjective
   etale atlas U0 of X0. The chart test lem-sfb-space-local-properties-chart-test,
   with identity target chart, makes U0 to T0 locally finitely presented.
   By lem-weil-pbc-lfp-affine-opens-finite-presentation its coordinate algebra B0
   is finitely presented over R0 = Gamma(T0,O).
2. Restrict M0 to U0. It is quasi-coherent by
   lem-sfb-space-module-pullback-quasicoherent. Local finite presentations restrict
   to the etale slice by lem-trf-space-chart-adjunction-tensor-realization.
   The Zariski/etale comparison lem-trf-scheme-zariski-etale-quasi-coherent-equivalence
   and lem-sfb-scheme-etale-module-exact-finiteness-comparison preserve finite
   presentation. By lem-weil-pbc-quasi-coherent-finite-type-affine its sections N0
   are a finitely presented B0-module.
3. Pull the atlas back along every displayed Cartesian square, using
   lem-trf-space-fibre-products-etale-covers. By lem-weil-pbc-limit-affine-transition
   the limit base is Spec R, with R the filtered colimit of Ri. By
   lem-weil-pbc-fibre-product-affine-spectra the chart rings are Ri tensor_R0 B0
   and R tensor_R0 B0. The composition comparisons of
   lem-trf-space-chart-adjunction-tensor-realization and the scheme comparison in
   step 2 identify the restricted modules with scheme tensor pullbacks.
   By lem-weil-pbc-module-pullback-affine-sections their sections are
   Ni = Ri tensor_R0 N0 and N = R tensor_R0 N0. Here the balancing isomorphism sends
   n tensor (a tensor b) to a tensor bn, with inverse a tensor n to n tensor (a tensor 1).
4. By lem-sfb-space-module-flat-chart-test and
   lem-pc-affine-chart-relative-flat-criterion, limit flatness makes N flat over R.
   Apply lem-pc-affine-flat-module-descent with its first algebra R0, second algebra
   B0 and module N0. Both algebra finiteness conditions and module finite
   presentation hold by steps 1 and 2. The first algebra is presented with zero
   generators and relations. Thus Ni is flat over Ri for every i beyond one j.
5. Apply lem-pc-affine-chart-relative-flat-criterion on each whole affine chart,
   then lem-sfb-space-module-flat-chart-test in the reverse direction. The pulled
   module is flat over the corresponding base on every etale chart, equivalently
   at every geometric stalk. The same j works for all later k. Empty atlases have
   zero coordinate ring and zero section module, so introduce no exception.
-/
theorem module_eventually_flat_of_affineLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))))
    (haff : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left)
    (htrans : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a).left)
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c)) (i0 : I)
    (X0 : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f0 : X0 ⟶ schemeSpace (D.obj (op i0)))
    (hqc : MapIsQuasiCompact f0.hom.hom)
    (hqs : MapIsQuasiSeparated f0.hom.hom)
    (hlfp : MapIsLocallyOfFinitePresentation f0)
    (M0 : X0.Modules) (hMqc : M0.IsQuasicoherent) (hMfp : M0.IsFinitePresentation)
    (Xi : {i : I // i0 ≤ i} → AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (p : ∀ i : {i : I // i0 ≤ i}, Xi i ⟶ X0)
    (fi : ∀ i : {i : I // i0 ≤ i}, Xi i ⟶ schemeSpace (D.obj (op i.val)))
    (sq : ∀ i : {i : I // i0 ≤ i},
      IsPullback (p i).hom.hom (fi i).hom.hom f0.hom.hom
        (yoneda.map (D.map (homOfLE i.property).op)))
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) (q : X ⟶ X0)
    (f : X ⟶ schemeSpace c.pt)
    (sqLimit : IsPullback q.hom.hom f.hom.hom f0.hom.hom
      (yoneda.map (c.π.app (op i0))))
    (hflat : ModuleIsFlatOver f ((moduleTensorPullback q).obj M0)) :
    ∃ (j : I) (hij : i0 ≤ j), ∀ (k : I) (hjk : j ≤ k),
      ModuleIsFlatOver (fi ⟨k, hij.trans hjk⟩)
        ((moduleTensorPullback (p ⟨k, hij.trans hjk⟩)).obj M0) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
