/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ZlImmersionWeilLocalData
import WeilConjectures.AlgebraicGeometry.ZlImmersionRestrictionAssembly
import WeilConjectures.AlgebraicGeometry.ZlOpenExtensionAssembly

/-! # Exact immersion operations and local Frobenius on Weil stalks
Source: the Restriction paragraph and Part 2 of open--closed reduction.
(blueprint: lem-zl-immersion-weil-local-behavior). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Endofunctor
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  {W₀ X₀ U₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
/-- Pullback along a locally closed immersion and open extension by zero are exact
on the constructible Weil hearts, commute with all cohomology as Weil functors, and
have the specified Frobenius-equivariant stalks. The geometric residue maps are
isomorphisms; equality of their degrees records the identical residue-field size.

Source: main-20261015, sec-deligne-laumon-general/sk-l-dl-general-excision,
lem-zl-morphism-open-closed-reduction.proof.md, Restriction and Part 2
(blueprint: lem-zl-immersion-weil-local-behavior).

Proof, following the eleven steps of the DAG node:
1. Represent the finitely many Weil arrows, inverses and inverse equations over a
common finite coefficient field. No Frobenius-stable integral lattice is required.
2. Apply lem-a1-constructible-pullback-t-exact to h and to geometric Frobenius.
The two rationalized integral composition comparisons across g_X h = h g_W give
alpha, and the induced structure is alpha followed by h-star(theta).
3. Uniqueness of truncation triangles gives the Weil cohomology comparisons, with
exactly the underlying canonical truncation maps in comparison.cohomology.
4. Factor h₀ as closed then open. The closed map quotients the local ring; the open
map identifies local rings. Their residue maps are isomorphisms. A closed point
has finite residue field, so its image is closed, with the same positive degree.
5. The inverse pullback-composition comparison at compatible geometric points,
followed by the recorded point fibre, is the normalized stalk comparison.
6. Expand the iterated induced Weil structure. Associativity of the integral
composition comparisons and naturality of point transport identify each of the
three factors in local geometric Frobenius, giving the stated operator equation.
7. X is Noetherian, so j is quasi-compact. Use the compactification (j,id). The
integral open reduction comparison identifies compact support with termwise exact
extension by zero, preserves completeness and constructibility, and gives t-exactness.
8. Rationalize, then pass to common stages. Scalar comparisons and extension by
zero through derived limits preserve these comparisons and both standard halves.
9. Completed open base change along Frobenius gives the induced Weil structure.
The normalized open adjunction unit is Weil-equivariant. Truncation uniqueness
then makes the open cohomology comparisons equivariant as in Step 3.
10. Inside the open, compose inverse restriction and inverse open unit. Step 6
intertwines Frobenius with the unchanged residue degree. Outside the open, base
change to the point factors extension through the empty site, whose module is zero.
11. Kernels and cokernels of equivariant maps inherit invertible Weil structures
from exact Frobenius pullback. The two exact underlying heart functors preserve
them, proving preservation of finite limits and colimits on the Weil hearts. -/
theorem zlImmersionWeilLocalBehavior
    [IsSeparated W₀.hom] [IsSeparated X₀.hom] [IsSeparated U₀.hom]
    (h₀ : W₀ ⟶ X₀) [IsImmersion h₀.left]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] :
    ∃ (dX : ZlFrobeniusComparison D c X₀) (dW : ZlFrobeniusComparison D c W₀)
      (dU : ZlFrobeniusComparison D c U₀)
      (FX : ZlWeilLocalOperators D c X₀) (FW : ZlWeilLocalOperators D c W₀)
      (FU : ZlWeilLocalOperators D c U₀),
      Nonempty (ZlImmersionPullback D c h₀ dX dW FX FW) ∧
        Nonempty (ZlOpenExtension D c j₀ dX dU FX FU) := by
  obtain ⟨dX, dW, dU, FX, FW, FU, Rh, Rj, hRj⟩ :=
    zlImmersionRestrictionAssembly D c h₀ j₀
  obtain ⟨Z⟩ := zlOpenExtensionAssembly D c j₀ dX dU FX FU Rj hRj
  exact ⟨dX, dW, dU, FX, FW, FU, ⟨Rh⟩, ⟨Z⟩⟩

end WeilConjectures
