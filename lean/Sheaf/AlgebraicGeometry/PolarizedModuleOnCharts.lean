/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescentData

/-! # Descent of the line module on fixed scheme charts

Source: Stacks Project, Descent, Tags 023T and 05VG; Spaces Descent, Tag 04W8
(blueprint: lem-trf-polarized-module-on-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Once the underlying scheme and its charts are fixed, the line-module cocycle is
an effective module descent datum on that scheme. No scheme is constructed by this lemma.

Source: Stacks Project, Descent, Tags 023T and 05VG; Spaces Descent, Tag 04W8
(blueprint: lem-trf-polarized-module-on-charts).

Proof:
1. The maps e_i^{-1} followed by the first projections form an etale covering of Y:
   transport the base change of the given covering U_i of S along the isomorphisms e_i.
   The theta equation and pullback uniqueness identify its double overlaps with the
   specified polarizedOverlap, with second projection theta_ij followed by p_j.
2. Transport lambda to this covering's module descent data. Its diagonal and cocycle
   conditions follow from D.lambda_identity and D.lambda_cocycle using the canonical
   tensor-pullback composition and identity comparisons. Invertibility makes each
   component quasi-coherent. Fpqc effectivity (Descent Tag 023T) supplies M and the
   compatible local module isomorphisms. Finite local freeness of rank one descends,
   so M is invertible (Tag 05VG).
3. Pull these local identifications along e_i to obtain c on Y times_S U_i. The
   unit and associativity of the canonical comparisons identify their direct chart
   expressions polarizedChartLine with the identifications just descended. Their
   overlap equation is precisely the lambda field of IsPolarizedDescentRealization.
   The theta field is the assumed htheta. The empty scheme and empty cover satisfy
   the same sheaf equalizers and require no nonemptiness assumption. -/
theorem exists_polarizedModule_on_schemeCharts
    {S : Scheme.{u}} {I : Type v} {U : I → Scheme.{u}}
    {uMap : ∀ i, U i ⟶ S} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ U i}
    {L : ∀ i, (X i).Modules} {hL : ∀ i, Scheme.Modules.IsInvertible (L i)}
    (D : PolarizedSchemeEtaleDescentDatum S I U uMap X f L hL)
    (Y : Scheme.{u}) (g : Y ⟶ S) (e : ∀ i, pullback g (uMap i) ≅ X i)
    (he : ∀ i, (e i).hom ≫ f i = pullback.snd g (uMap i))
    (htheta : ∀ i j,
      polarizedOverlapX U uMap X f i j ≫ (e i).inv ≫ pullback.fst g (uMap i) =
        (D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i ≫
          (e j).inv ≫ pullback.fst g (uMap j))
    : ∃ (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M)
        (c : ∀ i, (Scheme.Modules.tensorPullback (pullback.fst g (uMap i))).obj M ≅
          (Scheme.Modules.tensorPullback (e i).hom).obj (L i)),
      IsPolarizedDescentRealization D
        { Y := Y, g := g, M := M, isInvertible := hM,
          chart := fun i ↦ { schemeIso := e i, over := he i, moduleIso := c i } } := by sorry

end AlgebraicGeometry
