/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.CohenMacaulayMorphismAtPoint
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.RestrictedFibreLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FibreCohenMacaulayLocus
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange
import Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension

/-! # Descent of the Cohen-Macaulay locus of a groupoid saturation

Source: Stacks Project, More on Groupoids, Tags 04LH (lemma-local-source) and
047W (remark-local-source-apply), item (5); More on Morphisms, Tags 0399 and 045U.
(blueprint: lem-sfb-groupoid-cm-locus-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The Cohen-Macaulay locus of `h = s ∘ pr_R : B ×[g,U,t] R → U` is the inverse
image of an open of `B`. The restriction to this inverse-image open is
Cohen-Macaulay and locally of finite presentation, and Cohen-Macaulayness at the
canonical identity-section point puts the corresponding point of `B` in the open.
The five compatibility equations express that every groupoid structure map is
over `S`. The inverse-image open uses its canonical open subscheme structure.

Source: Stacks Project, Tags 04LH and 047W (5), with pointwise openness from
More on Morphisms, Tags 0399 and 045U.
(blueprint: lem-sfb-groupoid-cm-locus-descent).

Proof, following the seven steps of the node:
1. The map H → R is the base change of g, hence locally finitely presented by
   lem-weil-pbc-qcqs-morphism-permanence (3). Composing with s is locally finitely
   presented by lem-sbc-locally-finite-presentation-composition. Apply
   lem-sbc-restricted-fibre-locally-noetherian with the whole target to see that
   every fibre is locally Noetherian.
2. Apply lem-sfb-relative-flat-affine-charts with S = Y = U, q = id and p = f = h.
   The identity is locally of finite type (empty generators), and h is locally
   finitely presented. The flat locus F is open on every affine chart, hence open.
   Its restriction is flat by def-weil-flat-morphism. Open inclusions are etale
   by lem-weil-pbc-open-immersion-etale; clause (i) of
   lem-sfb-scheme-etale-source-target-properties gives local finite presentation
   of the restriction to F.
3. Apply lem-sbc-fibre-cohen-macaulay-locus-open to this flat restriction. Its
   fibre-depth-equals-dimension locus D is open in F, hence in H. Open restriction
   preserves source stalks and fibre stalks (def-weil-open-immersion), so D is
   exactly the pointwise Cohen-Macaulay locus of h, including flatness and the
   Noetherian clause. The restriction h|D is Cohen-Macaulay and locally finitely
   presented, the latter by the same etale source restriction as in step 2.
4. For a locally finitely presented f and a flat base map v, pointwise flatness
   of f is equivalent to that of its base change by
   lem-sfb-pointwise-flatness-base-change. By lem-weil-pbc-fibre-of-base-change,
   each new fibre is the old fibre extended along the residue-field map. The
   finite-presentation affine calculation shows that each old fibre is locally
   of finite type over its field. The first assertion of
   lem-pur-cohen-macaulay-field-extension identifies the CM fibre-stalk conditions.
   Thus the CM locus pulls back under flat base change, without a Noetherian base.
5. On C = H ×[B] H, write a,b for the projections and (beta,r1,r2) for its
   components. Set d = c(i(r1),r2). Then td = ha and sd = hb. The maps (a,d)
   and (b,d) identify C with H ×[h,U,t] R and H ×[h,U,s] R respectively.
   Their inverses are ((beta,r),v) ↦ (beta,r,c(r,v)) and
   ((beta,r),v) ↦ (beta,c(r,i(v)),r). The pullback universal property and the
   groupoid unit, inverse and associativity laws verify all constraints and
   inverse identities (def-a1-groupoid-scheme, def-pc-fibre-product).
6. Apply step 4 to the two cartesian squares in step 5, using flatness of t and s.
   At each point of C, CMness of d is equivalent both to membership of a(z) in D
   and to membership of b(z) in D. Hence a⁻¹D = b⁻¹D. The identity section
   sigma = (id_B, e g) of p exists by the groupoid laws. Put W = sigma⁻¹D.
   It is open. Pull back the equality along (id_H, sigma p) : H → C to obtain
   D = p⁻¹W, also as open subschemes by def-weil-open-immersion.
7. Step 3 now gives both properties of h restricted to p⁻¹W. If h is CM at
   sigma(b), then sigma(b) belongs to D, so b belongs to W. If B is empty,
   H, D and W are empty and the pointwise clauses are vacuous. -/
theorem groupoid_cohenMacaulayLocus_descends
    {S U R B : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (uS : U ⟶ S) (rS : R ⟶ S)
    (_hs : s ≫ uS = rS) (_ht : t ≫ uS = rS)
    (_he : e ≫ rS = uS) (_hi : i ≫ rS = rS)
    (_hc : c ≫ rS = pullback.fst s t ≫ rS)
    (hG : IsGroupoidScheme s t e i c) (g : B ⟶ U)
    [Flat s] [Flat t] [LocallyOfFinitePresentation s]
    [LocallyOfFinitePresentation t] [LocallyOfFinitePresentation g] :
    ∃ W : B.Opens,
      (∀ z : ↥(pullback g t : Scheme.{u}), z ∈ (pullback.fst g t ⁻¹ᵁ W) ↔
        Scheme.Hom.IsCohenMacaulayAtPoint (pullback.snd g t ≫ s) z) ∧
      Scheme.Hom.IsCohenMacaulay
        ((pullback.fst g t ⁻¹ᵁ W).ι ≫ (pullback.snd g t ≫ s)) ∧
      LocallyOfFinitePresentation
        ((pullback.fst g t ⁻¹ᵁ W).ι ≫ (pullback.snd g t ≫ s)) ∧
      ∀ b : B, Scheme.Hom.IsCohenMacaulayAtPoint (pullback.snd g t ≫ s)
        ((pullback.lift (𝟙 B) (g ≫ e)
          (by simp only [Category.id_comp, Category.assoc, hG.identity_target,
            Category.comp_id])) b) → b ∈ W := by
  sorry

end AlgebraicGeometry
