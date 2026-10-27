/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.QuasiFiniteLocusOpen

/-!
# Descent of the quasi-finite locus of a groupoid saturation map

Source: Stacks Project, More on Groupoids, Tag 04LH (lemma-local-source), specialized
by Tag 047W (remark-local-source-apply), item (2)
(blueprint: lem-sfb-groupoid-quasifinite-locus-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a groupoid over a scheme, the quasi-finite locus of `B ×[g,U,t] R → U`
is pulled back from an open of `B`. Its restriction is locally quasi-finite, and
quasi-finiteness at the identity-section point puts the original point in that open.
The maps `uS`, `rS` and their five compatibility equations say that all groupoid
structure morphisms are over `S`. The identity-section point is the image under the
canonical pullback lift of `(𝟙 B, g ≫ e)`, rather than a choice of a point with two
specified projections.

Source: Stacks Project, More on Groupoids, Tag 04LH (lemma-local-source), specialized
by Tag 047W (remark-local-source-apply), item (2)
(blueprint: lem-sfb-groupoid-quasifinite-locus-descent).

Proof:
1. The projection to `R` is a base change of `g`, hence locally of finite type by
   `lem-weil-pbc-lft-base-change`. Composing with `s` remains locally of finite type
   by clause (e) of `lem-weil-pbc-proper-fp-permanence`. By
   `lem-sc-quasi-finite-points-open`, its quasi-finite locus `D` is open and its
   restriction to `D` is locally quasi-finite.
2. On `C = H ×[B] H`, with projections `a,b`, write the components as `(beta,r1,r2)`
   and set `d = c(i(r1),r2)`. The squares with `(a,t)` and `(b,s)` over `h` are
   cartesian. Their inverse maps are respectively
   `((beta,r),v) ↦ (beta,r,c(r,v))` and
   `((beta,r),v) ↦ (beta,c(r,i(v)),r)`. Their constraints and inverse identities
   follow from the groupoid laws and the pullback universal property (Tag 03C6).
3. Apply `lem-sfb-scheme-quasifinite-at-base-change` to these squares. At a point
   of `C`, quasi-finiteness of `d` is equivalent both to that of `h` at its image
   under `a` and at its image under `b`. Thus `a⁻¹(D) = b⁻¹(D)` as opens.
4. Let `sigma = (id, e g)` be the identity section of `p`, and set `W = sigma⁻¹(D)`.
   The pair `(id_H, sigma p)` gives `j : H → C`. Pull back the equality in step 3
   along `j` to obtain `D = p⁻¹(W)`, also as open subschemes.
5. The locally quasi-finite restriction from step 1 is therefore the restriction
   to `p⁻¹(W)`. If `h` is quasi-finite at `sigma(b)`, then `sigma(b) ∈ D`, so `b ∈ W`.
-/
theorem groupoid_quasiFiniteLocus_descends
    {S U R B : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (uS : U ⟶ S) (rS : R ⟶ S)
    (_hs : s ≫ uS = rS) (_ht : t ≫ uS = rS)
    (_he : e ≫ rS = uS) (_hi : i ≫ rS = rS)
    (_hc : c ≫ rS = pullback.fst s t ≫ rS)
    (hG : IsGroupoidScheme s t e i c) (g : B ⟶ U)
    [LocallyOfFiniteType s] [LocallyOfFiniteType t] [LocallyOfFiniteType g] :
    ∃ W : B.Opens,
      (∀ z : ↥(pullback g t : Scheme.{u}), z ∈ (pullback.fst g t ⁻¹ᵁ W) ↔
        Scheme.Hom.IsQuasiFiniteAtPoint (pullback.snd g t ≫ s) z) ∧
      Scheme.Hom.IsLocallyQuasiFinite
        ((pullback.fst g t ⁻¹ᵁ W).ι ≫ (pullback.snd g t ≫ s)) ∧
      ∀ b : B, Scheme.Hom.IsQuasiFiniteAtPoint (pullback.snd g t ≫ s)
        ((pullback.lift (𝟙 B) (g ≫ e)
          (by simp only [Category.id_comp, Category.assoc, hG.identity_target,
            Category.comp_id])) b) → b ∈ W := by
  sorry

end AlgebraicGeometry
