/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Open subgroupoids give étale maps of quotient stacks

Source: Stacks Project, stacks-morphisms.tex, Tag 0DU2
(blueprint: lem-sfb-open-subgroupoid-etale-quotient).

Quotients are specified by the existing fppf quotient presentation. The comparison
with the inclusion is required on arrows as well as objects, so the resulting map
is the induced quotient map. No quotient or map is chosen by a definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An open subgroupoid on the same objects induces a representable, surjective,
étale morphism of algebraic quotient stacks, and its source is DM if its target is.

Source: Stacks Project, stacks-morphisms.tex, Tag 0DU2; Tag 06N3 for the final
atlas consequence (blueprint: lem-sfb-open-subgroupoid-etale-quotient).

The supplied quotient presentations mean exactly `[V/R]` and `[V/P]`. The equations
on `eP`, `iP`, and `cP` express that the operations on `P` restrict those on `R`.
The comparison `β` identifies the object maps; the following square on every
`P`-arrow identifies the arrow map with inclusion. Thus it specifies the extension
of the subgroupoid functor, rather than an arbitrary map between the quotients.

Proof:
1. Open immersions are étale (lem-weil-pbc-open-immersion-etale). The chartwise
   calculus (lem-sfb-stack-chartwise-smooth-etale-calculus) makes the restricted
   source and target flat and locally finitely presented. Apply
   lem-sfb-flat-groupoid-algebraic-quotient to both groupoids to obtain algebraicity.
   Stackification universality (lem-sfb-groupoid-stackification-local-description)
   extends the inclusion, with its object and arrow comparisons.
2. Locally lift two objects to V. Their isomorphism sheaves are the corresponding
   fibres of P and R, since spaces are fppf sheaves. The inclusion is monic, so
   the induced functor is faithful. Apply lem-sfb-faithful-stack-map-representable.
3. Lift a field-valued target object after a field extension to V, using
   lem-sfb-flat-groupoid-algebraic-quotient. That same object gives a source lift.
4. By lem-sfb-quotient-map-cartesian-action-groupoid, the pullback along V is
   [R/(P ×_(s,V,t) R)]. The relation map sends (p,r) to (c(p,r),r). Its inverse
   on the inverse image of P is (r₁,r₂) ↦ (c(r₁,i(r₂)),r₂). The groupoid laws
   identify these as inverses. This relation is open in R ×_(s,V,s) R, hence
   lem-sfb-open-relation-etale-quotient makes its quotient étale over V.
5. Descend étaleness along the flat locally finitely presented surjective map
   V → [V/R], using lem-sfb-representable-fppf-etale-open-descent.
6. If the target is DM, pull back its étale scheme atlas through the representable
   map j. Take an étale scheme chart of this algebraic-space pullback. The
   chartwise calculus makes its composite an étale surjective scheme atlas of
   the source. Its diagonal is already representable, giving the DM assertion.
The same argument covers empty spaces and uses no quasi-compactness assumption. -/
theorem open_subgroupoid_etale_quotient {S : Scheme.{u}}
    {V R P : AlgebraicSpace S} (s t : R ⟶ V)
    (e : V.obj.obj ⟶ R.obj.obj) (i : R.obj.obj ⟶ R.obj.obj)
    (c : Limits.pullback s.hom.hom t.hom.hom ⟶ R.obj.obj)
    (q : P.obj.obj ⟶ R.obj.obj)
    (hq : IsRepresentableWith (fun _ _ f ↦ IsOpenImmersion f.left) q)
    (eP : V.obj.obj ⟶ P.obj.obj) (iP : P.obj.obj ⟶ P.obj.obj)
    (cP : Limits.pullback (q ≫ s.hom.hom) (q ≫ t.hom.hom) ⟶ P.obj.obj)
    (he : eP ≫ q = e) (hi : iP ≫ q = q ≫ i)
    (hc : cP ≫ q =
      pullback.map (q ≫ s.hom.hom) (q ≫ t.hom.hom) s.hom.hom t.hom.hom
        q q (𝟙 V.obj.obj) (by simp) (by simp) ≫ c)
    (hs : MapIsFlat s) (ht : MapIsFlat t)
    (hsfp : MapIsLocallyOfFinitePresentation s)
    (htfp : MapIsLocallyOfFinitePresentation t)
    (X : BasedCategory.{max u v₁, max (u + 1) w₁} (Over S))
    (Y : BasedCategory.{max u v₂, max (u + 1) w₂} (Over S))
    (aR : BasedFunctor (discreteModuli V.obj.obj) X)
    (aP : BasedFunctor (discreteModuli V.obj.obj) Y)
    (hR : SpaceGroupoidQuotientPresentation s.hom.hom t.hom.hom e i c X aR)
    (hP : SpaceGroupoidQuotientPresentation (q ≫ s.hom.hom) (q ≫ t.hom.hom)
      eP iP cP Y aP) :
    IsAlgebraicModuliStack Y ∧ IsAlgebraicModuliStack X ∧
      ∃ (j : BasedFunctor Y X) (β : ModuliTwoIso (aP.comp j) aR),
        (∀ z : (discreteModuli P.obj.obj).obj,
          j.map (hP.arrows.val.hom.app z) ≫
              β.val.hom.app ((discreteModuliMap (q ≫ t.hom.hom)).obj z) =
            β.val.hom.app ((discreteModuliMap (q ≫ s.hom.hom)).obj z) ≫
              hR.arrows.val.hom.app ((discreteModuliMap q).obj z)) ∧
        IsRepresentableByAlgebraicSpaces j ∧ IsSurjectiveModuliMap j ∧
        ModuliSpaceTest (@Etale) j ∧
        (IsDeligneMumfordModuliStack X → IsDeligneMumfordModuliStack Y) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
