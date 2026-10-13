module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Target isomorphisms and module cohomology maps

Source: Stacks Project, Cohomology of Sheaves, Lemma 01F8 and Remark 01FB;
Derived Categories, Tags 013P, 013S and 05TG.
(blueprint: lem-weil-pbc-module-cohomology-fmap-target-iso-naturality).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- Target naturality for an isomorphism of the target module.
Source: Stacks Project, Cohomology of Sheaves, Lemma 01F8 and Remark 01FB;
Derived Categories, Tags 013P, 013S and 05TG.
(blueprint: lem-weil-pbc-module-cohomology-fmap-target-iso-naturality).

Proof (resolution comparison, independent of functoriality of h-maps):
1. Let D and E be the data chosen in the two occurrences of moduleCohomologyFMap.
   Write P = h_*. Lift e.hom to c : D.I -> E.I and the identity of G to
   d : D.J -> E.J. Their augmentation equations are I_D.ι c = e.hom I_E.ι
   and J_D.ι d = J_E.ι. Injective-resolution comparison gives these lifts.
2. Extend the natural-indexed complexes by zero to integer indices. E.K is bounded
   below and termwise injective, hence K-injective. Since D.lambda is a
   quasi-isomorphism, precomposition with it is bijective on homotopy classes
   into E.K (Tag 05TG). Lift P(c) followed by E.lambda to t : D.K -> E.K,
   with D.lambda followed by t homotopic to P(c) followed by E.lambda.
3. D.beta followed by t and d followed by E.beta have homotopic composites
   with D.J's augmentation: use D.compatible, the preceding lambda homotopy,
   c's augmentation equation, E.compatible and d's augmentation equation.
   The augmentation of D.J is a quasi-isomorphism, so uniqueness of lifts
   into the bounded below injective E.K makes these two maps homotopic.
4. Apply additive global sections and homology in degree p to these homotopies.
   Restriction from h inverse top to top is natural in the module, so the
   canonical sections comparisons D.a and E.a commute with c. Thus the vertical
   sections maps mu_D and mu_E satisfy H(mu_D) H(t) = H(Gamma(c)) H(mu_E),
   while the horizontal maps satisfy H(Gamma(D.beta)) H(t) =
   H(Gamma(d)) H(Gamma(E.beta)). Both H(mu_D) and H(mu_E) are invertible by
   the data's invertible fields. Cancelling them gives the corresponding square
   between the two horizontal-then-inverse-vertical cohomology maps.
5. Naturality of isoRightDerivedObj identifies the sections map of c with
   H^p(e.hom) and that of d with the identity of H^p(G). Naturality of the
   forgetful homology comparisons transports the square to additive groups.
   Substitution into ModuleCohomologyFMapData.map gives the displayed equation.
   This argument uses no restriction theorem and no h-map functoriality theorem.
-/
theorem moduleCohomologyFMap_target_iso_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F F' : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (e : F ≅ F') (p : ℕ) :
    moduleCohomologyFMap h φ p ≫ (forget₂ _ AddCommGrpCat).map
      ((RingedSpace.moduleCohomology X.toRingedSpace p).map e.hom) =
      moduleCohomologyFMap h (φ ≫ (pushforward h).map e.hom) p := by
  sorry

end AlgebraicGeometry.Scheme.Modules
