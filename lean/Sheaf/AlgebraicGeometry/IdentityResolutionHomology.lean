/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Resolution homology square for the identity scheme morphism

Source: Stacks Project, Cohomology of Sheaves, Remark 01FB; Derived Categories, Tag 013S.
(blueprint: lem-weil-pbc-module-cohomology-fmap-identity-resolution-homology).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false in
/-- The horizontal map in the identity-scheme construction factors on sections homology
through the ordinary resolution descent and the vertical comparison. No derived-functor
resolution transports are part of this conclusion.
Source: Stacks Project, Cohomology of Sheaves, Remark 01FB; Derived Categories, Tag 013S.
(blueprint: lem-weil-pbc-module-cohomology-fmap-identity-resolution-homology).

Proof:
1. Let alpha be the ordinary resolution descent of psi from D.J to D.I. The inverse
   pushforward-identity comparison, applied degreewise, identifies D.I with its identity
   pushforward. Follow it by D.lambda to obtain l : D.I.cocomplex ⟶ D.K.
2. The descent augmentation equation and D.compatible imply that D.beta and alpha
   followed by l have equal composites with the augmentation of D.J. The latter is a
   quasi-isomorphism; D.K has injective terms and is bounded below. Extend by zero to
   integer indices and apply uniqueness up to homotopy (013S), then restrict back to
   natural indices. Thus beta and alpha followed by l are homotopic.
3. Apply additive global sections and then homology. This gives H(beta) = H(alpha)H(l).
   The component formula D.sections identifies D.a with global sections of the inverse
   pushforward-identity comparison: both are identity on sections, using the canonical
   restriction along id^{-1}(Z) = Z. Hence sections of l are D.a followed by sections
   of D.lambda. Substitute this equality to get the asserted factorization. The proof
   works for every D, so no independence theorem is needed.
-/
theorem moduleCohomologyFMap_identity_resolution_homology {Z : Scheme.{u}}
    (G F : SheafOfModules.{u} Z.ringCatSheaf) (ψ : G ⟶ F)
    (D : ModuleCohomologyFMapData (𝟙 Z) G F ψ) (p : ℕ) :
    let Γ := RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
    let Γc := Γ.mapHomologicalComplex (ComplexShape.up ℕ)
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
    H.map (Γc.map D.β) =
      H.map (Γc.map (InjectiveResolution.desc ψ D.I D.J)) ≫
        H.map (D.a.hom ≫ Γc.map D.lambda) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
