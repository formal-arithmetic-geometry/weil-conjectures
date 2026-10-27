/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionBinary

/-!
# Unit and associativity laws from normalized binary composition

Source: Stacks Project, Tag 02V0; canonical site-composition comparisons and their mates.
(blueprint: lem-sfb-locally-closed-module-extension-unit-associativity).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Any normalized natural binary comparison on the fixed, fully faithful model has
coherent identity comparisons and satisfies associativity. This is the formal last
step of the argument; it does not construct any geometric binary comparison.

Source: Stacks Project, Tag 02V0; Step 9 of
lem-sfb-locally-closed-module-extension-coherence, using the canonical fibre-product
composition comparisons of the pro-etale sites.
(blueprint: lem-sfb-locally-closed-module-extension-unit-associativity).

Proof: the coefficient-identified identity inverse image is canonically the identity.
The fixed model for the identity is the open extension for the identity, by the boundary
comparison, so its normalized open adjunction gives an isomorphism to the identity
functor. Alternatively apply the closed boundary comparison and the sectionwise
identity direct-image isomorphism. Choose the normalization whose pullback equals
modelRestriction. The canonical inverse-image unit laws show that either unit path,
after equality transport of the coefficient immersion, has the same restriction as
gamma; full faithfulness with modelRestriction makes those paths equal. For three
immersions, fibre-product associativity makes the two direct-image pasting maps equal:
their projections to each of the three factors are the same. Conjugating through the
specified adjunctions gives the inverse-image associativity equation and, on ring
sheaves, the equality (a.comp b).comp d = a.comp (b.comp d). Apply normalized twice to
each of the two extension-composition paths. Naturality of pullComp and of each
modelRestriction moves the intermediate restrictions across gamma; inverse-image
associativity makes the final restriction formulas equal. The source of either path
is isomorphic to the extension image for the triple composite, by two applications
of gamma. Conjugate by one path and use full faithfulness and modelRestriction to
cancel restriction, proving equality. The proof uses no composite shriek adjunction.
In particular arbitrary normalized binary choices give the same laws. -/
theorem locallyClosedModel_unit_associativity (G : LocallyClosedModelComposition.{u}) :
    ∃ identity : ∀ X : LocallyClosedCoefficients.{u},
        (LocallyClosedCoefficientImmersion.identity X).modelExtension ≅
          𝟭 (proEtaleRingModules X.scheme X.ring),
      (∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
        ∃ h : a.comp (.identity S) = a,
          G.gamma a (.identity S) ≪≫
              eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h) =
            Functor.isoWhiskerRight (identity S) a.modelExtension ≪≫
              Functor.leftUnitor a.modelExtension) ∧
      (∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
        ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
          G.gamma (.identity X) a ≪≫
              eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h) =
            Functor.isoWhiskerLeft a.modelExtension (identity X) ≪≫
              Functor.rightUnitor a.modelExtension) ∧
      (∀ {S X T W : LocallyClosedCoefficients.{u}}
        (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
        (d : LocallyClosedCoefficientImmersion W T),
        ∃ h : (a.comp b).comp d = a.comp (b.comp d),
          Functor.isoWhiskerRight (G.gamma b d) a.modelExtension ≪≫ G.gamma a (b.comp d) =
            Functor.associator d.modelExtension b.modelExtension a.modelExtension ≪≫
              Functor.isoWhiskerLeft d.modelExtension (G.gamma a b) ≪≫
                G.gamma (a.comp b) d ≪≫
                  eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h)) := by
  sorry

end AlgebraicGeometry.Scheme
