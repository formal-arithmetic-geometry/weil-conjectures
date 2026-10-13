/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
public import Sheaf.AlgebraicGeometry.CoherentFormalModule

import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.FormalSystemsPullback

/-! # The finite completed-module model of the affine section-limit functor

Source: Stacks Project, Lemmas 087W and 087X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On an affine open, the section-limit functor is naturally the restriction functor
followed by the finite completed-module equivalence, inclusion and restriction of scalars.
This statement supplies the natural comparison, and asserts no exactness or annihilator bound.

Source: Stacks Project, Lemma 087W, the definition of M as the inverse limit in its proof,
and the affine calculation in Lemma 087X.
(blueprint: lem-weil-pbc-formal-affine-limit-model)

Proof: Identify V with Spec of A = Gamma(V, O_X) using the canonical affine-open
isomorphism. Under this isomorphism the restricted ideal corresponds to J = I(V).
Transport formal modules along the isomorphism by termwise pullback. Apply the equivalence
of Lemma 087W with this ideal J; compose it with that transport to obtain E. The cones in
Lemma 087W identify the underlying A-module of E(F) with the inverse limit of the sections
of F on V. Termwise restriction identifies these sections with sections on the open
subscheme, and the Spec/global-sections identification transports them to A-modules.
Compare each such limiting cone with the chosen limit cone. Uniqueness gives invertible
A-linear comparison maps. The naturality of the cones on morphisms shows these maps form
a natural isomorphism for every global formal module and morphism after restriction.
For the empty affine open A is the zero ring and both categories consist of zero modules;
the same comparison applies. For J=0 the towers are constant and completion is A;
for J=A all levels and the completion are zero. No proper-ideal hypothesis is needed. -/
theorem coherentFormalModule_affine_limit_model
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData) (V : X.affineOpens)
    [IsNoetherian V.1.toScheme] :
    ∃ E : CoherentFormalModule V.1.toScheme (I.comap V.1.ι) ≌
      ObjectProperty.FullSubcategory
        (fun N : ModuleCat.{u} (AdicCompletion (I.ideal V) Γ(X, V.1)) ↦
          Module.Finite (AdicCompletion (I.ideal V) Γ(X, V.1)) N),
    Nonempty
      (((IsCoherentFormalModule I).ι ⋙
          (Functor.whiskeringRight ℕᵒᵖ X.Modules (ModuleCat Γ(X, V.1))).obj
            (SheafOfModules.evaluation X.ringCatSheaf (op V.1)) ⋙ lim) ≅
        coherentFormalModulesRestriction I V.1 ⋙ E.functor ⋙
          ObjectProperty.ι
            (fun N : ModuleCat.{u} (AdicCompletion (I.ideal V) Γ(X, V.1)) ↦
              Module.Finite (AdicCompletion (I.ideal V) Γ(X, V.1)) N) ⋙
          ModuleCat.restrictScalars
            (algebraMap Γ(X, V.1) (AdicCompletion (I.ideal V) Γ(X, V.1)))) := by sorry

end AlgebraicGeometry
