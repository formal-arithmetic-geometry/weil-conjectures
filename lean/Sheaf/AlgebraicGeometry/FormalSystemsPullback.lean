/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.TensorPullback
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Pullback of coherent formal systems

Source: Stacks Project, Cohomology of Schemes, Lemma 0887 and the completion identity
in the proof of Lemma 088B (blueprint: lem-weil-pbc-formal-systems-pullback).
-/

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Termwise tensor pullback defines the functor on coherent formal systems, and it
commutes naturally with completion. On an open subscheme it is restriction, and restriction
commutes naturally with completion with respect to the restricted ideal.

Source: Stacks, Lemma 0887 and proof of Lemma 088B
(blueprint: lem-weil-pbc-formal-systems-pullback).

Proof (the seven steps of the node):
1. The extended ideal is `J.comap f`. By lem-weil-pbc-module-pullback-ideal-quotient,
   extension commutes with powers and pullback of G/J^n G is f*G/I^n f*G, naturally in G.
2. Each pulled-back term is quasi-coherent and of finite type, hence coherent on the
   locally Noetherian source (pqf-lem-coherent-ft-locnoeth,
   lem-weil-pbc-module-pullback-quasi-coherent,
   lem-weil-pbc-support-pullback-finite-type).
3. J^n G_n = 0 makes the quotient projection an isomorphism. Its pullback is an
   isomorphism whose kernel is I^n f*G_n, so that product is zero.
4. Factor each transition through the quotient isomorphism in step 1 and the pullback
   of the original quotient-to-term isomorphism. This is again an isomorphism.
5. Pull back compatible families of maps termwise. Functoriality of tensorPullback
   gives compatibility and the identity and composition laws.
6. The quotient comparisons commute with transitions: precompose both composites with
   the quotient projection, use the defining equations, and cancel the epimorphism.
   Their componentwise inverses give an isomorphism of systems. Naturality of the
   quotient comparisons makes this an isomorphism of completion functors.
7. For an open immersion tensor pullback is naturally restriction
   (lem-weil-pbc-open-immersion-module-pullback-restriction). The structure-sheaf
   comparison identifies the extended ideal with the restricted ideal
   (lem-weil-pbc-module-pullback-structure-sheaf, def-nagata-extended-ideal).
   Restriction preserves cokernels and ideal products
   (lem-weil-pbc-ideal-times-quasi-coherent-affine-sections), giving the final comparison.

The equations with the full-subcategory inclusions specify both objects and morphisms
of the two functors; thus the existential functors cannot be arbitrary functors.
The final comparison is stated in the ambient system category, whose full-subcategory
inclusion is fully faithful. -/
theorem exists_formalSystemsPullback {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) (J : Y.IdealSheafData) :
    (∃ (P : CoherentFormalModule Y J ⥤ CoherentFormalModule X (J.comap f))
        (C : CoherentModules Y ⥤ CoherentModules X),
      P ⋙ ObjectProperty.ι (IsCoherentFormalModule (J.comap f)) =
        ObjectProperty.ι (IsCoherentFormalModule J) ⋙
          (Functor.whiskeringRight ℕᵒᵖ Y.Modules X.Modules).obj
            (Scheme.Modules.tensorPullback f) ∧
      C ⋙ ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) =
        ObjectProperty.ι (RingedSpace.IsCoherent Y.toRingedSpace) ⋙
          Scheme.Modules.tensorPullback f ∧
      Nonempty (completion Y J ⋙ P ≅ C ⋙ completion X (J.comap f))) ∧
    (∀ U : Y.Opens,
      Nonempty (Scheme.Modules.tensorPullback U.ι ≅ Scheme.Modules.restrictFunctor U.ι) ∧
      Nonempty (
        (ObjectProperty.ι (RingedSpace.IsCoherent Y.toRingedSpace) ⋙
          formalCompletionFunctor J) ⋙
            (Functor.whiskeringRight ℕᵒᵖ Y.Modules U.toScheme.Modules).obj
              (Scheme.Modules.restrictFunctor U.ι) ≅
        (ObjectProperty.ι (RingedSpace.IsCoherent Y.toRingedSpace) ⋙
          Scheme.Modules.restrictFunctor U.ι) ⋙ formalCompletionFunctor (J.comap U.ι))) := by
  sorry

end AlgebraicGeometry
