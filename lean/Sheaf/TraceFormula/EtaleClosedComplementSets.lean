/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.SixFunctors.OpenClosed.Stalk

/-!
# Closed immersion on small étale sheaves of sets

Source: Stacks Project, `literature/stacks-project/etale-cohomology.tex`, Tag 04CA,
`proposition-closed-immersion-pushforward`, part (1) and final assertion
(blueprint: lem-trf-etale-closed-complement-sets).

The set-valued inverse and direct images are the continuous-site constructions, and the
statement records full faithfulness, the essential-image characterization, and the counit.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The direct image of sheaves of sets along a scheme morphism, by restriction along
base change of the small étale sites.

Source: Stacks Project, Étale Cohomology, Tag 04CA
(blueprint: lem-trf-etale-closed-complement-sets).
-/
noncomputable def etaleSetDirectImage {X Z : Scheme.{u}} (i : Z ⟶ X) :
    Sheaf Z.smallEtaleTopology (Type (u + 1)) ⥤ Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  (MorphismProperty.Over.pullback @Etale ⊤ i).sheafPushforwardContinuous
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Z.smallGrothendieckTopology @Etale)

/-- The inverse image of sheaves of sets along a scheme morphism, by sheafified left Kan
extension along base change of the small étale sites.

Source: Stacks Project, Étale Cohomology, Tag 04CA
(blueprint: lem-trf-etale-closed-complement-sets).
-/
noncomputable def etaleSetInverseImage {X Z : Scheme.{u}} (i : Z ⟶ X) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤ Sheaf Z.smallEtaleTopology (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
    (X.smallGrothendieckTopology @Etale)
    (Z.smallGrothendieckTopology @Etale)

/-- The set-sheaf inverse/direct-image adjunction associated with a scheme morphism.

Source: Stacks Project, Étale Cohomology, Tag 04CA
(blueprint: lem-trf-etale-closed-complement-sets).
-/
noncomputable def etaleSetAdjunction {X Z : Scheme.{u}} (i : Z ⟶ X) :
    etaleSetInverseImage i ⊣ etaleSetDirectImage i :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
    (X.smallGrothendieckTopology @Etale)
    (Z.smallGrothendieckTopology @Etale)

/-- For a closed immersion `i : Z ⟶ X` and its canonical open complement, direct image of
small étale sheaves of sets is fully faithful; its essential image is exactly the sheaves
whose restriction to the complement is terminal, and the inverse/direct-image counit is an
isomorphism.

Source: Stacks Project, `literature/stacks-project/etale-cohomology.tex`, Tag 04CA,
`proposition-closed-immersion-pushforward`, part (1) and final assertion
(blueprint: lem-trf-etale-closed-complement-sets).

Proof plan: (1) use the set-sheaf adjunction and its explicit section and unit formulas from
`lem-weil-pbc-sets-etale-inverse-image-composition-units`; (2) convert the initiality of the
pointed-neighbourhood base-change functor from `lemma-openclosed-stalk-lowerstar` into the
set-valued stalk comparison using `lem-weil-pbc-initial-functor-limit` and the colimit
universal property; (3) identify the actual counit on germs by the triangle identity and the
set-valued inverse-image stalk-germ comparison, then use set-sheaf stalk detection;
(4) deduce full faithfulness by adjunction algebra; (5) refine étale neighbourhoods over the
open complement to show the direct-image stalks are singleton, then detect terminality;
(6) for a sheaf terminal on the complement, identify the actual unit on closed-image germs,
use singleton stalks on the complement, and detect its isomorphism. The argument includes the
empty-scheme and empty-open cases and does not assume reducedness or finiteness.
-/
theorem etaleClosedComplementSets {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (etaleSetDirectImage i).Full ∧ (etaleSetDirectImage i).Faithful ∧
    (∀ F : Sheaf X.smallEtaleTopology (Type (u + 1)),
      (etaleSetDirectImage i).essImage F ↔
        Nonempty (IsTerminal ((etaleSetInverseImage (i.openComplement.ι)).obj F))) ∧
    (∀ G : Sheaf Z.smallEtaleTopology (Type (u + 1)),
      IsIso ((etaleSetAdjunction i).counit.app G)) := by
  sorry

end AlgebraicGeometry
