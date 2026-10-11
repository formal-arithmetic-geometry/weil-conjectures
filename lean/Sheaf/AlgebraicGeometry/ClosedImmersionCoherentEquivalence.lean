/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Coherent modules and adic systems on a closed subscheme

Source: Stacks Project, Cohomology of Schemes, Tags 087T, 088A, 088C, and 088E
(blueprint: lem-weil-pbc-closed-immersion-coherent-equivalence).

## Main statements
* `closedImmersion_coherent_equivalence`: pushforward identifies coherent modules with
  coherent modules annihilated by the defining ideal.
* `closedImmersion_coherent_support`: support is the image of support.
* `closedImmersion_coherentFormal_equivalence`: the termwise equivalence and its natural
  compatibility with completion, including the canonical quotient projections.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Pushforward induces the equivalence on coherent modules of Stacks Tag 087T.
(blueprint: lem-weil-pbc-closed-immersion-coherent-equivalence)
Proof (node steps 1--4): a closed immersion is finite
(lem-weil-pbc-closed-immersion-finite), so its pushforward preserves coherence
(lem-weil-pbc-finite-pushforward-coherent). Its defining ideal kills the pushforward
(lem-weil-pbc-closed-immersion-pushforward-annihilated). The pushforward is fully faithful
on all modules (lem-weil-pbc-closed-immersion-pushforward-fully-faithful), hence on these
full subcategories. A coherent module killed by the ideal is the pushforward of its
quasi-coherent finite type pullback (lem-weil-pbc-closed-immersion-pushforward-annihilated).
On the locally Noetherian source this pullback is coherent
(pqf-lem-coherent-ft-locnoeth). Thus the restricted pushforward is essentially surjective
and fully faithful, and yields the displayed equivalence and comparison with pushforward.
-/
theorem closedImmersion_coherent_equivalence {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X] [IsLocallyNoetherian Z] :
    ∃ E : CoherentModules Z ≌
        ObjectProperty.FullSubcategory (fun F : CoherentModules X ↦
          CoherentModuleSupportedOn F i),
      Nonempty (E.functor ⋙
        ObjectProperty.ι (fun F : CoherentModules X ↦ CoherentModuleSupportedOn F i) ⋙
        ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ≅
        ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
          Scheme.Modules.pushforward i) := by
  sorry

/-- The support formula accompanying Stacks Tag 087T, by the stalk calculation of
Sheaves, Tag 00AE (blueprint: lem-weil-pbc-closed-immersion-coherent-equivalence).
Proof (node step 5): outside the closed image the stalk of the pushforward is zero;
at i(z) it is isomorphic, as an additive group, to the stalk at z
(lem-weil-pbc-closed-pushforward-stalks). A zero stalk is precisely a subsingleton stalk
(def-weil-pbc-closed-subset-proper-over-base). Injectivity of the closed immersion
therefore gives equality with the image of the nonzero-stalk locus. -/
theorem closedImmersion_coherent_support {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (G : CoherentModules Z) :
    {x : X | ¬ Subsingleton (((Scheme.Modules.pushforward i).obj G.obj).presheaf.stalk x)} =
      i '' {z : Z | ¬ Subsingleton (G.obj.presheaf.stalk z)} := by
  sorry

/-- The termwise closed pushforward equivalence and its natural completion comparison.
Source: Stacks Tags 088A, 088C, 088E, using Tag 087T without further mention; completion
is equation 0880 (blueprint: lem-weil-pbc-closed-immersion-coherent-equivalence).
Proof (node steps 6--10): the closed subscheme of a Noetherian scheme is Noetherian
(pqf-def-locnoeth, def-weil-closed-immersion). The extended ideal is I.comap i
(def-nagata-extended-ideal). Ideal powers commute with pushforward on products, and
pushforward identifies their quotients, naturally and compatibly with quotient maps
(lem-weil-pbc-closed-immersion-pushforward-ideal-powers). Thus termwise pushforward
preserves the defining adic-system conditions (def-weil-pbc-coherent-formal-module).
The termwise maps are fully faithful by step 3. Conversely choose coherent preimages
of each term by step 4; full faithfulness uniquely lifts the transition maps. The
quotient comparison and reflection of zero objects and isomorphisms give the adic
conditions on these preimages. This proves essential surjectivity onto precisely the
systems annihilated by i.ker. Finally the natural quotient comparisons assemble into
a natural isomorphism of completion systems, because they respect all transitions.
The displayed projection equation specifies these as the canonical quotient comparisons.
The index op n represents positive level n+1. -/
theorem closedImmersion_coherentFormal_equivalence {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] (I : X.IdealSheafData) :
    (∃ E : @CoherentFormalModule Z (isNoetherian_of_locallyOfFiniteType i) (I.comap i) ≌
        ObjectProperty.FullSubcategory (fun M : CoherentFormalModule X I ↦
          SupportedOn I M i),
      Nonempty (E.functor ⋙
        ObjectProperty.ι (fun M : CoherentFormalModule X I ↦ SupportedOn I M i) ⋙
        ObjectProperty.ι (IsCoherentFormalModule I) ≅
        ObjectProperty.ι (IsCoherentFormalModule (I.comap i)) ⋙
          (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj (Scheme.Modules.pushforward i))) ∧
    (∃ θ : ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
        Scheme.Modules.pushforward i ⋙ formalCompletionFunctor I ≅
        ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
        formalCompletionFunctor (I.comap i) ⋙
          (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj (Scheme.Modules.pushforward i),
      ∀ (G : CoherentModules Z) (n : ℕ),
        formalModuleQuotientπ I (n + 1) ((Scheme.Modules.pushforward i).obj G.obj) ≫
          (θ.hom.app G).app (op n) =
        (Scheme.Modules.pushforward i).map (formalModuleQuotientπ (I.comap i) (n + 1) G.obj))
    := by
  sorry

end AlgebraicGeometry
