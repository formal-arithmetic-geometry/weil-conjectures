/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Supported
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement

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

private noncomputable def setOpenRestrictionIso {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    etaleSetInverseImage j ≅ Etale.openImmersionRestriction (Type (u + 1)) j :=
  (etaleSetAdjunction j).leftAdjointUniq
    (Etale.openImmersionRestrictionLowerStarAdjunction (Type (u + 1)) j)

private theorem set_isSheaf_induced {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hK : ∀ V : X.Etale, Set.range V.hom.base ⊆ Set.range j.base →
      Nonempty (IsTerminal (K.obj.obj (op V)))) :
    Presheaf.IsSheaf (i.Etale.inducedTopology Z.smallEtaleTopology) K.obj := by
  -- Adapt the induced-topology argument of OpenClosed.Supported to terminal sections.
  intro E W S hS
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hS
  have hR := Etale.sup_sieveOfRangeSubset_mem j i hij S hS
  refine Presieve.isSheafFor_trans _ (S ⊔ Etale.sieveOfRangeSubset j W) S
    (K.property E _ hR)
    (fun V f _ ↦ (K.property E _
      (X.smallEtaleTopology.pullback_stable f hR)).isSeparatedFor)
    (fun V f hf ↦ ?_)
  rcases hf with hf | hf
  · rw [Sieve.pullback_eq_top_of_mem S hf]
    exact Presieve.isSheafFor_top _
  · have ht (V' : X.Etale) (g : V' ⟶ V) : IsTerminal (K.obj.obj (op V')) :=
      (hK V' ((Etale.sieveOfRangeSubset j W).downward_closed hf g)).some
    intro x _
    exact ⟨(ht V (𝟙 _)).from E, fun V' g _ ↦ (ht V' g).hom_ext _ _,
      fun y _ ↦ (ht V (𝟙 _)).hom_ext _ _⟩

private theorem set_terminal_sections {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {K : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (hK : IsTerminal ((etaleSetInverseImage j).obj K))
    (V : X.Etale) (hV : Set.range V.hom.base ⊆ Set.range j.base) :
    Nonempty (IsTerminal (K.obj.obj (op V))) := by
  let l := IsOpenImmersion.lift j V.hom hV
  have : Etale (l ≫ j) := by rw [IsOpenImmersion.lift_fac]; infer_instance
  have : Etale l := Etale.of_comp l j
  let e : (MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ j)).obj
      (Scheme.Etale.mk l) ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simp [l])
  have h₀ : IsTerminal ((Etale.openImmersionRestriction (Type (u + 1)) j).obj K) :=
    hK.ofIso ((setOpenRestrictionIso j).app K)
  have h₁ := IsTerminal.isTerminalObj (sheafToPresheaf _ _) _ h₀
  have h₂ := IsTerminal.isTerminalObj ((evaluation _ _).obj (op (Scheme.Etale.mk l))) _ h₁
  exact ⟨IsTerminal.ofIso h₂ (K.obj.mapIso e.op).symm⟩

private theorem set_supported_essImage {X Z U : Scheme.{u}} (i : Z ⟶ X)
    (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (hK : IsTerminal ((etaleSetInverseImage j).obj K)) :
    (etaleSetDirectImage i).essImage K := by
  -- Comparison for the induced topology produces a sheaf with this underlying presheaf.
  let F := i.Etale.sheafPushforwardContinuous (Type (u + 1))
    (i.Etale.inducedTopology Z.smallEtaleTopology) Z.smallEtaleTopology
  have : F.IsEquivalence := inferInstanceAs (i.Etale.sheafPushforwardContinuous
    (Type (u + 1)) (i.Etale.inducedTopology Z.smallEtaleTopology)
    Z.smallEtaleTopology).IsEquivalence
  let K' : Sheaf (i.Etale.inducedTopology Z.smallEtaleTopology) (Type (u + 1)) :=
    ⟨K.obj, set_isSheaf_induced i j hij K (set_terminal_sections j hK)⟩
  exact ⟨F.objPreimage K', ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso
    ((sheafToPresheaf (i.Etale.inducedTopology Z.smallEtaleTopology) (Type (u + 1))).mapIso
      (F.objObjPreimageIso K'))⟩⟩

private noncomputable def set_direct_terminal {X Z U : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hji : Disjoint (Set.range j.base) (Set.range i.base))
    (G : Sheaf Z.smallEtaleTopology (Type (u + 1))) :
    IsTerminal ((etaleSetInverseImage j).obj ((etaleSetDirectImage i).obj G)) := by
  apply IsTerminal.ofIso _ ((setOpenRestrictionIso j).app _).symm
  refine Sheaf.isTerminalOfIsTerminalObj _ ?_
  rintro ⟨T⟩
  -- The empty covering forces terminal sections on the disjoint base change.
  letI := Scheme.Etale.isEmpty_left_pullback_map i j hji.symm T
  exact Scheme.Etale.isTerminalSectionsOfIsEmpty G
    ((MorphismProperty.Over.pullback @Etale ⊤ i).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ j)).obj T))

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
  have hfull : (etaleSetDirectImage i).Full :=
    Etale.full_lowerStar_of_isClosedImmersion i (Type (u + 1))
  have hfaith : (etaleSetDirectImage i).Faithful :=
    Etale.faithful_lowerStar_of_isClosedImmersion i (Type (u + 1))
  refine ⟨hfull, hfaith, ?_, ?_⟩
  · intro F
    constructor
    · rintro ⟨G, ⟨e⟩⟩
      exact ⟨(set_direct_terminal i i.openComplement.ι (by
        rw [Scheme.Opens.range_ι]; exact disjoint_compl_left) G).ofIso
          ((etaleSetInverseImage i.openComplement.ι).mapIso e)⟩
    · rintro ⟨hF⟩
      exact set_supported_essImage i i.openComplement.ι
        i.range_eq_compl_range_openComplement_ι hF
  · intro G
    exact isIso_of_fully_faithful (etaleSetDirectImage i) _

end AlgebraicGeometry
