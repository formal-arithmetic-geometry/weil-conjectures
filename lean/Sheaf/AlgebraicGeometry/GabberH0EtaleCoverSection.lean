/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.Sheaves.Stalks
import Sheaf.Topology.ClosedPushforwardConstantStalks
import Sheaf.AlgebraicGeometry.EtaleInverseImageSectionDescription
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # A surjective étale cover representing a Gabber section

Source: Stacks Project, Tag 09ZF, fourth proof paragraph, through surjectivity
of the union of the local representing étale schemes.
(blueprint: lem-weil-pbc-gabber-h0-etale-cover-section).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A global inverse-image section has a representative on a surjective étale cover.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph, before finite refinement.
(blueprint: lem-weil-pbc-gabber-h0-etale-cover-section).

Proof:
1. Every nonempty closed subset of X meets i(Z). Otherwise the two constant
   sections of the closed pushforward of the constant two-element sheaf have
   equal restrictions, because its inverse-image stalks on Z are singletons.
   Section determination by germs contradicts injectivity of hZar.
2. Apply local sheafification and colimit representatives to t, after identifying
   the base change of the identity object with the identity object of Z. This
   gives an étale cover V_j of Z, étale X-schemes U_j, sections s_j, and maps
   V_j to U_j times_X Z on which the restrictions of t and i^*s_j agree.
3. Each map V_j to U_j times_X Z is étale, hence has open image. Since the latter
   embeds as a closed subscheme of U_j, extend that image to an ambient open and
   restrict U_j and s_j. The map V_j is now surjective, so separatedness for this
   one-member étale cover gives equality on all of U_j times_X Z.
4. The open union of the images of U_j contains i(Z); its closed complement is
   empty by step 1. By compactness choose finitely many of these images covering X.
   Take their finite disjoint union U. It is étale and surjective over X. The
   sections s_j glue on this disjoint union (overlaps are empty), giving s.
   Naturality of the inverse-image unit and the sheaf axiom on its base change
   give the displayed equation. Finite disjoint unions keep U in universe u.
For empty X use the empty étale cover, whose sections exist uniquely by the
empty-cover sheaf axiom. No nonemptiness of X or Z is assumed. -/
theorem gabber_h0_etale_cover_section
    {X Z : Scheme.{u}} [CompactSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hZar :
      letI : ∀ P : X.Opensᵒᵖ ⥤ Type (u + 1),
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)).op.HasPointwiseLeftKanExtension P :=
            fun P U ↦
              @Types.hasColimit.{u, u + 1, u}
                (CostructuredArrow.{u, u, u, u} (Opens.map i.base).op U)
                inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ P)
      ∀ G : TopCat.Sheaf (Type (u + 1)) X.toTopCat,
      Function.Injective
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)) (Type (u + 1))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app G).hom.app
            (op (⊤ : X.Opens))))
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X))))) :
    ∃ (U : Scheme.{u}) (q : U ⟶ X) (_ : Etale q) (_ : Surjective q)
      (s : F.obj.obj (op (Scheme.Etale.mk q))),
      etaleSetDescentUnit i F (Scheme.Etale.mk q) s =
        ((Scheme.etaleSetPullback i).obj F).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ i).map
            (MorphismProperty.Over.homMk q (Category.comp_id q) :
              Scheme.Etale.mk q ⟶ Scheme.Etale.mk (𝟙 X))).op t := by
  sorry

end AlgebraicGeometry
