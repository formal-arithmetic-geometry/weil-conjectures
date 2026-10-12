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
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.Paper.GabberZariskiEtaleRestrictionInjective
import Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites

/-! # Zariski gluing after a local refinement of an étale representative

Source: Stacks Project, Tag 09ZF, fourth proof paragraph, construction of the
section of the Zariski inverse image and compatibility with its unit.
(blueprint: lem-weil-pbc-gabber-h0-zariski-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Locally factoring a morphism through an étale representative puts the restricted
section in the Zariski inverse image. The map lift identifies global Zariski
sections with étale sections, and compare is compatible with the Zariski unit.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph, construction of t'
and its membership in the Zariski inverse-image subsheaf.
(blueprint: lem-weil-pbc-gabber-h0-zariski-gluing).

Proof:
1. Put F' = h^*F and i' = pullback.snd i h. Restrict F' to the open-subscheme
   site of X' to obtain G. The canonical identification of the top open scheme
   with X', and of X' with the pullback of the identity of X, gives the map lift.
2. On W_a, use phi_a and its commuting equation to pull s back to a section of
   F'. Naturality and the unit-compatible composition isomorphism show that its
   restriction to W_a times_X Z is the transported pullback t' of t.
3. Apply the injective Zariski-to-étale comparison for the closed immersion i'.
   Send these local F' sections by the Zariski inverse-image unit. On overlaps
   their comparison images are both restrictions of t'. Injectivity therefore
   makes their Zariski images agree. Glue them by the topological sheaf axiom
   to sigma. The preimages of the W_a cover Z', including when the cover is empty.
4. Compose the global component of this comparison with the étale composition
   isomorphism and the canonical fibre-product identifications to define compare.
   Its value at sigma equals the pullback of t by the sheaf axiom. Its value on
   a Zariski unit equals the pullback of lift a, by the comparison-unit equation.
   Transport the latter along pullback.condition to get exactly the displayed
   equation. No finite-morphism, compactness, or global-section-bijectivity
   hypothesis is used in this gluing argument. -/
theorem gabber_h0_zariski_gluing
    {X Z U X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (q : U ⟶ X) [Etale q] (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X)))))
    (s : F.obj.obj (op (Scheme.Etale.mk q)))
    (hs : etaleSetDescentUnit i F (Scheme.Etale.mk q) s =
      ((Scheme.etaleSetPullback i).obj F).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ i).map
          (MorphismProperty.Over.homMk q (Category.comp_id q) :
            Scheme.Etale.mk q ⟶ Scheme.Etale.mk (𝟙 X))).op t)
    (J : Type) (W : J → X'.Opens) (phi : ∀ a, (W a).toScheme ⟶ U)
    (hW : ⨆ a, W a = ⊤) (hphi : ∀ a, phi a ≫ q = (W a).ι ≫ h) :
    let b : CategoryTheory.Functor.{u, u, u, u}
        X'.Opens (pullback i h : Scheme.{u}).Opens :=
      Opens.map ((pullback.snd i h : (pullback i h : Scheme.{u}) ⟶ X').base)
    letI : ∀ P : X'.Opensᵒᵖ ⥤ Type (u + 1), b.op.HasPointwiseLeftKanExtension P :=
      fun P V ↦
        @Types.hasColimit.{u, u + 1, u} (CostructuredArrow.{u, u, u, u} b.op V)
          inferInstance (small_succ.{u} _) (CostructuredArrow.proj b.op V ⋙ P)
    ∃ (G : TopCat.Sheaf (Type (u + 1)) X'.toTopCat)
      (lift : G.obj.obj (op (⊤ : X'.Opens)) →
        ((Scheme.etaleSetPullback h).obj F).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
            (Scheme.Etale.mk (𝟙 X)))))
      (compare :
        ((Functor.sheafPullbackConstruction.sheafPullback b (Type (u + 1))
          (Opens.grothendieckTopology X')
          (Opens.grothendieckTopology (pullback i h : Scheme.{u}))).obj G).obj.obj
            (op (⊤ : (pullback i h : Scheme.{u}).Opens)) →
        ((Scheme.etaleSetPullback (pullback.fst i h ≫ i)).obj F).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst i h ≫ i)).obj
            (Scheme.Etale.mk (𝟙 X)))))
      (sigma :
        ((Functor.sheafPullbackConstruction.sheafPullback b (Type (u + 1))
          (Opens.grothendieckTopology X')
          (Opens.grothendieckTopology (pullback i h : Scheme.{u}))).obj G).obj.obj
            (op (⊤ : (pullback i h : Scheme.{u}).Opens))),
      compare sigma =
        etaleSetDescentComparison i (pullback.fst i h) F (Scheme.Etale.mk (𝟙 X)) t ∧
      ∀ a : G.obj.obj (op (⊤ : X'.Opens)),
        compare
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            b (Type (u + 1)) (Opens.grothendieckTopology X')
            (Opens.grothendieckTopology (pullback i h : Scheme.{u}))).unit.app G).hom.app
              (op (⊤ : X'.Opens)) a) =
          eqToHom (congrArg
            (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)
            (etaleSetDescentComparison h (pullback.snd i h) F
              (Scheme.Etale.mk (𝟙 X)) (lift a)) := by
  sorry

end AlgebraicGeometry
