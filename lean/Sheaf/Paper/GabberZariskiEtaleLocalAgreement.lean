/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.Paper.SiteSheafificationSectionsLocal

/-! # Local reflection of equality for the Zariski–étale unit
Source: Stacks Project, Tag 09ZF, first proof paragraph.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Equality of pulled-back sections on a neighbourhood of z reflects to equality
on an open neighbourhood of i(z) in X.
Source: Stacks Project, Tag 09ZF (lemma-gabber-h0), first proof paragraph.
(blueprint: lem-weil-pbc-gabber-zariski-etale-local-agreement).

Proof: express the étale unit as the identity-indexed coprojection into the
presheaf left Kan extension followed by sheafification. Equality in the
sheafification is locally equality in that presheaf. Choose a point over z
in the resulting étale cover. Base change preserves finite limits, so the
index category is filtered; equality of the two classes is witnessed on an
étale X-scheme U with a point above i(z). Its image W0 is open, contains i(z),
and lies in W. Factor U through W0. This is a surjective étale morphism, hence
an étale covering. The two sections agree after restriction to U; separatedness
of F on that cover makes them agree on W0. Naturality and injectivity of the
presheaf isomorphism eX give the asserted equality in Fzar. The maps a and ha
identify the open preimage with the fibre product and its projection.
The assumed z in V rules out empty neighbourhoods; for empty Z the statement
has no instances. No finiteness hypothesis or closedness beyond that supplied
by the parent is used. -/
theorem gabber_zariski_etale_local_agreement
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (Fzar : TopCat.Sheaf (Type (max (u + 1) v)) X.carrier)
    (eX : Fzar.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        X.restrictFunctor (fun U => (inferInstance : Etale U.ι)) (fun _ => trivial)
        (fun _ => trivial)).op ⋙ F.obj)
    (iFzar : TopCat.Sheaf (Type (max (u + 1) v)) Z.carrier)
    (eZ : iFzar.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        Z.restrictFunctor (fun U => (inferInstance : Etale U.ι)) (fun _ => trivial)
        (fun _ => trivial)).op ⋙
      ((Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
        (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj F).obj)
    (a : ∀ W : X.Opens, Scheme.Etale.mk (i ⁻¹ᵁ W).ι ≅
      (MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk W.ι))
    (ha : ∀ W : X.Opens,
      (a W).hom.left ≫ pullback.fst W.ι i = i ∣_ W)
    (W : X.Opens) (z : Z.carrier) (hzW : i.base z ∈ W)
    (V : Z.Opens) (hzV : z ∈ V) (f : V ⟶ i ⁻¹ᵁ W)
    (s t : Fzar.obj.obj (op W))
    (heq : iFzar.obj.map f.op
      (eZ.inv.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafPullback
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
            (X.smallGrothendieckTopology @Etale)
            (Z.smallGrothendieckTopology @Etale)).obj F).obj.map (a W).hom.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
              (X.smallGrothendieckTopology @Etale)
              (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) s)))) =
      iFzar.obj.map f.op
      (eZ.inv.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafPullback
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
            (X.smallGrothendieckTopology @Etale)
            (Z.smallGrothendieckTopology @Etale)).obj F).obj.map (a W).hom.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
              (X.smallGrothendieckTopology @Etale)
              (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) t))))) :
    ∃ (W0 : X.Opens) (_ : i.base z ∈ W0) (g : W0 ⟶ W),
      Fzar.obj.map g.op s = Fzar.obj.map g.op t := by
  sorry

end AlgebraicGeometry
