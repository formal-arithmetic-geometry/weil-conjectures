/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.Topology.SpectralLimitCohomologyMap

/-! # Acyclic replacement of a compatible system on a spectral limit

Source: Stacks Project, Cohomology of Sheaves, Tag 0A37, lemma-colimit,
compatible injective construction and positive acyclicity paragraphs.
(blueprint: lem-weil-pbc-spectral-limit-acyclic-replacement)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace TopCat.Sheaf

/-- Dimension shifting for a compatible coefficient system on a spectral limit.
An embedding into compatible stage injectives with acyclic limit gives a quotient
system and connecting maps with a surjective boundary on the limit. The canonical
legs for the original and quotient systems commute with connecting morphisms for
every normalized cohomology pullback family. No finite-stage representation of
cohomology classes is asserted.

Source: Stacks Project, Cohomology of Sheaves, Tag 0A37, lemma-colimit,
second through fourth proof paragraphs.
(blueprint: lem-weil-pbc-spectral-limit-acyclic-replacement)

Proof: choose monomorphisms F_k to injectives A_k. Set G_i to the product, over k ≥ i,
of the direct images of A_k along f_ik. This is injective because continuous direct
image preserves injectives and products of injectives are injective. The component
of F_i to the k-factor is alpha_ik followed by the direct image of its embedding.
The identity factor proves this map monic. Define transitions by dropping factors
whose indices are not above the new index; the remaining factors agree by the
composition law for f. The alpha cocycle proves compatibility of the embeddings.
Take stage cokernels R_i. Exact inverse image and the cokernel universal property
give quotient transitions and their identity and composition laws. Pull back to X
and take filtered colimits. Exactness of inverse image and of filtered colimits of
abelian sheaves gives the asserted short exact sequence. The coprojections give
morphisms from its stage pullbacks, with the stated first and third components.
For positive acyclicity, compact opens pulled back from stages form a basis, closed
under finite intersections. Every finite covering in this basis descends to a
finite-stage covering, including its covering equality. Section comparison identifies
the limit Cech complex with the filtered colimit of the stage Cech complexes: each
degree uses only finitely many factors, so sections and their equalities have common
upper stages, and restrictions and alternating differentials agree. Each stage
complex has zero positive cohomology by injectivity. Exact filtered colimits preserve
this vanishing. The basis Cech criterion gives positive sheaf-cohomology vanishing,
in particular at the terminal open. Finally map each pulled-back stage short exact
sequence to the colimit short exact sequence using its coprojections. The first and
third components are exactly the canonical legs via eP and eQ. The normalized
pullback identity moves the stage connecting class into its inverse-image sequence.
Naturality of the Yoneda extension class under this short-complex morphism then
moves it into the colimit sequence. The final restriction from the inverse image
of the terminal open is along an equality and commutes with the boundary by equality
induction. Define d and D to be the stage and limit Yoneda boundaries. The limit
boundary is surjective because its middle sheaf has zero positive cohomology, by
the Ext long exact sequence. These identities give the asserted boundary square.
No induction or representation of a cohomology class is used. Empty opens and
covers cause no exception.
-/
theorem spectralLimit_acyclic_replacement
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u}) [∀ i : I, SpectralSpace (S i)]
    (f : ∀ (i j : I), i ≤ j → (S j ⟶ S i))
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfid : ∀ i : I, f i i le_rfl = 𝟙 (S i))
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      f j k hjk ≫ f i j hij = f i k (hij.trans hjk))
    (X : TopCat.{u}) [SpectralSpace X] (p : ∀ i : I, X ⟶ S i)
    (hpcomp : ∀ (i j : I) (h : i ≤ j), p j ≫ f i j h = p i)
    (hlimit : ∀ a : ∀ i : I, S i,
      (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) →
      ∃! x : X, ∀ i : I, p i x = a i)
    (htop : X.str = ⨅ i : I, TopologicalSpace.induced (p i) (S i).str)
    (F : ∀ i : I, (S i).Sheaf AddCommGrpCat.{u})
    (α : ∀ (i j : I) (h : i ≤ j),
      F i ⟶ (pushforward AddCommGrpCat.{u} (f i j h)).obj (F j))
    (hαid : ∀ (i : I) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq ((α i i le_rfl).hom.app (op U) s) s)
    (hαcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k)
      (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq ((α i k (hij.trans hjk)).hom.app (op U) s)
        ((α j k hjk).hom.app (op ((Opens.map (f i j hij)).obj U))
          ((α i j hij).hom.app (op U) s)))
    (P : I ⥤ X.Sheaf AddCommGrpCat.{u}) [HasColimit P]
    (eP : ∀ i : I, P.obj i ≅
      (sheafPullback (Opens.map (p i)) AddCommGrpCat.{u}
        (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).obj (F i))
    (hP : ∀ (i j : I) (h : i ≤ j) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq (((eP i).inv ≫ P.map (homOfLE h) ≫ (eP j).hom).hom.app
          (op ((Opens.map (p i)).obj U))
        (((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).unit.app
            (F i)).hom.app (op U) s))
        (((sheafAdjunctionContinuous (Opens.map (p j)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).unit.app
            (F j)).hom.app (op ((Opens.map (f i j h)).obj U))
              ((α i j h).hom.app (op U) s)))
 :
    ∃ (R : ∀ i : I, (S i).Sheaf AddCommGrpCat.{u})
      (ρ : ∀ (i j : I) (h : i ≤ j),
        R i ⟶ (pushforward AddCommGrpCat.{u} (f i j h)).obj (R j))
      (hρid : ∀ (i : I) (U : Opens (S i)) (s : (R i).obj.obj (op U)),
        HEq ((ρ i i le_rfl).hom.app (op U) s) s)
      (hρcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k)
        (U : Opens (S i)) (s : (R i).obj.obj (op U)),
        HEq ((ρ i k (hij.trans hjk)).hom.app (op U) s)
          ((ρ j k hjk).hom.app (op ((Opens.map (f i j hij)).obj U))
            ((ρ i j hij).hom.app (op U) s)))
      (Q : I ⥤ X.Sheaf AddCommGrpCat.{u}) (_ : HasColimit Q)
      (eQ : ∀ i : I, Q.obj i ≅
        (sheafPullback (Opens.map (p i)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).obj (R i))
      (hQ : ∀ (i j : I) (h : i ≤ j) (U : Opens (S i)) (s : (R i).obj.obj (op U)),
        HEq (((eQ i).inv ≫ Q.map (homOfLE h) ≫ (eQ j).hom).hom.app
            (op ((Opens.map (p i)).obj U))
          (((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).unit.app
              (R i)).hom.app (op U) s))
          (((sheafAdjunctionContinuous (Opens.map (p j)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).unit.app
              (R j)).hom.app (op ((Opens.map (f i j h)).obj U))
                ((ρ i j h).hom.app (op U) s)))
      (d : ∀ (i : I) (n : ℕ),
        CategoryTheory.Sheaf.H' (R i) n ⊤ → CategoryTheory.Sheaf.H' (F i) (n + 1) ⊤)
      (D : ∀ n : ℕ, CategoryTheory.Sheaf.H' (colimit Q) n ⊤ →
        CategoryTheory.Sheaf.H' (colimit P) (n + 1) ⊤),
      (∀ n : ℕ, Function.Surjective (D n)) ∧
      ∀ (i : I)
        (c : SiteCohomologyFamily (Opens.grothendieckTopology (S i))
          (Opens.grothendieckTopology X) (Opens.map (p i)))
        (_ : @SiteCohomologyFamily.IsPullback _ _ _ _
          (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)
          (Opens.map (p i)) inferInstance
          (@Adjunction.left_adjoint_additive _ _ _ _ _ _ _ _
            (sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
              (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X))
            (Functor.additive_of_preserves_binary_products _))
          inferInstance inferInstance c)
        (n : ℕ) (x : CategoryTheory.Sheaf.H' (R i) n ⊤),
        (spectralLimitCohomologyMap (p i) c
          ((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).homEquiv
              (F i) (colimit P) ((eP i).inv ≫ colimit.ι P i)) (n + 1)).hom (d i n x) =
        D n ((spectralLimitCohomologyMap (p i) c
          ((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).homEquiv
              (R i) (colimit Q) ((eQ i).inv ≫ colimit.ι Q i)) n).hom x) := by sorry

end TopCat.Sheaf
