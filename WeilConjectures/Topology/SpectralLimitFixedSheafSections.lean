/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Topology.AbelianLargeCompactOpenColimit
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Topology.InverseImageStalk

/-!
# Fixed-sheaf sections on a spectral inverse limit

Source: Stacks Project, Sheaves on Spaces, Tag 0A32, lemma-compute-pullback-to-limit,
with abelian coefficients as in Section 008N and composition as in Tag 008I
(blueprint: lem-sfb-spectral-limit-fixed-sheaf-sections).

The helpers abbreviate the recorded inverse-image construction and construct its
unit-normalized section maps. The theorem permits any presentation of the resulting
diagram and canonical colimit comparison, specifying both on every section group.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Sheaf.SpectralFixedSections

/-- The recorded sheafification of presheaf inverse image, allowing larger coefficients.
Source: Stacks, Tags 008C and 008N
(blueprint: lem-sfb-spectral-limit-fixed-sheaf-sections). -/
abbrev inverseImage {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Y.Sheaf AddCommGrpCat.{max u v} ⥤ X.Sheaf AddCommGrpCat.{max u v} :=
  Functor.sheafPullbackConstruction.sheafPullback (Opens.map f)
    AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- Its actual adjunction, whose unit is the presheaf unit followed by sheafification.
Source: Stacks, Tags 008C and 008N
(blueprint: lem-sfb-spectral-limit-fixed-sheaf-sections). -/
abbrev inverseImageAdjunction {X Y : TopCat.{u}} (f : X ⟶ Y) :
    inverseImage.{u, v} f ⊣ pushforward AddCommGrpCat.{max u v} f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
    AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The inverse-image compositor uniquely normalized by the composite adjunction unit.
Source: Stacks, Tag 008I (blueprint: lem-sfb-spectral-limit-fixed-sheaf-sections). -/
@[irreducible] def compositionIso {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Z.Sheaf AddCommGrpCat.{max u v}) :
    (inverseImage f).obj ((inverseImage g).obj G) ≅ (inverseImage (f ≫ g)).obj G :=
  (((inverseImageAdjunction g).comp (inverseImageAdjunction f)).leftAdjointUniq
    (inverseImageAdjunction (f ≫ g))).app G

/-- Pull back a section by the unit, then apply the normalized compositor and the
specified equality of the composite continuous map.
Source: Stacks, Tags 008I and 0A32
(blueprint: lem-sfb-spectral-limit-fixed-sheaf-sections). -/
@[irreducible] def compositionMap {X Y Z : TopCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (G : Z.Sheaf AddCommGrpCat.{max u v}) :
    (inverseImage g).obj G ⟶
      (pushforward AddCommGrpCat.{max u v} f).obj ((inverseImage k).obj G) :=
  (inverseImageAdjunction f).unit.app _ ≫
    (pushforward AddCommGrpCat.{max u v} f).map
      ((compositionIso f g G).hom ≫
        eqToHom (congrArg (fun a ↦ (inverseImage a).obj G) h))

/-- The section group at a stage above the chosen index.
Source: Stacks, Tag 0A32 (blueprint: lem-sfb-spectral-limit-fixed-sheaf-sections). -/
abbrev sections {I : Type u} [Preorder I] (S : I → TopCat.{u})
    (f : ∀ (j k : I), j ≤ k → (S k ⟶ S j))
    (i : I) (G : (S i).Sheaf AddCommGrpCat.{max u v}) (U : Opens (S i))
    (j : I) (hij : i ≤ j) : AddCommGrpCat.{max u v} :=
  ((inverseImage (f i j hij)).obj G).obj.obj (op ((Opens.map (f i j hij)).obj U))

/-- The transition homomorphism, including transport across the equal inverse-image opens.
Source: Stacks, Tag 0A32 (blueprint: lem-sfb-spectral-limit-fixed-sheaf-sections). -/
@[irreducible] def transition {I : Type u} [Preorder I] (S : I → TopCat.{u})
    (f : ∀ (j k : I), j ≤ k → (S k ⟶ S j))
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      f j k hjk ≫ f i j hij = f i k (hij.trans hjk))
    (i : I) (G : (S i).Sheaf AddCommGrpCat.{max u v}) (U : Opens (S i))
    (j k : I) (hij : i ≤ j) (hjk : j ≤ k) :
    sections S f i G U j hij ⟶ sections S f i G U k (hij.trans hjk) :=
  (compositionMap (f j k hjk) (f i j hij) (f i k (hij.trans hjk))
    (hfcomp i j k hij hjk) G).hom.app (op ((Opens.map (f i j hij)).obj U)) ≫
    ((inverseImage (f i k (hij.trans hjk))).obj G).obj.map
      (eqToHom (congrArg (fun a ↦ (Opens.map a).obj U) (hfcomp i j k hij hjk)).symm).op

/-- The comparison leg from a stage to the limit section group, with the same normalization.
Source: Stacks, Tag 0A32 (blueprint: lem-sfb-spectral-limit-fixed-sheaf-sections). -/
@[irreducible] def comparison {I : Type u} [Preorder I] (S : I → TopCat.{u})
    (f : ∀ (j k : I), j ≤ k → (S k ⟶ S j))
    (X : TopCat.{u}) (p : ∀ j : I, X ⟶ S j)
    (hpcomp : ∀ (j k : I) (h : j ≤ k), p k ≫ f j k h = p j)
    (i : I) (G : (S i).Sheaf AddCommGrpCat.{max u v}) (U : Opens (S i))
    (j : I) (hij : i ≤ j) :
    sections S f i G U j hij ⟶
      ((inverseImage (p i)).obj G).obj.obj (op ((Opens.map (p i)).obj U)) :=
  (compositionMap (p j) (f i j hij) (p i) (hpcomp i j hij) G).hom.app
    (op ((Opens.map (f i j hij)).obj U)) ≫
    ((inverseImage (p i)).obj G).obj.map
      (eqToHom (congrArg (fun a ↦ (Opens.map a).obj U) (hpcomp i j hij)).symm).op

/-- Fixed-sheaf section continuity, with the canonical abelian comparison and its two
explicit elementwise consequences. `eB` only presents the specified stage section groups;
`hBmap` and `hm` fix all transitions and coprojection images to the constructed maps.

Source: Stacks Project, Sheaves on Spaces, Tag 0A32, lines 3558--3625, with abelian
coefficients via Section 008N and normalized composition from Tag 008I
(blueprint: lem-sfb-spectral-limit-fixed-sheaf-sections).

Proof, following the node:
1. Upper tails have the same tuple limit (extend coordinates using a common upper bound).
   The spectral limit projections lemma, Tag 0A2Z, makes the limit and projections spectral.
2. Uniqueness of adjoints defines the compositor, with the composite unit normalization.
   Uniqueness also gives identity and triple coherence, hence the section diagram and cocone.
3. For sections of any sheaf at any stage with equal limit images, use the inverse-image
   stalk isomorphism to identify the unequal-germ loci at all later stages compatibly.
4. These loci are constructibly closed: equality of germs is open and the ambient compact
   open is constructibly clopen. The patch-closed nonempty-system lemma, Tag 0A2W, would
   produce an unequal germ at the limit if all loci were nonempty. Some locus is therefore
   empty; the underlying-set sheaf condition and determination by germs give equality.
5. Projection preimages of compact opens form a basis. Finite unions and a common upper
   bound descend each compact open. Patch-closed compactness similarly descends finitely
   many inclusions and cover equalities, giving the argument of Topology Tag 0A30.
6. Represent a limit section locally by unit images using the inverse-image stalk lemma.
   Compactness gives finitely many compact-open representatives, or the empty cover.
7. Descend this cover and its inclusions to one stage. On each compact overlap, steps 3--4
   give eventual equality; take one upper bound for the finitely many overlap stages.
8. The sheaf equalizer axiom glues the sections at that stage. Separation identifies its
   image with the original section. Steps 3--4 also give same-stage eventual equality.
9. For any compatible family of homomorphisms, assign a section the value of a stage
   representative. Eventual equality makes it well defined; common stages prove additivity.
   Surjectivity makes it unique. This is the abelian colimit universal property, so the
   canonical comparison is an isomorphism. Empty spaces and empty opens are allowed. -/
theorem continuity
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u}) [∀ j : I, SpectralSpace (S j)]
    (f : ∀ (j k : I), j ≤ k → (S k ⟶ S j))
    (hf : ∀ (j k : I) (h : j ≤ k), IsSpectralMap (f j k h))
    (hfid : ∀ j : I, f j j le_rfl = 𝟙 (S j))
    (hfcomp : ∀ (j k l : I) (hjk : j ≤ k) (hkl : k ≤ l),
      f k l hkl ≫ f j k hjk = f j l (hjk.trans hkl))
    (X : TopCat.{u}) (p : ∀ j : I, X ⟶ S j)
    (hpcomp : ∀ (j k : I) (h : j ≤ k), p k ≫ f j k h = p j)
    (hlimit : ∀ a : ∀ j : I, S j,
      (∀ (j k : I) (h : j ≤ k), f j k h (a k) = a j) →
      ∃! x : X, ∀ j : I, p j x = a j)
    (htop : X.str = ⨅ j : I, TopologicalSpace.induced (p j) (S j).str)
    (i : I) (G : (S i).Sheaf AddCommGrpCat.{max u v}) (U : Opens (S i))
    (hU : IsCompact (U : Set (S i)))
    (B : Set.Ici i ⥤ AddCommGrpCat.{max u v})
    (eB : ∀ j : Set.Ici i, B.obj j ≅ sections S f i G U j.val j.property)
    (hBmap : ∀ (j k : Set.Ici i) (hjk : j ≤ k),
      (eB j).hom ≫ transition S f hfcomp i G U j.val k.val j.property hjk =
        B.map (homOfLE hjk) ≫ (eB k).hom)
    (m : colimit B ⟶ ((inverseImage (p i)).obj G).obj.obj (op ((Opens.map (p i)).obj U)))
    (hm : ∀ j : Set.Ici i,
      (eB j).inv ≫ colimit.ι B j ≫ m = comparison S f X p hpcomp i G U j.val j.property) :
    IsIso m ∧
      (∀ s : ((inverseImage (p i)).obj G).obj.obj (op ((Opens.map (p i)).obj U)),
        ∃ (j : I) (hij : i ≤ j) (t : sections S f i G U j hij),
          comparison S f X p hpcomp i G U j hij t = s) ∧
      (∀ (j : I) (hij : i ≤ j) (t t' : sections S f i G U j hij),
        comparison S f X p hpcomp i G U j hij t =
          comparison S f X p hpcomp i G U j hij t' →
        ∃ (k : I) (hjk : j ≤ k),
          transition S f hfcomp i G U j k hij hjk t =
            transition S f hfcomp i G U j k hij hjk t') := by
  sorry

end TopCat.Sheaf.SpectralFixedSections
