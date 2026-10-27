/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism
import Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection
import WeilConjectures.AlgebraicGeometry.EtaleSubsheafFinalOpen
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

/-! # Realization over an algebraic-space base

Source: Stacks Project, Properties of Spaces, Tag 0GF6, its preceding construction
and size condition; Tags 03G1, 03G2 and 03LP
(blueprint: lem-sfb-space-etale-sheaf-realization).

The common bound is expressed by a scheme presentation: an epimorphism from the
Hom sheaf of one étale scheme. This is exactly the presentation obtained by forming
the coproduct of the scheme generators with sections in the stated ambient universe.
The realization equivalence is existential, with its values and both naturalities
specified. No algebraic space is defined by choosing an unspecified existence witness.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {B : Scheme.{u}}

/-- The actual relative Hom presheaf, restricted to scheme objects.
Source: Stacks 0GF6 (blueprint: lem-sfb-space-etale-sheaf-realization). -/
def spaceEtaleHomPresheaf (H : AlgebraicSpace B) (V : H.EnlargedEtaleSite) :
    H.EtaleSiteᵒᵖ ⥤ Type (u + 1) :=
  (enlargedSchemeInclusion H).op ⋙ yoneda.obj V

/-- Relative Hom presheaves are sheaves for the small étale topology.
Source: Stacks 0GF6, representable sheaves in its proof
(blueprint: lem-sfb-space-etale-sheaf-realization).
Proof (node Step 1): glue maps to the algebraic space `V` on an étale covering by
its fppf sheaf axiom. Their composites to `H` agree with the given structural map
locally, hence globally by the separatedness of `H`. Uniqueness gives the sheaf axiom.
This uses no representability of `V → H`. -/
theorem spaceEtaleHom_isSheaf (H : AlgebraicSpace B) (V : H.EnlargedEtaleSite) :
    Presheaf.IsSheaf H.etaleTopology (spaceEtaleHomPresheaf H V) := by
  sorry

/-- The functor `V ↦ h_V`; its arrows are postcomposition by all maps over `H`.
Source: Stacks 0GF6 (blueprint: lem-sfb-space-etale-sheaf-realization). -/
def spaceEtaleHomFunctor (H : AlgebraicSpace B) :
    H.EnlargedEtaleSite ⥤ Sheaf H.etaleTopology (Type (u + 1)) where
  obj V := ⟨spaceEtaleHomPresheaf H V, spaceEtaleHom_isSheaf H V⟩
  map f := ⟨Functor.whiskerLeft (enlargedSchemeInclusion H).op (yoneda.map f)⟩

/-- The explicit common bound of Stacks 0GF6: the coproduct of the chosen scheme
presentation generators is a scheme in the ambient site. Equivalently the sheaf
has an epimorphism from one scheme Hom sheaf. This records only the size condition,
not a choice of quotient, realization, or an arbitrary map to the base.
Source: Stacks 0GF6, third proof paragraph and size footnote
(blueprint: lem-sfb-space-etale-sheaf-realization). -/
def SpaceEtaleSheafInBound (H : AlgebraicSpace B)
    (F : Sheaf H.etaleTopology (Type (u + 1))) : Prop :=
  ∃ (P : H.EtaleSite)
    (p : (spaceEtaleHomFunctor H).obj ((enlargedSchemeInclusion H).obj P) ⟶ F), Epi p

/-- Sheaves in the common presentation bound, with all sheaf morphisms.
Source: Stacks 0GF6, size condition
(blueprint: lem-sfb-space-etale-sheaf-realization). -/
abbrev SpaceEtaleSheaves (H : AlgebraicSpace B) :=
  ObjectProperty.FullSubcategory (SpaceEtaleSheafInBound H)

/-- Every chartwise étale algebraic space has its Hom sheaf in the same bound.
Source: Stacks 0GF6 and the scheme-atlas construction
(blueprint: lem-sfb-space-etale-sheaf-realization).
Proof (node Steps 1 and 6, for an arbitrary space): choose a surjective étale scheme
atlas of `V`. Its composite to `H` is representable étale by chartwise étaleness.
Every map from a scheme object to `V` lifts locally along this atlas; its scheme
pullback is a covering. These local lifts make the induced map of Hom sheaves epi.
The atlas is a scheme in the given bound. -/
theorem spaceEtaleHom_inBound (H : AlgebraicSpace B) (V : H.EnlargedEtaleSite) :
    SpaceEtaleSheafInBound H ((spaceEtaleHomFunctor H).obj V) := by
  sorry

/-- Relative Hom valued in the common bound, still with every morphism over `H`.
Source: Stacks 0GF6 (blueprint: lem-sfb-space-etale-sheaf-realization). -/
def spaceEtaleBoundedHomFunctor (H : AlgebraicSpace B) :
    H.EnlargedEtaleSite ⥤ SpaceEtaleSheaves H :=
  ObjectProperty.lift _ (spaceEtaleHomFunctor H) (spaceEtaleHom_inBound H)

/-- Canonical inverse image on the enlarged sites. Its right adjoint is prescribed
as evaluation on fibre products; hence its data are determined up to the unique
adjunction-compatible isomorphism. Source: Stacks 03G2
(blueprint: lem-sfb-space-etale-sheaf-realization). -/
def spaceRealizationInverse {X Y : AlgebraicSpace B} (f : X ⟶ Y) :
    Sheaf Y.enlargedEtaleTopology (Type (u + 1)) ⥤
      Sheaf X.enlargedEtaleTopology (Type (u + 1)) :=
  (enlargedDirectImage_geometric.{u, 0} f).choose.inverse

/-- The adjunction to the prescribed direct image, retaining its normalization.
Source: Stacks 03G2 (blueprint: lem-sfb-space-etale-sheaf-realization). -/
def spaceRealizationAdjunction {X Y : AlgebraicSpace B} (f : X ⟶ Y) :
    spaceRealizationInverse f ⊣ enlargedDirectImage f (Type (u + 1)) :=
  (enlargedDirectImage_geometric.{u, 0} f).choose.adj.ofNatIsoRight
    (eqToIso (enlargedDirectImage_geometric.{u, 0} f).choose_spec)

/-- Pull a global section back by inverse image and its canonical terminal comparison.
Source: Stacks 03G2 (blueprint: lem-sfb-space-etale-sheaf-realization). -/
def spaceRealizationPullSection {X Y : AlgebraicSpace B} (f : X ⟶ Y)
    (F : Sheaf Y.enlargedEtaleTopology (Type (u + 1)))
    (s : ⊤_ (Sheaf Y.enlargedEtaleTopology (Type (u + 1))) ⟶ F) :
    ⊤_ (Sheaf X.enlargedEtaleTopology (Type (u + 1))) ⟶
      (spaceRealizationInverse f).obj F :=
  letI : PreservesFiniteLimits (spaceRealizationInverse f) :=
    (enlargedDirectImage_geometric.{u, 0} f).choose.leftExact
  (PreservesTerminal.iso (spaceRealizationInverse f)).inv ≫ (spaceRealizationInverse f).map s

/-- A scheme arrow as the actual Yoneda map of algebraic spaces.
Source: Stacks 025Y and 0GF6 (blueprint: lem-sfb-space-etale-sheaf-realization). -/
def spaceRealizationSchemeMap {T T' : Over B} (g : T' ⟶ T) :
    schemeSpace T' ⟶ schemeSpace T :=
  ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map g)

/-- The displayed pair formula on every scheme test. Global sections are morphisms
from the terminal sheaf. Scheme restriction identifies these with sections on `T_et`.
Source: Stacks 0GF6, construction preceding the lemma
(blueprint: lem-sfb-space-etale-sheaf-realization). -/
def SpaceRealizationPairs (H : AlgebraicSpace B)
    (F : Sheaf H.etaleTopology (Type (u + 1))) (T : Over B) :=
  Σ h : schemeSpace T ⟶ H,
    (⊤_ (Sheaf (schemeSpace T).enlargedEtaleTopology (Type (u + 1))) ⟶
      (spaceRealizationInverse h).obj ((enlargedSetEquivalence.{u, 0} H).inverse.obj F))

/-- Restriction is `(h,s) ↦ (g ≫ h,g⁻¹s)` using the canonical composition comparison.
Source: Stacks 0GF6 and 03G2(2)
(blueprint: lem-sfb-space-etale-sheaf-realization). -/
def spaceRealizationPairRestrict (H : AlgebraicSpace B)
    (F : Sheaf H.etaleTopology (Type (u + 1))) {T T' : Over B} (g : T' ⟶ T)
    (a : SpaceRealizationPairs H F T) : SpaceRealizationPairs H F T' :=
  ⟨spaceRealizationSchemeMap g ≫ a.1,
    spaceRealizationPullSection (spaceRealizationSchemeMap g) _ a.2 ≫
      (enlargedInverseCompositionIso (Type (u + 1))
        (fun _ _ f ↦ spaceRealizationInverse f) (fun f ↦ spaceRealizationAdjunction f)
        (spaceRealizationSchemeMap g) a.1).hom.app _⟩

/-- A sheaf morphism acts on the second component by its inverse image.
Source: Stacks 0GF6 (blueprint: lem-sfb-space-etale-sheaf-realization). -/
def spaceRealizationPairMap (H : AlgebraicSpace B)
    {F G : Sheaf H.etaleTopology (Type (u + 1))} (a : F ⟶ G) (T : Over B)
    (s : SpaceRealizationPairs H F T) : SpaceRealizationPairs H G T :=
  ⟨s.1, s.2 ≫ (spaceRealizationInverse s.1).map
    ((enlargedSetEquivalence.{u, 0} H).inverse.map a)⟩

/-- Realization of small étale sheaves over an arbitrary algebraic space, in the
explicit common presentation bound. The equivalence has the specified Hom inverse;
the bijections give its exact pair formula, projection, and both naturalities.
Source: Stacks 0GF6, construction and parts (1)--(3), with its size condition;
03G2 and 03LP (blueprint: lem-sfb-space-etale-sheaf-realization).

Proof:
1. By fppf descent relative Hom on the scheme étale site is a sheaf, including
   scheme representables (def-trf-algebraic-space, def-pc-fppf-site).
2. Form the scheme coproduct of the chosen generators with sections, allowed by
   the common bound (lem-weil-pbc-scheme-coproduct-family). Its map to `H` is
   representable étale by lem-weil-pbc-etale-local-on-source. Yoneda gives an epi
   `h_P → F`; equivalently use the scheme presentation in SpaceEtaleSheafInBound.
3. On `P ×_H P`, equality of its two sections is a subsheaf of the final sheaf.
   Represent it by an open `R` using lem-weil-pbc-etale-subsheaf-final-open.
   Chartwise permanence identifies `h_R` with the kernel pair on all étale tests.
4. Yoneda gives reflexivity, symmetry and composition as actual scheme maps.
   The open relation is monomorphic. The epi kernel-pair coequalizer theorem
   (lem-weil-pbc-site-sheaf-sets-epi-kernel-pair-coequalizer) gives `F = h_P/h_R`.
5. lem-trf-etale-relation-quotient produces `Q=P/R`, its atlas and kernel pair.
   The descended map to `H` is chartwise étale by source-atlas detection (3).
6. Local atlas lifts make `h_P → h_Q` epi with kernel pair `h_R`. The same
   coequalizer universal property gives `F ≅ h_Q`.
7. Represented sheaves on the enlarged site satisfy descent: refine covers by
   scheme atlases, glue by the fppf axiom, and descend from a scheme atlas of
   the target. Scheme density identifies their restrictions with small-site Hom.
8. The enlarged-site adjunction and Yoneda give `h⁻¹h_A ≅ h_(T×_H A)`, since
   direct image evaluates on exactly `T×_H A`. Transport by scheme restriction.
9. Apply this to `Q`. Global sections at `T/T` become `Hom_H(T,Q)` via
   `a ↦ (id_T,a)`. Thus the pair presheaf is the algebraic space `Q`, and its
   projection is the chartwise étale structural map. Adjunction naturality
   gives the displayed restriction along every scheme map.
10. The same calculation for every chartwise étale `V` gives the natural counit,
    compatible with every map over `H`; representability is never required.
11. For an étale scheme `U → H`, localization gives `Γ(U,u⁻¹F)=F(U)`.
    These bijections give the natural unit, compatible with every sheaf map.
    Together the unit and counit give the stated equivalence. -/
theorem spaceEtaleSheaf_realization (H : AlgebraicSpace B) :
    ∃ e : SpaceEtaleSheaves H ≌ H.EnlargedEtaleSite,
      e.inverse = spaceEtaleBoundedHomFunctor H ∧
      ∃ b : ∀ (F : SpaceEtaleSheaves H) (T : Over B),
          (schemeSpace T ⟶ (e.functor.obj F).obj.left) ≃ SpaceRealizationPairs H F.obj T,
        (∀ (F : SpaceEtaleSheaves H) (T : Over B)
          (a : schemeSpace T ⟶ (e.functor.obj F).obj.left),
          (b F T a).1 = a ≫ (e.functor.obj F).obj.hom) ∧
        (∀ (F : SpaceEtaleSheaves H) (T T' : Over B) (g : T' ⟶ T)
          (a : schemeSpace T ⟶ (e.functor.obj F).obj.left),
          b F T' (spaceRealizationSchemeMap g ≫ a) =
            spaceRealizationPairRestrict H F.obj g (b F T a)) ∧
        (∀ (F G : SpaceEtaleSheaves H) (a : F ⟶ G) (T : Over B)
          (s : schemeSpace T ⟶ (e.functor.obj F).obj.left),
          b G T (s ≫ (e.functor.map a).hom.left) =
            spaceRealizationPairMap H a.hom T (b F T s)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
