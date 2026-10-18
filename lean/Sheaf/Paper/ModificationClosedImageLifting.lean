module

public import Sheaf.Paper.OrgogozoInductionData
public import WeilConjectures.Blowup.AdmissibleBlowup
public import Mathlib.Topology.GDelta.Basic

import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Density
import WeilConjectures.Blowup.Extension
import WeilConjectures.Compactification.StrictTransformBlowup
import Sheaf.Paper.AlterationBlowupFinite
import Sheaf.TraceFormula.ClosedImageGenericAlteration

/-!
# Gabber finite cover of a modified closed image

Source: Orgogozo, Modifications et cycles proches sur une base générale, Lemma 3.2.1, pp. 7--8
(blueprint: lem-trf-modification-closed-image-lifting).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Orgogozo

/-- Gabber's finite cover after a modification of the reduced closed image.
Source: Orgogozo, Modifications et cycles proches sur une base générale, Lemma 3.2.1, pp. 7--8
(blueprint: lem-trf-modification-closed-image-lifting).

Proof.
1. Factor the proper morphism `g` through the reduced closed image `F`: on affine charts a
   function in the radical ideal of the image pulls back to a function vanishing at every point
   of the reduced scheme `F'`, hence to zero. For every integral closed subscheme `Z` of `F`,
   `lem-trf-closed-image-generic-alteration` gives an integral closed `W_Z ⊆ F'` and an
   alteration `W_Z → Z` compatible with `g` (and with `F' → F`, since `F → S` is a monomorphism).
2. `lem-trf-alteration-blowup-finite` gives a nowhere dense centre `R_Z ⊊ Z`, the blow-up
   `Z~ = Bl_{R_Z} Z`, a blow-up modification `W~_Z → W_Z` and a finite surjective
   `W~_Z → Z~` over `Z`.
3. The constructible sets `Z \ R_Z` cover `F`. Since `F` is Noetherian it is spectral
   (`lem-weil-pbc-qcqs-scheme-spectral`); each `Z \ R_Z` is constructible
   (`def-weil-constructible-subset`), hence open in the constructible topology
   (`lem-weil-pbc-spectral-constructible-clopen-constructible-topology`), which is
   quasi-compact (`lem-weil-pbc-spectral-constructible-topology-quasi-compact`); so finitely
   many pairs `(Z_i, R_i)` cover `F`.
4. Each `R_i` misses the generic points of `S`. Iterating
   `lemma-nagata-product-ideal-common-blowup` gives `S' = Bl_{∏ J_i} S` dominating every
   `S_i = Bl_{R_i} S`; its centre is nowhere dense, and by
   `lemma-nagata-admissible-blowup-over-open`, `lemma-nagata-blowup-proper` and
   `lemma-nagata-conrad-dense-in-admissible-blowup` it is a modification in the sense of
   `def-trf-orgogozo-induction-data`. If `F` is empty, take the unit ideal and `G = ∅`.
5. For each reduced irreducible component `T_j` of `H = F ×_S S'`, choose `i` with the image of
   its generic point in `Z_i \ R_i`; by `lemma-nagata-strict-transform-ambient-closed` and
   `lemma-nagata-admissible-blowup-over-open`, the generic point of `T_j` maps into the strict
   transform `Z~_i ⊆ S_i`.
6. Since `T_j` is integral, the pulled-back ideal of `Z~_i` vanishes in the function field and
   hence on an affine cover, giving `a_j : T_j → Z~_i` over `S` and over `F`.
7. Put `G_j = T_j ×_{Z~_i} W~_{Z_i}`; its projection to `T_j` is finite by
   `lem-trf-finite-radicial-basechange` and surjective by `lem-weil-pbc-surjective-base-change`,
   and `G_j → W~_{Z_i} → W_{Z_i} → F'` is an `F`-morphism by the compatibilities of steps 1, 2, 6.
8. `H` is Noetherian, so it has finitely many components; `G = ∐_j G_j → H` is finite
   (`def-weil-finite-integral-morphism`) and surjective, and the maps `G_j → F'` assemble into the
   asserted `F`-morphism `G → F'`.
-/
theorem exists_finite_cover_modified_closedImage {S F' : Scheme.{u}}
    [IsReduced S] [IsNoetherian S] [IsReduced F'] [IsNoetherian F'] (g : F' ⟶ S) [IsProper g]
    (F : Scheme.{u}) (i : F ⟶ S) [IsClosedImmersion i] [IsReduced F]
    (himage : Set.range i = Set.range g)
    (factor : ∃ gF : F' ⟶ F, gF ≫ i = g) :
    ∃ (I : S.IdealSheafData),
      IsNowhereDense (I.support : Set S) ∧ IsModification I.blowupMap ∧
      ∃ (G : Scheme.{u}) (gG : G ⟶ F),
        ∃ (a : G ⟶ F') (q : G ⟶ pullback i I.blowupMap),
          a ≫ g = gG ≫ i ∧
          q ≫ pullback.fst i I.blowupMap = gG ∧
          IsFinite q ∧ Surjective q := by
  sorry

end AlgebraicGeometry.Orgogozo
