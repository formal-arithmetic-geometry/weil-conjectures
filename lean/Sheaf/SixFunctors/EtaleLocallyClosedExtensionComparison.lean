module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex

/-!
# Étale extension by zero for locally closed immersions

Source: literature/stacks-project/etale-cohomology.tex, Tag 0GJ1
(blueprint: lem-sfb-etale-locally-closed-extension-comparison).

The finite-open comparison is stated for the canonical pullback square.  The
closure-defined extension uses the scheme-theoretic image and its canonical
open factor.  Its factorization and closed-immersion compatibilities are
recorded as natural-isomorphism existence statements.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- The closure-defined étale extension associated to a quasi-compact immersion.

Source: Stacks Project, Morphisms, Tags 01R6--01R8
(blueprint: lem-sfb-etale-locally-closed-extension-comparison). It is the composite of
extension by zero along `a.toImage` and direct image along `a.imageι`.
-/
noncomputable def etaleLocallyClosedExtension
    {A : Type (u + 1)} [CommRing A]
    {S X : Scheme.{u}} (a : S ⟶ X) [IsImmersion a]
    (hqa : QuasiCompact a) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) := by
  letI : QuasiCompact a := hqa
  exact Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) a.toImage ⋙
    Etale.lowerStar (ModuleCat.{u + 1} A) a.imageι

/-- The canonical restriction normalization for the closure-defined extension.

Source: literature/stacks-project/etale-cohomology.tex, Tags 0F70 and 04CA;
Morphisms, Tags 01R6--01R8
(blueprint: lem-sfb-etale-locally-closed-extension-comparison).

This is the inverse of the open-extension unit, followed by the closed
pushforward counit, with the pullback composition comparison for
`a = a.toImage ≫ a.imageι`. -/
noncomputable def etaleLocallyClosedExtensionRestrictionIso
    {A : Type (u + 1)} [CommRing A]
    {S X : Scheme.{u}} (a : S ⟶ X) [IsImmersion a]
    (hqa : QuasiCompact a) :
    etaleLocallyClosedExtension (A := A) a hqa ⋙ Etale.upperStar (ModuleCat.{u + 1} A) a ≅
      𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  letI : QuasiCompact a := hqa
  let L := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) a.toImage
  let R := Etale.lowerStar (ModuleCat.{u + 1} A) a.imageι
  let P := Etale.upperStar (ModuleCat.{u + 1} A) a
  let Q := Etale.upperStar (ModuleCat.{u + 1} A) a.imageι
  let T := Etale.upperStar (ModuleCat.{u + 1} A) a.toImage
  let ecomp := Etale.upperStarComp (ModuleCat.{u + 1} A) a.toImage a.imageι
    a (Scheme.Hom.toImage_imageι a).symm
  exact
    Functor.associator L R P ≪≫
      Functor.isoWhiskerLeft L (
        Functor.isoWhiskerLeft R ecomp ≪≫
          (Functor.associator R Q T).symm ≪≫
          Functor.isoWhiskerRight
            (asIso (Etale.upperStarLowerStarAdjunction
              (ModuleCat.{u + 1} A) a.imageι).counit) T ≪≫
          Functor.leftUnitor T) ≪≫
      (asIso (Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) a.toImage).unit).symm

/-- The canonical restriction normalization for a closed-then-open factorization.

Source: literature/stacks-project/etale-cohomology.tex, Tags 0F70, 04CA and 0GJ1
(blueprint: lem-sfb-etale-locally-closed-extension-comparison).

The two adjunction units/counits and the pullback composition comparison specify
the restriction to the identity on the locally closed source. -/
noncomputable def etaleFactorizationRestrictionIso
    {A : Type (u + 1)} [CommRing A]
    {S W X : Scheme.{u}} (a : S ⟶ X)
    (h : S ⟶ W) (u : W ⟶ X)
    [IsClosedImmersion h] [IsOpenImmersion u]
    (ha : h ≫ u = a) :
    (Etale.lowerStar (ModuleCat.{u + 1} A) h ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) u) ⋙
      Etale.upperStar (ModuleCat.{u + 1} A) a ≅
      𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  let F := Etale.lowerStar (ModuleCat.{u + 1} A) h
  let G := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) u
  let P := Etale.upperStar (ModuleCat.{u + 1} A) a
  let Q := Etale.upperStar (ModuleCat.{u + 1} A) u
  let T := Etale.upperStar (ModuleCat.{u + 1} A) h
  let ecomp := Etale.upperStarComp (ModuleCat.{u + 1} A) h u a ha.symm
  exact
    Functor.associator F G P ≪≫
      Functor.isoWhiskerLeft F (
        Functor.isoWhiskerLeft G ecomp ≪≫
          (Functor.associator G Q T).symm ≪≫
          Functor.isoWhiskerRight
            (asIso (Etale.openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) u).unit).symm T ≪≫
          Functor.leftUnitor T) ≪≫
      asIso (Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) h).counit

/-- The canonical restriction normalization after a further closed immersion.

Source: literature/stacks-project/etale-cohomology.tex, Tags 0F70 and 04CA;
Morphisms, Tags 01R6--01R8
(blueprint: lem-sfb-etale-locally-closed-extension-comparison).
It uses pullback composition, the closed counit for `i`, and the closure normalization
for `b`. -/
noncomputable def etaleClosedCompositionRestrictionIso
    {A : Type (u + 1)} [CommRing A]
    {S Y X : Scheme.{u}} (a : S ⟶ X) (b : S ⟶ Y) (i : Y ⟶ X)
    [IsClosedImmersion i] [IsImmersion b]
    (hqb : QuasiCompact b) (ha : b ≫ i = a) :
    (etaleLocallyClosedExtension (A := A) b hqb ⋙
        Etale.lowerStar (ModuleCat.{u + 1} A) i) ⋙
      Etale.upperStar (ModuleCat.{u + 1} A) a ≅
      𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  let E := etaleLocallyClosedExtension (A := A) b hqb
  let F := Etale.lowerStar (ModuleCat.{u + 1} A) i
  let P := Etale.upperStar (ModuleCat.{u + 1} A) a
  let Q := Etale.upperStar (ModuleCat.{u + 1} A) i
  let T := Etale.upperStar (ModuleCat.{u + 1} A) b
  let ecomp := Etale.upperStarComp (ModuleCat.{u + 1} A) b i a ha.symm
  exact
    Functor.associator E F P ≪≫
      Functor.isoWhiskerLeft E (
        Functor.isoWhiskerLeft F ecomp ≪≫
          (Functor.associator F Q T).symm ≪≫
          Functor.isoWhiskerRight
            (asIso (Etale.upperStarLowerStarAdjunction
              (ModuleCat.{u + 1} A) i).counit) T ≪≫
          Functor.leftUnitor T) ≪≫
      etaleLocallyClosedExtensionRestrictionIso (A := A) b hqb

/-- Étale closed/open interchange and closure-defined extension by zero.

Source: literature/stacks-project/etale-cohomology.tex, Tag 0GJ1,
lemma-compatible-shriek-push-finite, together with Morphisms, Tags 01R6--01R8
(blueprint: lem-sfb-etale-locally-closed-extension-comparison).

Proof route. (1) Closed immersions are finite, so
`Etale.isIso_finiteOpenComparison` applied to
`IsPullback.of_hasPullback g u` proves the first conjunct.  By the definition
of `Etale.finiteOpenComparison`, its map is the transpose under
`u_! ⊣ u^*` of the inverse of the exchange map
`u^* g_* v_! L ≅ h_* v^* v_! L ≅ h_* L`.
(2) This comparison is linear over the constant finite ring: naturality under
scalar endomorphisms gives linearity on sections, and the module adjunction
has the same units and counits as the underlying abelian adjunction.
(3) A locally closed immersion into a Noetherian scheme is quasi-compact and
quasi-separated; the same holds after passing to a closed ambient subscheme.
The scheme-theoretic image therefore supplies the open factor `a.toImage` and
closed factor `a.imageι`.
(4) The restriction of the image square to an open factorization is the
cartesian square obtained from `S ×_X W ≅ S`; the scheme-image restriction and
closed-image lemmas identify its closed edge with `S`.
(5) The inverse finite-open comparison gives the factorization comparison.
The displayed helpers `etaleLocallyClosedExtensionRestrictionIso` and
`etaleFactorizationRestrictionIso` are the explicit composites of the open
unit, closed counit, and pullback composition isomorphism.  Thus the comparison
restricts to the identity. Restriction is fully faithful on the essential image
of the fully faithful closure extension, making this normalized comparison unique.
(6) For `b : S ⟶ Y` and a closed `i : Y ⟶ X`, the universal property of
scheme-theoretic images identifies the closure of `b` with that of `a` over
`X`; this gives the canonical comparison after `i_*`.  The helper
`etaleClosedCompositionRestrictionIso` records its identity restriction, and
full faithfulness on the essential image of the closure extension gives uniqueness.
(7) Direct images compose by their étale test-object formula, so the closure
identification is natural in module sheaves and compatible with the constant
coefficient action.  The cited inputs are
`lem-weil-pbc-closed-immersion-finite`,
`lemma-weil-pbc-finite-pushforward-extension-zero`,
`def-weil-pbc-finite-open-comparison`,
`lem-weil-pbc-extension-by-zero-unit-iso`,
`def-weil-pbc-direct-image`, `def-weil-pbc-extension-by-zero`,
`def-weil-pbc-constant-sheaf`, `def-weil-sheaf-of-modules-category`,
`def-weil-pbc-inverse-image`, `def-weil-closed-immersion`,
`def-weil-open-immersion`, `lem-weil-pbc-noetherian-open-subscheme-noetherian`,
`lemma-nagata-immersion-open-in-scheme-image`,
`lemma-nagata-scheme-image-restrict-open`,
`lemma-nagata-scheme-image-of-closed-immersion`, `lem-kun-04ca`,
`lemma-nagata-scheme-image-universal`, and `def-pc-fibre-product`.
-/
theorem etale_locallyClosed_extension_comparison
    {A : Type (u + 1)} [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X]
    {Z W : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (u : W ⟶ X) [IsOpenImmersion u] :
    IsIso (Etale.finiteOpenComparison (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback g u)) ∧
      ∀ {S : Scheme.{u}} (a : S ⟶ X) [IsImmersion a],
        ∃ hqa : QuasiCompact a,
          (∀ {W' : Scheme.{u}} (h : S ⟶ W') (u' : W' ⟶ X)
              [IsClosedImmersion h] [IsOpenImmersion u'],
              (ha : h ≫ u' = a) →
              ∃ e : etaleLocallyClosedExtension (A := A) a hqa ≅
                  Etale.lowerStar (ModuleCat.{u + 1} A) h ⋙
                    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) u',
                  Functor.isoWhiskerRight e (Etale.upperStar (ModuleCat.{u + 1} A) a) ≪≫
                    etaleFactorizationRestrictionIso (A := A) a h u' ha =
                  etaleLocallyClosedExtensionRestrictionIso (A := A) a hqa ∧
                ∀ e' : etaleLocallyClosedExtension (A := A) a hqa ≅
                    Etale.lowerStar (ModuleCat.{u + 1} A) h ⋙
                      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) u',
                  Functor.isoWhiskerRight e' (Etale.upperStar (ModuleCat.{u + 1} A) a) ≪≫
                      etaleFactorizationRestrictionIso (A := A) a h u' ha =
                    etaleLocallyClosedExtensionRestrictionIso (A := A) a hqa →
                  e' = e) ∧
          (∀ {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
              (b : S ⟶ Y) [IsImmersion b],
              (ha : b ≫ i = a) →
              ∃ hqb : QuasiCompact b,
                ∃ e : etaleLocallyClosedExtension (A := A) b hqb ⋙
                    Etale.lowerStar (ModuleCat.{u + 1} A) i ≅
                      etaleLocallyClosedExtension (A := A) a hqa,
                  Functor.isoWhiskerRight e (Etale.upperStar (ModuleCat.{u + 1} A) a) ≪≫
                      etaleLocallyClosedExtensionRestrictionIso (A := A) a hqa =
                      etaleClosedCompositionRestrictionIso (A := A) a b i hqb ha ∧
                  ∀ e' : etaleLocallyClosedExtension (A := A) b hqb ⋙
                      Etale.lowerStar (ModuleCat.{u + 1} A) i ≅
                        etaleLocallyClosedExtension (A := A) a hqa,
                    Functor.isoWhiskerRight e' (Etale.upperStar (ModuleCat.{u + 1} A) a) ≪≫
                        etaleLocallyClosedExtensionRestrictionIso (A := A) a hqa =
                      etaleClosedCompositionRestrictionIso (A := A) a b i hqb ha →
                    e' = e) := by
  sorry

end AlgebraicGeometry
