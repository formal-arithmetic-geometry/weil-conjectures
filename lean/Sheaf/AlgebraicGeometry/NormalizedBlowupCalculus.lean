/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Blowup.InvertibleCenter
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.BlowupUniversal
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# Normalized blowups and smooth comparison

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII, sections 2.2.1--2.2.4
and 2.2.7--2.2.9; Stacks Project, Tags 035S and 035Q
(blueprint: lem-trf-normalized-blowup-calculus).

The comparison with a fibre product is expressed by its pullback square. Thus the map to
that fibre product is the canonical comparison, with both projections prescribed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The normalized blowup is the componentwise normalization of the ordinary blowup.
Source: ILO, Expose VIII, 2.2.3 (blueprint: lem-trf-normalized-blowup-calculus). -/
noncomputable def normalizedBlowup {S : Scheme.{u}} (J : S.IdealSheafData) : Scheme.{u} :=
  J.blowup.reducedNormalization

/-- The normalized blowup's structural map is the normalization map followed by the blowup
map. Source: ILO, Expose VIII, 2.2.3 (blueprint: lem-trf-normalized-blowup-calculus). -/
noncomputable def normalizedBlowupMap {S : Scheme.{u}} (J : S.IdealSheafData) :
    J.normalizedBlowup ⟶ S :=
  J.blowup.fromReducedNormalization ≫ J.blowupMap

/-- Normalized blowup calculus for a reduced finite-type rational scheme. Coherence of the
quasi-coherent ideal is finite generation on affine opens, since the base is Noetherian.
Normality is the explicit condition that all stalks are integrally closed domains.
Birationality on components is expressed by a dense open isomorphism with dense inverse
image. Maximally dominating means `Set.MapsTo` on the sets `genericPoints`.

The two smooth comparison squares are pullbacks, equivalently their canonical comparison
maps to the displayed fibre products are isomorphisms. The last two clauses spell out
identity and composition compatibility; the equalities of extended centres are passed
explicitly, so that the maps being compared have literally the same source scheme.

Source: ILO, Expose VIII, 2.2.1--2.2.4, 2.2.7--2.2.9; Stacks Tags 035S and 035Q
(blueprint: lem-trf-normalized-blowup-calculus).

Proof plan:
1. Work on the finitely many reduced integral components. Normalize the ordinary blowup
on each component. Normalization is finite over a finite-type rational scheme (035S),
normal and surjective (035Q), and an isomorphism on a dense open. The centre avoids all
generic points, so blowing up retains them. This proves normality, reducedness, finite
type, surjectivity and componentwise birationality.
2. Principalization makes the extended ideal invertible. For a maximally dominating map
from a normal scheme, the ordinary blowup universal property gives a unique lift, and
normalization lifting factors it uniquely through the component normalizations. The
local lifts agree by uniqueness and glue. This proves finality and rigidity over S.
3. Lift the normalized blowup to S's normalization. Finality gives the map from the
normalized blowup over that normalization in the other direction. The two universal
properties show that the composites are identities, giving the isomorphism over S^nu.
No claim that integral closure commutes with adjoining chart fractions is used.
4. A smooth map is flat, locally finitely presented and has geometrically regular,
hence reduced, fibres (the smooth criterion and smooth-geometrically-reduced nodes).
Its source is reduced. ILO 2.2.9 identifies its normalization with the pullback of S^nu:
the comparison is integral and generically an isomorphism, and its target is normal,
being regular over a normal scheme. Ordinary blowups commute with flat base change;
apply the same normalization comparison to them. Smoothness follows by base change.
5. Flatness and openness of a flat locally finitely presented map imply that the inverse
image of the dense complement of the centre is dense. The uniquely characterized
comparison maps preserve identities and composition; extend the centres by comap_id
and comap_comp to compare the literal source objects.
6. Blowing up an invertible ideal, in particular the unit ideal, is an isomorphism.
Normalizing gives B_O(S) = S^nu. Normal schemes are their own normalization. Regular
schemes are normal by rem-pc-regular-normal, so their normalization maps are isomorphisms.
The empty scheme is covered by the empty component coproduct throughout. -/
theorem normalizedBlowup_calculus (S : Scheme.{u})
    (q : S ⟶ Spec (.of (ULift.{u} ℚ))) [IsReduced S]
    [LocallyOfFiniteType q] [QuasiCompact q] (J : S.IdealSheafData)
    (hJ : ∀ U : S.affineOpens, (J.ideal U).FG)
    (hcentre : Dense (J.support.compl : Set S)) :
    (∀ x : J.normalizedBlowup,
      IsDomain (J.normalizedBlowup.presheaf.stalk x) ∧
      IsIntegrallyClosed (J.normalizedBlowup.presheaf.stalk x)) ∧
    IsReduced J.normalizedBlowup ∧
    LocallyOfFiniteType (J.normalizedBlowupMap ≫ q) ∧
    QuasiCompact (J.normalizedBlowupMap ≫ q) ∧
    Surjective J.normalizedBlowupMap ∧
    Set.MapsTo J.normalizedBlowupMap (genericPoints J.normalizedBlowup) (genericPoints S) ∧
    (∃ U : S.Opens, Dense (U : Set S) ∧
      Dense (J.normalizedBlowupMap ⁻¹ᵁ U : Set J.normalizedBlowup) ∧
      IsIso (J.normalizedBlowupMap ∣_ U)) ∧
    (J.comap J.normalizedBlowupMap).IsInvertible ∧
    (∀ (Y : Scheme.{u}) (f : Y ⟶ S),
      (∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
        IsIntegrallyClosed (Y.presheaf.stalk y)) →
      Set.MapsTo f (genericPoints Y) (genericPoints S) → (J.comap f).IsInvertible →
      ∃! l : Y ⟶ J.normalizedBlowup, l ≫ J.normalizedBlowupMap = f) ∧
    (∀ e : J.normalizedBlowup ≅ J.normalizedBlowup,
      e.hom ≫ J.normalizedBlowupMap = J.normalizedBlowupMap → e = Iso.refl _) ∧
    (∃! n : J.normalizedBlowup ⟶ S.reducedNormalization,
      n ≫ S.fromReducedNormalization = J.normalizedBlowupMap) ∧
    (∀ n : J.normalizedBlowup ⟶ S.reducedNormalization,
      n ≫ S.fromReducedNormalization = J.normalizedBlowupMap →
      ∃! e : J.normalizedBlowup ≅ (J.comap S.fromReducedNormalization).normalizedBlowup,
        e.hom ≫ (J.comap S.fromReducedNormalization).normalizedBlowupMap = n) ∧
    (∀ (T : Scheme.{u}) (h : T ⟶ S) [Smooth h]
      [LocallyOfFiniteType (h ≫ q)] [QuasiCompact (h ≫ q)],
      IsReduced T ∧ Dense ((J.comap h).support.compl : Set T) ∧
      (∃! n : T.reducedNormalization ⟶ S.reducedNormalization,
        n ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h) ∧
      (∀ n : T.reducedNormalization ⟶ S.reducedNormalization,
        n ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h →
        IsPullback n T.fromReducedNormalization S.fromReducedNormalization h) ∧
      (∃! b : (J.comap h).normalizedBlowup ⟶ J.normalizedBlowup,
        b ≫ J.normalizedBlowupMap = (J.comap h).normalizedBlowupMap ≫ h) ∧
      (∀ b : (J.comap h).normalizedBlowup ⟶ J.normalizedBlowup,
        b ≫ J.normalizedBlowupMap = (J.comap h).normalizedBlowupMap ≫ h →
        IsPullback b (J.comap h).normalizedBlowupMap J.normalizedBlowupMap h ∧ Smooth b)) ∧
    (IsRegularScheme S → IsIso S.fromReducedNormalization) ∧
    (∃! e : (⊤ : S.IdealSheafData).normalizedBlowup ≅ S.reducedNormalization,
      e.hom ≫ S.fromReducedNormalization = (⊤ : S.IdealSheafData).normalizedBlowupMap) ∧
    ((∀ x : S, IsDomain (S.presheaf.stalk x) ∧
      IsIntegrallyClosed (S.presheaf.stalk x)) →
      IsIso S.fromReducedNormalization ∧ IsIso (⊤ : S.IdealSheafData).normalizedBlowupMap) ∧
    ((∀ n : S.reducedNormalization ⟶ S.reducedNormalization,
      n ≫ S.fromReducedNormalization = S.fromReducedNormalization → n = 𝟙 _) ∧
      (∀ (K : S.IdealSheafData) (hK : J.comap (𝟙 S) = K)
        (b : K.normalizedBlowup ⟶ J.normalizedBlowup),
        b ≫ J.normalizedBlowupMap = K.normalizedBlowupMap →
        b = eqToHom (congrArg normalizedBlowup (hK.symm.trans J.comap_id)))) ∧
    (∀ (T U : Scheme.{u}) (h : T ⟶ S) (g : U ⟶ T) [Smooth h] [Smooth g]
      [LocallyOfFiniteType (h ≫ q)] [QuasiCompact (h ≫ q)]
      [LocallyOfFiniteType (g ≫ h ≫ q)] [QuasiCompact (g ≫ h ≫ q)],
      (∀ (n₁ : T.reducedNormalization ⟶ S.reducedNormalization)
        (n₂ : U.reducedNormalization ⟶ T.reducedNormalization)
        (n₃ : U.reducedNormalization ⟶ S.reducedNormalization),
        n₁ ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h →
        n₂ ≫ T.fromReducedNormalization = U.fromReducedNormalization ≫ g →
        n₃ ≫ S.fromReducedNormalization = U.fromReducedNormalization ≫ g ≫ h →
        n₂ ≫ n₁ = n₃) ∧
      (∀ (K : U.IdealSheafData) (hK : (J.comap h).comap g = K)
        (b₁ : (J.comap h).normalizedBlowup ⟶ J.normalizedBlowup)
        (b₂ : K.normalizedBlowup ⟶ (J.comap h).normalizedBlowup)
        (b₃ : (J.comap (g ≫ h)).normalizedBlowup ⟶ J.normalizedBlowup),
        b₁ ≫ J.normalizedBlowupMap = (J.comap h).normalizedBlowupMap ≫ h →
        b₂ ≫ (J.comap h).normalizedBlowupMap = K.normalizedBlowupMap ≫ g →
        b₃ ≫ J.normalizedBlowupMap = (J.comap (g ≫ h)).normalizedBlowupMap ≫ g ≫ h →
        b₂ ≫ b₁ = eqToHom
          (congrArg normalizedBlowup (hK.symm.trans (J.comap_comp g h).symm)) ≫ b₃)) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
