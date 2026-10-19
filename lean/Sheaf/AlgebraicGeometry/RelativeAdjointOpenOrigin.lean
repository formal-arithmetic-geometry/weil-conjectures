/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.Paper.EtaleOriginDerivedCategory
public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The two etale origins of restricted relative exceptional values

Source: retained repaired proof of `prop-exc-base-change-proper`, paragraph "Choose K";
Stacks Project, proetale.tex, Tag 0GLZ
(blueprint: lem-exc-relative-adjoint-open-origin).

The two arrows are pastes of the comparison unit and the canonical pullback comparison.
They are natural transformations on the comma category of origin arrows. Invertibility is
asserted only at bounded-below etale origins. No comparison between the two values is used.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- The etale right adjoint at the specified compactification, with exactly the same
compactification instance as `sfFiniteExceptionalFixed`.
Source: retained proper/open proof, paragraph "Choose K"
(blueprint: lem-exc-relative-adjoint-open-origin). -/
noncomputable abbrev sfRelativeEtaleAdjoint (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  letI := c.hasCompactification
  Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f

/-- The comparison-unit arrow `nu_X^* f_e^times -> Rf! nu_Y^*`.
Source: retained proper/open proof, comparison-unit identification of the relative formula
(blueprint: lem-exc-relative-adjoint-open-origin). -/
noncomputable def sfRelativeAdjointOriginUnit (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    sfRelativeEtaleAdjoint A c ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory ⋙
        sfFiniteExceptionalFixed A c :=
  whiskerRight
    (derivedComparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).unit
    (sfRelativeEtaleAdjoint A c ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory)

/-- Comma objects are arrows `nu_Y^* K0 -> K`; their morphisms are commuting pairs.
The theorem below evaluates at isomorphisms with bounded-below `K0`. Keeping the whole
comma category makes naturality in both entries part of the type of the witness arrows.
Source: retained proper/open proof, naturality in `(K0, alpha)`
(blueprint: lem-exc-relative-adjoint-open-origin). -/
noncomputable abbrev SfRelativeOriginArrows (A : Type u) [CommRing A] (Y : Scheme.{u}) :=
  Comma
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory
    (𝟭 (DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))))

/-- The first specified etale complex, functorially in the origin arrow.
Source: retained proper/open proof, `B0 = g'^* f_e^times K0`
(blueprint: lem-exc-relative-adjoint-open-origin). -/
noncomputable def sfRelativeOpenOriginLeftEtale (A : Type u) [CommRing A] [Finite A]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) :
    SfRelativeOriginArrows A Y ⥤ DerivedCategory
      (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  Comma.fst _ _ ⋙ sfRelativeEtaleAdjoint A (Compactification.ofIsProper f) ⋙
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.fst f g)).mapDerivedCategory

/-- The second specified etale complex, functorially in the origin arrow.
Source: retained proper/open proof, `C0 = f'_e^times g^* K0`
(blueprint: lem-exc-relative-adjoint-open-origin). -/
noncomputable def sfRelativeOpenOriginRightEtale (A : Type u) [CommRing A] [Finite A]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) :
    SfRelativeOriginArrows A Y ⥤ DerivedCategory
      (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  Comma.fst _ _ ⋙
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategory ⋙
    sfRelativeEtaleAdjoint A (Compactification.ofIsProper (pullback.snd f g))

/-- The first canonical witness arrow: inverse pullback comparison, then the comparison
unit, then the given origin arrow. All factors are natural transformations.
Source: retained proper/open proof, first displayed witness
(blueprint: lem-exc-relative-adjoint-open-origin). -/
noncomputable def sfRelativeOpenOriginLeftMap (A : Type u) [CommRing A] [Finite A]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) :
    sfRelativeOpenOriginLeftEtale A f g ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (pullback f g)).mapDerivedCategory ⟶
      Comma.snd _ _ ⋙ sfFiniteExceptionalFixed A (Compactification.ofIsProper f) ⋙
        sfFixedDerivedPullback A (pullback.fst f g) :=
  whiskerLeft (Comma.fst _ _)
      (whiskerLeft (sfRelativeEtaleAdjoint A (Compactification.ofIsProper f))
        (sfDerivedComparisonPullbackIso A (pullback.fst f g)).inv) ≫
    whiskerLeft (Comma.fst _ _)
      (whiskerRight (sfRelativeAdjointOriginUnit A (Compactification.ofIsProper f))
        (sfFixedDerivedPullback A (pullback.fst f g))) ≫
    whiskerRight (Comma.natTrans _ _)
      (sfFiniteExceptionalFixed A (Compactification.ofIsProper f) ⋙
        sfFixedDerivedPullback A (pullback.fst f g))

/-- The second canonical witness arrow: the comparison unit for `f'`, inverse pullback
comparison for `g`, and the image of the origin arrow under `g^*` and `Rf'^!`.
Source: retained proper/open proof, second displayed witness
(blueprint: lem-exc-relative-adjoint-open-origin). -/
noncomputable def sfRelativeOpenOriginRightMap (A : Type u) [CommRing A] [Finite A]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) :
    sfRelativeOpenOriginRightEtale A f g ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (pullback f g)).mapDerivedCategory ⟶
      Comma.snd _ _ ⋙ sfFixedDerivedPullback A g ⋙
        sfFiniteExceptionalFixed A (Compactification.ofIsProper (pullback.snd f g)) :=
  whiskerLeft (Comma.fst _ _)
      (whiskerLeft
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategory
        (sfRelativeAdjointOriginUnit A
          (Compactification.ofIsProper (pullback.snd f g)))) ≫
    whiskerLeft (Comma.fst _ _)
      (whiskerRight (sfDerivedComparisonPullbackIso A g).inv
        (sfFiniteExceptionalFixed A (Compactification.ofIsProper (pullback.snd f g)))) ≫
    whiskerRight (Comma.natTrans _ _)
      (sfFixedDerivedPullback A g ⋙
        sfFiniteExceptionalFixed A (Compactification.ofIsProper (pullback.snd f g)))


/-- Realize a fixed-coefficient origin isomorphism in the recorded coefficient-sheaf
presentation. The comparison is the actual exact-functor composition isomorphism.
Source: retained proper/open proof, witnessed-category conclusion
(blueprint: lem-exc-relative-adjoint-open-origin). -/
noncomputable def sfRelativeOriginRealizationIso (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    (L : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (K : DerivedCategory
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (e : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      T).mapDerivedCategory.obj L.obj ≅ K) :
    ((@finiteCoefficientComparison T (ULift.{u + 1, u} A) _ _ ⊥
        (discreteTopology_bot _)).mapDerivedCategoryPlus.obj L).obj ≅
      (@finiteCoefficientRealization T (ULift.{u + 1, u} A) _ _ ⊥
        (discreteTopology_bot _)).mapDerivedCategory.obj K :=
  (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T)
    (@finiteCoefficientRealization T (ULift.{u + 1, u} A) _ _ ⊥
      (discreteTopology_bot _))).app L.obj ≪≫
    (@finiteCoefficientRealization T (ULift.{u + 1, u} A) _ _ ⊥
      (discreteTopology_bot _)).mapDerivedCategory.mapIso e

/-- Retain the specified etale complex and its specified isomorphism as an object of the
recorded witnessed full category, after the canonical coefficient realization. The target
is the realization of `K`, not a replacement by its comparison image. Boundedness is
transported along the displayed realized isomorphism; no witness is chosen.
Source: retained proper/open proof, witnessed-category conclusion
(blueprint: lem-exc-relative-adjoint-open-origin). -/
noncomputable def sfRelativeOriginObject (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    (L : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (K : DerivedCategory
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (e : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      T).mapDerivedCategory.obj L.obj ≅ K) :
    @EtaleOriginDerivedCategory T (ULift.{u + 1, u} A) _ _ ⊥ (discreteTopology_bot _) :=
  letI : TopologicalSpace (ULift.{u + 1, u} A) := ⊥
  letI : DiscreteTopology (ULift.{u + 1, u} A) := discreteTopology_bot _
  ⟨⟨(@finiteCoefficientRealization T (ULift.{u + 1, u} A) _ _ ⊥
        (discreteTopology_bot _)).mapDerivedCategory.obj K,
      DerivedCategory.TStructure.t.plus.prop_of_iso
        (sfRelativeOriginRealizationIso T A L K e)
        ((@finiteCoefficientComparison T (ULift.{u + 1, u} A) _ _ ⊥
          (discreteTopology_bot _)).mapDerivedCategoryPlus.obj L).property⟩,
    ⟨L, ObjectProperty.isoMk _ (sfRelativeOriginRealizationIso T A L K e)⟩⟩

/-- Both specified etale complexes are bounded below and both canonical origin arrows
are invertible. The arrows above are natural on the comma category, so their inverses at
these objects are natural in the bounded-below witness `(K0, alpha)`.
Source: retained repaired proper/open proof, paragraph "Choose K"; Stacks Tag 0GLZ
(blueprint: lem-exc-relative-adjoint-open-origin).

Proof:
1. A field is Noetherian. Finite type makes `Y` Noetherian. Its open subscheme `Y'` is
Noetherian and every affine inverse image of `g` is quasi-compact. Thus `g` is finite type,
`Y'` and `X'` are finite type over the field, `f'` is proper and `g'` is open. Use the two
identity-open compactifications. Finite type supplies finite dimension bounds, taking zero
for an empty source, so thm-sf-ambient-adjoint-class applies to both.
2. The ordinary etale adjoints preserve bounded-below objects by the finite-amplitude
clause of def-weil-exceptional-inverse-image. Exact etale inverse image preserves lower
bounds (prop-weil-pbc-inverse-image-modules-exact and
lem-weil-pbc-exact-functor-bounded-below). Hence `B0` and `C0` are bounded below.
3. By thm-weil-pbc-site-comparison, `eta_K0` is invertible. Its composite with `Rnu_*(alpha)`
is invertible. Applying the etale adjoint and exact comparison identifies `nu^* f_e^times K0`
with `Rf! K`. The same applies to `g^* K0` and the comparison-pullback transport of `alpha`.
4. Paste with the canonical inverse-image comparison of lem-weil-pbc-comparison-pullback.
This is precisely the two natural transformations above; hence both components are
invertible. Every factor is natural in the origin arrow, giving the stated naturality.
5. Retain each of the bounded-below etale complexes and its displayed isomorphism. The
constructor `sfRelativeOriginObject` gives the corresponding object of
def-sf-etale-origin-subcategory.
No isomorphism between these objects or arbitrary pro-etale adjoint is asserted. -/
theorem sfRelativeAdjointOpenOrigin
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsProper f]
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g]
    (K0 : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
    (K : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
    (alpha : ((siteComparisonDerivedPullbackPlus Y
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))).obj K0).obj ≅ K) :
    DerivedCategory.TStructure.t.plus
        ((sfRelativeOpenOriginLeftEtale (Padic.coefficientExtensionRing l E (n + 1)) f g).obj
          ⟨K0.obj, K, alpha.hom⟩) ∧
      DerivedCategory.TStructure.t.plus
        ((sfRelativeOpenOriginRightEtale (Padic.coefficientExtensionRing l E (n + 1)) f g).obj
          ⟨K0.obj, K, alpha.hom⟩) ∧
      IsIso ((sfRelativeOpenOriginLeftMap (Padic.coefficientExtensionRing l E (n + 1)) f g).app
        ⟨K0.obj, K, alpha.hom⟩) ∧
      IsIso ((sfRelativeOpenOriginRightMap (Padic.coefficientExtensionRing l E (n + 1)) f g).app
        ⟨K0.obj, K, alpha.hom⟩) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of D.k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of D.k))
  have : QuasiCompact g := inferInstance
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace g
  have hK0 : DerivedCategory.TStructure.t.plus K0.obj := K0.property
  have := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y K0.obj hK0
  have hgK : DerivedCategory.TStructure.t.plus
      ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategory.obj
        K0.obj) :=
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategoryPlus.obj
      K0).property
  have hfK : DerivedCategory.TStructure.t.plus
      ((sfRelativeEtaleAdjoint A (Compactification.ofIsProper f)).obj K0.obj) := by
    let := (Compactification.ofIsProper f).hasCompactification
    exact Etale.plus_rightDerivedUpperShriek_obj _ _ K0.obj hK0
  have := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y'
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategory.obj
      K0.obj) hgK
  constructor
  · exact ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.fst f g)).mapDerivedCategoryPlus.obj ⟨_, hfK⟩).property
  constructor
  · change DerivedCategory.TStructure.t.plus
      ((sfRelativeEtaleAdjoint A (Compactification.ofIsProper (pullback.snd f g))).obj
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategory.obj
          K0.obj))
    let := (Compactification.ofIsProper (pullback.snd f g)).hasCompactification
    exact Etale.plus_rightDerivedUpperShriek_obj _ _ _ hgK
  constructor
  · dsimp [sfRelativeOpenOriginLeftMap, sfRelativeAdjointOriginUnit,
      Comma.fst, Comma.natTrans]
    infer_instance
  · dsimp [sfRelativeOpenOriginRightMap, sfRelativeAdjointOriginUnit,
      Comma.fst, Comma.natTrans]
    infer_instance


/-- The two actual objects of the recorded witnessed full category. Their retained etale
complexes are exactly `B0` and `C0`; their isomorphisms are the two specified natural
components. This uses only the proof fields of sfRelativeAdjointOpenOrigin, never a choice
of etale complex or isomorphism.
Source: retained proper/open proof, witnessed-category conclusion
(blueprint: lem-exc-relative-adjoint-open-origin). -/
noncomputable def sfRelativeAdjointOpenOriginObjects
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsProper f]
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g]
    (K0 : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
    (K : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
    (alpha : ((siteComparisonDerivedPullbackPlus Y
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))).obj K0).obj ≅ K) :
    (@EtaleOriginDerivedCategory (pullback f g)
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) _ _ ⊥
      (discreteTopology_bot _)) ×
    (@EtaleOriginDerivedCategory (pullback f g)
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) _ _ ⊥
      (discreteTopology_bot _)) :=
  let h := sfRelativeAdjointOpenOrigin D l _hl E n X Y f g K0 K alpha
  (sfRelativeOriginObject (pullback f g) (Padic.coefficientExtensionRing l E (n + 1))
      ⟨_, h.1⟩ _
      (@asIso _ _ _ _
        ((sfRelativeOpenOriginLeftMap (Padic.coefficientExtensionRing l E (n + 1)) f g).app
          ⟨K0.obj, K, alpha.hom⟩) h.2.2.1),
    sfRelativeOriginObject (pullback f g) (Padic.coefficientExtensionRing l E (n + 1))
      ⟨_, h.2.1⟩ _
      (@asIso _ _ _ _
        ((sfRelativeOpenOriginRightMap (Padic.coefficientExtensionRing l E (n + 1)) f g).app
          ⟨K0.obj, K, alpha.hom⟩) h.2.2.2))

end AlgebraicGeometry.ProEtale
