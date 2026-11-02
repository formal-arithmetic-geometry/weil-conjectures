/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness

/-!
# The general-field Brown exceptional inverse image

For a finite coefficient ring and a separated finite-type morphism over a field, the
constructible pro-etale exceptional inverse image is the fixed functor
`Rf^! := ν_X^* f^× Rν_{Y,*}`.  The finite-Tor restriction carries the canonical
pro-etale compact-support functor to this fixed functor as a right adjoint.  These
definitions provide the general-field Brown object used by the chart realization.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/`
`sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`, Charts, step 3
(blueprint: def-pur-general-field-brown-right-adjoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The fixed pro-etale Brown exceptional inverse image `h_R^!` for a finite
coefficient ring.  The compactification argument is retained as data so that the
functor is tied to the separated finite-type map used by the chart.
Source: Charts, step 3 of `sk-lem-sp-reduction-exceptional.proof.md`
(blueprint: def-pur-general-field-brown-right-adjoint). -/
noncomputable def generalFieldBrownRightAdjoint
    (k : Type u) [Field k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (c : Compactification f) :
    let _ : HasCompactification f := c.hasCompactification
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) := by
  letI : HasCompactification f := c.hasCompactification
  exact rightDerivedUpperShriek Λ f

/-- The canonical finite-Tor Brown adjunction attached to
`generalFieldBrownRightAdjoint`.  Its right functor is the restriction of the
same pro-etale exceptional inverse image, and its counit is the canonical
pro-etale compact-support counit.
Source: Charts, step 3 of `sk-lem-sp-reduction-exceptional.proof.md`
(blueprint: def-pur-general-field-brown-right-adjoint). -/
noncomputable def generalFieldBrownRightAdjunction
    (k : Type u) [Field k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (c : Compactification f) [QuasiCompact f]
    (hΛ : HasInvertibleExponent Λ Y) :
    let _ : HasCompactification f := c.hasCompactification
    let _ : HasInvertibleExponent Λ Y := hΛ
    let _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).lift
        ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).ι ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f)
        (fun K ↦ constructibleFiniteTor_rightDerivedLowerShriek Λ aY f K.property) ⊣
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).lift
        ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι ⋙
          rightDerivedUpperShriek Λ f)
        (fun L ↦ constructibleFiniteTor_rightDerivedUpperShriek Λ aY f L.property) := by
  letI : HasCompactification f := c.hasCompactification
  letI : HasInvertibleExponent Λ Y := hΛ
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  exact DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f

/-- On a bounded-below etale-origin object, the fixed Brown functor is canonically
identified with the etale exceptional inverse image after comparison pullback.
Source: Charts, step 3 of `sk-lem-sp-reduction-exceptional.proof.md`
(blueprint: def-pur-general-field-brown-right-adjoint). -/
noncomputable def generalFieldBrownComparisonIso
    (k : Type u) [Field k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (c : Compactification f)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    let _ : HasCompactification f := c.hasCompactification
    let _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    (generalFieldBrownRightAdjoint k Λ aY f c).obj
        (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj K) ≅
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
        ((Etale.rightDerivedUpperShriek Λ f).obj K) := by
  letI : HasCompactification f := c.hasCompactification
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  exact rightDerivedUpperShriekComparisonIso Λ f K hK

/-- The chart-level Brown comparison.  For any ordinary right adjoint `G` of the
compactified etale lower-shriek, this is the canonical comparison from the fixed
pro-etale Brown functor to `G`, followed by comparison pullback.  The right-adjoint
uniqueness construction makes its counit equation part of the definition.
Source: Charts, step 3 of `sk-lem-sp-reduction-exceptional.proof.md`
(blueprint: def-pur-general-field-brown-right-adjoint). -/
noncomputable def generalFieldBrownChartIso
    (k : Type u) [Field k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (c : Compactification f) [QuasiCompact f]
    (G : Etale.DerivedCategoryModule Λ Y ⥤ Etale.DerivedCategoryModule Λ X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c ⊣ G)
    (K : Etale.DerivedCategoryModule Λ Y)
    (hK : DerivedCategory.TStructure.t.plus K) :
    let _ : HasCompactification f := c.hasCompactification
    let _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    (generalFieldBrownRightAdjoint k Λ aY f c).obj
        (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj K) ≅
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (G.obj K) := by
  letI : HasCompactification f := c.hasCompactification
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  let adj₀ := (Etale.rightDerivedUpperShriekAdjunction Λ f).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIso Λ c).symm
  let eG := adj₀.rightAdjointUniq adj
  exact generalFieldBrownComparisonIso k Λ aY f c K hK ≪≫
    (D(ν^*(X)[ModuleCat.{u + 1} Λ])).mapIso (eG.app K)

/-- The ordinary bounded constructible finite-Tor subcategory used for the Brown
comparison.  Its image under `ν^*` is the domain of the fixed pro-etale functor.
Source: Charts, step 3 of `sk-lem-sp-reduction-exceptional.proof.md`
(blueprint: def-pur-general-field-brown-right-adjoint). -/
abbrev generalFieldBrownOrdinaryCtf (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) :=
  (Etale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).FullSubcategory

/-- Canonical restriction of the coefficient-realization equivalence to finite-ctf
objects.  The predicate identification is the existing intrinsic Tor and
constructibility comparison, rather than a newly chosen subcategory.
Source: `sk-lem-sp-reduction-exceptional.proof.md`, Charts, steps 1 and 3
(blueprint: def-pur-general-field-brown-right-adjoint). -/
def generalFieldBrownCtfEquivalence (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] :
    (DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).FullSubcategory ≌
        spFiniteConstructibleTorCategory T A := by
  letI : (spFiniteConstructibleTor T A).IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ reductionCtf_of_iso T A e h⟩
  exact (sfIntrinsicDerivedEquivalence T A).congrFullSubcategory
    (funext fun K ↦ propext (reductionCtf_realization_iff T A K))

/-- The fixed Brown lower-shriek, expressed in intrinsic finite-ctf coordinates.
Source: `sk-lem-sp-reduction-exceptional.proof.md`, Charts, step 3
(blueprint: def-pur-general-field-brown-right-adjoint). -/
def generalFieldBrownCtfLeft
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (c : Compactification f) [QuasiCompact f]
    (hΛ : HasInvertibleExponent (ULift.{u + 1, u} A) Y) :
    spFiniteConstructibleTorCategory X A ⥤ spFiniteConstructibleTorCategory Y A := by
  letI : HasCompactification f := c.hasCompactification
  letI := hΛ
  exact (generalFieldBrownCtfEquivalence X A).inverse ⋙
    (DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).lift
      ((DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).ι ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
      (fun K ↦ constructibleFiniteTor_rightDerivedLowerShriek
        (ULift.{u + 1, u} A) aY f K.property) ⋙
    (generalFieldBrownCtfEquivalence Y A).functor

/-- The restriction of the fixed pro-etale exceptional inverse image, expressed
in intrinsic finite-ctf coordinates.  This is not an ordinary etale right adjoint
or a functor selected from the item's transported adjunction.
Source: `sk-lem-sp-reduction-exceptional.proof.md`, Charts, step 3
(blueprint: def-pur-general-field-brown-right-adjoint). -/
def generalFieldBrownCtfRight
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (c : Compactification f) [QuasiCompact f]
    (hΛ : HasInvertibleExponent (ULift.{u + 1, u} A) Y) :
    spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A := by
  letI : HasCompactification f := c.hasCompactification
  letI := hΛ
  exact (generalFieldBrownCtfEquivalence Y A).inverse ⋙
    (DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).lift
      ((DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).ι ⋙
          rightDerivedUpperShriek (ULift.{u + 1, u} A) f)
      (fun L ↦ constructibleFiniteTor_rightDerivedUpperShriek
        (ULift.{u + 1, u} A) aY f L.property) ⋙
    (generalFieldBrownCtfEquivalence X A).functor

/-- The fixed pro-etale Brown finite-Tor adjunction transported only by the
canonical coefficient-realization equivalences.  Its counit is retained, so a
comparison with a separately transported etale adjunction can preserve that counit.
Source: `sk-lem-sp-reduction-exceptional.proof.md`, Charts, step 3
(blueprint: def-pur-general-field-brown-right-adjoint). -/
def generalFieldBrownCtfAdjunction
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (c : Compactification f) [QuasiCompact f]
    (hΛ : HasInvertibleExponent (ULift.{u + 1, u} A) Y) :
    generalFieldBrownCtfLeft k A aY f c hΛ ⊣
      generalFieldBrownCtfRight k A aY f c hΛ := by
  exact (((generalFieldBrownCtfEquivalence X A).symm.toAdjunction).comp
    (generalFieldBrownRightAdjunction k (ULift.{u + 1, u} A) aY f c hΛ)).comp
    (generalFieldBrownCtfEquivalence Y A).toAdjunction

/-- The left Brown functor on an etale-origin input is compared with ordinary
compact support by the coefficient-realization unit and the canonical site square.
This fixes the normalization of its comparison with a given compactification.
Source: `sk-lem-sp-reduction-exceptional.proof.md`, Charts, steps 2 and 3
(blueprint: def-pur-general-field-brown-right-adjoint). -/
def generalFieldBrownLeftOriginIso
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (c : Compactification f) [QuasiCompact f]
    (hΛ : HasInvertibleExponent (ULift.{u + 1, u} A) Y)
    (K : generalFieldBrownOrdinaryCtf A X) :
    letI : HasCompactification f := c.hasCompactification
    ((generalFieldBrownCtfLeft k A aY f c hΛ).obj ((reductionSiteCtf X A).obj K)).obj ≅
      (reductionSite A Y).obj
        ((Etale.rightDerivedLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj K.obj) := by
  letI : HasCompactification f := c.hasCompactification
  exact (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
    (((rightDerivedLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapIso
        ((sfIntrinsicDerivedEquivalence X A).unitIso.symm.app
          (D(ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1, u} A)]).obj K.obj))) ≪≫
      (rightDerivedLowerShriekComparisonIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).app ⟨K.obj, K.property.1.1.1⟩)

/-- Normalization of the comparison between compact support for the supplied
compactification and the fixed Brown left functor.  On every ordinary finite-ctf
input the equation is exactly the proper/open site square, followed by the
canonical compactification-refinement comparison.  In particular the left
comparison is not a free rescaling.
Source: `sk-lem-sp-reduction-exceptional.proof.md`, Charts, steps 2 and 3
(blueprint: def-pur-general-field-brown-right-adjoint). -/
def generalFieldBrownLeftNormalization
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y) [IsProper r]
    [QuasiCompact (j ≫ r)]
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j r).obj M.obj))
    (hΛ : HasInvertibleExponent (ULift.{u + 1, u} A) Y)
    (ρ : reductionCtfCompactSupport A j r hF ≅
      generalFieldBrownCtfLeft k A aY (j ≫ r)
        (⟨Z, r, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ r)) hΛ) : Prop :=
  let c : Compactification (j ≫ r) := ⟨Z, r, j, rfl, inferInstance, inferInstance⟩
  letI : HasCompactification (j ≫ r) := c.hasCompactification
  ∀ K : generalFieldBrownOrdinaryCtf A X,
    (ρ.hom.app ((reductionSiteCtf X A).obj K)).hom ≫
      (generalFieldBrownLeftOriginIso k A aY (j ≫ r) c hΛ K).hom =
    (reductionSiteCompactSupportIso A j r).hom.app ⟨K.obj, K.property.1.1.1⟩ ≫
      (reductionSite A Y).map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso
          (ULift.{u + 1, u} A) c (HasCompactification.compactification (j ≫ r))).hom.app
            ⟨K.obj, K.property.1.1.1⟩)

end AlgebraicGeometry.ProEtale
