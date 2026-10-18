/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: SHEAF group Q89
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Sheaf.Compactification.BoundaryRefinement
import Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import Sheaf.Compactification.NagataSketchClosure
import Sheaf.Compactification.NagataDensityNormalizationSetup

/-!
# Passing to the schematic closure

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-lem-nagata-density-normalization/_section.md, node order 748
  (blueprint: sk-lem-nagata-density-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Coefficient transport along the canonical coefficient isomorphism, for arbitrary
condensed rings. Unlike tensor extension of scalars this construction needs no commutativity.
It is restriction of scalars along the isomorphism, with inverse restriction along its inverse.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization`, pulled-back coefficient sheaves
(blueprint: sk-lem-nagata-density-normalization). -/
abbrev nagataCoefficientChangeEquivalence
    {U T : Scheme.{u}} (h : U ⟶ T)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj Λ U) ≌
      CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        ((h)^*[Ab.{u + 1}].obj (condensedRingObj Λ T)) :=
  CategoryTheory.Equivalence.mk (CategoryTheory.Mod.comap (condensedPullbackHom Λ h))
    (CategoryTheory.Mod.comap (asIso (condensedPullbackHom Λ h)).inv)
    ((CategoryTheory.Mod.comapId _).symm ≪≫
      CategoryTheory.Mod.comapCongr (asIso (condensedPullbackHom Λ h)).inv_hom_id.symm ≪≫
      CategoryTheory.Mod.comapComp _ _)
    ((CategoryTheory.Mod.comapComp _ _).symm ≪≫
      CategoryTheory.Mod.comapCongr (asIso (condensedPullbackHom Λ h)).hom_inv_id ≪≫
      CategoryTheory.Mod.comapId _)

/-- Exact coefficient pullback used for normalization with a possibly noncommutative ring.
It transports the existing sheaf pullback on modules along the coefficient isomorphism.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization`, first proof paragraph
(blueprint: sk-lem-nagata-density-normalization). -/
abbrev nagataModulePullback
    {U T : Scheme.{u}} (h : U ⟶ T)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] :=
  (h)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ T) ⋙
    CategoryTheory.Mod.comap (asIso (condensedPullbackHom Λ h)).inv

/-- The canonical pullback/direct-image adjunction after coefficient transport.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization`, first proof paragraph
(blueprint: sk-lem-nagata-density-normalization). -/
def nagataModulePullbackAdjunction
    {U T : Scheme.{u}} (h : U ⟶ T)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] :
    nagataModulePullback h Λ ⊣ (h)_*⟦Λ⟧ :=
  (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} h).mapModAdjunction
    (condensedRingObj Λ T)).comp
    (nagataCoefficientChangeEquivalence h Λ).symm.toAdjunction).ofNatIsoRight
    (comapPullbackHomCompIso Λ h)

/-- The unbounded derived pullback/direct-image adjunction, using exact pullback and
K-injective resolutions. No monoidal structure on modules is needed.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization`, first proof paragraph
(blueprint: sk-lem-nagata-density-normalization). -/
abbrev nagataDerivedPullbackAdjunction
    {U T : Scheme.{u}} (h : U ⟶ T)
    [EssentiallySmall.{u + 1} Profinite.{u}]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] :
    D(nagataModulePullback h Λ) ⊣ R((h)_*⟦Λ⟧) :=
  (nagataModulePullbackAdjunction h Λ).mapDerivedCategoryRightDerivedAdjunction

/-- The open extension-by-zero adjunction after canonical coefficient transport.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization`, first proof paragraph
(blueprint: sk-lem-nagata-density-normalization). -/
def nagataOpenAdjunction
    {U T : Scheme.{u}} (h : U ⟶ T) [IsOpenImmersion h]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] :
    (h)_!open⟦Λ⟧ ⊣ nagataModulePullback h Λ :=
  (nagataCoefficientChangeEquivalence h Λ).toAdjunction.comp
    (linearOpenImmersionLowerShriekAdjunction Λ h)

/-- The degreewise open adjunction, obtained using exact pullback and K-injective
resolutions only. This avoids the commutative monoidal K-flat API.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization`, first proof paragraph
(blueprint: sk-lem-nagata-density-normalization). -/
def nagataDerivedOpenAdjunction
    {U T : Scheme.{u}} (h : U ⟶ T) [IsOpenImmersion h]
    [EssentiallySmall.{u + 1} Profinite.{u}]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] :
    D((h)_!open⟦Λ⟧) ⊣ D(nagataModulePullback h Λ) :=
  ((nagataOpenAdjunction h Λ).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
    (nagataModulePullback h Λ).rightDerivedFunctorIsoMapDerivedCategory

/-- Pullback composition, determined as the conjugate of the existing pushforward
composition isomorphism, for the exact coefficient-transport pullbacks.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization`, canonical coefficient identifications
(blueprint: sk-lem-nagata-density-normalization). -/
def nagataModulePullbackComp
    {U T V : Scheme.{u}} (h : U ⟶ T) (g : T ⟶ V)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] :
    nagataModulePullback (h ≫ g) Λ ≅
      nagataModulePullback g Λ ⋙ nagataModulePullback h Λ :=
  ((conjugateIsoEquiv (nagataModulePullbackAdjunction (h ≫ g) Λ)
      ((nagataModulePullbackAdjunction g Λ).comp
        (nagataModulePullbackAdjunction h Λ))).symm (lowerStarComp Λ h g).symm).symm

/-- The canonical pullback composition identification for the schematic closure.
It is induced by `j_Z ≫ i = j`, pullback composition, and exactness of pullback.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization`, first proof paragraph
(blueprint: sk-lem-nagata-density-normalization). -/
def nagataClosurePullbackCompIso
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f)
    [IsNoetherian c.Z] [EssentiallySmall.{u + 1} Profinite.{u}]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] :
    D(nagataModulePullback c.i Λ) ≅
      D(nagataModulePullback c.i.imageι Λ) ⋙ D(nagataModulePullback c.i.toImage Λ) :=
  eqToIso (congrArg (fun h : X ⟶ c.Z ↦ D(nagataModulePullback h Λ))
      c.i.toImage_imageι.symm) ≪≫
    Functor.mapDerivedCategoryNatIso (nagataModulePullbackComp c.i.toImage c.i.imageι Λ) ≪≫
    Functor.mapDerivedCategoryCompIso
      (nagataModulePullback c.i.imageι Λ) (nagataModulePullback c.i.toImage Λ)

/-- The canonical map `j_Z! K ⟶ i^* j! K`. Its adjoint is the open-extension unit,
transported by pullback composition. The inverse of this map identifies closed restriction
with extension by zero on the closure; this specifies the canonical comparison without
choosing an arbitrary isomorphism.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization`, first proof paragraph
(blueprint: sk-lem-nagata-density-normalization). -/
def nagataClosureOpenComparison
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f)
    [IsNoetherian c.Z] [EssentiallySmall.{u + 1} Profinite.{u}]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ]
    (K : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) :
    (D((c.i.toImage)_!open⟦Λ⟧)).obj K ⟶
      (D(nagataModulePullback c.i.imageι Λ)).obj ((D((c.i)_!open⟦Λ⟧)).obj K) :=
  ((nagataDerivedOpenAdjunction c.i.toImage Λ).homEquiv _ _).symm
    ((nagataDerivedOpenAdjunction c.i Λ).unit.app K ≫
      (nagataClosurePullbackCompIso c Λ).hom.app ((D((c.i)_!open⟦Λ⟧)).obj K))

/-- The canonical derived direct-image composition isomorphism for the closure inclusion
and the proper structural map. It is the conjugate of derived pullback composition.
Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization`, second proof paragraph
(blueprint: sk-lem-nagata-density-normalization). -/
def nagataClosurePushforwardCompIso
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f)
    [EssentiallySmall.{u + 1} Profinite.{u}]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] :
    R((c.i.imageι)_*⟦Λ⟧) ⋙ R((c.g)_*⟦Λ⟧) ≅ R((c.i.imageι ≫ c.g)_*⟦Λ⟧) :=
  conjugateIsoEquiv
    ((nagataDerivedPullbackAdjunction c.g Λ).comp
      (nagataDerivedPullbackAdjunction c.i.imageι Λ))
    (nagataDerivedPullbackAdjunction (c.i.imageι ≫ c.g) Λ)
    (Functor.mapDerivedCategoryNatIso (nagataModulePullbackComp c.i.imageι c.g Λ) ≪≫
      Functor.mapDerivedCategoryCompIso
        (nagataModulePullback c.g Λ) (nagataModulePullback c.i.imageι Λ))

/--
Canonical natural identifications after replacing a Noetherian compactification by the
schematic closure. The adjunct of `eZ.hom` is inverse to the specified open comparison,
and `eS` is its proper pushforward followed by canonical direct-image composition.
Thus their components give the two identifications for every unbounded derived object.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-lem-nagata-density-normalization/_section.md`, node order 748
(blueprint: sk-lem-nagata-density-normalization).

Proof (postponed), following the two DAG steps:
1. The setup node `det-nagata-density-normalization-setup` supplies the factorization
   `j_Z ≫ i = j`, the quasi-compact open immersion `j_Z`, the quasi-compact open complement
   of the closed image, and the quasi-compact and quasi-separated ambient scheme.
   Clause (2) of `det-sf-open-closed-pullback-limits` makes closed restriction exact;
   exactness preserves kernels and images, so it preserves acyclic complexes and is
   computed degreewise on the unbounded derived category. Apply the unbounded clause of
   `det-nagata-density-normalization-sheaves`: the open-closed sequence identifies the
   unit `j! K ⟶ Ri_* i^* j! K` with an isomorphism, using the inverse of the canonical
   open comparison to identify the restriction with `j_Z! K`. This yields `eZ`, with
   the displayed two inverse equations specifying the source's canonical map.
2. Apply `det-nagata-density-normalization-pushforward`. Whisker `eZ` with `Rp_*` and
   compose with the direct-image composition isomorphism to obtain `eS`. The setup's
   clauses (1) and (4) give a quasi-compact open `j_Z` and a proper `i ≫ p`;
   `j_Z ≫ (i ≫ p) = f` follows from the image factorization and `c.comm`.
   Hence this is again a compactification in `sk-def-nagata-sketch-data`, and its
   compact-support expression is exactly the target of `eS`. This proves invariance,
   in particular for schemes of finite type over a field, without density or reducedness
   assumptions on the original compactification.
-/
theorem nagata_density_normalization
    {X S : Scheme.{u}} (f : X ⟶ S) (c : Compactification f)
    [IsNoetherian c.Z] [EssentiallySmall.{u + 1} Profinite.{u}]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] :
    ∃ eZ : D((c.i)_!open⟦Λ⟧) ≅
        D((c.i.toImage)_!open⟦Λ⟧) ⋙ R((c.i.imageι)_*⟦Λ⟧),
    ∃ eS : rightDerivedLowerShriekOfCompactification Λ c ≅
        D((c.i.toImage)_!open⟦Λ⟧) ⋙ R((c.i.imageι ≫ c.g)_*⟦Λ⟧),
      (∀ K : DerivedCategory
          (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj Λ X)),
        nagataClosureOpenComparison c Λ K ≫
            ((nagataDerivedPullbackAdjunction c.i.imageι Λ).homEquiv _ _).symm
              (eZ.hom.app K) = 𝟙 _ ∧
        ((nagataDerivedPullbackAdjunction c.i.imageι Λ).homEquiv _ _).symm
            (eZ.hom.app K) ≫ nagataClosureOpenComparison c Λ K = 𝟙 _) ∧
      eS = Functor.isoWhiskerRight eZ R((c.g)_*⟦Λ⟧) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (nagataClosurePushforwardCompIso c Λ) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
