/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicOpenUnit
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
import WeilConjectures.RingTheory.ProperBaseChange.WContractibleClosedLocalization
import WeilConjectures.AlgebraicGeometry.Affine.AffineClosedSpecializationLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleShriekSpecializationZero
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenCounitMono
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenCounitEpi

/-!
# Proper/open comparison for all pro-etale module sheaves

Source: blueprint main-20261015, proposition-composition-open-restriction-compactifications-f--5,
proof Steps 3–4; Stacks Project, Tags 09AE and 09BN (open functors), with etale analogue Tag 0F7B
(blueprint: lem-exc-proetale-proper-open-sheaf-comparison).

The comparison uses sectionwise open restriction and the inverse open unit, followed
by the counit of the specified open extension adjunction. No etale-origin condition
is imposed on the sheaf.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- Reexpress the existing sectionwise direct image in canonical realization coordinates.
The comparison is fixed on scalar-unit sections, so this introduces no arbitrary map.
Source: Stacks, Tags 00YV and 03D1; blueprint proof Steps 3–4
(blueprint: lem-exc-proetale-proper-open-sheaf-comparison). -/
noncomputable def sfProperOpenDirectImageCoordinates {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantModuleDirectImage f A ≅
      sfIntrinsicTransport A (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f) :=
  (isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (sfIntrinsicDirectImageComparison f A).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (sfIntrinsicModuleEquivalence X A).counitIso _ ≪≫
    Functor.leftUnitor _).symm

/-- Open restriction of a direct image, in fixed-scalar coordinates, induced by the
canonical map `Q ×_W U → Q ×_T V`. For a Cartesian square this map is an isomorphism.
Thus the comparison is exactly evaluation on the same fibre product, including maps.
Source: blueprint proof Steps 3–4; Stacks, Tag 09AE
(blueprint: lem-exc-proetale-proper-open-sheaf-comparison). -/
noncomputable def sfProperOpenFixedRestrictionIso {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i ≅
      ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) r :=
  letI := Functor.isContinuous_comp
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r)
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale k))
    (ProEt.topology W) (ProEt.topology U) (ProEt.topology V)
  letI := Functor.isContinuous_comp
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale i))
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p)
    (ProEt.topology W) (ProEt.topology T) (ProEt.topology V)
  letI := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : WeaklyEtale i) (inferInstance : WeaklyEtale k) sq
  asIso (Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison
      (inferInstance : WeaklyEtale i) (inferInstance : WeaklyEtale k) sq.toCommSq)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (ProEt.topology W) (ProEt.topology V))

/-- The same sectionwise open-restriction isomorphism with the intrinsic constant-ring
module actions. Only the canonical realization unit, counit and scalar-normalized
comparison of direct images are inserted.
Source: blueprint proof Steps 3–4; Stacks, Tags 00YV and 09AE
(blueprint: lem-exc-proetale-proper-open-sheaf-comparison). -/
noncomputable def sfProperOpenRestrictionIso {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    proEtaleConstantModuleDirectImage p A ⋙ sfIntrinsicOpenRestriction i A ≅
      sfIntrinsicOpenRestriction k A ⋙ proEtaleConstantModuleDirectImage r A :=
  isoWhiskerRight (sfProperOpenDirectImageCoordinates A p) (sfIntrinsicOpenRestriction i A) ≪≫
    (sfIntrinsicTransportComp A _ _).symm ≪≫
    sfIntrinsicTransportIso A (sfProperOpenFixedRestrictionIso A r k i p sq) ≪≫
    sfIntrinsicTransportComp A _ _ ≪≫
    isoWhiskerLeft (sfIntrinsicOpenRestriction k A) (sfProperOpenDirectImageCoordinates A r).symm

/-- The open unit as a natural isomorphism, using the already recorded open-unit theorem.
Source: Stacks, Tag 09BN; blueprint proof Steps 3–4
(blueprint: lem-exc-proetale-proper-open-sheaf-comparison). -/
noncomputable def sfProperOpenUnitIso {U V : Scheme.{u}} (k : U ⟶ V)
    [IsOpenImmersion k] : 𝟭 _ ≅ sfIntrinsicExtensionByZero k A ⋙
      sfIntrinsicOpenRestriction k A :=
  NatIso.ofComponents (fun M ↦
    letI := sfIntrinsicOpenUnit_isIso k A M
    asIso ((sfIntrinsicExtensionByZeroAdjunction k A).unit.app M))
    (fun {_ _} f ↦ (sfIntrinsicExtensionByZeroAdjunction k A).unit.naturality f)

/-- The specified `λ`: open restriction followed by the inverse of the open unit.
Source: blueprint proof Steps 3–4; Stacks, Tags 09AE and 09BN
(blueprint: lem-exc-proetale-proper-open-sheaf-comparison). -/
noncomputable def sfProperOpenLambda {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    sfIntrinsicExtensionByZero k A ⋙ proEtaleConstantModuleDirectImage p A ⋙
        sfIntrinsicOpenRestriction i A ≅ proEtaleConstantModuleDirectImage r A :=
  isoWhiskerLeft (sfIntrinsicExtensionByZero k A) (sfProperOpenRestrictionIso A r k i p sq) ≪≫
    isoWhiskerRight (sfProperOpenUnitIso A k).symm (proEtaleConstantModuleDirectImage r A)

/-- The specified `γ`, the transpose of `λ⁻¹` under `i_! ⊣ i^*`.
Its component is `i_!(λ_M⁻¹)` followed by the open counit at `p_* k_! M`.
Source: blueprint proof Steps 3–4; Stacks, Tag 09AE; etale analogue Tag 0F7B
(blueprint: lem-exc-proetale-proper-open-sheaf-comparison). -/
noncomputable def sfProperOpenSheafComparison {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    proEtaleConstantModuleDirectImage r A ⋙ sfIntrinsicExtensionByZero i A ⟶
      sfIntrinsicExtensionByZero k A ⋙ proEtaleConstantModuleDirectImage p A :=
  whiskerRight (sfProperOpenLambda A r k i p sq).inv (sfIntrinsicExtensionByZero i A) ≫
    whiskerLeft (sfIntrinsicExtensionByZero k A ⋙ proEtaleConstantModuleDirectImage p A)
      (sfIntrinsicExtensionByZeroAdjunction i A).counit

/-- The proper-support input for the open counit appearing in the comparison.
The proof is the affine specialization-localization argument in Steps 2--11 of the
blueprint proof of `lem-exc-proetale-proper-open-sheaf-comparison`: after a base
change to an affine pro-etale object, quasi-compact representatives reduce to a
finite principal open and the specialization-zero lemma kills the complement.
This statement is strictly the componentwise counit assertion needed below.
(blueprint: lem-exc-proetale-proper-open-sheaf-comparison). -/
theorem sfProperOpenCounit_isIso {V W T : Scheme.{u}} (p : V ⟶ T) [IsProper p]
    (i : W ⟶ T) [IsOpenImmersion i] (M :
      proEtaleRingModules (pullback p i)
        (proEtaleConstantRing (pullback p i) A)) :
    IsIso ((sfIntrinsicExtensionByZeroAdjunction i A).counit.app
      ((sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
        proEtaleConstantModuleDirectImage p A).obj M)) := by
  let f := (sfIntrinsicExtensionByZeroAdjunction i A).counit.app
    ((sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
      proEtaleConstantModuleDirectImage p A).obj M)
  letI : Mono f := sfProperOpenCounit_mono A p i M
  letI : Epi f := sfProperOpenCounit_epi A p i M
  exact isIso_of_mono_of_epi f

/-- Proper direct image commutes with open extension by zero for every pro-etale module
sheaf over a finite commutative constant ring, with its canonical comparison and naturality.
There is no quasi-compactness condition on the open immersion and no boundedness or
etale-origin restriction on the module sheaf.
Source: blueprint main-20261015, proposition-composition-open-restriction-compactifications-f--5,
proof Steps 3–4, agent-extracted degree-zero obligation; Stacks, Tags 09AE and 09BN; etale analogue
0F7B (blueprint: lem-exc-proetale-proper-open-sheaf-comparison).

Proof plan, following the node's twelve steps:
1. Restrict the zero-extension presheaf to the open and use localization to identify
   its sheafification with the original sheaf. This identifies the open unit as an
   isomorphism. Direct-image evaluation on the identical fibre products gives `λ`.
   The triangle identity says that the open restriction of `γ`, followed by `λ`, is
   the identity (`def-weil-extension-by-zero`, `lem-weil-proetale-weakly-etale-localization`,
   `prose-03-02`).
2. The presheaf map defining the open counit is the identity over the open and the map
   from zero otherwise, hence injective. Exact module sheafification makes it monic;
   therefore `γ` is monic. The same argument makes the maps of zero extensions from
   smaller opens monic (`lem-weil-pbc-ringed-site-module-sheafification-exact`).
3. Localize at an affine pro-etale object `Q → T`. Open-extension base change and
   fibre-product evaluation identify the restricted map with the same `γ` for
   `V_Q → Q`; its normalization is preserved by the open adjunction. Properness and
   openness survive base change, and `V_Q` is quasi-compact and separated over Q
   (`proposition-extension-zero-restriction-closed-subscheme--11`,
   `lem-weil-pbc-proper-base-change`, `lem-weil-pbc-open-immersion-base-change`,
   `def-weil-finite-type-morphism`).
4. First take the open of affine Q to be quasi-compact, hence a finite union of
   principal opens `D(f_a)`, including the empty union. Let I be their ideal and
   localize at the elements invertible modulo I. The principal opens and this closed
   localization form a pro-etale cover. Every point of the latter specializes into
   the closed complement (`lem-weil-pbc-wcontractible-closed-localization`,
   `lem-weil-pbc-affine-closed-specialization-localization`; Stacks 096V and 09AH).
5. The source has zero sections on this affine localization: its open is disjoint
   from the closed complement, so apply the specialization-zero theorem. This also
   applies to module sheaves since module sheafification has the corresponding
   underlying abelian sheaf (`lem-weil-pbc-proetale-shriek-specialization-zero`,
   `def-weil-presheaf-modules-sheafification`,
   `lem-weil-pbc-closed-immersion-base-change`; Stacks 09AG).
6. The proper pullback P over the closed localization has every point specializing
   to its closed fibre C. Indeed the closed image of the closure of a point contains
   a specialization of its image in the base complement. P is quasi-compact and
   separated over that affine base (`def-weil-proper-morphism`).
7. Take a finite affine cover of P and closed-localize each chart at its ideal of C.
   These charts cover P because an open containing a specialization also contains
   its generalizations. They form a pro-etale cover: intersections of affine opens
   are affine by separatedness over the affine base, and their inverse images in
   the localization have finite principal affine covers
   (`lem-weil-pbc-separated-affine-open-intersection`, `def-weil-closed-immersion`,
   `definition-small-pro-etale-site--1`,
   `lem-weil-pbc-affine-closed-specialization-localization`).
8. Apply specialization-zero on each chart of this cover. Open-extension base
   change and sheaf separatedness give `(k_! M)(P) = 0`. Thus the target also has
   zero sections on the base localization. On each principal open `γ` is already
   invertible by Step 1. The lifts agree by Step 2 and glue. Repeat over every
   affine site object, whose base-changed open is again a finite principal union,
   to obtain the quasi-compact-open case. Only sections on the localization vanish;
   its entire restricted sheaf need not vanish (Stacks 09AG).
9. For an arbitrary open, a section of `k_! M` on the quasi-compact `V_Q` has local
   presheaf representatives. Local surjectivity of the sheafification unit and the
   fpqc covering condition give finitely many affine representatives. The images
   in Q of the representatives which factor through the open are quasi-compact;
   choose finitely many principal opens inside W covering these images. Their
   union W₀ is quasi-compact. Every nonzero representative factors through
   `U₀ = V_Q ×_Q W₀`, by open factorization and localization; the empty union is
   allowed when all representatives are zero
   (`lem-weil-pbc-site-sheafification-iso-locally-bijective`,
   `lem-weil-pbc-morphism-factors-through-open-subscheme`; Stacks 00WK and 09AE).
10. Let M₀ be the restriction to U₀. Lift the representatives to `k₀! M₀`, using
    zero for all other representatives. The inclusion `k₀! M₀ → k_! M` is monic by
    Step 2, so the lifts agree on overlaps and glue to a section mapping to the
    original one. No preservation of arbitrary colimits by proper direct image is used.
11. Apply the quasi-compact-open case to W₀ to lift this section through `γ₀`.
    Fibre-product evaluation and the smaller-open inclusions give maps a and b
    with `a ≫ γ = γ₀ ≫ b` in diagrammatic order: transpose
    both composites under the W₀-open adjunction; both become the identity under
    the same open-unit identification. The image of the lift is the original
    section. Thus `γ` is surjective on every affine site object and, by Step 2,
    bijective there; affine coverings prove it is an isomorphism.
12. Fibre-product evaluation, the open unit and the counit are natural in M, so
    their composite `γ` is natural. Cancellation gives naturality of its inverses.
    No step uses boundedness, etale origin, or quasi-compactness of the original open.
No conservativity of ordinary geometric stalks or etale descent is assumed. -/
theorem sfProperOpenSheafComparison_isIso {V W T : Scheme.{u}} (p : V ⟶ T) [IsProper p]
    (i : W ⟶ T) [IsOpenImmersion i] :
    IsIso (sfProperOpenSheafComparison A (pullback.snd p i) (pullback.fst p i) i p
      (IsPullback.of_hasPullback p i).flip) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro M
  dsimp only [sfProperOpenSheafComparison]
  have hc := sfProperOpenCounit_isIso A p i M
  letI : IsIso ((sfIntrinsicExtensionByZeroAdjunction i A).counit.app
      ((sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
        proEtaleConstantModuleDirectImage p A).obj M)) := hc
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

end AlgebraicGeometry.Scheme
