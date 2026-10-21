/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-!
# Restriction of the actual Koszul completion unit

Source: Bhatt--Scholze, Lemma 6.5.8, Remark 6.5.10 and Proposition 6.6.11;
Stacks Project, proetale.tex, Tags 099L and 099M, and algebraization.tex, Tag 0A0E
(blueprint: lem-sfb-adic-stratum-completion-unit).

We use the recorded equivalent small model of each pro-etale site. Its object and
morphism universes are both `u+1`; the original site's morphism universe remains `u`.
Algebraic inverse-image data fixes operations on all generalized sections. In particular
its completed coefficient map is the recorded limit lift of the finite projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.all false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local irreducible] ConstantCompletion.completed ConstantCompletion.derivedPull
  HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.SfbAdicRestriction

/-- The equivalence from the small model to the original pro-etale sheaf category.
Source: Stacks Tags 00YY and 09A5
(blueprint: lem-sfb-adic-stratum-completion-unit). -/
def modelEquivalence (X : Scheme.{u}) (D : Type v) [Category.{u + 1} D] :
    Sheaf (proEtaleModelTopology X) D ≌ Sheaf (ProEt.topology X) D :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      D (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      D (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)

attribute [local irreducible] modelEquivalence

/-- The specified pro-etale inverse image, transported through the site equivalences.
Source: Stacks Tags 09A5 and 00YV
(blueprint: lem-sfb-adic-stratum-completion-unit). -/
def inverse {X S : Scheme.{u}} (i : S ⟶ X) :
    Sheaf (proEtaleModelTopology X) (Type (u + 1)) ⥤
      Sheaf (proEtaleModelTopology S) (Type (u + 1)) :=
  (modelEquivalence X (Type (u + 1))).functor ⋙
    proEtaleSheafInverseImage i (Type (u + 1)) ⋙
      (modelEquivalence S (Type (u + 1))).inverse

/-- Its transported right adjoint, the actual pro-etale direct image.
Source: Stacks Tags 09A5 and 00YV
(blueprint: lem-sfb-adic-stratum-completion-unit). -/
def direct {X S : Scheme.{u}} (i : S ⟶ X) :
    Sheaf (proEtaleModelTopology S) (Type (u + 1)) ⥤
      Sheaf (proEtaleModelTopology X) (Type (u + 1)) :=
  (modelEquivalence S (Type (u + 1))).functor ⋙
    proEtaleSheafDirectImage i (Type (u + 1)) ⋙
      (modelEquivalence X (Type (u + 1))).inverse

/-- Transport of the specified inverse-image adjunction, with no new functor choice.
Source: Stacks Tag 00YV (blueprint: lem-sfb-adic-stratum-completion-unit). -/
def adjunction {X S : Scheme.{u}} (i : S ⟶ X) : inverse i ⊣ direct i :=
  ((modelEquivalence X (Type (u + 1))).toAdjunction.comp
    (proEtaleSheafAdjunction i (Type (u + 1)))).comp
      (modelEquivalence S (Type (u + 1))).symm.toAdjunction

/-- Finite-limit structure inherited from the original inverse image and equivalences.
Source: Stacks Tag 00YV (blueprint: lem-sfb-adic-stratum-completion-unit). -/
instance inverse_finiteLimits {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i] :
    PreservesFiniteLimits (inverse i) :=
  haveI := (proEtale_immersion_inverseImage_preservesLimits i).1
  inferInstanceAs (PreservesFiniteLimits
    ((modelEquivalence X (Type (u + 1))).functor ⋙
      proEtaleSheafInverseImage i (Type (u + 1)) ⋙
        (modelEquivalence S (Type (u + 1))).inverse))


attribute [local irreducible] inverse direct adjunction

section Slice

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C) (U : C)

/-- Slice restriction with all algebraic operations evaluated on the underlying object.
Source: Stacks Tags 00XZ and 03D2
(blueprint: lem-sfb-adic-stratum-completion-unit). -/
def sliceAlgebra : ConstantCompletion.InverseImageData (J.overPullback (Type v) U) where
  rings := J.overPullback CommRingCat.{v} U
  algebra O :=
    { ringUnderlying := Iso.refl _
      ringAdd := fun _ _ _ _ h V x ↦ h (op V.unop.left) x
      ringMul := fun _ _ _ _ h V x ↦ h (op V.unop.left) x
      ringZero := fun _ _ h V x ↦ h (op V.unop.left) x
      ringOne := fun _ _ h V x ↦ h (op V.unop.left) x
      modules := SheafOfModules.overFunctor (siteModuleRings O) U
      moduleUnderlying := Iso.refl _
      moduleAdd := fun _ _ _ _ _ h V x ↦ h (op V.unop.left) x
      moduleZero := fun _ _ _ h V x ↦ h (op V.unop.left) x
      moduleSMul := fun _ _ _ _ _ h V x ↦ h (op V.unop.left) x }
  ring_naturality := fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm
  constants := NatIso.ofComponents
    (fun A ↦ ((Over.forget U).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{v} (J.over U) J).app ((Functor.const Cᵒᵖ).obj A) |>.symm)
    (fun f ↦ by
      exact ((Over.forget U).pushforwardContinuousSheafificationCompatibility
        CommRingCat.{v} (J.over U) J).inv.naturality
          ((Functor.const Cᵒᵖ).map f))

/-- The right adjoint of slice restriction, from the canonical site localization.
Source: Stacks Tag 00XZ (blueprint: lem-sfb-adic-stratum-completion-unit). -/
abbrev sliceDirect :=
  (Over.forget U).sheafPushforwardCocontinuous (Type v) (J.over U) J

/-- The canonical localization adjunction, rather than a chosen module map.
Source: Stacks Tag 00XZ (blueprint: lem-sfb-adic-stratum-completion-unit). -/
def sliceAdjunction : J.overPullback (Type v) U ⊣ sliceDirect J U :=
  (Over.forget U).sheafAdjunctionCocontinuous (Type v) (J.over U) J

attribute [local irreducible] sliceAlgebra sliceAdjunction

end Slice


section Comparisons

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
  (F : ConstantCompletion.InverseImageData L)
  (V : Sheaf K (Type v) ⥤ Sheaf J (Type v)) (adj : L ⊣ V)
  [PreservesFiniteLimits L] (A : Type v) [CommRing A] (I : Ideal A)

/-- Derived module inverse image with the finite-projection completed coefficient map.
Source: Stacks Tags 099L and 06YY
(blueprint: lem-sfb-adic-stratum-completion-unit). -/
def completedPull :
    ConstantCompletion.D (ConstantCompletion.completed J A I) ⥤
      ConstantCompletion.D (ConstantCompletion.completed K A I) :=
  (ConstantCompletion.derivedPull F V adj (ConstantCompletion.completedMap F A I)).functor

/-- The finite derived comparison in the actual quotient coefficient category. Its three
factors are the recorded K-flat-normalized finite scalar comparisons and the uniquely
normalized completed finite pullback comparison. Thus its source uses the actual
projection of the completed ring, not a replacement finite coefficient object.
Source: Stacks Tags 099L and 06YY
(blueprint: lem-sfb-adic-stratum-completion-unit). -/
def finiteComparison [IsNoetherianRing A] (n : ℕ) :
    completedPull F V adj A I ⋙
        ConstantCompletion.extend (ConstantCompletion.projection K A I n) ≅
      ConstantCompletion.extend (ConstantCompletion.projection J A I n) ⋙
        (ConstantCompletion.derivedPull F V adj
          (ConstantCompletion.constantMap F (A ⧸ I ^ (n + 1)))).functor :=
  Functor.isoWhiskerLeft (completedPull F V adj A I)
    (ConstantCompletion.finiteDerivedComparison K A I n).choose.symm ≪≫
  (ConstantCompletion.completedFinitePull_existsUnique F V adj A I n).exists.choose ≪≫
  Functor.isoWhiskerRight (ConstantCompletion.finiteDerivedComparison J A I n).choose
    (ConstantCompletion.derivedPull F V adj
      (ConstantCompletion.constantMap F (A ⧸ I ^ (n + 1)))).functor

/-- The three restriction clauses: the specified coefficient map is invertible; the
universal derived pullback computes on every complex; and the actual strict Koszul units
agree under a natural completion comparison. The finite comparison satisfies the
canonical scalar-insertion normalization in each quotient coefficient category. Finally local
internal-Hom completeness
restricts. This is just a package of the conclusions, not a replacement definition of
completeness or of completion.
Source: Bhatt--Scholze, Lemma 6.5.8 and Remark 6.5.10; Stacks Tags 099M and 0A0E
(blueprint: lem-sfb-adic-stratum-completion-unit). -/
def UnitRestriction [IsNoetherianRing A] (r : ℕ) (a : Fin r → A) : Prop :=
  IsIso (ConstantCompletion.completedMap F A I) ∧
  (∀ P : ConstantCompletion.Cx (ConstantCompletion.completed J A I),
    IsIso ((ConstantCompletion.derivedPull F V adj
      (ConstantCompletion.completedMap F A I)).comparison.app P)) ∧
  (∀ (PX : ConstantCompletion.KoszulPresentation J A I true r a)
      (PS : ConstantCompletion.KoszulPresentation K A I true r a),
    ∃ e : ConstantCompletion.koszulCompletion J A I PX ⋙ completedPull F V adj A I ≅
        completedPull F V adj A I ⋙ ConstantCompletion.koszulCompletion K A I PS,
      ∀ M : ConstantCompletion.D (ConstantCompletion.completed J A I),
        (completedPull F V adj A I).map (ConstantCompletion.koszulUnit J A I PX M) ≫
            e.hom.app M =
          ConstantCompletion.koszulUnit K A I PS ((completedPull F V adj A I).obj M)) ∧
  (∀ (n : ℕ) (M : ConstantCompletion.D (ConstantCompletion.completed J A I)),
    (ConstantCompletion.extend (ConstantCompletion.quotient K A I n)).map
          ((ConstantCompletion.derivedPullComparison F V adj A I).app M) ≫
        (ConstantCompletion.finiteDerivedComparison K A I n).choose.hom.app
          ((completedPull F V adj A I).obj M) =
      (ConstantCompletion.finitePull F V adj A I n).hom.app
          ((ConstantCompletion.dres (ConstantCompletion.coefficientMap J A I)).obj M) ≫
        (ConstantCompletion.derivedPull F V adj
          (ConstantCompletion.constantMap F (A ⧸ I ^ (n + 1)))).functor.map
            ((ConstantCompletion.finiteDerivedComparison J A I n).choose.hom.app M) ≫
        (finiteComparison F V adj A I n).inv.app M) ∧
  (∀ M : ConstantCompletion.D (ConstantCompletion.completed J A I),
    ConstantCompletion.IsComplete (ConstantCompletion.projection J A I 0) M →
      ConstantCompletion.IsComplete (ConstantCompletion.projection K A I 0)
        ((completedPull F V adj A I).obj M))

attribute [local irreducible] completedPull finiteComparison

end Comparisons

section Strata

variable {X : Scheme.{u}} (s : FiniteLocallyClosedStratification X)
  (F : ∀ α : Fin s.n, ConstantCompletion.InverseImageData (inverse (s.immersion α)))
  (A : Type (u + 1)) [CommRing A] (I : Ideal A)

/-- Restriction along the actual immersion realizing one stratum. The finite-limit
structure comes from that immersion, so it is not an extra hypothesis on a stratum.
Source: Bhatt--Scholze, Lemma 6.5.8
(blueprint: lem-sfb-adic-stratum-completion-unit). -/
def stratumPull (α : Fin s.n) :
    ConstantCompletion.D (ConstantCompletion.completed (proEtaleModelTopology X) A I) ⥤
      ConstantCompletion.D
        (ConstantCompletion.completed (proEtaleModelTopology (s.domain α)) A I) :=
  haveI := s.isImmersion α
  completedPull (F α) (direct (s.immersion α)) (adjunction (s.immersion α)) A I

/-- The composite of stratum inverse image and the actual localization at a site object,
with coefficient change given by the canonical finite-projection comparison.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication; Stacks Tag 00XZ
(blueprint: lem-sfb-adic-stratum-completion-unit). -/
def stratumSlicePull (α : Fin s.n) (U : proEtaleSiteModel (s.domain α)) :
    ConstantCompletion.D (ConstantCompletion.completed (proEtaleModelTopology X) A I) ⥤
      ConstantCompletion.D
        (ConstantCompletion.completed ((proEtaleModelTopology (s.domain α)).over U) A I) :=
  stratumPull s F A I α ⋙
    completedPull (sliceAlgebra (proEtaleModelTopology (s.domain α)) U)
      (sliceDirect (proEtaleModelTopology (s.domain α)) U)
      (sliceAdjunction (proEtaleModelTopology (s.domain α)) U) A I

attribute [local irreducible] stratumPull stratumSlicePull

end Strata

/-- Immersion and slice restriction preserve the finite-projection completed coefficients,
the actual Koszul completion units, and local derived ideal completeness, without a
boundedness assumption. The auxiliary `finiteComparison` gives the normalized comparison
for every finite derived reduction.

Source: Bhatt--Scholze, Lemma 6.5.8(1),(2), Remark 6.5.10 and Proposition 6.6.11;
Stacks Project, proetale.tex, Tags 099L and 099M, algebraization.tex, Tag 0A0E
(blueprint: lem-sfb-adic-stratum-completion-unit).

Proof, following steps 1--4 and the forward part of step 5 of the node:
1. Constant inverse-image comparisons identify every finite quotient and its transitions.
   Immersion inverse image preserves limits, by
   lem-weil-pbc-proetale-immersion-limit-preservation, so the limit lift formed from these
   projections is invertible. Its module inverse image is exact and preserves products.
2. Slice restriction is the recorded exact module overFunctor, with extension by zero
   as a left adjoint, by lem-pur-site-restriction-module-adjunction-exact. It preserves
   products and the quotient projections. Weakly-etale localization identifies its site
   with the covering scheme's site; lem-sfb-proetale-object-inverse-image-restriction
   identifies this restriction with the specified inverse image, also for ring sheaves.
3. The canonical ringed-topos tensor pullback comparison gives finiteComparison.
   Pull back a flat-term K-flat model and its finite-free Koszul tensor tower. The powers
   a_j^(m+1), the transitions (a_j,1), and the degree-zero augmentation all restrict to
   the corresponding strict maps. No perfectness of A/I^(m+1) over A is needed.
4. Exact countable products on each pro-etale site and slice allow the normalized strict
   Roos comparison (lem-weil-strict-roos-comparison). The additive comparison
   lem-pur-roos-additive-comparison identifies 1-shift on both product coordinates and
   takes the actual augmentation (gamma_m,0) to its restricted augmentation. This gives
   the displayed equality of the actual units, not just an isomorphism of their targets.
5. lem-weil-pbc-constant-completion-equivalence identifies local completeness with
   invertibility of these units. Their comparison therefore proves preservation.
-/
theorem adicStratumCompletionUnit (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = I) :
    (∀ (S : Scheme.{u}) (i : S ⟶ X) [IsImmersion i]
        (F : ConstantCompletion.InverseImageData (inverse i)),
      UnitRestriction F (direct i) (adjunction i) A I r a) ∧
    (∀ (S : Scheme.{u}) (i : S ⟶ X) [IsImmersion i]
        (U : proEtaleSiteModel S),
      UnitRestriction (sliceAlgebra (proEtaleModelTopology S) U)
        (sliceDirect (proEtaleModelTopology S) U)
        (sliceAdjunction (proEtaleModelTopology S) U) A I r a) := by
  sorry

/-- Finite strata with chosen pro-etale covering sieves detect local derived completeness.
A covering family is represented by its generated covering sieve; testing its arrows
also tests every further pullback, so includes arbitrary chosen covering families.

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication, and Remark 6.5.10;
Stacks Project, proetale.tex, Tags 099L and 099M
(blueprint: lem-sfb-adic-stratum-completion-unit).

Proof, step 5 of the node: apply adicStratumCompletionUnit to every stratum and then
its covering slices. By lem-weil-pbc-constant-completion-equivalence every restricted
unit is invertible exactly when the restricted object is locally complete. The module
underlying-sheaf comparisons identify these exact functors with the inverse images in
lem-weil-pbc-noetherian-stratum-detection; the object inverse-image/restriction theorem
identifies the covering localizations. Apply their joint conservativity to the unbounded
derived completion unit. Invertibility of that unit is local completeness on X. For the
forward implication use the already proved preservation clauses. Empty schemes and empty
strata use the empty-cover sheaf axiom; no nonemptiness hypothesis is introduced.
-/
theorem adicStratumCompletionUnit_detection (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (s : FiniteLocallyClosedStratification X)
    (V : ∀ α : Fin s.n,
      Sieve ((AsSmall.up : (s.domain α).ProEt ⥤ proEtaleSiteModel (s.domain α)).obj
        (⊤_ (s.domain α).ProEt)))
    (hV : ∀ α : Fin s.n, V α ∈ proEtaleModelTopology (s.domain α)
      ((AsSmall.up : (s.domain α).ProEt ⥤ proEtaleSiteModel (s.domain α)).obj
        (⊤_ (s.domain α).ProEt)))
    (F : ∀ α : Fin s.n, ConstantCompletion.InverseImageData (inverse (s.immersion α)))
    (M : ConstantCompletion.D (ConstantCompletion.completed (proEtaleModelTopology X) A I)) :
    ConstantCompletion.IsComplete
        (ConstantCompletion.projection (proEtaleModelTopology X) A I 0) M ↔
      ∀ (α : Fin s.n) (U : proEtaleSiteModel (s.domain α))
        (f : U ⟶ (AsSmall.up : (s.domain α).ProEt ⥤
          proEtaleSiteModel (s.domain α)).obj (⊤_ (s.domain α).ProEt)), V α f →
        ConstantCompletion.IsComplete
          (ConstantCompletion.projection ((proEtaleModelTopology (s.domain α)).over U) A I 0)
          ((stratumSlicePull s F A I α U).obj M) := by
  sorry

end AlgebraicGeometry.Scheme.SfbAdicRestriction
