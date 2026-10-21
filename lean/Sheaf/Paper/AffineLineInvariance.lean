/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
import Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.AlgebraicGeometry.PurityClopenAffineLineFiniteType
import Sheaf.Paper.ConcentratedComplexShift
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.PurityLisseUniqueness

/-! # Invariance along the affine line

Source: blueprint sec-smooth-purity/sk-prop-a1-inv/prop-pur-a1-invariance.md,
order 1961 (blueprint: prop-pur-a1-invariance).

The finite-level purity conventions are used. Fixed-scalar module sheaves are
transported by the published canonical intrinsic realization when testing membership
in Dctf. Pullbacks are the published exact inverse images, descended termwise.
The local shape retains its integer twist and shift. The finite Tate sheaf uses the
existing signed root-of-unity construction at the characteristic of the finite ring,
then the canonical comparison inverse image. This is the finite torsion Tate line;
no choice of a trivialization or of a root of unity is made. No common shift is required.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

namespace PurityFiniteSetting

/-- Finiteness of the actual positive coefficient quotient. Source: the finite purity
conventions and Padic.finite_coefficientExtensionRing (blueprint: prop-pur-a1-invariance). -/
instance a1RingFinite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The fixed-scalar presentation of the same small pro-etale derived category.
Source: blueprint order 1961, finite-level convention (blueprint: prop-pur-a1-invariance). -/
abbrev a1Category (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))

/-- Membership in Dctf transported by the existing canonical coefficient realization.
Source: blueprint order 1961 and def-weil-finite-tor-amplitude
(blueprint: prop-pur-a1-invariance). -/
def a1Ctf (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (K : P.a1Category T) : Prop :=
  finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T
    ((ProEtale.finiteCoefficientIntrinsicRealization T P.Ring).mapDerivedCategory.obj K)

/-- Exact constant-coefficient inverse image, with no completion or derived truncation.
Source: blueprint order 1961, def-weil-derived-pullback-tensor-hom, finite-level clause
(blueprint: prop-pur-a1-invariance). -/
abbrev a1Pullback (P : PurityFiniteSetting.{u}) {T S : Scheme.{u}} (f : T ⟶ S) :
    P.a1Category S ⥤ P.a1Category T :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategory

/-- The canonical composition comparison, descended from the published inverse-image mate.
Source: blueprint order 1961, canonical composition convention
(blueprint: prop-pur-a1-invariance). -/
def a1PullbackComp (P : PurityFiniteSetting.{u}) {T S R : Scheme.{u}}
    (f : T ⟶ S) (g : S ⟶ R) :
    P.a1Pullback (f ≫ g) ≅ P.a1Pullback g ⋙ P.a1Pullback f :=
  Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Canonical restriction of a pullback along a section. The equality is the defining
section equation, and the comparison uses the identity and composition mates.
Source: blueprint order 1961, i_s^* a^* = id (blueprint: prop-pur-a1-invariance). -/
def a1SectionComparison (P : PurityFiniteSetting.{u}) {T S : Scheme.{u}}
    (f : T ⟶ S) (s : S ⟶ T) (h : s ≫ f = 𝟙 S) :
    P.a1Pullback f ⋙ P.a1Pullback s ≅ 𝟭 (P.a1Category S) :=
  (P.a1PullbackComp s f).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarCongr (ModuleCat.{u + 1} P.Coefficient) h ≪≫
        ProEtale.upperStarId (ModuleCat.{u + 1} P.Coefficient) S) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The naturality square for restriction to t=1, with its actual affine-space maps.
The proof inside the construction checks the coordinate of the canonical square;
it supplies no hypothesis on the sheaves. Source: blueprint order 1961, normalization
on Y_alpha (blueprint: prop-pur-a1-invariance). -/
def a1OneBaseChange (P : PurityFiniteSetting.{u}) {T S : Scheme.{u}} (f : T ⟶ S) :
    P.a1Pullback (AffineSpace.map (ULift.{u} (Fin 1)) f) ⋙
        P.a1Pullback (AffineSpace.oneSection (ULift.{u} (Fin 1)) T) ≅
      P.a1Pullback (AffineSpace.oneSection (ULift.{u} (Fin 1)) S) ⋙ P.a1Pullback f :=
  (P.a1PullbackComp _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarCongr (ModuleCat.{u + 1} P.Coefficient)
        (by
          simp only [AffineSpace.oneSection, AffineSpace.homOfVector_comp_map,
            AffineSpace.comp_homOfVector, Category.id_comp, Category.comp_id]
          congr 1
          funext j
          exact (map_one f.appTop.hom).symm)) ≪≫
    P.a1PullbackComp _ _

/-- A finite locally constant rank-one module sheaf, in the fixed-scalar presentation.
The local-constancy predicate is the recorded dependency and rank is tested on its
canonical associated module sheaf. Since the coefficient ring is finite, rank one
also makes the local stalks finite. Source: blueprint order 1961, local shape clause
(blueprint: prop-pur-a1-invariance). -/
def a1RankOne (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (L : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) : Prop :=
  IsLocallyConstantProEtaleFixedModuleSheaf T P.Coefficient L ∧
    SheafOfModules.IsFiniteLocallyFreeOfRank
      ((ProEtale.finiteCoefficientIntrinsicRealization T P.Ring).obj L) 1

/-- The signed finite Tate sheaf from the published roots-of-unity construction.
The characteristic is a canonical annihilator of the actual finite quotient, so
extension of scalars from Z/(char A) is defined without an extra divisibility hypothesis.
Source: blueprint order 1961 and Stacks Tag 03PK, finite torsion Tate twists
(blueprint: prop-pur-a1-invariance). -/
def a1TateLine (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (m : ℤ) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj
    (finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient) T
      (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) m)

/-- Twist a sheaf by the actual finite Tate line. Its flat rank-one factor means
ordinary sheaf tensor represents the derived twist of a sheaf placed in degree zero.
Source: blueprint order 1961, local shape and proof Step 1; Stacks Tag 03PK
(blueprint: prop-pur-a1-invariance). -/
def a1TwistedSheaf (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (L : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) (m : ℤ) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient) :=
  letI := Sheaf.monoidalCategory (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)
  L ⊗ P.a1TateLine T m

/-- Restriction of an affine-line comparison to either standard section, followed
by the canonical identification with C. Source: blueprint order 1961, clauses (2)
and (3) (blueprint: prop-pur-a1-invariance). -/
def a1FibreComparison (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (F : P.a1Category (AffineSpace (ULift.{u} (Fin 1)) Y)) (C : P.a1Category Y)
    (κ : F ≅ (P.a1Pullback (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)).obj C)
    (s : Y ⟶ AffineSpace (ULift.{u} (Fin 1)) Y)
    (hs : s ≫ (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) = 𝟙 Y) :
    (P.a1Pullback s).obj F ≅ C :=
  (P.a1Pullback s).mapIso κ ≪≫ (P.a1SectionComparison _ s hs).app C

end PurityFiniteSetting

/-- Normalized local comparisons on the affine line glue, are uniquely determined by
restriction to t=1, and identify the two fibres by i_0^*κ followed by θ inverse.
Source: blueprint sec-smooth-purity/sk-prop-a1-inv/prop-pur-a1-invariance.md,
order 1961 (blueprint: prop-pur-a1-invariance).

Proof:
1. Work at the finite coefficient level of def-pur-conventions. The cover and all its
base changes are pro-etale covers (lem-weil-pbc-etale-covering-base-change), and exact
inverse images commute with cohomology and shifts. Use the canonical composition
comparisons throughout (lem-weil-pbc-proetale-derived-pullback-composition).
2. Absorb each twist into its rank-one local system using lem-pur-twist-sheaf-locally-free.
Pull back the local comparison at t=1 to describe C on every cover member.
3. Group covering members by their shifts. Exact geometric stalks show that intersecting
nonempty members have the same shift. Their open images give a disjoint clopen partition;
boundedness of C makes it finite. Empty members contribute nothing.
4. On a finite clopen partition, module sheaves and maps are reconstructed componentwise
by the product formula on the disjoint cover. Restriction and extension by zero on each
piece are exact. Apply them termwise and descend through localization to reconstruct
derived objects and morphisms componentwise (lem-weil-pbc-localization-universal-property).
5. On each nonempty piece there is one shift n. Cover-local detection gives vanishing
of cohomology outside -n. Apply lem-pur-concentrated-complex-shift and
lem-weil-pbc-derived-single-fully-faithful to replace all maps by ordinary sheaf maps.
6. On overlaps the normalized maps agree, first on G_m by the second assertion of
lem-pur-lisse-uniqueness and then on A1 by its first assertion.
7. Use lem-pur-sheaf-hom-cover-gluing to glue the maps and their inverses. The composites
are identities by the same uniqueness. Shift back and reassemble the clopen pieces.
8. Normalization holds locally on Y and hence globally. Any other normalized map agrees
by the two lisse uniqueness assertions; faithfulness of the single embedding returns
the equality in the derived category. This also proves independence of cover and maps.
9. Apply both section pullbacks and the canonical section comparisons. Their composite
with θ inverse is the specified isomorphism between the fibres; its canonicity follows
from the uniqueness just proved. The empty scheme gives singleton Hom sets throughout. -/
theorem affineLine_invariance
    (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of P.field.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (F : P.a1Category (AffineSpace (ULift.{u} (Fin 1)) Y)) (C : P.a1Category Y)
    (hF : P.a1Ctf _ F) (hC : P.a1Ctf Y C)
    (θ : (P.a1Pullback (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)).obj F ≅ C)
    {I : Type v} (U : I → Scheme.{u}) (u : ∀ α : I, U α ⟶ Y)
    [∀ α : I, Etale (u α)]
    [∀ α : I, IsSeparated (u α ≫ Y ↘ Spec (CommRingCat.of P.field.k))]
    [∀ α : I, LocallyOfFiniteType (u α ≫ Y ↘ Spec (CommRingCat.of P.field.k))]
    [∀ α : I, QuasiCompact (u α ≫ Y ↘ Spec (CommRingCat.of P.field.k))]
    (hcover : ∀ y : Y, ∃ α : I, ∃ x : U α, u α x = y)
    (hshape : ∀ α : I,
      ∃ (L : Sheaf (ProEt.topology (AffineSpace (ULift.{u} (Fin 1)) (U α)))
          (ModuleCat.{u + 1} P.Coefficient)) (m n : ℤ),
        P.a1RankOne _ L ∧
          Nonempty ((P.a1Pullback (AffineSpace.map (ULift.{u} (Fin 1)) (u α))).obj F ≅
            ((DerivedCategory.singleFunctor _ 0).obj (P.a1TwistedSheaf _ L m))⟦n⟧))
    (κloc : ∀ α : I,
      (P.a1Pullback (AffineSpace.map (ULift.{u} (Fin 1)) (u α))).obj F ≅
        (P.a1Pullback (AffineSpace.map (ULift.{u} (Fin 1)) (u α))).obj
          ((P.a1Pullback (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)).obj C))
    (hnormal : ∀ α : I,
      ((P.a1Pullback (AffineSpace.oneSection (ULift.{u} (Fin 1)) (U α))).mapIso (κloc α) ≪≫
        (P.a1OneBaseChange (u α)).app
          ((P.a1Pullback (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)).obj C) ≪≫
        (P.a1Pullback (u α)).mapIso
          ((P.a1SectionComparison (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)
            (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)
            (AffineSpace.oneSection_comp_over _ _)).app C)) =
      (P.a1OneBaseChange (u α)).app F ≪≫ (P.a1Pullback (u α)).mapIso θ) :
    ∃ κ : F ≅ (P.a1Pullback (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)).obj C,
      (∀ α : I,
        (P.a1Pullback (AffineSpace.map (ULift.{u} (Fin 1)) (u α))).mapIso κ = κloc α) ∧
      (∀ κ' : F ≅ (P.a1Pullback (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)).obj C,
        (∀ α : I,
          (P.a1Pullback (AffineSpace.map (ULift.{u} (Fin 1)) (u α))).mapIso κ' = κloc α) →
        κ' = κ) ∧
      P.a1FibreComparison Y F C κ (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)
          (AffineSpace.oneSection_comp_over _ _) = θ ∧
      (∀ κ' : F ≅ (P.a1Pullback (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)).obj C,
        P.a1FibreComparison Y F C κ' (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)
            (AffineSpace.oneSection_comp_over _ _) = θ → κ' = κ) ∧
      ∃ e : (P.a1Pullback (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj F ≅
          (P.a1Pullback (AffineSpace.oneSection (ULift.{u} (Fin 1)) Y)).obj F,
        e = P.a1FibreComparison Y F C κ (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)
          (AffineSpace.zeroSection_comp_over _ _) ≪≫ θ.symm := by
  sorry

end WeilConjectures
