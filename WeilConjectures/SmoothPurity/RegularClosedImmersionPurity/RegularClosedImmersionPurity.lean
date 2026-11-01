/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionPurity
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.SixFunctors.AdicSmoothDualizing.AdicSmoothDualizingFinitePowers
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection

/-! # Purity and the normalized class of a regular closed immersion

Source: latest blueprint, sec-smooth-purity/sk-thm-regular/_section.md,
clauses (a)--(d) and proof Steps 1--5 (blueprint: sk-thm-regular).

Classes use the published supported Hom, concrete Kummer boundaries, and exact
site comparison. The closed exceptional adjunction gives the map sending one
to the class. Its right adjoint is the existing sections-with-support functor;
on the constructible domain this is the canonical closed presentation of Ri!.
The signed smooth comparison is stated by its tensor/projection/counit equation,
which uniquely characterizes the comparison assembled in proof Steps 1--2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures.RegularClosedImmersionPurity

/-- The canonical Cartesian square associated to a scheme-theoretic frame.
Source: the frame paragraph (blueprint: sk-thm-regular). -/
def frameSquare {Z X : Scheme.{u}} {i : Z ⟶ X} {c : ℕ} (F : i.EtaleFrame c) :
    ChosenCartesianSquare F.toZ (F.U.zeroLocusSubschemeι (Set.range F.f)) i F.e where
  w := F.isPullback.w
  isoPullback := F.isPullback.isoPullback
  hom_fst := F.isPullback.isoPullback_hom_fst
  hom_snd := F.isPullback.isoPullback_hom_snd

/-- Restriction to every frame is its actual ordered product of individual
Kummer support boundaries. The empty product is included.
Source: clause (b), displayed class formula (blueprint: sk-thm-regular). -/
def IsFundamentalClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ)
    (α : P.FunctorialCupH true i (2 * (c : ℤ)) c) : Prop :=
  ∀ F : i.EtaleFrame c,
    P.functorialCupPullback true i (F.U.zeroLocusSubschemeι (Set.range F.f))
      F.e F.toZ (frameSquare F) aX (2 * (c : ℤ)) c α =
        P.frameBoundaryProduct F.U (F.e ≫ aX) c F.f

/-- The actual constant coefficient complex in degree zero.
Source: clause (c) (blueprint: sk-thm-regular). -/
abbrev unit (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  (P.functorialCupSingle true X).obj (P.constant X)

/-- The Kummer frame classes glue uniquely, with no relative-dimension constraint
on a connected component and no chosen global frame.
Source: clause (b), proof Step 3 (blueprint: sk-thm-regular).
Proof: smooth purity and co-projection give degree-zero concentration locally on
each component. The supported adjunction reads frame classes as sections of its
H^0 sheaf. On common refinements the generating tuples differ by local elementary
operations: unit scaling has zero extra boundary, transpositions of degree-two
factors have sign one, and affine-line homotopy identifies shear endpoints.
Therefore the classes agree on overlaps. Regularity supplies local frames; the
sheaf axiom glues their sections uniquely. The empty tuple gives the unit when
c=0, and the empty support gives its unique zero class. -/
theorem existsUnique_fundamentalClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    ∃! α : P.FunctorialCupH true i (2 * (c : ℤ)) c,
      IsFundamentalClass P i aX c α := by
  sorry

/-- The uniquely specified glued class; choice is applied only to the unique
class characterized by its actual Kummer-frame restrictions.
Source: clause (b) (blueprint: sk-thm-regular). -/
def fundamentalClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    P.FunctorialCupH true i (2 * (c : ℤ)) c :=
  (existsUnique_fundamentalClass P i aX c hreg hZ).exists.choose

/-- The ordinary representative is uniquely fixed by finite etale/pro-etale comparison.
Source: supported adjunction in (a), Step 2b (blueprint: sk-thm-regular).
Proof: the support constant and finite Tate target are bounded below etale-origin
complexes. The derived site comparison is fully faithful on these objects. The
canonical source and target comparisons identify its Hom bijection with the
published functorialCupCompare, so the given global class has exactly one lift. -/
theorem existsUnique_ordinaryClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    ∃! α : P.FunctorialCupH false i (2 * (c : ℤ)) c,
      P.functorialCupCompare i (2 * (c : ℤ)) c α = fundamentalClass P i aX c hreg hZ := by
  let hbij := (PurityFiniteSetting.supportedCupFunctoriality P).2.supported_bijective
    (i := i) aX (2 * (c : ℤ)) c
  obtain ⟨α, hα⟩ := hbij.2 (fundamentalClass P i aX c hreg hZ)
  refine ⟨α, hα, ?_⟩
  intro β hβ
  apply hbij.1
  exact hβ.trans hα.symm

set_option maxHeartbeats 800000 in
-- The published root-tensor comparison unfolds several derived-site layers.
end WeilConjectures.RegularClosedImmersionPurity
