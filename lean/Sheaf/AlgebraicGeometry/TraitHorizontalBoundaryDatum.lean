/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.CartierExtensionFactorialComplement
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.AlgebraicGeometry.AffineOpenBoundaryCodimensionOne

/-!
# A horizontal Cartier boundary compatible with trait descent

Source: BLR, Néron Models, 6.5 Theorem 1, proof of case (a), printed p.160;
EGA IV4, 21.12.7 (blueprint: lem-sfb-trait-horizontal-boundary-datum).

`lineIsoAt` evaluates an actual isomorphism on the universal transport scheme at a
scheme-valued point. The theorem states the closure, its full ideal invariance, and
the cocycle of the line isomorphism using the published transport descent datum.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.TraitHorizontalBoundary

/-- Evaluate the line isomorphism on the universal transport scheme at a point.
This is pullback of the supplied isomorphism, with the canonical composition comparisons;
its two endpoints are the original point and its transport by `α`.
Source: BLR 6.5 Theorem 1, proof of (a), p.160; Stacks 0097
(blueprint: lem-sfb-trait-horizontal-boundary-datum). -/
noncomputable def lineIsoAt {S S' : Scheme.{u}} {p : S' ⟶ S} {X : Over S'}
    (α : Over.DescentDatum p X) (M : X.left.Modules)
    (φ : (Scheme.Modules.tensorPullback (pullback.fst (X.hom ≫ p) p)).obj M ≅
      (Scheme.Modules.tensorPullback α.toHom).obj M)
    {T : Scheme.{u}} (f₁ f₂ : T ⟶ S') (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ X) :
    (Scheme.Modules.tensorPullback a.left).obj M ≅
      (Scheme.Modules.tensorPullback (α.transport f₁ f₂ h a).left).obj M :=
  (eqToIso (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj M)
    (pullback.lift_fst a.left f₂ (by rw [← Category.assoc, Over.w a]; exact h)))).symm ≪≫
  (Scheme.Modules.tensorPullbackSectionComp
    (pullback.lift a.left f₂ (by rw [← Category.assoc, Over.w a]; exact h))
    (pullback.fst (X.hom ≫ p) p)).app M ≪≫
  (Scheme.Modules.tensorPullback
    (pullback.lift a.left f₂ (by rw [← Category.assoc, Over.w a]; exact h))).mapIso φ ≪≫
  ((Scheme.Modules.tensorPullbackSectionComp
    (pullback.lift a.left f₂ (by rw [← Category.assoc, Over.w a]; exact h))
    α.toHom).app M).symm ≪≫
  eqToIso (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj M)
    (α.transport_left_eq_lift_toHom f₁ f₂ h a).symm)

/-- The cocycle for an isomorphism on the universal transport scheme. Evaluating at
three base points gives exactly the original scheme datum's threefold-overlap cocycle.
Source: BLR 6.5 Theorem 1, proof of (a), p.160; Stacks 023V
(blueprint: lem-sfb-trait-horizontal-boundary-datum). -/
def IsLineCocycle {S S' : Scheme.{u}} {p : S' ⟶ S} {X : Over S'}
    (α : Over.DescentDatum p X) (M : X.left.Modules)
    (φ : (Scheme.Modules.tensorPullback (pullback.fst (X.hom ≫ p) p)).obj M ≅
      (Scheme.Modules.tensorPullback α.toHom).obj M) : Prop :=
  ∀ (T : Scheme.{u}) (f₁ f₂ f₃ : T ⟶ S')
    (h₁₂ : f₁ ≫ p = f₂ ≫ p) (h₂₃ : f₂ ≫ p = f₃ ≫ p) (a : Over.mk f₁ ⟶ X),
    lineIsoAt α M φ f₁ f₂ h₁₂ a ≪≫
      lineIsoAt α M φ f₂ f₃ h₂₃ (α.transport f₁ f₂ h₁₂ a) =
    lineIsoAt α M φ f₁ f₃ (h₁₂.trans h₂₃) a ≪≫
      eqToIso (congrArg
        (fun b : Over.mk f₃ ⟶ X ↦ (Scheme.Modules.tensorPullback b.left).obj M)
        (α.transport_transport f₁ f₂ f₃ h₁₂ h₂₃ a).symm)

/-- A generic boundary and its schematic closure carry the original descent datum.
Source: BLR 6.5 Theorem 1, proof of case (a), p.160, and EGA IV4, 21.12.7
(blueprint: lem-sfb-trait-horizontal-boundary-datum).

Proof plan:
1. DVRs are regular Noetherian rings; faithful flatness embeds B in C and sends a
   uniformizer to a unit times a positive power of a uniformizer. Thus C tensor K is L
   (lem-sc-dvr-dimension-one, lem-trf-flat-module-torsionfree-domain,
   lem-weil-pbc-faithfully-flat-surjective-spectrum,
   lem-weil-pbc-dvr-unit-times-uniformizer-power and the localization/open-base-change lemmas).
2. Smooth affine charts are regular Noetherian; their stalks are UFDs and flat over C.
   The total space is separated, and the uniformizer is nonzero at every stalk
   (lem-weil-pbc-regular-ring-smooth-ascent, lem-trf-regular-local-ufd-boundary-factorization,
   lem-pc-smooth-flat, lem-sc-separated-over-affine-scheme-separated).
3. Fpqc descent makes X0 smooth separated finite type over K; regular-normal decomposition
   gives finitely many integral open-and-closed components, each meeting the generic open
   (the smooth/separated/finite-type base-change and fpqc descent nodes,
   lem-weil-pbc-smooth-scheme-over-field-regular, rem-pc-regular-normal).
4. The generic open is affine. Apply lem-sfb-smooth-affine-cartier-boundary componentwise
   and glue across the disjoint components, including the empty case. Flat pullback to L
   gives the divisor on the generic fibre (lem-pc-flat-pullback-effective-cartier-ideal).
5. Its inclusion in X' is affine and quasi-compact; the scheme-image kernel formula gives
   exactly the schematic closure, retaining multiplicities (lem-weil-pbc-scheme-image-qc-kernel,
   lemma-nagata-scheme-image-ideal-qc, lem-sfb-scheme-image-flat-base-change).
6. First extend the divisor using lem-sfb-cartier-extension-factorial-complement. In a
   factorial stalk, saturate a local equation h by powers of the uniformizer a.
7. Delete from h precisely the prime powers dividing a. The remaining product generates
   the saturation and is a nonzerodivisor. Lem-sfb-stalk-nonzerodivisor-cartier-spreading
   makes the specified closure Cartier, not merely an unspecified extension.
8. Fibrewise density implies density in X' and in its special fibre (regular-normal
   decomposition and faithful flatness of field extension).
9. By lem-sfb-affine-open-boundary-codimension-one every boundary component has codimension
   one. A vertical generic point would be a special-fibre generic point, contradicting
   fibrewise density. Thus the closure's support is exactly the whole boundary.
10. Both projections from the double cover are flat. Flat scheme-image base change and
    the generic model identify the two full pulled-back ideals under the datum.
11. Dualize the ideal identification to obtain the isomorphism of divisor lines;
    lem-pc-divisor-line-bundle-invertible and lem-pc-divisor-line-bundle-flat-pullback
    identify these with the specified tensor pullbacks. Locally the comparison sends
    b tensor lambda to (c tensor s maps to bc lambda(s)); it is independent of a frame.
12. On the triple cover, all ideal identifications are induced by the original scheme
    datum. Its cocycle, and compatibility of the displayed dual comparison with scalar
    extension, imply the stated line cocycle. No group or ampleness assertion is used.
-/
theorem exists_horizontal_boundary
    (B C K L : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra B C] [Module.FaithfullyFlat B C]
    [Field K] [Algebra B K] [IsFractionRing B K]
    [Field L] [Algebra C L] [IsFractionRing C L]
    [Algebra K L] [Algebra B L] [IsScalarTower B C L] [IsScalarTower B K L]
    (X : Over (Spec (.of C))) [Smooth X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (α : Over.DescentDatum (Spec.map (CommRingCat.ofHom (algebraMap B C))) X)
    (Xη : Over (Spec (.of L))) (r : Xη.left ⟶ X.left)
    (hr : IsPullback r Xη.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap C L))))
    (X₀ : Over (Spec (.of K))) (q : Xη.left ⟶ X₀.left)
    (hq : IsPullback q Xη.hom X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (hgeneric : ∀ (T : Scheme.{u}) (a b : T ⟶ Xη.left)
      (h : (a ≫ r ≫ X.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) =
        (b ≫ r ≫ X.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))),
      (α.transport (a ≫ r ≫ X.hom) (b ≫ r ≫ X.hom) h
        (Over.homMk (a ≫ r) rfl)).left = b ≫ r ↔ a ≫ q = b ≫ q)
    (U : Over (Spec (.of B))) [IsAffineHom U.hom]
    (W : X.left.Opens) [IsAffine W.toScheme] (uW : W.toScheme ⟶ U.left)
    (huW : IsPullback uW (W.ι ≫ X.hom) U.hom
      (Spec.map (CommRingCat.ofHom (algebraMap B C))))
    (hrestricted : ∀ (T : Scheme.{u}) (a b : T ⟶ W.toScheme)
      (h : (a ≫ W.ι ≫ X.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) =
        (b ≫ W.ι ≫ X.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))),
      (α.transport (a ≫ W.ι ≫ X.hom) (b ≫ W.ι ≫ X.hom) h
        (Over.homMk (a ≫ W.ι) rfl)).left = b ≫ W.ι ↔ a ≫ uW = b ≫ uW)
    (hdense : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ Spec (.of C)),
      Dense ((pullback.fst X.hom s) ⁻¹' (W : Set X.left)))
    (UK : Over (Spec (.of K))) (v : UK.left ⟶ U.left)
    (hv : IsPullback v UK.hom U.hom (Spec.map (CommRingCat.ofHom (algebraMap B K))))
    (iK : UK.left ⟶ X₀.left) [IsOpenImmersion iK] (hiK : iK ≫ X₀.hom = UK.hom)
    (hopen : ∀ (T : Scheme.{u}) (a : T ⟶ W.toScheme) (l : T ⟶ Spec (.of L))
      (b : T ⟶ UK.left) (c : T ⟶ Xη.left),
      a ≫ W.ι ≫ X.hom = l ≫ Spec.map (CommRingCat.ofHom (algebraMap C L)) →
      b ≫ v = a ≫ uW →
      b ≫ UK.hom = l ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) →
      c ≫ r = a ≫ W.ι → c ≫ Xη.hom = l → b ≫ iK = c ≫ q) :
    ∃ (D₀ : X₀.left.IdealSheafData) (D' : X.left.IdealSheafData),
      D₀.IsInvertible ∧ (D₀.support : Set X₀.left) = (Set.range iK)ᶜ ∧
      (∀ V : X.left.affineOpens, D'.ideal V =
        RingHom.ker (((D₀.comap q).subschemeι ≫ r).app V.1).hom) ∧
      D'.IsInvertible ∧ (D'.support : Set X.left) = (W : Set X.left)ᶜ ∧
      D'.comap (pullback.fst (X.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (Spec.map (CommRingCat.ofHom (algebraMap B C)))) = D'.comap α.toHom ∧
      (Scheme.Modules.dual D'.toModules).IsInvertible ∧
      ∃ φ : (Scheme.Modules.tensorPullback (pullback.fst (X.hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap B C)))
          (Spec.map (CommRingCat.ofHom (algebraMap B C))))).obj
          (Scheme.Modules.dual D'.toModules) ≅
        (Scheme.Modules.tensorPullback α.toHom).obj (Scheme.Modules.dual D'.toModules),
        IsLineCocycle α (Scheme.Modules.dual D'.toModules) φ := by
  sorry

end AlgebraicGeometry.TraitHorizontalBoundary
