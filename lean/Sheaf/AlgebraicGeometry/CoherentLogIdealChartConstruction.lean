/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Compactification.FiniteTypeExtension
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import WeilConjectures.AlgebraicGeometry.Descent
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.TraceFormula.FsFaceSharpening
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.GroupTheory.FineMonoidFiniteSaturation

/-!
# Coherent log ideals and their fine and saturated chart constructions

Source: ILO VIII 3.1.17--3.1.21, 3.2.9, 3.3.5--3.3.9 and 3.4.2
(blueprint: lem-trf-coherent-log-ideal-chart-construction).

The chart-cover structures express actual gluing on common localizations over each
strict étale affine chart. A single pair of global log schemes works for every such
chart, expressing descent and independence of presentations. The final clause gives
strict étale compatibility of the objects and their canonical saturation map.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A nonempty coherent log ideal has a finite-type quasi-coherent algebraization, a
fine principalization and an fs principalization, with the prescribed tensor charts,
common-localization overlaps and finite canonical saturation morphism. These descend
and commute with strict étale restriction.

Source: ILO VIII 3.1.17--3.1.21 (printed pp. 100--101), 3.2.9 (p. 104),
3.3.5--3.3.9 (pp. 107--108), 3.4.2 (p. 110)
(blueprint: lem-trf-coherent-log-ideal-chart-construction).

Proof:
1. On a strict chart, every ideal section is locally a generator times a chart
section times a unit. Its ring image therefore generates precisely the displayed
finite span. Descend the ideals and inclusions by `lem-pc-fpqc-descent`, using
`lem-weil-pbc-fpqc-finer-than-etale`. Faithful flatness reflects injectivity and
`lem-weil-pbc-faithfully-flat-descent-finite-module` descends finite generation.
2. Generators of P and the finitely many h/e generate Q_e. It is integral inside
P^gp, and its group completion is P^gp since it contains P. Apply
`lem-trf-fine-monoid-finite-saturation` for its saturation, finite generation,
canonical completion, and a finite set of translates covering the saturation.
3. Form A tensor Z[Q_e], respectively A tensor Z[Q_e^sat], over Z[P]. Give its
spectrum the associated log structure of q mapping to 1 tensor z^q, using the
pushout chart condition of `def-trf-fs-log-blowup`. The pulled ideal is generated
by e since h=e(h/e); no nonzero or non-zero-divisor hypothesis is needed.
4. The common localization of Q_e at f/e equals that of Q_f at e/f. Both maps
are identities inside the common group, so their triple cocycle holds. The same
holds after saturation, by the localization clause of finite monoid saturation.
`lem-weil-pbc-glue-schemes` glues the affine schemes; glue their chart log sheaves.
5. If a fine test object's pulled ideal has generator m, write g(e)=m*a_e for
all e and m=g(e)*b for one e. Cancellation gives a_e*b=1. Thus one g(e) generates,
and every g(h)/g(e) is a log section locally. Extend the fixed group map to Q_e.
The tensor presentation and `lem-weil-pbc-morphism-into-affine-scheme` give the
local lift. Cancellation forces uniqueness. On overlaps the lifts agree and
`lem-trf-polarized-fine-log-etale-descent` descends the log morphisms.
6. Fs stalks are saturated: `lem-trf-fs-face-sharpening` gives saturation of their
characteristic monoids, and units lift. The fixed group map therefore extends
uniquely to Q_e^sat. The same tensor and descent argument gives the fs property.
7. Strict étale restriction uses the same monoids and tensor presentations.
The universal properties identify choices of charts and generators; uniqueness
forces all comparison cocycles and compatibility with further restriction.
8. Generators of the principal log ideal form an O^units torsor. Glue free line
modules with frames v_f=alpha(f/e)*v_e. The sections alpha(h/e)*v_e glue, and their
nonvanishing loci are precisely the affine h-charts. The ampleness criterion of
`def-weil-pbc-ample-invertible-module` makes this a relatively ample line bundle.
The generator-torsor construction is canonical and satisfies the descent cocycle.
9. Choose a strict étale affine chart cover with finite generators. Step 7 and
the polarizations of Step 8 meet `lem-trf-polarized-fine-log-etale-descent`, giving
global fine and fs log schemes. Their universal properties descend by uniqueness.
10. The fine universal property supplies the unique saturation map. The inverse
image of an e-chart is its saturated e-chart, since both are the locus where e
generates the ideal. The finite translate set from Step 2 gives spanning monomials
for Z[Q_e^sat] over Z[Q_e]; after tensoring they still span. Finiteness descends by
`lem-weil-pbc-fpqc-descend-finite`. Step 7 also identifies this map on restrictions.
-/
theorem coherentLogIdeal_chart_construction
    (Y : FineSaturatedLogScheme.{u}) (I : Y.logStructure.IdealFamily)
    (hI : Y.logStructure.IsNonemptyCoherentIdeal I) :
    ∃ K : Y.scheme.IdealSheafData,
      K.ofFiniteType ∧ K.toModules.IsQuasiCoherentFiniteType ∧
      (∀ (V : Y.scheme.affineOpens) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ Y.scheme)
        (w : (Scheme.pointSmallEtale t).fiber.obj (Scheme.Etale.mk V.1.ι)),
        (K.ideal V).map
            ((strictLocalGerm Y.scheme t (Scheme.Etale.mk V.1.ι) w).hom.comp
              V.1.topIso.inv.hom) =
          Ideal.span (Y.logStructure.toEtalePrelogStructure.stalkAlpha t ''
            Y.logStructure.idealStalk I t)) ∧
      (∀ C : LogIdealAffineChart Y I,
        ((K.comap (C.affine.inv ≫ C.W.hom)).idealOfOpens ⊤).map
          (Scheme.ΓSpecIso (.of C.A)).hom.hom = C.ringIdeal) ∧
      ∃ (Y₀ : Scheme.{u}) (N₀ : EtaleLogStructure Y₀)
        (b₀ : EtaleLogMap N₀ Y.logStructure)
        (Yₛ : FineSaturatedLogScheme.{u}) (bₛ : EtaleLogHom Yₛ Y)
        (s : EtaleLogMap Yₛ.logStructure N₀),
        b₀.IsFinePrincipalization I ∧ IsSaturatedLogBlowup bₛ I ∧
        bₛ.toLogMap.IsFSPrincipalization I ∧ s.CompEq b₀ bₛ.toLogMap ∧
        (∀ s' : EtaleLogMap Yₛ.logStructure N₀, s'.CompEq b₀ bₛ.toLogMap → s' = s) ∧
        IsFinite s.base ∧
        (∀ C : LogIdealAffineChart Y I,
          (∀ e : {e : C.P // e ∈ C.generators},
            Monoid.FG (logIdealChartMonoid C.generators e.val) ∧
            Function.Injective (Algebra.GrothendieckGroup.of
              (M := logIdealChartMonoid C.generators e.val)) ∧
            IsFineSaturatedMonoid (logIdealSaturatedChartMonoid C.generators e.val) ∧
            (∀ g : Algebra.GrothendieckGroup C.P,
              g ∈ logIdealSaturatedChartMonoid C.generators e.val ↔
                ∃ n : ℕ, 0 < n ∧ g ^ n ∈ logIdealChartMonoid C.generators e.val) ∧
            (∃ ε : Algebra.GrothendieckGroup (logIdealChartMonoid C.generators e.val) ≃*
                Algebra.GrothendieckGroup C.P,
              ∀ q, ε (Algebra.GrothendieckGroup.of q) = q.val) ∧
            (∃ ε : Algebra.GrothendieckGroup
                (logIdealSaturatedChartMonoid C.generators e.val) ≃*
                Algebra.GrothendieckGroup C.P,
              ∀ q, ε (Algebra.GrothendieckGroup.of q) = q.val)) ∧
          ∃ (D₀ : LogIdealTensorCover C b₀
              (fun e ↦ logIdealChartMonoid C.generators e.val)
              (fun e ↦ logIdealChartInclusion C.generators e.val))
            (Dₛ : LogIdealTensorCover C bₛ.toLogMap
              (fun e ↦ logIdealSaturatedChartMonoid C.generators e.val)
              (fun e ↦ logIdealSaturatedChartInclusion C.generators e.val))
            (r : pullback bₛ.base C.W.hom ⟶ pullback b₀.base C.W.hom),
            r ≫ pullback.fst b₀.base C.W.hom =
              pullback.fst bₛ.base C.W.hom ≫ s.base ∧
            r ≫ pullback.snd b₀.base C.W.hom = pullback.snd bₛ.base C.W.hom ∧
            ∀ e : {e : C.P // e ∈ C.generators},
              ∃ (j : logIdealChartMonoid C.generators e.val →*
                  logIdealSaturatedChartMonoid C.generators e.val)
                (φ : logIdealTensorRing C.A C.alpha
                    (logIdealChartInclusion C.generators e.val) →+*
                  logIdealTensorRing C.A C.alpha
                    (logIdealSaturatedChartInclusion C.generators e.val)),
                (∀ q, (j q).val = q.val) ∧
                φ.comp (logIdealTensorBase C.A C.alpha
                    (logIdealChartInclusion C.generators e.val)) =
                  logIdealTensorBase C.A C.alpha
                    (logIdealSaturatedChartInclusion C.generators e.val) ∧
                (∀ q, φ (logIdealTensorMonomial C.A C.alpha
                    (logIdealChartInclusion C.generators e.val) q) =
                  logIdealTensorMonomial C.A C.alpha
                    (logIdealSaturatedChartInclusion C.generators e.val) (j q)) ∧
                IsPullback (Spec.map (CommRingCat.ofHom φ)) (Dₛ.toPullback e) (D₀.toPullback e) r) ∧
        ∀ (Z : FineSaturatedLogScheme.{u}) (f : EtaleLogHom Z Y),
          f.toLogMap.IsStrictEtale →
          ∃ (Z₀ : Scheme.{u}) (M₀ : EtaleLogStructure Z₀)
            (c₀ : EtaleLogMap M₀ Z.logStructure) (q₀ : EtaleLogMap M₀ N₀)
            (t₀ : EtaleLogMap M₀ Y.logStructure)
            (Zₛ : FineSaturatedLogScheme.{u}) (cₛ : EtaleLogHom Zₛ Z)
            (qₛ : EtaleLogMap Zₛ.logStructure Yₛ.logStructure)
            (tₛ : EtaleLogMap Zₛ.logStructure Y.logStructure)
            (sZ : EtaleLogMap Zₛ.logStructure M₀)
            (v : EtaleLogMap Zₛ.logStructure N₀),
            c₀.IsFinePrincipalization (f.pullbackIdeal I) ∧
            IsSaturatedLogBlowup cₛ (f.pullbackIdeal I) ∧
            cₛ.toLogMap.IsFSPrincipalization (f.pullbackIdeal I) ∧
            c₀.CompEq f.toLogMap t₀ ∧ q₀.CompEq b₀ t₀ ∧
            cₛ.toLogMap.CompEq f.toLogMap tₛ ∧ qₛ.CompEq bₛ.toLogMap tₛ ∧
            IsPullback q₀.base c₀.base b₀.base f.base ∧
            IsPullback qₛ.base cₛ.base bₛ.base f.base ∧
            q₀.IsStrictEtale ∧ qₛ.IsStrictEtale ∧
            sZ.CompEq c₀ cₛ.toLogMap ∧ sZ.CompEq q₀ v ∧ qₛ.CompEq s v := by
  sorry

end AlgebraicGeometry
