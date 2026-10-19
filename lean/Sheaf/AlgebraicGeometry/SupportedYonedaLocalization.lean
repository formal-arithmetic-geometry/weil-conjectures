/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Sheaf.AlgebraicGeometry.ClosedSupportHom
import Sheaf.AlgebraicGeometry.EtaleSupportedSections
import Sheaf.CategoryTheory.FirstResolutionExtensionClass
import WeilConjectures.CategoryTheory.Abelian.HorseshoePrescribedResolutions
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.AlgebraicGeometry.RelativeEtaleCohomology
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Yoneda splicing and the signed localization boundary

Source: Stacks Project, Derived Categories, Tags 06XP, 06XR, 06XU and 06XV;
agent-stated signed localization refinement of the open-closed sequence
(blueprint: lem-per-supported-yoneda-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The existing open-closed sequence specialized to integral constant coefficients.
Its quotient is canonically `i_* ℤ_Z`, by inverse image of the constant sheaf.
Source: Stacks Tag 095L; Tags 06XP and 06XU
(blueprint: lem-per-supported-yoneda-localization). -/
def supportedYonedaOpenClosed {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (hcomp : Set.range i.base = (Set.range W.ι.base)ᶜ) :
    ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
    (disjoint_range_of_range_eq_compl W.ι i hcomp)
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The Yoneda splice is the positive localization boundary of the ordinary
coefficient boundary. The generator `t` is the unique lift of one over the open
in the integral open-closed sequence; evaluation at `t` specifies the adjoint
map `a` belonging to the section `h`. The equivalence `e` is normalized on every
resolution cocycle, so it is the stipulated supported-Hom identification, rather
than an arbitrary isomorphism. Ordinary boundaries are computed in every split
resolution of the coefficient sequence, with the supplied first resolution fixed.
No torsion condition is imposed on any of the three sheaves.

Source: Stacks Tags 06XP, 06XR, 06XU, 06XV and 095L; signed refinement
(blueprint: lem-per-supported-yoneda-localization).

Proof:
1. Keep I fixed and choose an endpoint resolution K of S.X₃. Use the prescribed
horseshoe (lem-sp-horseshoe-prescribed-resolutions) to write the middle differential
as d(y,z)=(d_I y+t z,d_K z), so d_I t+t d_K=0. Its augmentation (l,εg)
satisfies l|S.X₁=ε₁ and d_I l=-t⁰εg. Enough injectives and the nonnegative models
come from lem-weil-pbc-module-sheaves-enough-injectives and
lem-weil-pbc-left-exact-injective-resolution-degree-zero.
2. Write the open-closed sequence as A→B→F. Extension by zero adjunction identifies
Hom(A,M) with M(W), compatibly with restriction from Hom(B,M)=M(T).
Injectivity extends εh to u:B→K⁰. Its differential factors uniquely as z:F→K¹
with zp=d_K u, and z is closed since p is epi.
3. The pushout E_h maps to the first resolution extension using ε and u.
Naturality (lem-sc-p1-ext-class-naturality) and the first-row sign
(lem-amb-first-resolution-extension-class) give e_h=-[z], using
lem-weil-pbc-ext-via-injective-resolution.
4. Similarly the coefficient extension is represented by t⁰ε. The maps t form
a chain map K→I[1], because the shifted differential is negative.
5. Yoneda composition is shifted composition (lem-sc-ext-yoneda-composition-derived),
so its representative is w=-t¹z. Shifting the map t adds no component negation.
6. Put x=t⁰u and b=res(x)=t⁰εh. The split lift (0,εh) has differential (b,0),
so the ordinary coefficient boundary is [b], and localization is [(0,-b)]
(lem-pur-divisor-torsor-boundary-signs), for arbitrary coefficient sheaves.
7. The identity d_I x=-t¹d_Ku=wp puts the splice in the kernel of restriction.
Hom(F,I) is that kernel by the open-closed sequence. Restriction is surjective
on injective terms. Its inclusion in the signed fibre is a quasi-isomorphism:
the quotient has differential (a,b)↦(da,a-db) and contraction (a,b)↦(b,0).
This is the supported-Hom comparison (lem-amb-closed-support-hom) and the
kernel model (def-pur-etale-derived-supported-sections), with the stated normalization.
8. Finally D(x,0)=(d_I x,b), hence (d_I x,0)-(0,-b)=D(x,0). Thus the splice and
the localized ordinary boundary agree positively in the given relative complex
(def-amb-relative-etale-cohomology). The calculation applies to every model I
and every split resolution comparison, not just the chosen horseshoe. -/
theorem supported_yoneda_localization {T Z : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (W : T.Opens)
    (hcomp : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (S : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact) (I : InjectiveResolution S.X₁) :
    ∃ e : Ext (supportedYonedaOpenClosed i W hcomp).X₃ S.X₁ 2 ≃+
        relativeCohomology T (Scheme.Etale.mk W.ι) I 2,
      (∀ (z : (supportedYonedaOpenClosed i W hcomp).X₃ ⟶ I.cocomplex.X 2)
        (hz : z ≫ I.cocomplex.d 2 3 = 0),
        TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I.cocomplex 1
          (((supportedYonedaOpenClosed i W hcomp).g ≫ z).hom.app
            (op (Scheme.Etale.mk (𝟙 T)))
            (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T)))) 0
          (e (I.extMk z 3 rfl hz))) ∧
      ∃ t : (supportedYonedaOpenClosed i W hcomp).X₁.obj.obj
          (op (Scheme.Etale.mk W.ι)),
        (supportedYonedaOpenClosed i W hcomp).f.hom.app (op (Scheme.Etale.mk W.ι)) t =
          torsorExtensionOne T (Scheme.Etale.mk W.ι) ∧
        ∀ h : S.X₃.obj.obj (op (Scheme.Etale.mk W.ι)),
        ∃ a : (supportedYonedaOpenClosed i W hcomp).X₁ ⟶ S.X₃,
          a.hom.app (op (Scheme.Etale.mk W.ι)) t = h ∧
          ∀ (J : InjectiveResolution S.X₂) (K : InjectiveResolution S.X₃)
            (α : I.cocomplex ⟶ J.cocomplex) (β : J.cocomplex ⟶ K.cocomplex)
            (hαβ : α ≫ β = 0)
            (_hα : I.ι ≫ α = (CochainComplex.single₀ _).map S.f ≫ J.ι)
            (_hβ : J.ι ≫ β = (CochainComplex.single₀ _).map S.g ≫ K.ι)
            (_hs : ∀ n : ℕ, Nonempty (((ShortComplex.mk α β hαβ).map
              (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
            (hOpen : (torsorOpenShortComplex T (Scheme.Etale.mk W.ι)
              (ShortComplex.mk α β hαβ)).ShortExact)
            (x : (relativeSections (Scheme.Etale.mk W.ι) K.cocomplex).homology 0),
            TorsorSectionRepresents (Scheme.Etale.mk W.ι) K.cocomplex 0
              ((K.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) h) x →
            e (((shortExact_openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
                ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
                  (AddCommGrpCat.of (ULift.{u + 1} ℤ))) hcomp).extClass.comp
                (Ext.mk₀ a) (add_zero 1)).comp hS.extClass (rfl : 1 + 1 = 2)) =
              torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I.cocomplex 1
                (hOpen.δ 0 1 rfl x) := by
  sorry

end AlgebraicGeometry.Etale
