module

public import Sheaf.Paper.FramedIntegralExtension
public import Sheaf.Paper.FramedProRealization
public import Sheaf.Paper.FramedTransport
public import Sheaf.Paper.FramedRealizationProperty
public import Sheaf.Paper.FramedRealizationEnlarge
public import Sheaf.Paper.FramedRealizationPullback
public import Sheaf.Paper.FramedRealizationAdditive
public import Sheaf.Paper.FramedRealizationIso
import Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality
import Sheaf.AlgebraicGeometry.PurityRelativeCone
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.Paper.PurityFrameClass
import Sheaf.AlgebraicGeometry.ClosedSupportHom
import Sheaf.AlgebraicGeometry.RelativeTorsorCohomology

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: lem-pur-divisor-normalized-realization).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
/-- Isomorphisms of framed pairs preserve both the integral extension and its two realizations.
Source: Stacks 03AJ and framed-line refinement, invariance clause
(blueprint: lem-pur-divisor-normalized-realization).
Proof: compose the equivariant extension map with the section-preserving torsor
isomorphism. The uniqueness characterization gives equality of beta. Apply the
scalar and pro-etale constructions to this equality. -/
theorem divisorRealization_iso (P : PurityFiniteSetting.{u}) : P.DivisorRealizationIso := by
  unfold DivisorRealizationIso
  intro Z T a _ _ _ i _ L M _ _ s t e he
  have h := divisorRelativeExtension_iso i L M s t e he
  exact ⟨h, congrArg (P.divisorScalarRealization a i) h,
    congrArg (P.divisorProRealization a i) h⟩

/-- Both realizations are additive in the integral extension class.
Source: Stacks 03PL and framed-line refinement, additivity clause
(blueprint: lem-pur-divisor-normalized-realization).
Proof: Yoneda composition and roots coefficient extension are additive. The inverse
of the DerivedUnit bijection is additive, since the bijection is induced by additive
functors and composition. Exact inverse image and the supported-Hom identification
are additive as well. Hence both normalized constructions preserve zero and sums. -/
theorem divisorRealization_additive (P : PurityFiniteSetting.{u}) :
    P.DivisorRealizationAdditive := by
  sorry

/-- Etale pullback preserves the framed realization, on both sites.
Source: Stacks 03AJ, 03PL, 0A45 and 099W
(blueprint: lem-pur-divisor-normalized-realization).
Proof: uniqueness of the relative torsor extension identifies the pulled integral class.
Exact inverse image preserves the actual Kummer extension and its Yoneda splice.
The root scalar map sends the same root to its tensor with one after pullback.
The integral derived-unit bijection identifies the resulting module lift. Supported-Hom
naturality and the comparison-pullback square identify the pro-etale class. The equality
hW merely records the complementary-open equality of the Cartesian square. -/
theorem divisorRealization_pullback (P : PurityFiniteSetting.{u}) :
    P.DivisorRealizationPullback := by
  sorry

/-- Enlarging support restricts the frame and precomposes the realized class.
Source: Stacks 03AJ and 0A45 (blueprint: lem-pur-divisor-normalized-realization).
Proof: restrict the equivariant extension map to the smaller complementary open.
The relative-extension uniqueness gives the pullback of beta along restriction of
supported integers. Yoneda composition commutes with this precomposition. The scalar
unit and supported-Hom normalization commute with the same restriction. The signed
relative cone comparison and exact site comparison then give the pro-etale equation. -/
theorem divisorRealization_enlarge (P : PurityFiniteSetting.{u}) : P.DivisorRealizationEnlarge := by
  sorry

/-- The normalized supported Kummer realization, with positive ordinary image.
Source: Stacks 03AJ, 03PL and 0A45; blueprint lem-pur-divisor-class, first sentence
and final paragraph (blueprint: lem-pur-divisor-normalized-realization).
Proof plan, in the six DAG steps:
1. Apply relative_extension_existsUnique to the open-closed integer sequence and
   frame torsor. The equivariant lift kills s, fixing beta with the Ext-normalized
   sign of lem-pur-relative-extension-cohomology-normalization.
2. Invertibility of ell on T makes the actual Kummer sequence short exact.
   Its connecting map is Yoneda composition by its extension class. Apply the
   root scalar unit z to z tensor one, without a module structure on Gm.
3. Apply lem-sp-etale-supported-integral-derived-unit at B[2] to obtain the unique
   module Ext lift, with exactly the displayed abelian-realization equation.
4. Apply lem-pur-supported-root-scalar-site-comparison: the root-tensor coefficient
   is sigma rho of def-pur-frame-class and the supported-Hom class lies in the
   existing right-derived support group. B[0] is the bounded-below etale witness.
5. Relative-extension uniqueness, exact pullback of Yoneda composites, supported-Hom
   naturality and lem-pur-divisor-relative-cone give invariance, pullback, support
   enlargement and additivity as separately stated in the companion declarations.
6. Precomposing beta with the integer restriction gives the positive ordinary
   torsor class. Kummer composition, the identical root map, and site comparison
   commute with this precomposition, giving both forget-support equations below.
No Cartier condition or extension of the frame to T enters this construction. -/
theorem divisor_normalized_realization (P : PurityFiniteSetting.{u}) :
    P.DivisorNormalizedRealization := by
  sorry


end WeilConjectures.PurityFiniteSetting
