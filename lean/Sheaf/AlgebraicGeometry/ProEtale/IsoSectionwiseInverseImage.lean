/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites

/-!
# Sectionwise inverse image along a scheme isomorphism

Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).

This is the sectionwise model of the recorded inverse image under its canonical
comma-coprojection identification. Coefficients may have any universe containing
the small site's objects; the site's object and morphism universes stay distinct.
The original site equivalence, comparison, and constant-module results are reexported.

## Main definitions and statements

- `isoSectionwiseInverseImage`: the canonical sectionwise model, with arbitrary Hom size.
- `isoSectionwiseInverseImage_equivalence`: equivalence and preservation of limits/colimits.
- `isoSectionwiseConstantMap`: coefficient transport uniquely normalized on constants.
- `isoSectionwiseModuleInverseImage`: the module action transported through the ring map.
- `isoSectionwiseModuleInverseImage_exact`: additivity and exactness of that functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t r d v w w'
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Postcomposition with an isomorphism preserves the topology.
Source: Stacks Tag 09A5 (blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: compose structure maps with g or its inverse. The underlying schemes,
arrows, and fpqc covering families do not change; the two operations are inverse.
Thus sheaves pull back by precomposition, in every coefficient universe. -/
@[instance] theorem proEtaleIsoPostcompose_isContinuous
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :
    (proEtaleIsoPostcompose g).IsContinuous (ProEt.topology X) (ProEt.topology Y) := by
  sorry

/-- The sectionwise model of inverse image under the canonical site-equivalence
identification: its value at U is the original sheaf at (U, g ∘ structure).
Source: Stacks Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
abbrev isoSectionwiseInverseImage {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (D : Type d) [Category.{v} D] :
    Sheaf (ProEt.topology Y) D ⥤ Sheaf (ProEt.topology X) D :=
  (proEtaleIsoPostcompose g).sheafPushforwardContinuous D
    (ProEt.topology X) (ProEt.topology Y)

/-- The sectionwise model is an equivalence in every coefficient universe, and
preserves every existing small limit and colimit.
Source: Stacks Tags 09A5, 00WX and 0038
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: precompose with postcomposition by the inverse scheme isomorphism. The
canonical identity-on-sections unit and counit are inverse, natural sheaf maps,
since both site functors preserve covers. Equivalences preserve limits and colimits;
the projection characterization gives the canonical inverse-limit comparison. -/
theorem isoSectionwiseInverseImage_equivalence {X Y : Scheme.{t}}
    (g : X ⟶ Y) [IsIso g] (D : Type d) [Category.{v} D] :
    (isoSectionwiseInverseImage g D).IsEquivalence ∧
      PreservesLimitsOfSize.{w', w} (isoSectionwiseInverseImage g D) ∧
      PreservesColimitsOfSize.{w', w} (isoSectionwiseInverseImage g D) := by
  sorry

/-- The constant coefficient comparison is uniquely fixed by constant sections.
Source: Stacks Tags 09A5, 00WX and 0H7J
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: the distinguished comma object is terminal in the inverse-image colimit.
Under its coprojection identification inverse image is sectionwise transport.
Constant presheaf sections are unchanged; sheafification extends the identity
uniquely. The inverse site transport gives its inverse. This is the recorded
constant coefficient comparison, expressed in its canonical sectionwise model. -/
theorem isoSectionwiseConstantMap_existsUnique {X Y : Scheme.{t}}
    (g : X ⟶ Y) [IsIso g] (A : CommRingCat.{max r (t + 1)}) :
    ∃! c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).obj A)) ⟶
        (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A),
      ∀ (U : X.ProEt) (a : A),
        c.hom.app (op U)
          ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
            (op ((proEtaleIsoPostcompose g).obj U)) a) =
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app (op U) a := by
  sorry

/-- Constant-section coefficient transport, with no choice of an unnormalized map.
Source: Stacks Tag 0H7J (blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
def isoSectionwiseConstantMap {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (A : CommRingCat.{max r (t + 1)}) :=
  (isoSectionwiseConstantMap_existsUnique g A).exists.choose

/-- The specified coefficient map is invertible.
Source: Stacks Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: inverse site transport gives the inverse constant-section map. Both
composites are identities on constant sections and hence on their sheafifications. -/
@[instance] theorem isoSectionwiseConstantMap_isIso {X Y : Scheme.{t}}
    (g : X ⟶ Y) [IsIso g] (A : CommRingCat.{max r (t + 1)}) :
    IsIso (isoSectionwiseConstantMap g A) := by
  sorry

/-- Inverse image with its action transported through the inverse coefficient map.
On sections a acts as c inverse(a); all underlying abelian groups are unchanged.
Source: Stacks Tags 00WX and 03D2
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
def isoSectionwiseModuleInverseImage {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX)
    [IsIso c] : SheafOfModules.{max r (t + 1)} RY ⥤
      SheafOfModules.{max r (t + 1)} RX :=
  SheafOfModules.pushforward (F := proEtaleIsoPostcompose g) (inv c)

/-- Scalar transport and site transport are additive and exact.
Source: Stacks Tags 00WX and 03DA
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: the site equivalence computes kernels and cokernels on their underlying
abelian sheaves. Transporting an action through a ring isomorphism leaves these
sheaves and maps unchanged; linearity of kernel inclusions and quotient maps
transports too. Finite limits, finite colimits and addition are therefore preserved. -/
theorem isoSectionwiseModuleInverseImage_exact {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX)
    [IsIso c] :
    (isoSectionwiseModuleInverseImage g c).Additive ∧
      PreservesFiniteLimits (isoSectionwiseModuleInverseImage g c) ∧
      PreservesFiniteColimits (isoSectionwiseModuleInverseImage g c) := by
  sorry

/-- Additivity supplied by the exact inverse-image theorem.
Source: Stacks Tag 03DA (blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
instance isoSectionwiseModuleInverseImage_additive {X Y : Scheme.{t}} (g : X ⟶ Y)
    [IsIso g] {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX) [IsIso c] :
    (isoSectionwiseModuleInverseImage g c).Additive :=
  (isoSectionwiseModuleInverseImage_exact g c).1

/-- Finite-limit preservation supplied by the exact inverse-image theorem.
Source: Stacks Tag 03DA (blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
instance isoSectionwiseModuleInverseImage_limits {X Y : Scheme.{t}} (g : X ⟶ Y)
    [IsIso g] {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX) [IsIso c] :
    PreservesFiniteLimits (isoSectionwiseModuleInverseImage g c) :=
  (isoSectionwiseModuleInverseImage_exact g c).2.1

/-- Finite-colimit preservation supplied by the exact inverse-image theorem.
Source: Stacks Tag 03DA (blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
instance isoSectionwiseModuleInverseImage_colimits {X Y : Scheme.{t}} (g : X ⟶ Y)
    [IsIso g] {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX) [IsIso c] :
    PreservesFiniteColimits (isoSectionwiseModuleInverseImage g c) :=
  (isoSectionwiseModuleInverseImage_exact g c).2.2

end AlgebraicGeometry.Scheme
