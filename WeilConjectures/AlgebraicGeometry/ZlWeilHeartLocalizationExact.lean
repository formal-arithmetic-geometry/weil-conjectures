/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicPunctualWeights
public import WeilConjectures.AlgebraicGeometry.CommonStageWeilShriek
public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ConstructibleTruncations
import WeilConjectures.CategoryTheory.Triangulated.TStructure.HeartAbelianKernelSplitting
import WeilConjectures.AlgebraicGeometry.IsomorphismFieldTransport
import WeilConjectures.AlgebraicGeometry.ZlImmersionWeilLocalBehavior
import WeilConjectures.AlgebraicGeometry.ZlFiniteAdicDirectImage
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
import WeilConjectures.AlgebraicGeometry.SfOpenClosedTriangleAllStages
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Canonical localization in the constructible Weil heart

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, final open--closed gluing paragraph
(blueprint: lem-zl-weil-heart-localization-exact).

The fixed-pair heart, inverse image, open extension and closed derived image are
existing constructions. The structures below state their exactness and the
normalization of the actual localization arrows, without choosing new operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Forget the Weil map, retaining the same object and arrows in the constructible heart.
Source: latest blueprint, final gluing paragraph
(blueprint: lem-zl-weil-heart-localization-exact). -/
def zlLocalizationForget (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageHeart l (D.geometricFiber X₀).left Ω where
  obj K := ⟨K.obj.carrier, K.property⟩
  map f := ObjectProperty.homMk f.hom.hom.f

/-- Creation of kernels, cokernels and inverse images, and the induced image comparison.
The abelian structure on Weil sheaves is the published `zlWeilHeartAbelian`.
Source: latest blueprint, final gluing paragraph, inverse images under the quotient
(blueprint: lem-zl-weil-heart-localization-exact). -/
structure ZlLocalizationHeart (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] where
  [underlying_abelian : Abelian (sfCommonStageHeart l (D.geometricFiber X₀).left Ω)]
  forget_additive : (zlLocalizationForget D l hl Ω X₀).Additive
  kernels : ∀ (H K : sfCommonStageWeilSheaf D l hl X₀ Ω) (f : H ⟶ K),
    CreatesLimit (parallelPair f 0) (zlLocalizationForget D l hl Ω X₀)
  cokernels : ∀ (H K : sfCommonStageWeilSheaf D l hl X₀ Ω) (f : H ⟶ K),
    CreatesColimit (parallelPair f 0) (zlLocalizationForget D l hl Ω X₀)
  images : ∀ (H K : sfCommonStageWeilSheaf D l hl X₀ Ω) (f : H ⟶ K),
    ∃ e : (zlLocalizationForget D l hl Ω X₀).obj (image f) ≅
        image ((zlLocalizationForget D l hl Ω X₀).map f),
      e.hom ≫ image.ι ((zlLocalizationForget D l hl Ω X₀).map f) =
        (zlLocalizationForget D l hl Ω X₀).map (image.ι f)
  inverse_images : ∀ (H K N : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (f : H ⟶ K) (m : N ⟶ K) [Mono m],
    CreatesLimit (cospan f m) (zlLocalizationForget D l hl Ω X₀)
  short_exact : ∀ (H K N : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (f : H ⟶ K) (g : K ⟶ N) (w : f ≫ g = 0),
    (ShortComplex.mk f g w).ShortExact ↔
      ∃ w' : (zlLocalizationForget D l hl Ω X₀).map f ≫
          (zlLocalizationForget D l hl Ω X₀).map g = 0,
        (ShortComplex.mk ((zlLocalizationForget D l hl Ω X₀).map f)
          ((zlLocalizationForget D l hl Ω X₀).map g) w').ShortExact

/-- The heart inclusion retains exactly the fixed pair and its equivariant morphisms.
Source: latest blueprint, final gluing paragraph
(blueprint: lem-zl-weil-heart-localization-exact). -/
def zlLocalizationInclusion (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    sfCommonStageWeilSheaf D l hl X₀ Ω ⥤ sfCommonStageWeilComplex D l hl X₀ Ω :=
  ((sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω).inverseImage
    (sfCommonStageWeilForget D l hl X₀ Ω)).ι

variable {U₀ Z₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Exact restrictions of the specified operations and their actual adjunction arrows.
The equalities through the full inclusion specify the functors on objects and arrows.
The counit and unit equations fix their normalization, including their Weil structures.
The derived closed image of Weil pairs is the right adjoint of the Weil inverse image,
with its adjunction (def-weil-derived-direct-image with its induced Weil structure);
it is unique up to the unique isomorphism compatible with the units.
Source: latest blueprint, displayed open--closed sequence in the final paragraph
(blueprint: lem-zl-weil-heart-localization-exact). -/
structure ZlWeilHeartLocalization (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left] where
  openExtension : sfCommonStageWeilSheaf D l hl U₀ Ω ⥤ sfCommonStageWeilSheaf D l hl X₀ Ω
  closed : sfCommonStageWeilSheaf D l hl Z₀ Ω ⥤ sfCommonStageWeilSheaf D l hl X₀ Ω
  open_fac : openExtension ⋙ zlLocalizationInclusion D l hl Ω X₀ =
    zlLocalizationInclusion D l hl Ω U₀ ⋙ IsoAlgebra.mapOfNatIso (zlOpenFrobenius D l hl Ω j₀)
  closedDerived : sfCommonStageWeilComplex D l hl Z₀ Ω ⥤ sfCommonStageWeilComplex D l hl X₀ Ω
  closedDerivedAdjunction :
    IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω i₀) ⊣ closedDerived
  closed_fac : closed ⋙ zlLocalizationInclusion D l hl Ω X₀ =
    zlLocalizationInclusion D l hl Ω Z₀ ⋙ closedDerived
  open_additive : openExtension.Additive
  open_limits : PreservesFiniteLimits openExtension
  open_colimits : PreservesFiniteColimits openExtension
  closed_additive : closed.Additive
  closed_limits : PreservesFiniteLimits closed
  closed_colimits : PreservesFiniteColimits closed
  open_adjunction : openExtension ⊣ zlWeilPull D l hl Ω j₀
  closed_adjunction : zlWeilPull D l hl Ω i₀ ⊣ closed
  counit_normalization : ∀ H : sfCommonStageWeilSheaf D l hl X₀ Ω,
    HEq (open_adjunction.counit.app H).hom.hom.f
      ((zlCommonStageOpenAdjunction D l hl Ω j₀).counit.app H.obj.carrier)
  unit_normalization : ∀ H : sfCommonStageWeilSheaf D l hl X₀ Ω,
    HEq (closed_adjunction.unit.app H).hom
      (closedDerivedAdjunction.unit.app H.obj)
  localization : ∀ H : sfCommonStageWeilSheaf D l hl X₀ Ω,
    ∃ w : open_adjunction.counit.app H ≫ closed_adjunction.unit.app H = 0,
      (ShortComplex.mk (open_adjunction.counit.app H)
        (closed_adjunction.unit.app H) w).ShortExact

/-- All scheme finiteness assertions, including arbitrary open and closed subschemes.
Source: latest blueprint, final gluing paragraph; node proof Steps 1--2
(blueprint: lem-zl-weil-heart-localization-exact).
Proof: a field spectrum is Noetherian. Finite type over it gives Noetherianity.
An open in a Noetherian scheme is quasi-compact, hence its open immersion is finite
type. Closed immersions are finite, hence finite type. Composition gives finite
type of both subschemes over the field. Immersions over a separated base are
separated. Base change preserves finite type and separatedness; finite type over
the closure field again gives Noetherianity. -/
theorem zlWeilLocalizationSchemes [IsSeparated X₀.hom] :
    IsNoetherian X₀.left ∧ IsNoetherian (D.geometricFiber X₀).left ∧
    IsSeparated (D.geometricFiber X₀).hom ∧
    LocallyOfFiniteType (D.geometricFiber X₀).hom ∧ QuasiCompact (D.geometricFiber X₀).hom ∧
    ∀ (W₀ : Over (Spec (.of D.k₀))) (f₀ : W₀ ⟶ X₀),
      (IsOpenImmersion f₀.left ∨ IsClosedImmersion f₀.left) →
      LocallyOfFiniteType W₀.hom ∧ QuasiCompact W₀.hom ∧ IsSeparated W₀.hom ∧
      IsNoetherian W₀.left ∧ IsNoetherian (pullback W₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
      IsSeparated (pullback.snd W₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
      LocallyOfFiniteType (pullback.snd W₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
      QuasiCompact (pullback.snd W₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) := by
  sorry

/-- Creation and detection in the abelian constructible Weil heart, exact restriction,
canonical localization, and the zero category on the empty scheme.
Source: latest blueprint, final gluing paragraph; node proof Steps 3--8
(blueprint: lem-zl-weil-heart-localization-exact).
Proof: the bounded standard heart is abelian. Frobenius and its inverse are t-exact,
so kernels and cokernels have unique induced invertible Frobenius maps. Images are
kernels of cokernels; inverse images of subobjects are kernels of the map to their
cokernel. The forgetful functor therefore creates these and detects short exactness.
For an immersion, the prescribed pullback is t-exact by
lem-zl-immersion-weil-local-behavior, and its heart restriction is exact. The same
node gives exact open extension. A closed immersion is finite, so
lem-zl-finite-adic-direct-image gives t-exactness of the actual direct image;
forgetting and detecting short exactness gives its exact Weil lift. These functors
are additive because they act on the same underlying additive morphisms.
The triangle of prop-sf-open-closed-triangle-all-stages has precisely the open
counit and closed unit, equivariant since the inclusions descend to the finite
field. Its vertices lie in the heart. The heart short-exact/triangle criterion
therefore gives the displayed short exact sequence with these same arrows.
On the empty pro-etale site the empty covering forces all sections to be zero.
The module category, complexes, rationalizations and common-stage heart are zero;
the unique Weil isomorphism on zero gives zero Weil sheaves. This includes empty
open or closed terms and uses no triangulation of the fixed-pair category. -/
theorem zlWeilHeartLocalizationExact (_iota : Ω ≃+* ℂ) [IsSeparated X₀.hom] :
    Nonempty (ZlLocalizationHeart D l hl Ω X₀) ∧
    (∀ (W₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
      (h₀ : W₀ ⟶ X₀) [IsImmersion h₀.left],
      PreservesFiniteLimits (zlWeilPull D l hl Ω h₀) ∧
        PreservesFiniteColimits (zlWeilPull D l hl Ω h₀)) ∧
    (∀ (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀.left]
      [IsClosedImmersion i₀.left],
      Set.range j₀.left.base = (Set.range i₀.left.base)ᶜ →
        Nonempty (ZlWeilHeartLocalization D l hl Ω j₀ i₀)) ∧
    (IsEmpty X₀.left → ∀ H : sfCommonStageWeilSheaf D l hl X₀ Ω, IsZero H) := by
  sorry

end WeilConjectures
