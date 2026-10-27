module

public import Sheaf.AlgebraicGeometry.SpaceRelativeDifferentialModule
public import Sheaf.AlgebraicGeometry.SpaceSquareZeroStalkData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # The infinitesimal lift sheaf is a quasi-coherent pseudo-torsor

Source: Stacks Project, More on Morphisms of Spaces, Tags 061A, 061C and 061D;
Properties of Spaces, Tags 05ZF and 03M1(6)
(blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor).

The kernel is presented with its actual inclusion and quotient scalar action. An additive
comparison identifies the associated sheaf of a Zariski module with the literal internal
Hom on the common étale site; its scalar equation identifies their module structures.
The chart equation for the action fixes its sign and its derivation interpretation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A scheme morphism as a morphism of its representable algebraic spaces.
Source: Stacks 025Y (blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalSchemeMap {A B : Over S} (a : A ⟶ B) : schemeSpace A ⟶ schemeSpace B :=
  ObjectProperty.homMk ⟨yoneda.map a⟩

/-- A small étale test scheme over T, still carrying its structure map to S.
Source: Stacks 061A (blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalTest (T : Over S) : T.left.Etale ⥤ Over S :=
  Scheme.Etale.forget T.left ⋙ Over.map T.hom

/-- Its map to T, as a map over S.
Source: Stacks 061A (blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalTestMap (T : Over S) (U : T.left.Etale) :
    (infinitesimalTest T).obj U ⟶ T := Over.homMk U.hom

/-- The actual set of lifts on a test scheme; the two equations are over Y and on U₀.
Source: Stacks 061A, 061D
(blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def InfinitesimalLifts {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T₀ T : Over S} (j : T₀ ⟶ T) (a₀ : yoneda.obj T₀ ⟶ X.obj.obj)
    (b : yoneda.obj T ⟶ Y.obj.obj) (U : T.left.Etale) :=
  {a : yoneda.obj ((infinitesimalTest T).obj U) ⟶ X.obj.obj //
    a ≫ f.hom.hom = yoneda.map (infinitesimalTestMap T U) ≫ b ∧
      yoneda.map (pullback.snd j (infinitesimalTestMap T U)) ≫ a =
        yoneda.map (pullback.fst j (infinitesimalTestMap T U)) ≫ a₀}

/-- Restrictions of lifts preserve their two equations.
Source: Stacks 061A (blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor).
Proof: precompose the equation over Y. For the reduction equation use the map between
scheme pullbacks induced by the restriction; its two projection identities turn the
new equation into the precomposition of the old one. -/
theorem infinitesimalLifts_restrict {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T₀ T : Over S} (j : T₀ ⟶ T) (a₀ : yoneda.obj T₀ ⟶ X.obj.obj)
    (b : yoneda.obj T ⟶ Y.obj.obj) {U V : T.left.Etale} (r : V ⟶ U)
    (a : InfinitesimalLifts f j a₀ b U) :
    (yoneda.map ((infinitesimalTest T).map r) ≫ a.val) ≫ f.hom.hom =
        yoneda.map (infinitesimalTestMap T V) ≫ b ∧
      yoneda.map (pullback.snd j (infinitesimalTestMap T V)) ≫
          (yoneda.map ((infinitesimalTest T).map r) ≫ a.val) =
        yoneda.map (pullback.fst j (infinitesimalTestMap T V)) ≫ a₀ := by
  sorry

/-- The presheaf of lifts, with restriction by composition, including empty fibres.
Source: Stacks 061A, 061D
(blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalLiftPresheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T₀ T : Over S} (j : T₀ ⟶ T) (a₀ : yoneda.obj T₀ ⟶ X.obj.obj)
    (b : yoneda.obj T ⟶ Y.obj.obj) : T.left.Etaleᵒᵖ ⥤ Type (u + 1) where
  obj U := InfinitesimalLifts f j a₀ b U.unop
  map r := TypeCat.ofHom fun a ↦
    ⟨yoneda.map ((infinitesimalTest T).map r.unop) ≫ a.val,
      infinitesimalLifts_restrict f j a₀ b r.unop a⟩
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    simp
  map_comp r s := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    simp [Category.assoc]

/-- The small étale scheme charts, viewed as charts of the representable space T.
Source: Stacks 03ED, 061A
(blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalCharts (T : Over S) : T.left.Etale ⥤ (schemeSpace T).EtaleSite :=
  ObjectProperty.lift _
    ((infinitesimalTest T).toCostructuredArrow yoneda (schemeSpace T).obj.obj
      (fun U ↦ yoneda.map (infinitesimalTestMap T U)) (by
        intro U V r
        rw [← yoneda.map_comp]
        congr 1
        apply Over.OverMorphism.ext
        exact MorphismProperty.Over.w r))
    (fun U ↦ (representable_etale_scheme_tests.2.2.2.2.2.2.2.1 _ _
      (infinitesimalTestMap T U)).2 U.prop)

/-- The identity chart of a scheme regarded as an algebraic space.
Source: Stacks 03ED (blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalIdentityChart (T : Over S) : (schemeSpace T).EtaleSite :=
  (infinitesimalCharts T).obj (Scheme.Etale.mk (𝟙 T.left))

/-- Agreement with the recorded scheme relative differential module on compatible
étale charts. The scheme map is not assumed étale or representable over the spaces.
Source: Stacks 05ZF, 03G7
(blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def HasInfinitesimalDifferentialCharts {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
    (b : yoneda.obj V ⟶ Y.obj.obj) (g : U ⟶ V),
    IsEtale a → IsEtale b → a ≫ f.hom.hom = yoneda.map g ≫ b →
    Nonempty
      (((schemeSpace U).schemeRestriction (infinitesimalIdentityChart U)).obj
        ((moduleTensorPullback (ObjectProperty.homMk ⟨a⟩ : schemeSpace U ⟶ X)).obj
          (relativeDifferentialModule f)) ≅ g.left.relativeDifferentials)

/-- The pullback E=a₀*Ω(X/Y), with the existing canonical tensor adjunction.
Source: Stacks 061C (blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalDifferentials {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T₀ : Over S) (a₀ : yoneda.obj T₀ ⟶ X.obj.obj) : (schemeSpace T₀).Modules :=
  (moduleTensorPullback (ObjectProperty.homMk ⟨a₀⟩ : schemeSpace T₀ ⟶ X)).obj
    (relativeDifferentialModule f)

/-- The internal Hom on the reduced small étale site. The larger universe records
all localized module homomorphisms; no equality of universes is imposed.
Source: Stacks 061C (blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalHom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T₀ : Over S) (a₀ : yoneda.obj T₀ ⟶ X.obj.obj) (I : (schemeSpace T₀).Modules) :=
  SheafOfModules.homObj (R := (schemeSpace T₀).commStructureSheaf)
    (infinitesimalDifferentials f T₀ a₀) I

/-- Direct image of internal Hom through the equivalence for a thickening, restricted
to ordinary small étale scheme tests. It is j*Hom(E,I), not a chosen group presheaf.
Source: Stacks 061C, 061D
(blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalTranslationPresheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T₀ T : Over S} {j : T₀ ⟶ T} (a₀ : yoneda.obj T₀ ⟶ X.obj.obj)
    (M : ThickeningSiteModel (infinitesimalSchemeMap j)) (I : SquareZeroIdeal M) :
    T.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (infinitesimalCharts T ⋙ M.equivalence.functor).op ⋙
    (infinitesimalHom f T₀ a₀ I.obj).val.presheaf

/-- The representing reduced scheme for U₀=T₀×_T U in the normalized site model.
Its pullback square is part of ThickeningSiteModel.cartesian.
Source: Stacks 05ZS, 061C
(blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
abbrev infinitesimalReducedTest {T₀ T : Over S} {j : T₀ ⟶ T}
    (M : ThickeningSiteModel (infinitesimalSchemeMap j)) (U : T.left.Etale) :=
  M.equivalence.functor.obj ((infinitesimalCharts T).obj U)

/-- From a chart of U₀ to its étale lift over U; the counit here is the inverse unit
at U because the site equivalence runs from thickened charts to reduced charts.
Source: Stacks 05ZS, 0619
(blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalThickenedTestMap {T₀ T : Over S} {j : T₀ ⟶ T}
    (M : ThickeningSiteModel (infinitesimalSchemeMap j)) (U : T.left.Etale)
    {V : (schemeSpace T₀).EtaleSite} (v : V ⟶ infinitesimalReducedTest M U) :
    (M.equivalence.inverse.obj V).obj.left ⟶ (infinitesimalTest T).obj U :=
  (M.equivalence.inverse.map v ≫
    M.equivalence.unitIso.inv.app ((infinitesimalCharts T).obj U)).hom.left

/-- The quotient ring action on the reduced chart associated to U.
Source: Stacks 061C (blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalReducedScalar {T₀ T : Over S} {j : T₀ ⟶ T}
    (M : ThickeningSiteModel (infinitesimalSchemeMap j)) (U : T.left.Etale) :
    Γ(U.left, ⊤) ⟶ Γ((infinitesimalReducedTest M U).obj.left.left, ⊤) :=
  Scheme.Γ.map
    ((M.reduction.app (infinitesimalReducedTest M U) ≫
      infinitesimalThickenedTestMap M U (𝟙 _)).left.op)

/-- The differential tensor 1⊗ds on a compatible reduced chart. This is the canonical
unit-normalized tensor section, so the action formula does not choose a derivation map.
Source: Stacks 0619 (blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def infinitesimalDifferentialTensor {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T₀ : Over S) (a₀ : yoneda.obj T₀ ⟶ X.obj.obj)
    (V : (schemeSpace T₀).EtaleSite) (W : X.SmallEtaleModel)
    (r : V.obj.left ⟶ (X.smallEtaleInclusion.obj W).obj.left)
    (hr : yoneda.map r ≫ (X.smallEtaleInclusion.obj W).obj.hom = V.obj.hom ≫ a₀)
    (s : X.smallStructureSheaf.obj.obj (op W)) :
    (infinitesimalDifferentials f T₀ a₀).val.obj (op V) :=
  moduleTensorSection (ObjectProperty.homMk ⟨a₀⟩ : schemeSpace T₀ ⟶ X)
    (relativeDifferentialModule f) (X.smallEtaleInclusion.obj W)
    (CostructuredArrow.mk (CostructuredArrow.homMk r hr)) 1
    (relativeDifferentialSection f W s)

/-- A module comparison with the literal j*Hom(E,I). Additive naturality and bijectivity
are the natural isomorphism; this equation retains the O_T action through the quotient.
On Zariski opens it identifies H with the restriction in the node, including its scalars.
Source: Stacks 061C, 061D, 03DX
(blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def IsInfinitesimalTranslationComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T₀ T : Over S} {j : T₀ ⟶ T} (a₀ : yoneda.obj T₀ ⟶ X.obj.obj)
    (M : ThickeningSiteModel (infinitesimalSchemeMap j)) (I : SquareZeroIdeal M)
    (H : T.left.Modules) [H.IsQuasicoherent]
    (e : (Scheme.Modules.etaleTensorSectionsSheaf H).obj ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      infinitesimalTranslationPresheaf f a₀ M I) : Prop :=
  ∀ (U : T.left.Etale) (r : Γ(U.left, ⊤))
    (h : (Scheme.Modules.etaleTensorSectionsSheaf H).obj.obj (op U)),
    e.hom.app (op U) (ULift.up (r • (@id (Γ((Scheme.Modules.tensorPullback U.hom).obj H, ⊤)) h))) =
      infinitesimalReducedScalar M U r •
        (@id ((infinitesimalHom f T₀ a₀ I.obj).val.obj
          (op (infinitesimalReducedTest M U))) (e.hom.app (op U) (ULift.up h)))

/-- The derivation normalization of the action. For every compatible affine target
chart and every pair of chart lifts, the new ring map is the old map plus the image of
1⊗ds under the homomorphism represented by the translating section. Testing the affine
basis suffices and includes all further restrictions and all chart lifts.
Source: Stacks 0618, 0619, 04D0
(blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor). -/
def IsInfinitesimalAddition {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T₀ T : Over S} {j : T₀ ⟶ T} (a₀ : yoneda.obj T₀ ⟶ X.obj.obj)
    (b : yoneda.obj T ⟶ Y.obj.obj)
    (M : ThickeningSiteModel (infinitesimalSchemeMap j)) (I : SquareZeroIdeal M)
    (H : T.left.Modules) [H.IsQuasicoherent]
    (e : (Scheme.Modules.etaleTensorSectionsSheaf H).obj ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      infinitesimalTranslationPresheaf f a₀ M I)
    (act : ∀ U : T.left.Etale,
      (Scheme.Modules.etaleTensorSectionsSheaf H).obj.obj (op U) →
        InfinitesimalLifts f j a₀ b U → InfinitesimalLifts f j a₀ b U) : Prop :=
  ∀ (U : T.left.Etale)
    (h : (Scheme.Modules.etaleTensorSectionsSheaf H).obj.obj (op U))
    (a : InfinitesimalLifts f j a₀ b U) (V : (schemeSpace T₀).EtaleSite)
    (v : V ⟶ infinitesimalReducedTest M U) (W : X.SmallEtaleModel)
    (r : V.obj.left ⟶ (X.smallEtaleInclusion.obj W).obj.left)
    (hr : yoneda.map r ≫ (X.smallEtaleInclusion.obj W).obj.hom = V.obj.hom ≫ a₀)
    (r₁ r₂ : (M.equivalence.inverse.obj V).obj.left ⟶
      (X.smallEtaleInclusion.obj W).obj.left),
    M.reduction.app V ≫ r₁ = r → M.reduction.app V ≫ r₂ = r →
    yoneda.map r₁ ≫ (X.smallEtaleInclusion.obj W).obj.hom =
      yoneda.map (infinitesimalThickenedTestMap M U v) ≫ a.val →
    yoneda.map r₂ ≫ (X.smallEtaleInclusion.obj W).obj.hom =
      yoneda.map (infinitesimalThickenedTestMap M U v) ≫ (act U h a).val →
    ∀ s : X.smallStructureSheaf.obj.obj (op W),
      (@id (Γ((M.equivalence.inverse.obj V).obj.left.left, ⊤))
        (Scheme.Γ.map r₂.left.op s)) =
      (@id (Γ((M.equivalence.inverse.obj V).obj.left.left, ⊤))
        (Scheme.Γ.map r₁.left.op s)) +
        (@id (Γ((M.equivalence.inverse.obj V).obj.left.left, ⊤)) (I.inclusion V
          ((e.hom.app (op U) (ULift.up h)).app (op (Over.mk v))
            (infinitesimalDifferentialTensor f T₀ a₀ V W r hr s))))

/-- The lift sheaf and its quasi-coherent pseudo-torsor, without any existence of lifts.
The existential module H is a presentation of the restriction of the specified internal
Hom: e is a natural additive isomorphism with the literal direct image and its scalar
condition makes this an isomorphism of modules. Restricting e to opens identifies H
with that restriction. The action is pinned by IsInfinitesimalAddition, not chosen up
to an automorphism of the translation group.

Source: Stacks Project, Tags 061A, 061C, 061D, 05ZF and 03M1(6)
(blueprint: lem-sfb-space-infinitesimal-lift-pseudotorsor).

Proof:
1. Relative differentials are finitely presented for a locally finitely presented
space map (lem-sfb-space-relative-differentials-finite-presentation). Tensor pullback
preserves their finite presentations by the module adjunction and preservation of
colimits by a left adjoint. The square-zero ideal has its quotient scalar action.
2. Locally present E by a finite matrix. Hom(E,I) is the kernel of the transpose map
between finite sums of I. Quasi-coherent kernels and sums on spaces, and the closed
immersion quasi-coherent direct-image theorem, show j*Hom(E,I) is quasi-coherent.
The scheme Zariski/étale quasi-coherent equivalence gives H and the linear comparison e.
3. Maps into X glue over étale covers by the fpqc sheaf theorem. The two equations
are local and persist under gluing, so the explicitly defined lift presheaf is a sheaf.
4. At a chosen lift, square-zero linearization identifies the difference of any two
lifts with a derivation. Naturality for f says that the difference vanishes on O_Y.
The universal differential property and tensor adjunction identify these derivations
with the specified internal Hom. Étale flatness identifies the base-changed ideal
with the pulled-back ideal, including its quotient scalar action.
5. Add this derivation to the ring map of a lift. Square-zero multiplication proves
it is again a ring map over Y, and linearization gives its unique geometric lift.
Zero and addition give the action laws; the difference bijection gives each orbit
bijection. Sum and difference commute with restriction, giving naturality and the
stated equation on chart functions. On an empty lift set the action is the empty map. -/
theorem space_infinitesimal_lift_pseudotorsor {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : MapIsLocallyOfFinitePresentation f)
    {T₀ T : Over S} (j : T₀ ⟶ T) (hj : IsFirstOrderThickening j.left)
    (a₀ : yoneda.obj T₀ ⟶ X.obj.obj) (b : yoneda.obj T ⟶ Y.obj.obj)
    (comm : a₀ ≫ f.hom.hom = yoneda.map j ≫ b) :
    HasInfinitesimalDifferentialCharts f ∧
      Presheaf.IsSheaf T.left.smallEtaleTopology (infinitesimalLiftPresheaf f j a₀ b) ∧
      ∃ (M : ThickeningSiteModel (infinitesimalSchemeMap j)) (I : SquareZeroIdeal M),
        I.obj.IsQuasicoherent ∧
        ∃ (H : T.left.Modules) (_hH : H.IsQuasicoherent)
          (e : (Scheme.Modules.etaleTensorSectionsSheaf H).obj ⋙
              AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
            infinitesimalTranslationPresheaf f a₀ M I),
          IsInfinitesimalTranslationComparison f a₀ M I H e ∧
          ∃ act : ∀ U : T.left.Etale,
              (Scheme.Modules.etaleTensorSectionsSheaf H).obj.obj (op U) →
                InfinitesimalLifts f j a₀ b U → InfinitesimalLifts f j a₀ b U,
            (∀ (U : T.left.Etale) (a : InfinitesimalLifts f j a₀ b U), act U 0 a = a) ∧
            (∀ (U : T.left.Etale)
              (h k : (Scheme.Modules.etaleTensorSectionsSheaf H).obj.obj (op U))
              (a : InfinitesimalLifts f j a₀ b U),
              act U (h + k) a = act U h (act U k a)) ∧
            (∀ (U V : T.left.Etale) (r : V ⟶ U)
              (h : (Scheme.Modules.etaleTensorSectionsSheaf H).obj.obj (op U))
              (a : InfinitesimalLifts f j a₀ b U),
              (infinitesimalLiftPresheaf f j a₀ b).map r.op (act U h a) =
                act V ((Scheme.Modules.etaleTensorSectionsSheaf H).obj.map r.op h)
                  ((infinitesimalLiftPresheaf f j a₀ b).map r.op a)) ∧
            (∀ (U : T.left.Etale) (a : InfinitesimalLifts f j a₀ b U),
              Function.Bijective (fun h ↦ act U h a)) ∧
            IsInfinitesimalAddition f a₀ b M I H e act := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
