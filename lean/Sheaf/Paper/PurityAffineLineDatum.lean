/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor

/-!
# The concrete finite-level affine-line datum

Source: blueprint sec-smooth-purity/sk-def-purity-conv/def-pur-affine-line-datum.md
(blueprint: def-pur-affine-line-datum).

The coordinate is an actual global unit on its basic open. The finite twist is the
published root sheaf with scalar extension. The Kummer class is the image of the
published Kummer connecting homomorphism, not an abstract class satisfying naturality.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The relative affine line, with its standard coordinate. Source: blueprint
sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def Line (Y : Scheme.{u}) : Scheme.{u} := AffineSpace (ULift.{u} (Fin 1)) Y

/-- The standard coordinate. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def coordinate (Y : Scheme.{u}) : Γ(Line Y, ⊤) :=
  AffineSpace.coord Y (ULift.up 0)

/-- The actual open complement of the zero section. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def Punctured (Y : Scheme.{u}) : Scheme.{u} :=
  ((Line Y).basicOpen (coordinate Y)).toScheme

/-- Its open immersion into the line. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def openImmersion (Y : Scheme.{u}) : Punctured Y ⟶ Line Y :=
  ((Line Y).basicOpen (coordinate Y)).ι

/-- The zero section. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def zeroSection (Y : Scheme.{u}) : Y ⟶ Line Y :=
  AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y

/-- The affine projection p. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def lineProjection (Y : Scheme.{u}) : Line Y ⟶ Y :=
  (AffineSpace (ULift.{u} (Fin 1)) Y) ↘ Y

/-- The punctured projection pi=pj. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def puncturedProjection (Y : Scheme.{u}) : Punctured Y ⟶ Y :=
  openImmersion Y ≫ lineProjection Y

/-- The coordinate is a genuine global unit on Gm. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum). -/
noncomputable def coordinateUnit (Y : Scheme.{u}) : Γ(Punctured Y, ⊤)ˣ :=
  (Line Y).basicOpenUnit (coordinate Y)

/-- The actual finite root cover of the coordinate, in the equivalent torsor description.
It is the published pullback of the spectrum of Gamma(Gm)[T]/(T^r-t).
Source: blueprint sk-def-purity-conv, torsor paragraph
(blueprint: def-pur-affine-line-datum). -/
noncomputable abbrev coordinateRootCover (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    Scheme.{u} :=
  (Punctured Y).kummerCover P.exponent (coordinateUnit Y : Γ(Punctured Y, ⊤))

/-- The structure morphism of the actual root cover.
Source: blueprint sk-def-purity-conv, torsor paragraph
(blueprint: def-pur-affine-line-datum). -/
noncomputable abbrev coordinateRootCoverProjection (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) : P.coordinateRootCover Y ⟶ Punctured Y :=
  (Punctured Y).kummerCoverπ P.exponent (coordinateUnit Y : Γ(Punctured Y, ⊤))

/-- The coefficient map from roots to the root line is characterized on every section
by z mapping to 1 tensor z. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum).
Proof: the pure-tensor map is additive and natural in etale restriction. Compose it with
the sheafification unit. Sectionwise equality determines a unique sheaf morphism. -/
theorem existsUnique_rootCoefficientMap (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    ∃! f : T.rootsOfUnitySheaf P.exponent ⟶
        (P.forgetEtale T).obj (P.twistEtale h T),
      ∀ (W : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf P.exponent).obj.obj W),
        f.hom.app W z = Scheme.finiteEtaleTateOneGenerator P.Coefficient P.exponent T
          (P.exponent_coefficient_eq_zero h) W 1 z := by
  sorry

/-- The canonical coefficient extension map, determined uniquely by its pure tensors.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def rootCoefficientMap (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    T.rootsOfUnitySheaf P.exponent ⟶ (P.forgetEtale T).obj (P.twistEtale h T) :=
  Classical.choose (P.existsUnique_rootCoefficientMap h T)

/-- The actual finite Kummer class of any unit, with A-coefficients. The inverse is of
a specified bijection, so the defining boundary determines the class uniquely.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def kummerEtale (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (hr : IsUnit (P.exponent : Γ(T, ⊤))) (t : Γ(T, ⊤)ˣ) :
    Abelian.Ext (P.constantEtale T) (P.twistEtale h T) 1 :=
  Equiv.ofBijective _ (P.moduleClassToAbelian_bijective T (P.twistEtale h T)) |>.symm
    (Sheaf.H.map (P.rootCoefficientMap h T) 1 (T.kummerδ₀ P.exponent hr (Additive.ofMul t)))

/-- The actual class transported to the small pro-etale site.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def kummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (hr : IsUnit (P.exponent : Γ(T, ⊤))) (t : Γ(T, ⊤)ˣ) :
    Abelian.Ext (P.constant T) (P.twist h T) 1 :=
  (P.kummerEtale h T hr t).mapExactFunctor
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T)

/-- The inverse image of roots has its canonical map to roots, characterized by the
kernel inclusion into Gm. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-affine-line-datum).
Proof: exact inverse image preserves the kernel of multiplication by r. Pullback of
units commutes with the power map. The universal property of the target kernel gives
existence, and its monic inclusion gives uniqueness. -/
theorem existsUnique_rootPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! b : (Etale.upperStar AddCommGrpCat.{u + 1} f).obj
        (Y.rootsOfUnitySheaf P.exponent) ⟶ X.rootsOfUnitySheaf P.exponent,
      b ≫ kernel.ι (P.exponent • 𝟙 X.gmSheaf) =
        (Etale.upperStar AddCommGrpCat.{u + 1} f).map
          (kernel.ι (P.exponent • 𝟙 Y.gmSheaf)) ≫ Scheme.upperStarGmSheafToGmSheaf f := by
  sorry

/-- The canonical map on roots, uniquely fixed by the kernel inclusion.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def rootPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).obj
        (Y.rootsOfUnitySheaf P.exponent) ⟶ X.rootsOfUnitySheaf P.exponent :=
  Classical.choose (P.existsUnique_rootPullback f)

/-- The canonical scalar extension of root pullback, uniquely characterized on roots.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum).
Proof: inverse image commutes with the sheafified tensor product. Extend the canonical
map on roots A-linearly. The root image generates its scalar extension locally, giving
uniqueness. The coefficient-forgetting comparison is its canonical adjunction mate. -/
theorem existsUnique_twistEtalePullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! b : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
        (P.twistEtale h Y) ⟶ P.twistEtale h X,
      (Etale.upperStar AddCommGrpCat.{u + 1} f).map (P.rootCoefficientMap h Y) ≫
          Etale.upperStarForget₂Comparison P.Coefficient f (P.twistEtale h Y) ≫
          (P.forgetEtale X).map b = P.rootPullback f ≫ P.rootCoefficientMap h X := by
  sorry

/-- The actual canonical pullback map of the finite root line.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def twistEtalePullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
        (P.twistEtale h Y) ⟶ P.twistEtale h X :=
  Classical.choose (P.existsUnique_twistEtalePullback h f)

/-- The root line commutes with arbitrary inverse image when r is invertible.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum).
Proof: etale locally choose a primitive r-th root. The root sheaf and its scalar
extension become constant Z/r and A; the specified map is the identity on their
standard generators. Hence it is an isomorphism locally, and therefore globally. -/
theorem isIso_twistEtalePullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hr : IsUnit (P.exponent : Γ(Y, ⊤))) : IsIso (P.twistEtalePullback h f) := by
  sorry

/-- The canonical punctured-line base-change arrow is uniquely determined by its open
immersion. Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum).
Proof: the standard affine-space base-change arrow pulls the coordinate to the
coordinate. Its restriction to the coordinate basic open therefore factors through
the target basic open. The open immersion is monic, giving uniqueness. -/
theorem existsUnique_puncturedMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! b : Punctured X ⟶ Punctured Y,
      b ≫ openImmersion Y = openImmersion X ≫ AffineSpace.map (ULift.{u} (Fin 1)) f := by
  sorry

/-- The actual punctured-line base-change arrow.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def puncturedMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Punctured X ⟶ Punctured Y :=
  Classical.choose (existsUnique_puncturedMap f)

/-- Its canonical square with the projections.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum).
Proof: compose the defining equality of puncturedMap with the affine projection and
use affine-space map_over. -/
theorem puncturedSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CommSq (puncturedMap f) (puncturedProjection X) (puncturedProjection Y) f := by
  sorry

/-- The class of the actual coordinate, transported through the exact site comparison.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-affine-line-datum). -/
noncomputable def coordinateKummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    Abelian.Ext (P.constant (Punctured Y)) (P.twist h (Punctured Y)) 1 :=
  P.kummer h (Punctured Y)
    (P.exponent_isUnit (Punctured Y) (puncturedProjection Y ≫ a)) (coordinateUnit Y)

end WeilConjectures.PurityFiniteSetting
