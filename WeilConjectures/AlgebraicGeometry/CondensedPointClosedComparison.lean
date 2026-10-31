/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.PodCtfAdjunctions
public import WeilConjectures.AlgebraicGeometry.CondensedVerdierBiduality
public import WeilConjectures.AlgebraicGeometry.GlobalVerdierDualityData
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
import WeilConjectures.AlgebraicGeometry.GlobalVerdierDuality

/-! # Evaluation-normalized closed comparison at the condensed geometric point

Source: current blueprint, sec-six-functors/sk-thm-sf-package/
thm-pod-identification-of-the-comparison.proof.md, third paragraph
(blueprint: lem-pod-condensed-point-closed-comparison).

All derived categories, tensor products and internal Homs are the actual unbounded
derived constructions, restricted to the recorded constructible finite-Tor objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedPointClosedComparison

section Closed
variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
  (F : C ⥤ D) [F.Monoidal]

/-- The closed comparison is the transpose of mapped evaluation after the
inverse of tau. Thus it is a fixed map, rather than a supplied isomorphism.
It is the component of the recorded `Functor.LaxMonoidal.ihomComparison`, the mate
of the tensorator, i.e. `curry (μ F U [U, V] ≫ F.map ev)`; that is the comparison
used by lem-sf-condensed-geometric-point-perfect, so no second notion is introduced.
Source: blueprint comparison proof, third paragraph
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def comparison (U V : C) : F.obj ((ihom U).obj V) ⟶ (ihom (F.obj U)).obj (F.obj V) :=
  (Functor.LaxMonoidal.ihomComparison F U).natTrans.app V

/-- The coefficient-dual map includes the specified unit comparison u0.
Source: blueprint comparison proof, third paragraph
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def coefficientDual (U : C) :
    F.obj ((ihom U).obj (𝟙_ C)) ⟶ (ihom (F.obj U)).obj (𝟙_ D) :=
  curry (Functor.LaxMonoidal.μ F U ((ihom U).obj (𝟙_ C)) ≫
    F.map ((ihom.ev U).app (𝟙_ C)) ≫ (Functor.Monoidal.εIso F).inv)

/-- An identity exceptional adjoint is represented by its actual adjunction.
The counit comparison is the unique right-adjoint comparison with the identity.
Source: blueprint comparison proof, identity-point normalization
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def identityCounit (S : C ⥤ C) (adj : 𝟭 C ⊣ S) : S.obj (𝟙_ C) ≅ 𝟙_ C :=
  (adj.rightAdjointUniq Adjunction.id).app (𝟙_ C)

/-- The point Verdier comparison uses evaluation into omega and the identity
exceptional counit, in precisely that order.
Source: blueprint comparison proof, third paragraph and inverse identification
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def pointVerdier (S : C ⥤ C) (adj : 𝟭 C ⊣ S) (U : C) :
    F.obj ((ihom U).obj (S.obj (𝟙_ C))) ⟶ (ihom (F.obj U)).obj (𝟙_ D) :=
  curry (Functor.LaxMonoidal.μ F U ((ihom U).obj (S.obj (𝟙_ C))) ≫
    F.map ((ihom.ev U).app (S.obj (𝟙_ C)) ≫ (identityCounit S adj).hom) ≫
    (Functor.Monoidal.εIso F).inv)

/-- Invertibility, both-variable naturality, the evaluation and currying equations,
and the coefficient/point-dual compatibility. The identity right adjoint is allowed
any adjunction-compatible presentation; it is not replaced by an arbitrary dualizing
object or an arbitrary map to the unit.
Source: blueprint comparison proof, third paragraph
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def ClosedLaws : Prop :=
  (∀ U V : C, IsIso (comparison F U V)) ∧
  (∀ (U U' V V' : C) (a : U' ⟶ U) (b : V ⟶ V'),
    F.map ((pre a).app V ≫ (ihom U').map b) ≫ comparison F U' V' =
      comparison F U V ≫ (pre (F.map a)).app (F.obj V) ≫ (ihom (F.obj U')).map (F.map b)) ∧
  (∀ U V : C,
    F.obj U ◁ comparison F U V ≫ (ihom.ev (F.obj U)).app (F.obj V) =
      Functor.LaxMonoidal.μ F U ((ihom U).obj V) ≫ F.map ((ihom.ev U).app V)) ∧
  (∀ (U T V : C) (v : U ⊗ T ⟶ V),
    curry (Functor.LaxMonoidal.μ F U T ≫ F.map v) =
      F.map (curry v) ≫ comparison F U V) ∧
  (∀ U : C, IsIso (coefficientDual F U)) ∧
  (∀ (S : C ⥤ C) (adj : 𝟭 C ⊣ S),
    (identityCounit S adj).hom = adj.counit.app (𝟙_ C) ∧
    ∀ U : C, IsIso (pointVerdier F S adj U) ∧
      pointVerdier F S adj U =
        F.map ((ihom U).map (identityCounit S adj).hom) ≫ coefficientDual F U)

end Closed

open AlgebraicGeometry.ProEtale.CondensedGeometricPoint
open AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

/-- Restrict the fixed extension J(P) = Lambda_s tensor over B with P to perfect
complexes. Only membership is supplied; objects and arrows are the existing construction.
Source: blueprint comparison proof, first point-equivalence assertion
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def perfectRealization (h : ∀ P : (perfect Λ).FullSubcategory,
    ctf Λ k ((condensedScalarRealization Λ (Spec (.of k))).obj P.obj)) :=
  (ctf Λ k).lift ((perfect Λ).ι ⋙ condensedScalarRealization Λ (Spec (.of k))) h

/-- The actual counit/projection/evaluation pairing at a structure morphism.
It uses ordinary pullback/direct-image adjunction and the exceptional counit.
Source: blueprint comparison proof, second and third paragraphs
(blueprint: lem-pod-condensed-point-closed-comparison). -/
@[irreducible]
def globalPairing
    [ObjectProperty.IsMonoidal (ctf Λ k)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (h : ∀ K : moduleDerived Λ X.left, dctfPred Λ X.left K →
      ctf Λ k ((condensedVerdierAmbientSupport Λ X).obj K))
    (G : (ctf Λ k).FullSubcategory ⥤ ConstantModelConstructibleFiniteTor Λ X.left)
    (adj : condensedVerdierSupport Λ X h ⊣ G)
    (M : ConstantModelConstructibleFiniteTor Λ X.left) :
    ((condensedVerdierSupport Λ X h).obj M).obj ⊗
        ((AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
          Λ (Over.mkIdTerminal.from X).left).rightDerivedFunctor.obj
          ((ihom M.obj).obj (G.obj (𝟙_ (ctf Λ k).FullSubcategory)).obj)) ⟶
      (𝟙_ (ctf Λ k).FullSubcategory).obj :=
  letI : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))
  letI : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))
  exceptionalProjectionMorphismOfCompactification Λ
      (compactificationOverField (Over.mkIdTerminal.from X)) M.obj _ ≫
    (condensedVerdierAmbientSupport Λ X).map
      (M.obj ◁ (AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction
        Λ (Over.mkIdTerminal.from X).left).counit.app
          ((ihom M.obj).obj (G.obj (𝟙_ (ctf Λ k).FullSubcategory)).obj)) ≫
    (condensedVerdierAmbientSupport Λ X).map
      ((ihom.ev M.obj).app (G.obj (𝟙_ (ctf Λ k).FullSubcategory)).obj) ≫
    (adj.counit.app (𝟙_ (ctf Λ k).FullSubcategory)).hom

/-- Detailed compatibility with the existing global-duality map, characterized by
its inverse being the transpose of the actual cup/evaluation/counit pairing.
Alpha is the canonical Verdier transpose, not an arbitrary isomorphism of its endpoints.
The right-adjoint comparison for the identity gives rho and hence e = rho followed
by alpha inverse, as required by the five adjunction bijections.
Source: blueprint comparison proof, final inverse identification
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def GlobalLaws (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    [ObjectProperty.IsMonoidal (ctf Λ D₀.k)] [ObjectProperty.IsMonoidal (perfect Λ)]
    [ObjectProperty.IsMonoidalClosed (ctf Λ D₀.k)]
    [ObjectProperty.IsMonoidalClosed (perfect Λ)]
    (hF : ∀ K : (ctf Λ D₀.k).FullSubcategory, perfect Λ ((fiber Λ D₀.k).obj K.obj))
    [(restricted Λ D₀.k hF).Monoidal]
    : Prop :=
  ∀ (X : Over (Spec (.of D₀.k))) [Smooth X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [GeometricallyConnected X.hom]
    (d : ℕ) (_hd : X.left.IsPureDimension d)
    (_hX : WeilConjectures.GlobalVerdierDuality.GeometricAlternative D₀ X),
    ∃ (h : ∀ K : moduleDerived Λ X.left, dctfPred Λ X.left K →
        ctf Λ D₀.k ((condensedVerdierAmbientSupport Λ X).obj K))
      (G : (ctf Λ D₀.k).FullSubcategory ⥤ ConstantModelConstructibleFiniteTor Λ X.left)
      (adj : condensedVerdierSupport Λ X h ⊣ G),
    ∀ M : ConstantModelConstructibleFiniteTor Λ X.left,
    ∃ hD : ctf Λ D₀.k
      ((AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
          Λ (Over.mkIdTerminal.from X).left).rightDerivedFunctor.obj
        ((ihom M.obj).obj (G.obj (𝟙_ (ctf Λ D₀.k).FullSubcategory)).obj)),
    ∃ α : (⟨(AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
          Λ (Over.mkIdTerminal.from X).left).rightDerivedFunctor.obj
        ((ihom M.obj).obj (G.obj (𝟙_ (ctf Λ D₀.k).FullSubcategory)).obj), hD⟩ :
          (ctf Λ D₀.k).FullSubcategory) ≅
        (ihom ((condensedVerdierSupport Λ X h).obj M)).obj (𝟙_ _),
      α.hom = curry (ObjectProperty.homMk (globalPairing Λ D₀.k X h G adj M)) ∧
    ∃ g : (ihom ((restricted Λ D₀.k hF).obj ((condensedVerdierSupport Λ X h).obj M))).obj
          (𝟙_ (perfect Λ).FullSubcategory) ≅
        (restricted Λ D₀.k hF).obj ⟨_, hD⟩,
      g.inv = curry
        (Functor.LaxMonoidal.μ (restricted Λ D₀.k hF)
            ((condensedVerdierSupport Λ X h).obj M) ⟨_, hD⟩ ≫
          (restricted Λ D₀.k hF).map (ObjectProperty.homMk (globalPairing Λ D₀.k X h G adj M)) ≫
          (Functor.Monoidal.εIso (restricted Λ D₀.k hF)).inv) ∧
      ∀ (S : (ctf Λ D₀.k).FullSubcategory ⥤ (ctf Λ D₀.k).FullSubcategory)
        (a : 𝟭 (ctf Λ D₀.k).FullSubcategory ⊣ S),
      ∃ j : (restricted Λ D₀.k hF).obj
          ((ihom ((condensedVerdierSupport Λ X h).obj M)).obj (S.obj (𝟙_ _))) ≅
          (ihom ((restricted Λ D₀.k hF).obj ((condensedVerdierSupport Λ X h).obj M))).obj
            (𝟙_ (perfect Λ).FullSubcategory),
      j.hom = pointVerdier (restricted Λ D₀.k hF) S a
        ((condensedVerdierSupport Λ X h).obj M) ∧
      g.hom = j.inv ≫
        (restricted Λ D₀.k hF).map
          (((ihom ((condensedVerdierSupport Λ X h).obj M)).map
            (identityCounit S a).hom) ≫ α.inv)

/-- A monoidal witness and all of its normalizations are shared across the closed,
dual and global clauses. The inverse functor is the prescribed scalar extension.
Source: blueprint comparison proof, third paragraph
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def MonoidalStatement (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    [ObjectProperty.IsMonoidal (ctf Λ D₀.k)] [ObjectProperty.IsMonoidal (perfect Λ)]
    [ObjectProperty.IsMonoidalClosed (ctf Λ D₀.k)]
    [ObjectProperty.IsMonoidalClosed (perfect Λ)]
    (hF : ∀ K : (ctf Λ D₀.k).FullSubcategory, perfect Λ ((fiber Λ D₀.k).obj K.obj))
    (m : (restricted Λ D₀.k hF).Monoidal) : Prop :=
  letI := m
  ClosedLaws (restricted Λ D₀.k hF) ∧ GlobalLaws Λ D₀ hF

/-- The inherited braidings are specified on the exact ambient localization
used by each full subcategory. This spells out the standard Koszul descent
without identifying the scalar category's localization and Grothendieck universes.
Source: blueprint comparison proof, canonical monoidal point equivalence
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def BraidedStatement (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    [hc : ObjectProperty.IsMonoidal (ctf Λ D₀.k)]
    [hp : ObjectProperty.IsMonoidal (perfect Λ)]
    [ObjectProperty.IsMonoidalClosed (ctf Λ D₀.k)]
    [ObjectProperty.IsMonoidalClosed (perfect Λ)]
    (hF : ∀ K : (ctf Λ D₀.k).FullSubcategory, perfect Λ ((fiber Λ D₀.k).obj K.obj)) : Prop :=
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (condensedScalarRing Λ)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _
  letI : BraidedCategory (ctf Λ D₀.k).FullSubcategory :=
    @ObjectProperty.fullBraidedSubcategory _ _ _ (ctf Λ D₀.k) hc
      (_root_.DerivedCategory.braidedCategory' _)
  letI : BraidedCategory (perfect Λ).FullSubcategory :=
    @ObjectProperty.fullBraidedSubcategory _ _ _ (perfect Λ) hp
      (_root_.DerivedCategory.braidedCategory'.{u + 1}
        (ModuleCat.{u + 1} (condensedScalarRing Λ)))
  ∃ m : (restricted Λ D₀.k hF).Braided,
    MonoidalStatement Λ D₀ hF m.toMonoidal

/-- Full direct point comparison, including the canonical inverse functor, tensor
and unit coherence, closed transposes and the global diagram.
Source: blueprint comparison proof, third paragraph
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def Statement (D₀ : WeilConjectures.FiniteFieldDatum.{u}) : Prop :=
  ∃ (hc : ObjectProperty.IsMonoidal (ctf Λ D₀.k))
    (hp : ObjectProperty.IsMonoidal (perfect Λ))
    (hch : ObjectProperty.IsMonoidalClosed (ctf Λ D₀.k))
    (hph : ObjectProperty.IsMonoidalClosed (perfect Λ))
    (hF : ∀ K : (ctf Λ D₀.k).FullSubcategory, perfect Λ ((fiber Λ D₀.k).obj K.obj))
    (hJ : ∀ P : (perfect Λ).FullSubcategory,
      ctf Λ D₀.k ((condensedScalarRealization Λ (Spec (.of D₀.k))).obj P.obj))
    (adj : perfectRealization Λ D₀.k hJ ⊣ restricted Λ D₀.k hF),
    IsIso adj.unit ∧ IsIso adj.counit ∧
    @BraidedStatement Λ _ _ D₀ hc hp hch hph hF

/-- The evaluation-normalized closed comparison for all four direct condensed rings.
Source: current blueprint comparison proof, third paragraph and final inverse
identification (blueprint: lem-pod-condensed-point-closed-comparison).

Proof:
1. Use lem-sf-condensed-geometric-point-perfect and the direct point adjunction
   def-weil-finite-coefficient-point. Its inverse is actual scalar extension J.
   Tau and u0 are the inverses of the monoidal tensor and unit comparisons.
2. The field has ell-cohomological dimension zero (sk-lem-base-field-cd).
   det-thm-sf-ctf-stability-adjunctions restricts the ambient tensor-Hom bijection.
   The closed comparison preserves evaluation; uniqueness of transpose identifies
   it with comparison and proves its invertibility and naturality.
3. Uncurry both sides of the asserted curry equation. Evaluation compatibility
   and naturality of the tensorator make both sides the image of v; transpose back.
4. Normalize the point identity by its exceptional counit, as in
   lem-pod-condensed-exchange-counit-normalization. Evaluation naturality in the
   target identifies pointVerdier with F(rho) followed by coefficientDual.
5. For X and M set U = Ra! M, W = RHom(M,Ra! unit) with the second shriek the
   exceptional inverse image. The same normalization lemma gives alpha as the
   transpose of globalPairing and the exchange e as rho followed by alpha inverse.
   Direct-image and Hom stability give every finite-Tor membership witness.
6. def-sf-cup identifies globalPairing with the cup/evaluation/exceptional-counit
   pairing. sk-thm-sf-global-duality specifies g inverse as its evaluated transpose.
   The curry equation computes it as F(alpha) followed by coefficientDual.
   def-weil-ordinary-compact-cohomology identifies the evaluated ordinary image
   with RΓ(X,D_X M), using the same actual coefficient ring.
7. Cancel F(rho) in j inverse followed by F(e), obtaining F(alpha) inverse
   followed by coefficientDual inverse, which is g. No purity orientation is used.
-/
theorem condensed_point_closed_comparison (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D₀.p)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E)
    (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E))
    (n : ℕ) (_hn : 1 ≤ n) :
    Statement (residueRingObj.{u} ℓ E π n) D₀ ∧
    Statement (Profinite.padicIntegersRingObj.{u} ℓ E) D₀ ∧
    Statement (Profinite.continuousMapRingObj.{u} E) D₀ ∧
    Statement (Profinite.padicAlgClRingObj.{u} ℓ) D₀ := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedPointClosedComparison
