/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Sheaf.CategoryTheory.ScalarLocalization

/-!
# Semilinear functors under raw scalar localization

Source: Weil conjectures blueprint, main-20261015, `sec-smooth-purity`,
`sk-lem-sp-field-extension/prop-pur-rational-purity-transitivity-summands.proof.md`,
finite-extension sentence (blueprint: lem-pur-semilinear-scalar-localization).

The construction uses the existing scalar-first tensor Hom modules. The unique additive
Hom extension specifies its data completely, so choosing that extension postpones only
proofs. Functor, transformation, coherence and exactness statements below express the
successive clauses of the node. HEq in coherence laws only transports equal endpoints;
it never replaces an equality by an isomorphism.
-/

@[expose] public section

universe r s q u v w x y z

open TensorProduct CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.ScalarLocalization

variable {R : Type r} [CommRing R] {S : Type s} [CommRing S]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type w} [Category.{x} D] [Preadditive D] [Linear S D]

/-- Semilinearity on Hom modules, with additivity supplied separately.
Source: the node's definition of semilinearity, extracted from the blueprint's
finite-extension sentence (blueprint: lem-pur-semilinear-scalar-localization). -/
def IsSemilinear (φ : R →+* S) (F : C ⥤ D) : Prop :=
  ∀ (K L : C) (a : R) (f : K ⟶ L), F.map (a • f) = φ a • F.map f

/-- The coefficient map induced by the localization universal property.
Source: Stacks Tag 00CO and the blueprint's finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable def coefficientMap (t : R) (b : S) (φ : R →+* S)
    (h : IsUnit (algebraMap S (Localization.Away b) (φ t))) :
    Localization.Away t →+* Localization.Away b :=
  IsLocalization.Away.lift t (S := Localization.Away t)
    (g := (algebraMap S (Localization.Away b)).comp φ) h

variable (t : R) (b : S) (φ : R →+* S)
  (h : IsUnit (algebraMap S (Localization.Away b) (φ t)))

/-- Existence and uniqueness of the induced coefficient homomorphism.
Source: Stacks Tag 00CO (blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 1): send r/t^n to φ(r)φ(t)^(-n). The fraction relation gives
well-definedness after cancelling the invertible image of t. Addition, multiplication
and one are preserved by the fraction formulas; the inverse of t has a forced image. -/
theorem coefficientMap_unique :
    ∀ k : Localization.Away t →+* Localization.Away b,
      k.comp (algebraMap R (Localization.Away t)) =
          (algebraMap S (Localization.Away b)).comp φ ↔ k = coefficientMap t b φ h := by
  sorry

/-- The uniquely prescribed additive extension on a tensor Hom module.
Source: Stacks Tags 07K0 and 00DK (blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Steps 2–3): view the target as an R-module through λφ. Multiplication
by t is bijective because λφ(t) is a unit. The module-localization universal property
extends f ↦ Q(F(f)) uniquely; identify the localized module with the tensor product.
For a=r/t^m the result on a⊗f is λφ(r)φ(t)^(-m)⊗F(f), giving the displayed formula.
Pure tensors generate, so this prescription uniquely determines the additive map. -/
theorem existsUnique_semilinearHom (F : C ⥤ D) [F.Additive]
    (hF : IsSemilinear φ F) (K L : C) :
    ∃! k : (Localization.Away t ⊗[R] (K ⟶ L)) →+
        (Localization.Away b ⊗[S] (F.obj K ⟶ F.obj L)),
      ∀ (a : Localization.Away t) (f : K ⟶ L),
        k (a ⊗ₜ[R] f) = coefficientMap t b φ h a ⊗ₜ[S] F.map f := by
  sorry

/-- The additive Hom map determined uniquely on all pure tensors.
Source: Stacks Tags 07K0 and 00DK (blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable def extensionHom (F : C ⥤ D) [F.Additive]
    (hF : IsSemilinear φ F) (K L : C) :
    (Localization.Away t ⊗[R] (K ⟶ L)) →+
      (Localization.Away b ⊗[S] (F.obj K ⟶ F.obj L)) :=
  Classical.choose (existsUnique_semilinearHom t b φ h F hF K L).exists

/-- Identity and composition laws of the extended Hom maps.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 4): on fractions both sides of the composition law are
φ(t)^(-m-n)Q(F(gf)), by bilinearity and the functor laws of F. Identities are
1⊗F(id)=1⊗id. Extend the equalities using the additive Hom maps and tensor generators. -/
theorem extensionHom_laws (F : C ⥤ D) [F.Additive] (hF : IsSemilinear φ F) :
    (∀ K : C, extensionHom t b φ h F hF K K (1 ⊗ₜ[R] 𝟙 K) = 1 ⊗ₜ[S] 𝟙 (F.obj K)) ∧
    (∀ (K L M : C) (f : Localization.Away t ⊗[R] (K ⟶ L))
        (g : Localization.Away t ⊗[R] (L ⟶ M)),
      extensionHom t b φ h F hF K M (composition R C t K L M g f) =
        composition S D b (F.obj K) (F.obj L) (F.obj M)
          (extensionHom t b φ h F hF L M g) (extensionHom t b φ h F hF K L f)) := by
  sorry

/-- The semilinear extension, with exactly the original object map.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable def extension (F : C ⥤ D) [F.Additive] (hF : IsSemilinear φ F) :
    ScalarLocalization R C t ⥤ ScalarLocalization S D b where
  obj K := ⟨F.obj K.obj⟩
  map {K L} f := extensionHom t b φ h F hF K.obj L.obj f
  map_id K := (extensionHom_laws t b φ h F hF).1 K.obj
  map_comp {K L M} f g := (extensionHom_laws t b φ h F hF).2 K.obj L.obj M.obj f g

/-- The extended functor is additive by its additive Hom maps.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable instance extensionAdditive (F : C ⥤ D) [F.Additive]
    (hF : IsSemilinear φ F) : (extension t b φ h F hF).Additive where
  map_add {K L} {f g} := (extensionHom t b φ h F hF K.obj L.obj).map_add f g

/-- Semilinearity, agreement on integral arrows, and the formula on every fraction.
Source: blueprint finite-extension sentence and Stacks Tags 00CO, 07K0, 00DK
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Steps 2–4): apply the specification of the unique Hom map. A fraction
f/t^n is t^(-n)⊗f; its coefficient image is φ(t)^(-n). Multiplying fractions proves
semilinearity over the induced coefficient map. Tensoring with one gives agreement
on integral arrows, and the prescribed object map gives the functor equality. -/
theorem extension_spec (F : C ⥤ D) [F.Additive] (hF : IsSemilinear φ F) :
    IsSemilinear (coefficientMap t b φ h) (extension t b φ h F hF) ∧
    localization R C t ⋙ extension t b φ h F hF = F ⋙ localization S D b ∧
    (∀ (K L : C) (f : K ⟶ L) (n : ℕ),
      (extension t b φ h F hF).map
          (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[R] f :
            ScalarLocalization.mk K ⟶ ScalarLocalization.mk L) =
        (Ring.inverse (algebraMap S (Localization.Away b) (φ t)) ^ n) ⊗ₜ[S] F.map f) := by
  sorry

/-- The additive semilinear extension with this object map and integral values is unique.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 3): each f/t^n is t^(-n)(f/1), so semilinearity forces the
fraction formula of `extension_spec`. All arrows are fractions by 00DK and 07K0;
functor extensionality, using the given object equalities, proves uniqueness. -/
theorem extension_unique (F : C ⥤ D) [F.Additive] (hF : IsSemilinear φ F)
    (J : ScalarLocalization R C t ⥤ ScalarLocalization S D b) [J.Additive]
    (hJ : IsSemilinear (coefficientMap t b φ h) J)
    (hobj : ∀ K : C, J.obj ⟨K⟩ = ⟨F.obj K⟩)
    (hint : localization R C t ⋙ J = F ⋙ localization S D b) :
    J = extension t b φ h F hF := by
  sorry

/-- Every additive semilinear functor admits a unique additive semilinear extension
with the original object map and integral values.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Steps 1–4): Step 1 gives the coefficient map; the unique module extension
of Step 2 gives `extensionHom`. The fraction calculation in Step 3 proves semilinearity
and uniqueness, and Step 4 verifies the functor laws. The resulting `extension` is
additive and has the required integral values by `extension_spec`. Conversely the
fraction calculation forces every candidate to equal it, as in `extension_unique`.
The remaining clauses of this node are stated in the transformation, coherence and
exactness declarations of this same module. -/
theorem existsUnique_semilinear_extension (F : C ⥤ D) [F.Additive]
    (hF : IsSemilinear φ F) :
    ∃! J : ScalarLocalization R C t ⥤ ScalarLocalization S D b,
      J.Additive ∧ IsSemilinear (coefficientMap t b φ h) J ∧
      (∀ K : C, J.obj ⟨K⟩ = ⟨F.obj K⟩) ∧
      localization R C t ⋙ J = F ⋙ localization S D b := by
  sorry

variable {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
  (hF : IsSemilinear φ F) (hG : IsSemilinear φ G) (hH : IsSemilinear φ H)

/-- The integral components are natural for the extended functors.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 5): on f/t^n naturality is the integral naturality equation for η
multiplied by φ(t)^(-n). Bilinearity moves this common scalar across composition. -/
theorem extensionNatTrans_naturality (η : F ⟶ G)
    (K L : ScalarLocalization R C t) (f : K ⟶ L) :
    (extension t b φ h F hF).map f ≫ (localization S D b).map (η.app L.obj) =
      (localization S D b).map (η.app K.obj) ≫ (extension t b φ h G hG).map f := by
  sorry

/-- Extend a natural transformation by localizing its integral components.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable def extensionNatTrans (η : F ⟶ G) :
    extension t b φ h F hF ⟶ extension t b φ h G hG where
  app K := (localization S D b).map (η.app K.obj)
  naturality K L f := extensionNatTrans_naturality t b φ h hF hG η K L f

/-- The specified localized components determine a natural transformation uniquely.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 5): objects are unchanged, so the component prescription fixes every
component; apply natural-transformation extensionality. Existence is `extensionNatTrans`. -/
theorem extensionNatTrans_unique (η : F ⟶ G) :
    ∃! τ : extension t b φ h F hF ⟶ extension t b φ h G hG,
      ∀ K : ScalarLocalization R C t, τ.app K = (localization S D b).map (η.app K.obj) := by
  sorry

/-- Natural isomorphisms extend, including their specified inverses.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable def extensionNatIso (e : F ≅ G) :
    extension t b φ h F hF ≅ extension t b φ h G hG :=
  NatIso.ofComponents (fun K ↦ (localization S D b).mapIso (e.app K.obj))
    (fun {K L} f ↦ extensionNatTrans_naturality t b φ h hF hG e.hom K L f)

/-- The localized isomorphism has exactly the extended hom and inverse transformations.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 5): the component formulas are Q(e.hom) and Q(e.inv); the inverse
equations follow by functoriality of Q. Apply transformation extensionality. -/
theorem extensionNatIso_spec (e : F ≅ G) :
    (extensionNatIso t b φ h hF hG e).hom = extensionNatTrans t b φ h hF hG e.hom ∧
    (extensionNatIso t b φ h hF hG e).inv = extensionNatTrans t b φ h hG hF e.inv := by
  sorry

/-- Localization preserves identities and vertical composition.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 7): components are Q(id)=id and Q(η≫θ)=Q(η)≫Q(θ).
For an equality of integral comparisons, apply Q at every component and extensionality.
Combined with the whiskering laws below, induction on finite expressions preserves all
well-typed unit, associator, shift and comparison-square equations. -/
theorem extensionNatTrans_laws :
    extensionNatTrans t b φ h hF hF (𝟙 F) = 𝟙 (extension t b φ h F hF) ∧
    (∀ (η : F ⟶ G) (θ : G ⟶ H),
      extensionNatTrans t b φ h hF hH (η ≫ θ) =
        extensionNatTrans t b φ h hF hG η ≫ extensionNatTrans t b φ h hG hH θ) := by
  sorry

/-- Every integral comparison square remains commutative after localization.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 7): preservation of vertical composition identifies each localized
path with the extension of the corresponding integral composite. Apply Q to the given
integral equality componentwise and use natural-transformation extensionality. -/
theorem extension_comparisonSquare (J : C ⥤ D) [J.Additive] (hJ : IsSemilinear φ J)
    (a : F ⟶ G) (b' : G ⟶ H) (c : F ⟶ J) (d : J ⟶ H)
    (hsquare : a ≫ b' = c ≫ d) :
    extensionNatTrans t b φ h hF hG a ≫ extensionNatTrans t b φ h hG hH b' =
      extensionNatTrans t b φ h hF hJ c ≫ extensionNatTrans t b φ h hJ hH d := by
  sorry

section Composition

variable {T : Type q} [CommRing T] {E : Type y} [Category.{z} E]
  [Preadditive E] [Linear T E] (c : T) (ψ : S →+* T)
  (hψ : IsUnit (algebraMap T (Localization.Away c) (ψ b)))

include h hψ in
/-- The inversion and semilinearity hypotheses are stable under composition.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 6): the induced coefficient map for ψ sends the unit λφ(t) to a unit.
Its value is λψφ(t), giving the first assertion. Apply the two semilinearity equations
successively for the second; additivity is preserved by functor composition. -/
theorem semilinear_composition (F : C ⥤ D) (J : D ⥤ E)
    (hF : IsSemilinear φ F) (hJ : IsSemilinear ψ J) :
    IsUnit (algebraMap T (Localization.Away c) ((ψ.comp φ) t)) ∧
      IsSemilinear (ψ.comp φ) (F ⋙ J) := by
  sorry

/-- Extension commutes with composition, including the induced coefficient maps.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 6): both coefficient maps extend ψφ, so Step 1 makes them equal.
The composite extended functor has the integral values and object map of JF and is
semilinear for this map. Step 3 gives equality with the extension of JF. -/
theorem extension_comp (F : C ⥤ D) (J : D ⥤ E) [F.Additive] [J.Additive]
    (hF : IsSemilinear φ F) (hJ : IsSemilinear ψ J) :
    coefficientMap t c (ψ.comp φ) (semilinear_composition t b φ h c ψ hψ F J hF hJ).1 =
        (coefficientMap b c ψ hψ).comp (coefficientMap t b φ h) ∧
    extension t c (ψ.comp φ) (semilinear_composition t b φ h c ψ hψ F J hF hJ).1
        (F ⋙ J) (semilinear_composition t b φ h c ψ hψ F J hF hJ).2 =
      extension t b φ h F hF ⋙ extension b c ψ hψ J hJ := by
  sorry

/-- Right whiskering commutes with extension after the functor equality `extension_comp`.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 7): at K, the right side is bar J(Q(η_K))=Q(J(η_K)), by integral
agreement, which is the left side. The endpoints are equal by Step 6. -/
theorem extensionNatTrans_whiskerRight (J : D ⥤ E) [J.Additive]
    (hJ : IsSemilinear ψ J) (η : F ⟶ G) :
    HEq (extensionNatTrans t c (ψ.comp φ)
        (semilinear_composition t b φ h c ψ hψ F J hF hJ).1
        (semilinear_composition t b φ h c ψ hψ F J hF hJ).2
        (semilinear_composition t b φ h c ψ hψ G J hG hJ).2
        (Functor.whiskerRight η J))
      (Functor.whiskerRight (extensionNatTrans t b φ h hF hG η)
        (extension b c ψ hψ J hJ)) := by
  sorry

/-- Left whiskering commutes with extension after the functor equality `extension_comp`.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 7): both components at K are Q(η_(F K)); Step 6 identifies the endpoints.
This and right whiskering prove preservation of arbitrary typed composite equations. -/
theorem extensionNatTrans_whiskerLeft (J K : D ⥤ E) [J.Additive] [K.Additive]
    (hJ : IsSemilinear ψ J) (hK : IsSemilinear ψ K) (η : J ⟶ K) :
    HEq (extensionNatTrans t c (ψ.comp φ)
        (semilinear_composition t b φ h c ψ hψ F J hF hJ).1
        (semilinear_composition t b φ h c ψ hψ F J hF hJ).2
        (semilinear_composition t b φ h c ψ hψ F K hF hK).2
        (Functor.whiskerLeft F η))
      (Functor.whiskerLeft (extension t b φ h F hF)
        (extensionNatTrans b c ψ hψ hJ hK η)) := by
  sorry

end Composition

/-- Linear functors are semilinear for the identity coefficient map.
Source: the node's definition of semilinearity
(blueprint: lem-pur-semilinear-scalar-localization).
Proof: this is exactly the scalar-preservation equation in `Functor.Linear`. -/
theorem isSemilinear_of_linear (J : C ⥤ C) [J.Linear R] :
    IsSemilinear (RingHom.id R) J := by
  sorry

/-- Identity extension and agreement with the existing extension of linear endofunctors.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Steps 3, 6): the identity has the same integral values and object map as its
extension, giving the identity equation by uniqueness. For a linear endofunctor the
existing tensor map sends a⊗f to a⊗J(f), the same prescription, so uniqueness identifies
the two constructions. In particular this applies to the induced linear shift. -/
theorem extension_id_and_linear :
    extension t t (RingHom.id R) (IsLocalization.Away.algebraMap_isUnit t)
        (𝟭 C) (isSemilinear_of_linear (𝟭 C)) = 𝟭 (ScalarLocalization R C t) ∧
    (∀ (J : C ⥤ C) [J.Additive] [J.Linear R],
      extension t t (RingHom.id R) (IsLocalization.Away.algebraMap_isUnit t)
        J (isSemilinear_of_linear J) = map R C t J) := by
  sorry

section Triangulated

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [triC : IsTriangulated C] [(shiftFunctor C (1 : ℤ)).Linear R]
  [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [triD : IsTriangulated D] [(shiftFunctor D (1 : ℤ)).Linear S]
  [HasZeroObject (ScalarLocalization R C t)] [HasShift (ScalarLocalization R C t) ℤ]
  [∀ n : ℤ, (shiftFunctor (ScalarLocalization R C t) n).Additive]
  [Pretriangulated (ScalarLocalization R C t)] [triLC : IsTriangulated (ScalarLocalization R C t)]
  [HasZeroObject (ScalarLocalization S D b)] [HasShift (ScalarLocalization S D b) ℤ]
  [∀ n : ℤ, (shiftFunctor (ScalarLocalization S D b) n).Additive]
  [Pretriangulated (ScalarLocalization S D b)] [triLD : IsTriangulated (ScalarLocalization S D b)]
  [(localization R C t).CommShift ℤ] [(localization S D b).CommShift ℤ]
  (hshiftC : shiftFunctor (ScalarLocalization R C t) (1 : ℤ) =
    map R C t (shiftFunctor C (1 : ℤ)))
  (hshiftD : shiftFunctor (ScalarLocalization S D b) (1 : ℤ) =
    map S D b (shiftFunctor D (1 : ℤ)))
  (hQC : ∀ K : C, HEq (((localization R C t).commShiftIso (1 : ℤ)).hom.app K)
    (𝟙 ((localization R C t).obj ((shiftFunctor C (1 : ℤ)).obj K))))
  (hQD : ∀ K : D, HEq (((localization S D b).commShiftIso (1 : ℤ)).hom.app K)
    (𝟙 ((localization S D b).obj ((shiftFunctor D (1 : ℤ)).obj K))))
  (hdistC : ∀ Δ : Triangle (ScalarLocalization R C t),
    Δ ∈ distTriang (ScalarLocalization R C t) ↔
      ∃ Δ₀ : Triangle C, Δ₀ ∈ distTriang C ∧
        Nonempty (Δ ≅ (localization R C t).mapTriangle.obj Δ₀))
  (hdistD : ∀ Δ : Triangle (ScalarLocalization S D b),
    Δ ∈ distTriang (ScalarLocalization S D b) ↔
      ∃ Δ₀ : Triangle D, Δ₀ ∈ distTriang D ∧
        Nonempty (Δ ≅ (localization S D b).mapTriangle.obj Δ₀))

include triC triD triLC triLD hshiftC hshiftD hQC hQD hdistC hdistD in
/-- Exactness with the localized, specified shift comparison. The ambient structures
and their normalizations are exactly those provided by
`exists_triangulated_scalarLocalization`, separately for C and D.
Source: blueprint finite-extension sentence; Stacks Tag 05R6
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 8): extend the given shift comparison and its inverse by Step 5.
Use Step 6 and `extension_id_and_linear` to identify its endpoints with the induced
shifts. Its components are Q(σ_K). A distinguished localized triangle is isomorphic
to Q(Δ₀) by the hypothesis from `lem-weil-linear-scalar-localization-triangulated`.
The image of Q(Δ₀) under the extended functor with this comparison is Q(F(Δ₀)),
including its last arrow, by the integral formula and functoriality. Exactness of F
makes F(Δ₀) distinguished, and the image-triangle description makes its Q-image
distinguished. Preserve the triangle isomorphism and use closure under isomorphisms.
This proves exactness with the specified comparison, rather than merely with some
unrelated shift structure. -/
theorem extension_exact (F : C ⥤ D) [F.Additive] (hF : IsSemilinear φ F)
    [F.CommShift ℤ] [F.IsTriangulated] :
    ∃ cs : (extension t b φ h F hF).CommShift ℤ,
      (fun [commInst : (extension t b φ h F hF).CommShift ℤ] ↦
        (extension t b φ h F hF).IsTriangulated ∧
        ∀ K : C,
          HEq (((extension t b φ h F hF).commShiftIso (1 : ℤ)).hom.app ⟨K⟩)
            ((localization S D b).map ((F.commShiftIso (1 : ℤ)).hom.app K)))
        (commInst := cs) := by
  sorry

include triC triD triLC triLD hshiftC hshiftD hQC hQD hdistC hdistD in
/-- Exact comparisons retain their shift equation; the isomorphism version follows
by taking the hom and inverse in `extensionNatIso`.
Source: blueprint `sk-prop-sf-localization/pur9-def-exact-transformation.md`
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 9): the defining equation is
σF_K ≫ η_K[1] = η_(K[1]) ≫ σG_K. Apply Q, use its functor laws, the induced shift
on arrows, and the prescribed component formulas for the extended σF, σG and η.
The result is precisely `NatTrans.CommShiftCore` at one. For an exact natural
isomorphism, localize both inverse transformations as in Step 5; the same equation
and the inverse laws give an exact natural comparison isomorphism. -/
theorem extension_exactComparison [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated]
    [(extension t b φ h F hF).CommShift ℤ] [(extension t b φ h G hG).CommShift ℤ]
    (hσF : ∀ K : C,
      HEq (((extension t b φ h F hF).commShiftIso (1 : ℤ)).hom.app ⟨K⟩)
        ((localization S D b).map ((F.commShiftIso (1 : ℤ)).hom.app K)))
    (hσG : ∀ K : C,
      HEq (((extension t b φ h G hG).commShiftIso (1 : ℤ)).hom.app ⟨K⟩)
        ((localization S D b).map ((G.commShiftIso (1 : ℤ)).hom.app K))) :
    (∀ (η : F ⟶ G), NatTrans.CommShiftCore η (1 : ℤ) →
      NatTrans.CommShiftCore (extensionNatTrans t b φ h hF hG η) (1 : ℤ)) ∧
    (∀ (e : F ≅ G), NatTrans.CommShiftCore e.hom (1 : ℤ) →
      NatTrans.CommShiftCore (extensionNatIso t b φ h hF hG e).hom (1 : ℤ) ∧
      NatTrans.CommShiftCore (extensionNatIso t b φ h hF hG e).inv (1 : ℤ)) := by
  sorry

end Triangulated

end CategoryTheory.ScalarLocalization
