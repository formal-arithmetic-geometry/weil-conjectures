/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.ResidueField
public import Sheaf.AlgebraicGeometry.FibreStalkQuotient
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.BaseChange

/-! # Compatible affine stalk models and fibre stalk maps

Source: Stacks Project, Tags 039C, 0HA1, 01HV, 00QM, 05G5 and 00DK
(blueprint: lem-sfb-fibre-flatness-compatible-stalk-data).

The structure only packages the witnesses and clauses of the statement. The affine
and fibre data use f ≫ q; the theorem includes f ≫ q = p, identifying these data
with those of the given map p.
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical map of fibres of the tower X → Y → S, at the image of x.
Source: Stacks Project, Tag 01K0, functoriality of fibre products
(blueprint: lem-sfb-fibre-flatness-compatible-stalk-data). -/
noncomputable def fibreFlatnessMap {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) (x : X) :
    (f ≫ q).fiber (q (f x)) ⟶ q.fiber (q (f x)) :=
  pullback.map (f ≫ q) (S.fromSpecResidueField (q (f x)))
    q (S.fromSpecResidueField (q (f x))) f (𝟙 _) (𝟙 _)
    (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Affine witnesses, their canonical germ localizations, and their scalar extensions.
Every algebra structure below is pinned to its section or germ map. The maps j and k
are pinned on every pure tensor, so their localization assertions refer to the
canonical maps, not arbitrary homomorphisms.
Source: Stacks Project, Tags 039C, 01HV, 05G5, 00DK and 00QM
(blueprint: lem-sfb-fibre-flatness-compatible-stalk-data). -/
structure FibreFlatnessAffineStalkModels {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (q : Y ⟶ S) (x : X) where
  V : S.Opens
  U : X.Opens
  W : Y.Opens
  affineV : IsAffineOpen V
  affineU : IsAffineOpen U
  affineW : IsAffineOpen W
  hx : x ∈ U
  hy : f x ∈ W
  hs : q (f x) ∈ V
  hUV : U ≤ (f ≫ q) ⁻¹ᵁ V
  hWV : W ≤ q ⁻¹ᵁ V
  [algebraAR : Algebra Γ(S, V) (S.presheaf.stalk (q (f x)))]
  [algebraAD : Algebra Γ(S, V) Γ(X, U)]
  [algebraAE : Algebra Γ(S, V) Γ(Y, W)]
  algebraAR_eq : algebraMap Γ(S, V) (S.presheaf.stalk (q (f x))) =
    (S.presheaf.germ V (q (f x)) hs).hom
  algebraAD_eq : algebraMap Γ(S, V) Γ(X, U) = ((f ≫ q).appLE V U hUV).hom
  algebraAE_eq : algebraMap Γ(S, V) Γ(Y, W) = (q.appLE V W hWV).hom
  finitePresentationD : Algebra.FinitePresentation Γ(S, V) Γ(X, U)
  finiteTypeE : Algebra.FiniteType Γ(S, V) Γ(Y, W)
  germR_localization : (affineV.primeIdealOf ⟨q (f x), hs⟩).asIdeal.primeCompl.IsLocalizationMap
    (S.presheaf.germ V (q (f x)) hs).hom
  germC_localization : (affineU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl.IsLocalizationMap
    (X.presheaf.germ U x hx).hom
  germB_localization : (affineW.primeIdealOf ⟨f x, hy⟩).asIdeal.primeCompl.IsLocalizationMap
    (Y.presheaf.germ W (f x) hy).hom
  germ_p : ∀ a : Γ(S, V),
    (f ≫ q).stalkMap x (S.presheaf.germ V (q (f x)) hs a) =
      X.presheaf.germ U x hx ((f ≫ q).appLE V U hUV a)
  germ_q : ∀ a : Γ(S, V),
    q.stalkMap (f x) (S.presheaf.germ V (q (f x)) hs a) =
      Y.presheaf.germ W (f x) hy (q.appLE V W hWV a)
  finitePresentationP : Algebra.FinitePresentation (S.presheaf.stalk (q (f x)))
    ((S.presheaf.stalk (q (f x))) ⊗[Γ(S, V)] Γ(X, U))
  finiteTypeQ : Algebra.FiniteType (S.presheaf.stalk (q (f x)))
    ((S.presheaf.stalk (q (f x))) ⊗[Γ(S, V)] Γ(Y, W))
  tensorP_localization :
    ((affineV.primeIdealOf ⟨q (f x), hs⟩).asIdeal.primeCompl.map
      (algebraMap Γ(S, V) Γ(X, U))).IsLocalizationMap
      (Algebra.TensorProduct.includeRight :
        Γ(X, U) →ₐ[Γ(S, V)] (S.presheaf.stalk (q (f x))) ⊗[Γ(S, V)] Γ(X, U))
  tensorQ_localization :
    ((affineV.primeIdealOf ⟨q (f x), hs⟩).asIdeal.primeCompl.map
      (algebraMap Γ(S, V) Γ(Y, W))).IsLocalizationMap
      (Algebra.TensorProduct.includeRight :
        Γ(Y, W) →ₐ[Γ(S, V)] (S.presheaf.stalk (q (f x))) ⊗[Γ(S, V)] Γ(Y, W))
  j : (S.presheaf.stalk (q (f x))) ⊗[Γ(S, V)] Γ(X, U) →+* X.presheaf.stalk x
  k : (S.presheaf.stalk (q (f x))) ⊗[Γ(S, V)] Γ(Y, W) →+* Y.presheaf.stalk (f x)
  j_tmul : ∀ (r : S.presheaf.stalk (q (f x))) (d : Γ(X, U)),
    j (r ⊗ₜ[Γ(S, V)] d) = (f ≫ q).stalkMap x r * X.presheaf.germ U x hx d
  k_tmul : ∀ (r : S.presheaf.stalk (q (f x))) (e : Γ(Y, W)),
    k (r ⊗ₜ[Γ(S, V)] e) = q.stalkMap (f x) r * Y.presheaf.germ W (f x) hy e
  j_localization :
    ((affineU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl.map
      (Algebra.TensorProduct.includeRight :
        Γ(X, U) →ₐ[Γ(S, V)] (S.presheaf.stalk (q (f x))) ⊗[Γ(S, V)] Γ(X, U))).IsLocalizationMap j
  k_localization :
    ((affineW.primeIdealOf ⟨f x, hy⟩).asIdeal.primeCompl.map
      (Algebra.TensorProduct.includeRight :
        Γ(Y, W) →ₐ[Γ(S, V)] (S.presheaf.stalk (q (f x))) ⊗[Γ(S, V)] Γ(Y, W))).IsLocalizationMap k

/-- Compatible stalk models and the induced quotient map on fibre stalks.
Source: Stacks Project, Tag 039C, first proof paragraph; expanded by Tags 0HA1,
01HV, 00QM, 05G5, and 00DK
(blueprint: lem-sfb-fibre-flatness-compatible-stalk-data).

Proof: (1) Choose affine V and U around the two points using local finite
presentation, and W over the same V using local finite type. No containment
f(U) ⊆ W is required. (2) Affine-open stalk localization identifies the three
germs with prime localizations; scheme stalk maps are local and compose, and
the germ formula identifies the induced localized maps. (3) Finite presentation
and finite type persist under the base change A → R, by finite-presentation
base change and finite algebra generators. (4) Localization tensor over the
base identifies D → P and E → Q with localizations at the image of A minus its
prime. On fractions the identifications preserve multiplication.
(5) The balancing relation gives j and k with the displayed tensor formulas.
Units, fraction representatives, and the zero-kernel criterion from affine
stalk localization show that j and k are further localizations, at the images
of the complementary primes. This also gives essential finite presentation
and essential finite type. (6) Apply the fibre-stalk quotient lemma to f ≫ q
and to q: the two equivalences have the specified formula on classes, namely
the point transport along the fibre projection followed by its stalk map.
(7) The fibre-product projection identity and injectivity of the fibre
projection give the point identity. Composition of stalk maps gives the
commuting square with the fibre projections. Since beta alpha is the base
stalk map, beta carries the extended maximal ideal into the extended maximal
ideal. The commuting square on each representative b is exactly the final
compatibility equation. -/
theorem nonempty_fibreFlatnessCompatibleStalkData {X Y S : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (_h : f ≫ q = p)
    [LocallyOfFinitePresentation p] [LocallyOfFiniteType q] (x : X) :
    Nontrivial (S.presheaf.stalk (q (f x))) ∧
    Nontrivial (Y.presheaf.stalk (f x)) ∧ Nontrivial (X.presheaf.stalk x) ∧
    IsLocalRing (S.presheaf.stalk (q (f x))) ∧
    IsLocalRing (Y.presheaf.stalk (f x)) ∧ IsLocalRing (X.presheaf.stalk x) ∧
    IsLocalHom (q.stalkMap (f x)).hom ∧ IsLocalHom (f.stalkMap x).hom ∧
    q.stalkMap (f x) ≫ f.stalkMap x = (f ≫ q).stalkMap x ∧
    Nonempty (FibreFlatnessAffineStalkModels f q x) ∧
    (q.stalkMap (f x)).hom.EssFiniteType ∧
    ∃ hpoint : fibreFlatnessMap f q x ((f ≫ q).asFiber x) = q.asFiber (f x),
      ∃ eX : (X.presheaf.stalk x ⧸
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (q (f x)))).map
            ((f ≫ q).stalkMap x).hom) ≃+*
          ((f ≫ q).fiber (q (f x))).presheaf.stalk ((f ≫ q).asFiber x),
      ∃ eY : (Y.presheaf.stalk (f x) ⧸
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (q (f x)))).map
            (q.stalkMap (f x)).hom) ≃+*
          (q.fiber (q (f x))).presheaf.stalk (q.asFiber (f x)),
        (∀ c : X.presheaf.stalk x,
          eX (Ideal.Quotient.mk _ c) =
            ((X.presheaf.stalkCongr (.of_eq ((f ≫ q).fiberι_asFiber x))).inv ≫
              ((f ≫ q).fiberι (q (f x))).stalkMap ((f ≫ q).asFiber x)).hom c) ∧
        (∀ b : Y.presheaf.stalk (f x),
          eY (Ideal.Quotient.mk _ b) =
            ((Y.presheaf.stalkCongr (.of_eq (q.fiberι_asFiber (f x)))).inv ≫
              (q.fiberι (q (f x))).stalkMap (q.asFiber (f x))).hom b) ∧
        ((IsLocalRing.maximalIdeal (S.presheaf.stalk (q (f x)))).map
          (q.stalkMap (f x)).hom).map (f.stalkMap x).hom ≤
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (q (f x)))).map
            ((f ≫ q).stalkMap x).hom ∧
        ∀ b : Y.presheaf.stalk (f x),
          (((q.fiber (q (f x))).presheaf.stalkCongr (.of_eq hpoint)).inv ≫
              (fibreFlatnessMap f q x).stalkMap ((f ≫ q).asFiber x))
            (eY (Ideal.Quotient.mk _ b)) =
          eX (Ideal.Quotient.mk _ ((f.stalkMap x).hom b)) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
