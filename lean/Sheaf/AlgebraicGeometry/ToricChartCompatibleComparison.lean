/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.FineLogSchemeMorphisms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# Compatible affine toric charts

Source: ILO VI 1.1, VIII 3.3.3--3.3.6, 3.3.8 and 3.3.11;
Stacks Tags 01I4, 01JQ, 02GI and 02GP
(blueprint: lem-trf-toric-chart-compatible-comparison).

Monoids use multiplicative notation. The tensor product below has the specified
coefficient actions and the usual tensor multiplication. Pair representatives use
the canonical universe lift of `associatedLogPresheaf`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The actual tensor ring for the two chart homomorphisms. Source: ILO VIII 3.3.5;
Stacks 01I4 (blueprint: lem-trf-toric-chart-compatible-comparison). -/
noncomputable abbrev toricCompatibleRing {A P Q : Type u} [CommRing A]
    [CommMonoid P] [CommMonoid Q] (α : P →* A) (g : P →* Q) : Type u :=
  letI := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ g).toAlgebra
  TensorProduct (MonoidAlgebra ℤ P) A (MonoidAlgebra ℤ Q)

/-- Tensor multiplication `(a ⊗ u)(b ⊗ v) = ab ⊗ uv`. Source: Stacks 01I4
(blueprint: lem-trf-toric-chart-compatible-comparison). -/
noncomputable instance toricCompatibleRingCommRing {A P Q : Type u} [CommRing A]
    [CommMonoid P] [CommMonoid Q] (α : P →* A) (g : P →* Q) :
    CommRing (toricCompatibleRing α g) :=
  letI := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ g).toAlgebra
  inferInstanceAs (CommRing (TensorProduct (MonoidAlgebra ℤ P) A (MonoidAlgebra ℤ Q)))

/-- The ring homomorphism `a ↦ a ⊗ 1`. Source: Stacks 01I4
(blueprint: lem-trf-toric-chart-compatible-comparison). -/
noncomputable def toricCompatibleLeft {A P Q : Type u} [CommRing A]
    [CommMonoid P] [CommMonoid Q] (α : P →* A) (g : P →* Q) :
    A →+* toricCompatibleRing α g :=
  letI := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ g).toAlgebra
  Algebra.TensorProduct.includeLeftRingHom

/-- The ring homomorphism `v ↦ 1 ⊗ v`. Source: Stacks 01I4
(blueprint: lem-trf-toric-chart-compatible-comparison). -/
noncomputable def toricCompatibleRight {A P Q : Type u} [CommRing A]
    [CommMonoid P] [CommMonoid Q] (α : P →* A) (g : P →* Q) :
    MonoidAlgebra ℤ Q →+* toricCompatibleRing α g :=
  letI := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ g).toAlgebra
  Algebra.TensorProduct.includeRight.toRingHom

/-- The chart `q ↦ 1 ⊗ z^q` as global functions on the affine tensor spectrum.
Source: ILO VIII 3.3.5 (blueprint: lem-trf-toric-chart-compatible-comparison). -/
noncomputable def toricCompatibleBeta {A P Q : Type u} [CommRing A]
    [CommMonoid P] [CommMonoid Q] (α : P →* A) (g : P →* Q) :
    Q →* Γ(Spec (.of (toricCompatibleRing α g)), ⊤) :=
  (Scheme.ΓSpecIso (.of (toricCompatibleRing α g))).inv.hom.toMonoidHom.comp
    ((toricCompatibleRight α g).toMonoidHom.comp (MonoidAlgebra.of ℤ Q))

/-- The canonical affine tensor-product identification, with its prescribed projections.
Source: Stacks 01I4, 01JQ (blueprint: lem-trf-toric-chart-compatible-comparison). -/
noncomputable def toricCompatibleIso {A P Q : Type u} [CommRing A]
    [CommMonoid P] [CommMonoid Q] (α : P →* A) (g : P →* Q) :
    pullback (Spec.map (CommRingCat.ofHom (MonoidAlgebra.lift ℤ A P α).toRingHom))
      (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g))) ≅
        Spec (.of (toricCompatibleRing α g)) :=
  letI := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ g).toAlgebra
  pullbackSpecIso (MonoidAlgebra ℤ P) A (MonoidAlgebra ℤ Q)

/-- The local representative `[r,a]` in an associated-log presentation.
Source: ILO VI 1.1 (blueprint: lem-trf-toric-chart-compatible-comparison). -/
noncomputable def toricCompatiblePair {X : Scheme.{u}} {R : Type u} [CommMonoid R]
    (β : R →* Γ(X, ⊤)) (L : EtaleLogStructure X)
    (η : associatedLogPresheaf.{u, u} β ⟶ L.monoidSheaf.obj)
    (W : X.Etale) (r : R) (a : Γ(W.left, ⊤)ˣ) : L.monoidSheaf.obj.obj (op W) :=
  η.app (op W) ((divisorialChartCongruence (P := ULift.{u, u} R)
    (associatedLogBetaLift.{u, u} β W).mrangeRestrict).mk' (ULift.up r, a))

/-- Compatible charts give the specified log morphism and an isomorphic, hence étale,
toric comparison. Both projections characterize the actual comparison map.

Source: ILO VI 1.1, VIII 3.3.3--3.3.6, 3.3.8, 3.3.11; Stacks 01I4, 01JQ, 02GP.
Proof (the six steps of the node):
1. Tensor balancing gives `α(p) ⊗ 1 = 1 ⊗ z^(g(p))`. The associated-log stalk
   pushouts make the `Q` chart fs (`lem-trf-associated-log-universal-stalks`,
   `def-trf-fs-log-blowup`), including the empty spectrum.
2. Étale base change makes `U ↦ M(X ×_Y U)` a monoid sheaf, and similarly for
   regular functions (`lem-weil-pbc-etale-base-change-finite-limits`,
   `lem-weil-pbc-etale-base-change-continuous`, `def-weil-size-convention`).
3. Send `[p,a]` to the restricted `g(p)` chart times the pulled-back unit. For a
   chart element with unit image the log axiom identifies it with that unit;
   hence this respects the pushout congruence, products, and restrictions.
4. Monoid sheafification extends this map uniquely to `N`. The structural maps
   agree on pair representatives and thus agree everywhere. Restriction along
   `V → X ×_Y U` gives the relative-test log morphism and the displayed formula
   (`lem-trf-commutative-monoid-sheafification`, `def-trf-fine-log-scheme-morphisms`).
5. The two tensor ring maps agree on all base monomials. The comparison therefore
   exists; its two projections agree with those of the inverse of the canonical
   affine tensor isomorphism. Pullback uniqueness identifies them
   (`def-pc-fibre-product`, `lem-weil-pbc-fibre-product-affine-spectra`).
6. The comparison is an isomorphism, hence an open immersion and étale
   (`def-weil-open-immersion`, `lem-weil-pbc-open-immersion-etale`). No condition
   on group completions or log regularity was used. For the zero tensor ring
   both spectra and their comparison are empty, with the same section formulas.
(blueprint: lem-trf-toric-chart-compatible-comparison). -/
theorem toricChart_compatible_comparison
    (A P Q : Type u) [CommRing A] [CommMonoid P] [CommMonoid Q]
    [IsLocallyNoetherian (Spec (.of A))]
    (N : EtaleLogStructure (Spec (.of A))) (hN : N.IsFineSaturated)
    (hP : IsFineSaturatedMonoid P) (hQ : IsFineSaturatedMonoid Q)
    (α : P →* A) (g : P →* Q)
    (c : ULift.{u, u} P →* N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 _))))
    (hc : N.IsChart (Scheme.Etale.mk (𝟙 _)) c)
    (hα : ∀ p : P, N.alpha.app (op (Scheme.Etale.mk (𝟙 _))) (c (ULift.up p)) =
      (Scheme.ΓSpecIso (.of A)).inv (α p))
    [IsLocallyNoetherian (Spec (.of (toricCompatibleRing α g)))] :
    ∃ (ηN : associatedLogPresheaf.{u, u}
        ((Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom.comp α) ⟶ N.monoidSheaf.obj)
      (M : EtaleLogStructure (Spec (.of (toricCompatibleRing α g))))
      (ηM : associatedLogPresheaf.{u, u} (toricCompatibleBeta α g) ⟶ M.monoidSheaf.obj)
      (hM : M.IsFineSaturated)
      (f : EtaleLogHom ⟨Spec (.of (toricCompatibleRing α g)), inferInstance, M, hM⟩
        ⟨Spec (.of A), inferInstance, N, hN⟩),
      IsAssociatedLogPresentation
        ((Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom.comp α) N ηN ∧
      associatedLogIota _ N ηN = c ∧
      IsAssociatedLogPresentation (toricCompatibleBeta α g) M ηM ∧
      M.IsChart (Scheme.Etale.mk (𝟙 _)) (associatedLogIota _ M ηM) ∧
      f.base = Spec.map (CommRingCat.ofHom (toricCompatibleLeft α g)) ∧
      (∀ (W : (Spec (.of A)).Etale)
        (V : (Spec (.of (toricCompatibleRing α g))).Etale)
        (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ f.base)
        (p : P) (a : Γ(W.left, ⊤)ˣ),
        f.sectionMap W V k hk
          (toricCompatiblePair ((Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom.comp α)
            N ηN W p a) =
          toricCompatiblePair (toricCompatibleBeta α g) M ηM V (g p)
            (Units.map k.appTop.hom.toMonoidHom a)) ∧
      ∃ κ : Spec (.of (toricCompatibleRing α g)) ⟶
        pullback (Spec.map (CommRingCat.ofHom (MonoidAlgebra.lift ℤ A P α).toRingHom))
          (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g))),
        κ ≫ pullback.fst _ _ = f.base ∧
        κ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (toricCompatibleRight α g)) ∧
        κ ≫ (toricCompatibleIso α g).hom = 𝟙 _ ∧ IsIso κ ∧ Etale κ := by
  sorry

end AlgebraicGeometry
