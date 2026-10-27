/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.AlgebraicGeometry.IntegralChartLogificationThickening

/-!
# The universal property of an integral saturated prelog chart

Source: ILO VIII 3.1.17, printed p.101; X, proof of Theorem 3.5, Step 6, printed p.164.
The universal-property formulation is the agent-supplied auxiliary statement of the DAG.
(blueprint: lem-per-prelog-chart-fs-universal).

Monoids are written multiplicatively, so powers express the additive multiples of the node.
The ring is the actual Mathlib module tensor product, with its canonical ring structure.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The saturation of the image in the canonical group completion. Source: ILO VIII 3.1.17
(blueprint: lem-per-prelog-chart-fs-universal). -/
abbrev prelogChartMonoid (S : Type v) [CommMonoid S] :=
  FineFan.saturation (MonoidHom.mrange (Algebra.GrothendieckGroup.of (M := S)))

/-- The canonical chart map into integralization followed by saturation.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
def prelogChartInclusion (S : Type v) [CommMonoid S] : S →* prelogChartMonoid S :=
  (FineFan.intoSaturation _).comp
    (MonoidHom.mrangeRestrict (Algebra.GrothendieckGroup.of (M := S)))

/-- The prescribed coefficient action, sending a monomial to its prelog value.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
@[instance_reducible]
noncomputable def prelogChartCoefficientAlgebra {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] (β : S →* A) : Algebra (MonoidAlgebra ℤ S) A :=
  (MonoidAlgebra.lift ℤ A S β).toRingHom.toAlgebra

/-- The prescribed action on the saturated monoid algebra.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
@[instance_reducible]
noncomputable def prelogChartSaturationAlgebra (S : Type v) [CommMonoid S] :
    Algebra (MonoidAlgebra ℤ S) (MonoidAlgebra ℤ (prelogChartMonoid S)) :=
  (MonoidAlgebra.mapDomainRingHom ℤ (prelogChartInclusion S)).toAlgebra

/-- The actual tensor ring `A ⊗[ℤ[S]] ℤ[Sfs]` for the two prescribed actions.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
noncomputable abbrev prelogChartRing {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] (β : S →* A) : Type (max u v) :=
  letI := prelogChartCoefficientAlgebra β
  letI := prelogChartSaturationAlgebra S
  TensorProduct (MonoidAlgebra ℤ S) A (MonoidAlgebra ℤ (prelogChartMonoid S))

/-- The canonical multiplication on the module tensor product.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
noncomputable instance prelogChartRingCommRing {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] (β : S →* A) : CommRing (prelogChartRing β) :=
  letI := prelogChartCoefficientAlgebra β
  letI := prelogChartSaturationAlgebra S
  inferInstanceAs (CommRing (TensorProduct (MonoidAlgebra ℤ S) A
    (MonoidAlgebra ℤ (prelogChartMonoid S))))

/-- The coefficient map `a ↦ a ⊗ 1`.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
noncomputable def prelogChartCoefficient {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] (β : S →* A) : A →+* prelogChartRing β :=
  letI := prelogChartCoefficientAlgebra β
  letI := prelogChartSaturationAlgebra S
  Algebra.TensorProduct.includeLeftRingHom

/-- The chart map `p ↦ 1 ⊗ zᵖ`.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
noncomputable def prelogChartMonomial {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] (β : S →* A) :
    prelogChartMonoid S →* prelogChartRing β :=
  letI := prelogChartCoefficientAlgebra β
  letI := prelogChartSaturationAlgebra S
  Algebra.TensorProduct.includeRight.toRingHom.toMonoidHom.comp (MonoidAlgebra.of ℤ _)

/-- The saturated chart as global functions on its actual affine spectrum.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
noncomputable def prelogChartBeta {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] (β : S →* A) :
    prelogChartMonoid S →* Γ(Spec (.of (prelogChartRing β)), ⊤) :=
  (Scheme.ΓSpecIso (.of (prelogChartRing β))).inv.hom.toMonoidHom.comp
    (prelogChartMonomial β)

/-- The structural scheme map, with no log structure assigned to its target.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
noncomputable def prelogChartProjection {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] (β : S →* A) :
    Spec (.of (prelogChartRing β)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (prelogChartCoefficient β))

/-- The fs log scheme with the stipulated underlying affine spectrum and log structure.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
noncomputable def prelogChartLogScheme {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] (β : S →* A)
    (L : EtaleLogStructure (Spec (.of (prelogChartRing β))))
    (hN : IsLocallyNoetherian (Spec (.of (prelogChartRing β))))
    (hfs : L.IsFineSaturated) : FineSaturatedLogScheme.{max u v} where
  scheme := Spec (.of (prelogChartRing β))
  locallyNoetherian := hN
  logStructure := L
  fineSaturated := hfs

/-- The original chart on the associated log structure, including the canonical universe lift.
Source: ILO VI 1.1; X, Theorem 3.5, Step 6
(blueprint: lem-per-prelog-chart-fs-universal). -/
noncomputable def prelogChartSection {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] (β : S →* A)
    (L : EtaleLogStructure (Spec (.of (prelogChartRing β))))
    (η : associatedLogPresheaf (prelogChartBeta β) ⟶ L.monoidSheaf.obj) :
    S →* L.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 _))) :=
  (associatedLogIota (prelogChartBeta β) L η).comp
    (MulEquiv.ulift.symm.toMonoidHom.comp (prelogChartInclusion S))

/-- The canonical forward map: compose the underlying scheme map and pull back the chart.
The target is the ambient product, whose compatible subset is specified in the theorem.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
noncomputable def prelogChartExtract {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] (β : S →* A)
    (L : EtaleLogStructure (Spec (.of (prelogChartRing β))))
    (η : associatedLogPresheaf (prelogChartBeta β) ⟶ L.monoidSheaf.obj)
    (hN : IsLocallyNoetherian (Spec (.of (prelogChartRing β))))
    (hfs : L.IsFineSaturated) (T : FineSaturatedLogScheme.{max u v})
    (F : EtaleLogHom T (prelogChartLogScheme β L hN hfs)) :
    (T.scheme ⟶ Spec (.of A)) ×
      (S →* T.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 T.scheme)))) :=
  (F.base ≫ prelogChartProjection β,
    (F.sectionMap (Scheme.Etale.mk (𝟙 _)) (Scheme.Etale.mk (𝟙 T.scheme)) F.base
      ((Category.comp_id _).trans (Category.id_comp _).symm)).comp
        (prelogChartSection β L η))

/-- Exactly the equation `α_T λ = v♯ β`, with the canonical affine-global-sections map.
Source: ILO VI 1.1; X, Theorem 3.5, Step 6
(blueprint: lem-per-prelog-chart-fs-universal). -/
def prelogChartCompatible {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] (β : S →* A) (T : FineSaturatedLogScheme.{max u v})
    (q : (T.scheme ⟶ Spec (.of A)) ×
      (S →* T.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 T.scheme))))) :
    Prop :=
  (T.logStructure.alpha.app (op (Scheme.Etale.mk (𝟙 T.scheme)))).hom.comp q.2 =
    q.1.appTop.hom.toMonoidHom.comp
      ((Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom.comp β)

/-- Pullback of the pair by an fs log morphism, using its actual map on global log sections.
Source: ILO X, Theorem 3.5, Step 6 (blueprint: lem-per-prelog-chart-fs-universal). -/
noncomputable def prelogChartPullbackPair {A : Type (max u v)} [CommRing A]
    {S : Type v} [CommMonoid S] {T' T : FineSaturatedLogScheme.{max u v}}
    (h : EtaleLogHom T' T)
    (q : (T.scheme ⟶ Spec (.of A)) ×
      (S →* T.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 T.scheme))))) :
    (T'.scheme ⟶ Spec (.of A)) ×
      (S →* T'.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 T'.scheme)))) :=
  (h.base ≫ q.1,
    (h.sectionMap (Scheme.Etale.mk (𝟙 T.scheme)) (Scheme.Etale.mk (𝟙 T'.scheme)) h.base
      ((Category.comp_id _).trans (Category.id_comp _).symm)).comp q.2)

/-- The saturated affine chart is fs and represents compatible prelog charts on fs tests.
Injectivity and the specified range state the bijection for the prescribed forward map.
`CompEq` states naturality for log composition. The final `BijOn` is the restriction to
an arbitrary base open: maps to the inverse-image open are maps to `C` whose image lies
there, with its restricted log structure; their pairs are exactly those landing in the
base open. Empty opens are included.

Source: ILO VIII 3.1.17, p.101; X, proof of Theorem 3.5, Step 6, p.164.
Proof (the agent-supplied six-step argument recorded in the node):
1. The image of `S` generates its completion. The root subset is a submonoid with the
   same group completion and is saturated, even with torsion. The assumed finite
   generation makes it fs (`def-trf-fs-log-blowup`).
2. Noetherianity of `B` makes its spectrum locally Noetherian (`pqf-def-locnoeth`).
   The associated-log stalk pushouts give a chart by this fs monoid, hence an fs log
   scheme (`lem-trf-associated-log-universal-stalks`), also when `B` is zero.
3. For an fs test the global log sections are integral and saturated
   (`lem-per-fs-log-sections-saturated`). Extend the chart into their group completion;
   saturation places the images of all roots in the monoid. Injectivity gives a unique
   extension. Uniqueness uses generation of the completion, not uniqueness of nth roots.
4. Send `a ⊗ zᵖ` to `v♯(a) α_T(λ̃(p))`. Compatibility makes this tensor-balanced;
   multiplication and the unit are preserved. Tensor generation proves uniqueness
   (`def-weil-pbc-module-tensor-product`). The affine adjunction gives the unique
   scheme map (`lem-a1-locally-ringed-space-affine-adjunction`).
5. The arbitrary-scheme-map chart bijection of
   `lem-per-integral-chart-logification-thickening`, identified with the associated
   log presentation, supplies the unique log map with this extended chart.
6. Starting with a log map, uniqueness in Steps 3--5 recovers both its scheme and log
   maps. Pullback along log morphisms and restriction to base opens preserve the chart
   and the tensor formula, so the same uniqueness proves both naturality clauses.
(blueprint: lem-per-prelog-chart-fs-universal). -/
theorem prelogChart_fs_universal (A : Type (max u v)) [CommRing A] [IsNoetherianRing A]
    (S : Type v) [CommMonoid S] (hS : Monoid.FG S) (β : S →* A)
    (hP : Monoid.FG (prelogChartMonoid S)) [IsNoetherianRing (prelogChartRing β)] :
    ∃ (L : EtaleLogStructure (Spec (.of (prelogChartRing β))))
      (η : associatedLogPresheaf (prelogChartBeta β) ⟶ L.monoidSheaf.obj)
      (hN : IsLocallyNoetherian (Spec (.of (prelogChartRing β))))
      (hfs : L.IsFineSaturated),
      IsAssociatedLogPresentation (prelogChartBeta β) L η ∧
      (∀ T : FineSaturatedLogScheme.{max u v},
        Function.Injective (prelogChartExtract β L η hN hfs T) ∧
        Set.range (prelogChartExtract β L η hN hfs T) =
          {q | prelogChartCompatible β T q}) ∧
      (∀ (T' T : FineSaturatedLogScheme.{max u v})
        (h : EtaleLogHom T' T) (F : EtaleLogHom T (prelogChartLogScheme β L hN hfs))
        (H : EtaleLogHom T' (prelogChartLogScheme β L hN hfs)), h.CompEq F H →
          prelogChartExtract β L η hN hfs T' H =
            prelogChartPullbackPair h (prelogChartExtract β L η hN hfs T F)) ∧
      ∀ (U : (Spec (.of A)).Opens) (T : FineSaturatedLogScheme.{max u v}),
        Set.BijOn (prelogChartExtract β L η hN hfs T)
          {F | Set.range F.base.base ⊆ (prelogChartProjection β).base ⁻¹' (U : Set _)}
          {q | prelogChartCompatible β T q ∧ Set.range q.1.base ⊆ (U : Set _)} := by
  sorry

end AlgebraicGeometry
