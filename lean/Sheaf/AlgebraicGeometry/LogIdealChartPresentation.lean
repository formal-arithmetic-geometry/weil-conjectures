/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Presentations of fine logarithmic ideal charts

Source: ILO VI 1.1; VIII 3.1.17--3.1.21, 3.3.5--3.3.9 and 3.4.2
(blueprint: def-trf-log-ideal-chart-presentation).

`EtaleLogMap` extends the recorded fs-only morphism interface to arbitrary log structures.
The chart monoids use multiplicative notation: `h / e` is the additive difference `h - e`.
All monoid algebras and tensor rings below are actual constructions.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Log morphisms without an fs restriction on their endpoints. This is the same relative
étale-test presentation as `EtaleLogHom`. Source: ILO VI 1.1, VIII 3.3.8
(blueprint: def-trf-log-ideal-chart-presentation). -/
structure EtaleLogMap {Y X : Scheme.{u}} (N : EtaleLogStructure Y)
    (M : EtaleLogStructure X) where
  base : Y ⟶ X
  sectionMap : ∀ (W : X.Etale) (V : Y.Etale)
    (k : V.left ⟶ W.left) (_hk : k ≫ W.hom = V.hom ≫ base),
    M.monoidSheaf.obj.obj (op W) →* N.monoidSheaf.obj.obj (op V)
  naturality : ∀ (W₁ W₂ : X.Etale) (V₁ V₂ : Y.Etale)
    (a : W₁ ⟶ W₂) (c : V₁ ⟶ V₂) (k₁ : V₁.left ⟶ W₁.left)
    (k₂ : V₂.left ⟶ W₂.left)
    (h₁ : k₁ ≫ W₁.hom = V₁.hom ≫ base) (h₂ : k₂ ≫ W₂.hom = V₂.hom ≫ base),
    c.left ≫ k₂ = k₁ ≫ a.left →
      (N.monoidSheaf.obj.map c.op).hom.comp (sectionMap W₂ V₂ k₂ h₂) =
        (sectionMap W₁ V₁ k₁ h₁).comp (M.monoidSheaf.obj.map a.op).hom
  compatibility : ∀ (W : X.Etale) (V : Y.Etale)
    (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ base)
    (s : M.monoidSheaf.obj.obj (op W)),
    N.alpha.app (op V) (sectionMap W V k hk s) = k.appTop (M.alpha.app (op W) s)

/-- The recorded fs morphism as a general log morphism, without changing its data.
Source: ILO VI 1.1 (blueprint: def-trf-log-ideal-chart-presentation). -/
def EtaleLogHom.toLogMap {Y X : FineSaturatedLogScheme.{u}} (f : EtaleLogHom Y X) :
    EtaleLogMap Y.logStructure X.logStructure where
  base := f.base
  sectionMap := f.sectionMap
  naturality := f.naturality
  compatibility := f.compatibility

/-- Equality with a composite, including the monoid sheaf maps. Source: ILO VIII 3.3.8
(blueprint: def-trf-log-ideal-chart-presentation). -/
def EtaleLogMap.CompEq {Z Y X : Scheme.{u}} {L : EtaleLogStructure Z}
    {N : EtaleLogStructure Y} {M : EtaleLogStructure X}
    (h : EtaleLogMap L N) (b : EtaleLogMap N M) (f : EtaleLogMap L M) : Prop :=
  h.base ≫ b.base = f.base ∧
    ∀ (W : X.Etale) (V : Y.Etale) (T : Z.Etale)
      (k : V.left ⟶ W.left) (l : T.left ⟶ V.left) (m : T.left ⟶ W.left)
      (hk : k ≫ W.hom = V.hom ≫ b.base)
      (hl : l ≫ V.hom = T.hom ≫ h.base) (hm : m ≫ W.hom = T.hom ≫ f.base),
      l ≫ k = m → (h.sectionMap V T l hl).comp (b.sectionMap W V k hk) =
        f.sectionMap W T m hm

/-- Sheaf-local ideal pullback for a general log morphism. It agrees with the recorded
fs pullback formula. Source: ILO VIII 3.3.7--3.3.8
(blueprint: def-trf-log-ideal-chart-presentation). -/
def EtaleLogMap.pullbackIdeal {Y X : Scheme.{u}} {N : EtaleLogStructure Y}
    {M : EtaleLogStructure X} (f : EtaleLogMap N M) (I : M.IdealFamily) : N.IdealFamily :=
  fun U ↦ {s | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (w : (Scheme.pointSmallEtale t).fiber.obj U),
    ∃ (W : X.Etale) (V : Y.Etale) (v : (Scheme.pointSmallEtale t).fiber.obj V)
      (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ f.base)
      (a : M.monoidSheaf.obj.obj (op W)) (n : N.toEtalePrelogStructure.stalk t),
      a ∈ I W ∧ N.toEtalePrelogStructure.germ t V v (f.sectionMap W V k hk a) * n =
        N.toEtalePrelogStructure.germ t U w s}


/-- The fine universal property: the center is principal and every fine test object with
principal pulled-back ideal has a unique log lift. Source: ILO VIII 3.3.8
(blueprint: def-trf-log-ideal-chart-presentation). -/
def EtaleLogMap.IsFinePrincipalization {Y X : Scheme.{u}} {N : EtaleLogStructure Y}
    {M : EtaleLogStructure X} (b : EtaleLogMap N M) (I : M.IdealFamily) : Prop :=
  N.IsFine ∧ N.IsInvertibleIdeal (b.pullbackIdeal I) ∧
    ∀ (T : Scheme.{u}) (L : EtaleLogStructure T), L.IsFine →
      ∀ f : EtaleLogMap L M, L.IsInvertibleIdeal (f.pullbackIdeal I) →
        ∃! h : EtaleLogMap L N, h.CompEq b f

/-- For an étale underlying map, strictness says that the log sheaf on each relative
étale object is exactly the restriction of the target log sheaf. Its structural ring on
that object is already the same, so this is the associated inverse-image log structure.
Source: ILO VIII 3.3.4(ii), 3.3.8 (blueprint: def-trf-log-ideal-chart-presentation). -/
def EtaleLogMap.IsStrictEtale {Y X : Scheme.{u}} {N : EtaleLogStructure Y}
    {M : EtaleLogStructure X} (f : EtaleLogMap N M) : Prop :=
  ∃ h : Etale f.base,
    ∀ (V : Y.Etale),
      Function.Bijective
        (f.sectionMap (@Scheme.Etale.mk _ _ (V.hom ≫ f.base) (by
          have := h
          infer_instance)) V (𝟙 V.left) (by simp))

/-- An ideal chart monoid inside the canonical group completion. Source: ILO VIII 3.1.19
(blueprint: def-trf-log-ideal-chart-presentation). -/
def logIdealChartMonoid {P : Type u} [CommMonoid P] (E : Finset P) (e : P) :
    Submonoid (Algebra.GrothendieckGroup P) :=
  Submonoid.closure (Set.range (Algebra.GrothendieckGroup.of (M := P)) ∪
    {g | ∃ h ∈ E, g = Algebra.GrothendieckGroup.of h / Algebra.GrothendieckGroup.of e})

/-- The saturated chart is constructed by adjoining all roots. The main chart theorem
identifies this closure with the root subset itself. Source: ILO VIII 3.1.17, 3.1.21
(blueprint: def-trf-log-ideal-chart-presentation). -/
def logIdealSaturatedChartMonoid {P : Type u} [CommMonoid P] (E : Finset P) (e : P) :
    Submonoid (Algebra.GrothendieckGroup P) :=
  Submonoid.closure ((logIdealChartMonoid E e : Set (Algebra.GrothendieckGroup P)) ∪
    {g | ∃ n : ℕ, 0 < n ∧ g ^ n ∈ logIdealChartMonoid E e})

/-- The inclusion of the original chart into the fraction chart. Source: ILO VIII 3.1.19
(blueprint: def-trf-log-ideal-chart-presentation). -/
def logIdealChartInclusion {P : Type u} [CommMonoid P] (E : Finset P) (e : P) :
    P →* logIdealChartMonoid E e :=
  (Algebra.GrothendieckGroup.of (M := P)).codRestrict _
    (fun p ↦ Submonoid.subset_closure (Or.inl ⟨p, rfl⟩))

/-- The inclusion of the original chart into the saturated fraction chart.
Source: ILO VIII 3.1.21 (blueprint: def-trf-log-ideal-chart-presentation). -/
def logIdealSaturatedChartInclusion {P : Type u} [CommMonoid P] (E : Finset P) (e : P) :
    P →* logIdealSaturatedChartMonoid E e :=
  (Algebra.GrothendieckGroup.of (M := P)).codRestrict _
    (fun p ↦ Submonoid.subset_closure (Or.inl (logIdealChartInclusion E e p).property))

/-- The actual tensor chart ring `A ⊗[ℤ[P]] ℤ[Q]`, with the two canonical scalar maps.
Source: ILO VIII 3.3.5--3.3.8 (blueprint: def-trf-log-ideal-chart-presentation). -/
noncomputable abbrev logIdealTensorRing {P Q : Type u} [CommMonoid P] [CommMonoid Q]
    (A : Type u) [CommRing A] (α : P →* A) (i : P →* Q) : Type u :=
  letI := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ i).toAlgebra
  TensorProduct (MonoidAlgebra ℤ P) A (MonoidAlgebra ℤ Q)

/-- The ring structure on the tensor presentation. Source: ILO VIII 3.3.5
(blueprint: def-trf-log-ideal-chart-presentation). -/
noncomputable instance logIdealTensorRing.commRing {P Q : Type u}
    [CommMonoid P] [CommMonoid Q] (A : Type u) [CommRing A] (α : P →* A) (i : P →* Q) :
    CommRing (logIdealTensorRing A α i) := by
  letI := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ i).toAlgebra
  exact inferInstanceAs (CommRing (TensorProduct (MonoidAlgebra ℤ P) A (MonoidAlgebra ℤ Q)))

/-- The structure map from `A` to its tensor chart. Source: ILO VIII 3.3.5
(blueprint: def-trf-log-ideal-chart-presentation). -/
noncomputable def logIdealTensorBase {P Q : Type u} [CommMonoid P] [CommMonoid Q]
    (A : Type u) [CommRing A] (α : P →* A) (i : P →* Q) :
    A →+* logIdealTensorRing A α i := by
  letI := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ i).toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom

/-- The canonical monomials `1 ⊗ z^q`. Source: ILO VIII 3.3.5
(blueprint: def-trf-log-ideal-chart-presentation). -/
noncomputable def logIdealTensorMonomial {P Q : Type u} [CommMonoid P] [CommMonoid Q]
    (A : Type u) [CommRing A] (α : P →* A) (i : P →* Q) :
    Q →* logIdealTensorRing A α i := by
  letI := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  letI := (MonoidAlgebra.mapDomainRingHom ℤ i).toAlgebra
  exact (Algebra.TensorProduct.includeRight.toRingHom.toMonoidHom).comp
    (MonoidAlgebra.of ℤ Q)

/-- An fs chart on an affine étale test object, together with finite nonempty generators
of the coherent log ideal. Equality of the generated ideals is sheaf-local, on geometric
stalks. Source: ILO VIII 3.3.7, 3.4.2
(blueprint: def-trf-log-ideal-chart-presentation). -/
structure LogIdealAffineChart (Y : FineSaturatedLogScheme.{u})
    (I : Y.logStructure.IdealFamily) where
  W : Y.scheme.Etale
  A : Type u
  ring : CommRing A
  affine : W.left ≅ Spec (.of A)
  P : Type u
  monoid : CommMonoid P
  fs : @IsFineSaturatedMonoid P monoid
  chart : P →* Y.logStructure.monoidSheaf.obj.obj (op W)
  isChart : Y.logStructure.IsChart W chart
  generators : Finset P
  nonempty : generators.Nonempty
  generates : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Y.scheme) (w : (Scheme.pointSmallEtale t).fiber.obj W),
    Y.logStructure.idealStalk I t = {m | ∃ p ∈ generators,
      ∃ n : Y.logStructure.toEtalePrelogStructure.stalk t,
        Y.logStructure.toEtalePrelogStructure.germ t W w (chart p) * n = m}

attribute [instance] LogIdealAffineChart.ring LogIdealAffineChart.monoid

/-- The monoid-to-ring map of an affine log chart. Source: ILO VIII 3.3.7
(blueprint: def-trf-log-ideal-chart-presentation). -/
noncomputable def LogIdealAffineChart.alpha {Y : FineSaturatedLogScheme.{u}}
    {I : Y.logStructure.IdealFamily} (C : LogIdealAffineChart Y I) : C.P →* C.A :=
  (Scheme.ΓSpecIso (.of C.A)).hom.hom.toMonoidHom.comp
    (C.affine.inv.appTop.hom.toMonoidHom.comp
      ((Y.logStructure.alpha.app (op C.W)).hom.comp C.chart))

/-- The chart ideal pulled back to any affine test chart. Source: ILO VIII 3.4.2
(blueprint: def-trf-log-ideal-chart-presentation). -/
def LogIdealAffineChart.ringIdeal {Y : FineSaturatedLogScheme.{u}}
    {I : Y.logStructure.IdealFamily} (C : LogIdealAffineChart Y I) : Ideal C.A :=
  Ideal.span (C.alpha '' (C.generators : Set C.P))

/-- The fs universal property on arbitrary fs test log structures, including those
whose underlying scheme is not locally Noetherian. Source: ILO VIII 3.3.9
(blueprint: def-trf-log-ideal-chart-presentation). -/
def EtaleLogMap.IsFSPrincipalization {Y X : Scheme.{u}} {N : EtaleLogStructure Y}
    {M : EtaleLogStructure X} (b : EtaleLogMap N M) (I : M.IdealFamily) : Prop :=
  N.IsFineSaturated ∧ N.IsInvertibleIdeal (b.pullbackIdeal I) ∧
    ∀ (T : Scheme.{u}) (L : EtaleLogStructure T), L.IsFineSaturated →
      ∀ f : EtaleLogMap L M, L.IsInvertibleIdeal (f.pullbackIdeal I) →
        ∃! h : EtaleLogMap L N, h.CompEq b f

/-- A cover of a strict étale restriction by the specified tensor charts. The overlap
formula identifies their intersections with the common principal localizations. Each
chart log structure is associated to the displayed monomials, and its map to the base
is induced by the original `P` chart. Thus these are log charts, not only scheme charts.
Source: ILO VIII 3.1.19, 3.3.5--3.3.9
(blueprint: def-trf-log-ideal-chart-presentation). -/
structure LogIdealTensorCover {Y : FineSaturatedLogScheme.{u}}
    {I : Y.logStructure.IdealFamily} (C : LogIdealAffineChart Y I)
    {Z : Scheme.{u}} {N : EtaleLogStructure Z} (b : EtaleLogMap N Y.logStructure)
    (Q : {e : C.P // e ∈ C.generators} → Submonoid (Algebra.GrothendieckGroup C.P))
    (i : ∀ e, C.P →* Q e) where
  inclusion : ∀ e p, (i e p).val = Algebra.GrothendieckGroup.of p
  toPullback : ∀ e, Spec (.of (logIdealTensorRing C.A C.alpha (i e))) ⟶
    pullback b.base C.W.hom
  openImmersion : ∀ e, IsOpenImmersion (toPullback e)
  covers : ∀ x : pullback (C := Scheme.{u}) b.base C.W.hom,
    ∃ e, ∃ y, toPullback e y = x
  baseMap : ∀ e, toPullback e ≫ pullback.snd b.base C.W.hom =
    Spec.map (CommRingCat.ofHom (logIdealTensorBase C.A C.alpha (i e))) ≫ C.affine.inv
  etale : ∀ e, Etale (toPullback e ≫ pullback.fst b.base C.W.hom)
  chart : ∀ e, Q e →* N.monoidSheaf.obj.obj
    (op (@Scheme.Etale.mk _ _ (toPullback e ≫ pullback.fst b.base C.W.hom) (etale e)))
  isChart : ∀ e, N.IsChart
    (@Scheme.Etale.mk _ _ (toPullback e ≫ pullback.fst b.base C.W.hom) (etale e)) (chart e)
  chartAlpha : ∀ e q,
    N.alpha.app
      (op (@Scheme.Etale.mk _ _ (toPullback e ≫ pullback.fst b.base C.W.hom) (etale e)))
      (chart e q) = (Scheme.ΓSpecIso (.of (logIdealTensorRing C.A C.alpha (i e)))).inv
        (logIdealTensorMonomial C.A C.alpha (i e) q)
  chartMap : ∀ e,
    (b.sectionMap C.W
      (@Scheme.Etale.mk _ _ (toPullback e ≫ pullback.fst b.base C.W.hom) (etale e))
      (toPullback e ≫ pullback.snd b.base C.W.hom) (by
        change toPullback e ≫ pullback.snd b.base C.W.hom ≫ C.W.hom =
          (toPullback e ≫ pullback.fst b.base C.W.hom) ≫ b.base
        rw [Category.assoc, pullback.condition])).comp C.chart = (chart e).comp (i e)
  difference : ∀ e _f : {e : C.P // e ∈ C.generators}, Q e
  difference_val : ∀ e f, (difference e f).val =
    Algebra.GrothendieckGroup.of f.val / Algebra.GrothendieckGroup.of e.val
  overlap : ∀ e f, Set.range (toPullback e) ∩ Set.range (toPullback f) =
    (toPullback e) '' ((Spec (.of (logIdealTensorRing C.A C.alpha (i e)))).basicOpen
      ((Scheme.ΓSpecIso (.of (logIdealTensorRing C.A C.alpha (i e)))).inv
        (logIdealTensorMonomial C.A C.alpha (i e) (difference e f))) : Set _)

end AlgebraicGeometry
