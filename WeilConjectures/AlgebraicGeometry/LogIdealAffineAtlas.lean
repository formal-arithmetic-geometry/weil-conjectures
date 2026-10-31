/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LogIdealChartPresentation
public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup
public import WeilConjectures.AlgebraicGeometry.FineLogEtaleDescentDatum
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Affine tensor atlases for logarithmic ideals

Source: ILO VIII 3.1.19, 3.3.5--3.3.9
(blueprint: def-trf-log-ideal-affine-atlas).

This presentation permits a fine integral base monoid, without imposing saturation or
Noetherian hypotheses on the coefficient ring. All tensor rings are the recorded constructions.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Pull a global chart section along a log morphism. Source: ILO VI 1.1, VIII 3.3.8
(blueprint: def-trf-log-ideal-affine-atlas). -/
def EtaleLogMap.globalChart {X Y : Scheme.{u}} {M : EtaleLogStructure X}
    {N : EtaleLogStructure Y} (b : EtaleLogMap N M) {P : Type u} [CommMonoid P]
    (c : P →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    P →* N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) :=
  (b.sectionMap (Scheme.Etale.mk (𝟙 X)) (Scheme.Etale.mk (𝟙 Y)) b.base (by
    change b.base ≫ 𝟙 X = 𝟙 Y ≫ b.base
    rw [Category.comp_id, Category.id_comp])).comp c

/-- The geometric germ of a pulled-back global chart. Source: ILO VIII 3.3.7--3.3.8
(blueprint: def-trf-log-ideal-affine-atlas). -/
noncomputable def EtaleLogMap.chartGerm {X Y : Scheme.{u}} {M : EtaleLogStructure X}
    {N : EtaleLogStructure Y} (b : EtaleLogMap N M) {P : Type u} [CommMonoid P]
    (c : P →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y) :
    P →* N.toEtalePrelogStructure.stalk t :=
  (N.toEtalePrelogStructure.germ t (Scheme.Etale.mk (𝟙 Y))
    (Over.homMk t (Category.comp_id t))).hom.comp (b.globalChart c)

/-- Open affine tensor charts, their associated log charts, exact monomial overlaps,
and distinguished generators. The base chart is not required to be fs.
The overlap transition is the one inside the global log structure: the maps from `P`
agree, so their extensions to the common fraction monoid agree as well.
Source: ILO VIII 3.1.19, 3.3.5--3.3.9
(blueprint: def-trf-log-ideal-affine-atlas). -/
structure LogIdealAffineAtlas {A P : Type u} [CommRing A] [CommMonoid P]
    (α : P →* A) (E : Finset P) {M : EtaleLogStructure (Spec (.of A))}
    (c : P →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of A))))))
    {X : Scheme.{u}} {N : EtaleLogStructure X} (b : EtaleLogMap N M)
    (Q : {e : P // e ∈ E} → Submonoid (Algebra.GrothendieckGroup P))
    (i : ∀ e, P →* Q e) where
  inclusion : ∀ e p, (i e p).val = Algebra.GrothendieckGroup.of p
  j : ∀ e, Spec (.of (logIdealTensorRing A α (i e))) ⟶ X
  openImmersion : ∀ e, IsOpenImmersion (j e)
  covers : ∀ x : X, ∃ e, ∃ y, j e y = x
  overBase : ∀ e, j e ≫ b.base =
    Spec.map (CommRingCat.ofHom (logIdealTensorBase A α (i e)))
  etale : ∀ e, Etale (j e)
  chart : ∀ e, Q e →* N.monoidSheaf.obj.obj
    (op (@Scheme.Etale.mk _ _ (j e) (etale e)))
  isChart : ∀ e, N.IsChart (@Scheme.Etale.mk _ _ (j e) (etale e)) (chart e)
  chartAlpha : ∀ e q,
    N.alpha.app (op (@Scheme.Etale.mk _ _ (j e) (etale e))) (chart e q) =
      (Scheme.ΓSpecIso (.of (logIdealTensorRing A α (i e)))).inv
        (logIdealTensorMonomial A α (i e) q)
  chartMap : ∀ e,
    (b.sectionMap (Scheme.Etale.mk (𝟙 (Spec (.of A))))
      (@Scheme.Etale.mk _ _ (j e) (etale e)) (j e ≫ b.base) (by
        change (j e ≫ b.base) ≫ 𝟙 _ = j e ≫ b.base
        exact Category.comp_id _)).comp c =
        (chart e).comp (i e)
  difference : ∀ e _f : {e : P // e ∈ E}, Q e
  difference_val : ∀ e f, (difference e f).val =
    Algebra.GrothendieckGroup.of f.val / Algebra.GrothendieckGroup.of e.val
  overlap : ∀ e f, Set.range (j e) ∩ Set.range (j f) =
    (j e) '' ((Spec (.of (logIdealTensorRing A α (i e)))).basicOpen
      ((Scheme.ΓSpecIso (.of (logIdealTensorRing A α (i e)))).inv
        (logIdealTensorMonomial A α (i e) (difference e f))) : Set _)
  principal : ∀ (e : {e : P // e ∈ E}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (_w : (Scheme.pointSmallEtale t).fiber.obj
      (@Scheme.Etale.mk _ _ (j e) (etale e))) (h : P), h ∈ E →
    ∃ n : N.toEtalePrelogStructure.stalk t, b.chartGerm c t h = b.chartGerm c t e.val * n

/-- Each generator chart is exactly its geometric generator locus. Equivalently this
specifies the underlying ordinary-point locus, since every point has a geometric lift.
Source: ILO VIII 3.1.19 and 3.3.8
(blueprint: def-trf-log-ideal-affine-atlas). -/
def LogIdealAffineAtlas.GeneratorLoci {A P : Type u} [CommRing A] [CommMonoid P]
    {α : P →* A} {E : Finset P} {M : EtaleLogStructure (Spec (.of A))}
    {c : P →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of A)))))}
    {X : Scheme.{u}} {N : EtaleLogStructure X} {b : EtaleLogMap N M}
    {Q : {e : P // e ∈ E} → Submonoid (Algebra.GrothendieckGroup P)}
    {i : ∀ e, P →* Q e} (D : LogIdealAffineAtlas α E c b Q i) : Prop :=
  ∀ (e : {e : P // e ∈ E}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X),
    (Scheme.SpecToEquivOfField Ω X t).1 ∈ Set.range (D.j e) ↔
      ∀ h ∈ E, ∃ n : N.toEtalePrelogStructure.stalk t,
        b.chartGerm c t h = b.chartGerm c t e.val * n

/-- Normalization of a tensor-ring homomorphism on coefficients and monomials. These
conditions uniquely determine it by the actual tensor and monoid-algebra presentations.
Source: ILO VIII 3.3.5 (blueprint: def-trf-log-ideal-affine-atlas). -/
def LogIdealTensorRingMap {A A' P Q Q' : Type u} [CommRing A] [CommRing A']
    [CommMonoid P] [CommMonoid Q] [CommMonoid Q']
    (α : P →* A) (α' : P →* A') (i : P →* Q) (i' : P →* Q')
    (ρ : A →+* A') (k : Q →* Q')
    (φ : logIdealTensorRing A α i →+* logIdealTensorRing A' α' i') : Prop :=
  φ.comp (logIdealTensorBase A α i) = (logIdealTensorBase A' α' i').comp ρ ∧
    ∀ q, φ (logIdealTensorMonomial A α i q) = logIdealTensorMonomial A' α' i' (k q)

/-- Canonical chart comparison, with the full log chart equation and Cartesian squares.
Source: ILO VIII 3.1.17, 3.3.9
(blueprint: def-trf-log-ideal-affine-atlas). -/
def LogIdealAffineAtlas.Comparison {A P : Type u} [CommRing A] [CommMonoid P]
    {α : P →* A} {E : Finset P} {M : EtaleLogStructure (Spec (.of A))}
    {c : P →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of A)))))}
    {X₀ Xₛ : Scheme.{u}} {N₀ : EtaleLogStructure X₀} {Nₛ : EtaleLogStructure Xₛ}
    {b₀ : EtaleLogMap N₀ M} {bₛ : EtaleLogMap Nₛ M}
    {Q₀ Qₛ : {e : P // e ∈ E} → Submonoid (Algebra.GrothendieckGroup P)}
    {i₀ : ∀ e, P →* Q₀ e} {iₛ : ∀ e, P →* Qₛ e}
    (D₀ : LogIdealAffineAtlas α E c b₀ Q₀ i₀)
    (Dₛ : LogIdealAffineAtlas α E c bₛ Qₛ iₛ) (s : EtaleLogMap Nₛ N₀) : Prop :=
  s.CompEq b₀ bₛ ∧ ∀ e,
    ∃ (k : Q₀ e →* Qₛ e)
      (φ : logIdealTensorRing A α (i₀ e) →+* logIdealTensorRing A α (iₛ e))
      (hw : Spec.map (CommRingCat.ofHom φ) ≫ D₀.j e = Dₛ.j e ≫ s.base),
      (∀ q : Q₀ e, (k q).val = q.val) ∧
      LogIdealTensorRingMap α α (i₀ e) (iₛ e) (RingHom.id A) k φ ∧
      IsPullback (Spec.map (CommRingCat.ofHom φ)) (Dₛ.j e) (D₀.j e) s.base ∧
      (s.sectionMap (@Scheme.Etale.mk _ _ (D₀.j e) (D₀.etale e))
        (@Scheme.Etale.mk _ _ (Dₛ.j e) (Dₛ.etale e))
        (Spec.map (CommRingCat.ofHom φ)) hw).comp (D₀.chart e) = (Dₛ.chart e).comp k

/-- A strict étale change of the base chart, with its ordinary Cartesian log pullback
and the specified coefficient/monomial maps on every affine chart. Thus both the chart
rings and the gluing are transported, not only the underlying finite morphism.
Source: ILO VIII 3.3.5--3.3.9
(blueprint: def-trf-log-ideal-affine-atlas). -/
structure LogIdealAffineAtlas.BaseChange {A P : Type u} [CommRing A] [CommMonoid P]
    {α : P →* A} {E : Finset P} {M : EtaleLogStructure (Spec (.of A))}
    {c : P →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of A)))))}
    {X : Scheme.{u}} {N : EtaleLogStructure X} {b : EtaleLogMap N M}
    {Q : {e : P // e ∈ E} → Submonoid (Algebra.GrothendieckGroup P)}
    {i : ∀ e, P →* Q e} (D : LogIdealAffineAtlas α E c b Q i)
    {A' : Type u} [CommRing A'] (ρ : A →+* A')
    {M' : EtaleLogStructure (Spec (.of A'))} (f : EtaleLogMap M' M) where
  X' : Scheme.{u}
  N' : EtaleLogStructure X'
  b' : EtaleLogMap N' M'
  q : EtaleLogMap N' N
  total : EtaleLogMap N' M
  overLeft : q.CompEq b total
  overRight : b'.CompEq f total
  cartesian : IsPullback q.base b'.base b.base f.base
  strict : q.IsStrictEtale
  atlas : LogIdealAffineAtlas (ρ.toMonoidHom.comp α) E (f.globalChart c) b' Q i
  chartSquares : ∀ e,
    ∃ φ : logIdealTensorRing A α (i e) →+*
      logIdealTensorRing A' (ρ.toMonoidHom.comp α) (i e),
      LogIdealTensorRingMap α (ρ.toMonoidHom.comp α) (i e) (i e) ρ
        (MonoidHom.id (Q e)) φ ∧
      IsPullback (Spec.map (CommRingCat.ofHom φ)) (atlas.j e) (D.j e) q.base

/-- Finite translates of an ideal chart monoid in its root saturation, written
multiplicatively. Source: ILO VIII 3.1.17, 3.2.9
(blueprint: def-trf-log-ideal-affine-atlas). -/
def LogIdealSaturationTranslates {P : Type u} [CommMonoid P] (E : Finset P) (e : P)
    (F : Finset (logIdealSaturatedChartMonoid E e)) : Prop :=
  ∀ q : logIdealSaturatedChartMonoid E e, ∃ f ∈ F,
    ∃ p : logIdealChartMonoid E e, q.val = f.val * p.val

/-- The monomial module-spanning assertion for every finite translate set, with existence
of such a set. The displayed finite sums express generation over the unsaturated tensor
ring, using the canonically normalized comparison ring map. No injectivity is imposed.
Source: ILO VIII 3.2.9, finiteness sentence
(blueprint: def-trf-log-ideal-affine-atlas). -/
def LogIdealSaturationSpanning {A P : Type u} [CommRing A] [CommMonoid P]
    (α : P →* A) (E : Finset P) : Prop :=
  ∀ e : {e : P // e ∈ E},
    (∃ F : Finset (logIdealSaturatedChartMonoid E e.val),
      LogIdealSaturationTranslates E e.val F) ∧
    ∀ F : Finset (logIdealSaturatedChartMonoid E e.val),
      LogIdealSaturationTranslates E e.val F →
      ∀ (k : logIdealChartMonoid E e.val →* logIdealSaturatedChartMonoid E e.val)
        (φ : logIdealTensorRing A α (logIdealChartInclusion E e.val) →+*
          logIdealTensorRing A α (logIdealSaturatedChartInclusion E e.val)),
        (∀ q : logIdealChartMonoid E e.val, (k q).val = q.val) →
        LogIdealTensorRingMap α α (logIdealChartInclusion E e.val)
          (logIdealSaturatedChartInclusion E e.val) (RingHom.id A) k φ →
        ∀ z : logIdealTensorRing A α (logIdealSaturatedChartInclusion E e.val),
          ∃ a : ↥F → logIdealTensorRing A α (logIdealChartInclusion E e.val),
            z = ∑ f : ↥F, φ (a f) *
              logIdealTensorMonomial A α (logIdealSaturatedChartInclusion E e.val) f.val

/-- The finite comparison property, including full affine inverse images and the exact
inverse-image equality of generator charts. Source: ILO VIII 3.3.9; Stacks, Tag 01WH
(blueprint: def-trf-log-ideal-affine-atlas). -/
def LogIdealAffineAtlas.FiniteComparison {A P : Type u} [CommRing A] [CommMonoid P]
    {α : P →* A} {E : Finset P} {M : EtaleLogStructure (Spec (.of A))}
    {c : P →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of A)))))}
    {X₀ Xₛ : Scheme.{u}} {N₀ : EtaleLogStructure X₀} {Nₛ : EtaleLogStructure Xₛ}
    {b₀ : EtaleLogMap N₀ M} {bₛ : EtaleLogMap Nₛ M}
    {Q₀ Qₛ : {e : P // e ∈ E} → Submonoid (Algebra.GrothendieckGroup P)}
    {i₀ : ∀ e, P →* Q₀ e} {iₛ : ∀ e, P →* Qₛ e}
    (D₀ : LogIdealAffineAtlas α E c b₀ Q₀ i₀)
    (Dₛ : LogIdealAffineAtlas α E c bₛ Qₛ iₛ) (s : EtaleLogMap Nₛ N₀) : Prop :=
  D₀.Comparison Dₛ s ∧
    (∀ e, s.base ⁻¹' Set.range (D₀.j e) = Set.range (Dₛ.j e)) ∧
    IsFinite s.base ∧
    ∀ (U : X₀.Opens), IsAffineOpen U →
      IsAffineOpen (s.base ⁻¹ᵁ U) ∧ (s.base.app U).hom.Finite

end AlgebraicGeometry
