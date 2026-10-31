/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedRelativeKunneth
import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
import WeilConjectures.DeligneLaumon.CondensedCoefficientUnit

/-!
# Normalization of compact Künneth on closed sections

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
  thm-pur-vector-bundle-thom.proof.md`, Steps 1 and 2
(blueprint: lem-pur-compact-kunneth-section-unit).

The source isomorphism is the closed direct-image exchange followed by the
compact-support projection formula and the coefficient unitors.  Its compact image is
then compared by the native relative Künneth isomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactKunnethSectionUnit

/-- The pullback lift of the closed section along the product projection.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, Step 1; this is the
base-change section `a : Z_s → P` with coordinates `(g ≫ s, 1)`.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
noncomputable def sectionMap {datum : WeilConjectures.FiniteFieldDatum.{u}}
    (d : RelativeKunneth.Diagram datum.k)
    (s : d.B ⟶ d.X) (_t : d.B ⟶ d.Y)
    (hs : s.hom.left ≫ d.f.hom.left = 𝟙 _) : d.Y ⟶ d.T :=
  SepFinType.homMk (Over.homMk
    (d.cartesian.lift (d.g.hom.left ≫ s.hom.left) (𝟙 _)
      (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp]))
    (by
      rw [← d.q.hom.w, ← Category.assoc, d.cartesian.lift_snd, Category.id_comp]))


/-- Native geometric data for the closed-section normalization.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, opening and Steps 1--2.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
structure Input (datum : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] where
  Λ : ScalarSixRing.{u}
  hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X
  d : RelativeKunneth.Diagram datum.k
  c : RelativeKunneth.Models d
  H : CompactSupportComposition.CoherentData Λ.X datum.k
  family : RelativeKunneth.IsoFamily Λ H
  s : d.B ⟶ d.X
  t : d.B ⟶ d.Y
  u : d.B ⟶ d.T
  hs : s.hom.left ≫ d.f.hom.left = 𝟙 _
  ht : t.hom.left ≫ d.g.hom.left = 𝟙 _
  hu_p : u.hom.left ≫ d.p.hom.left = s.hom.left
  hu_q : u.hom.left ≫ d.q.hom.left = t.hom.left
  closed_s : IsClosedImmersion s.hom.left
  closed_t : IsClosedImmersion t.hom.left
  closed_u : IsClosedImmersion u.hom.left
  A : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left
  C : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left
  A_spec : A.obj = (CompactificationReindexing.R Λ.X s.hom.left).obj
    (𝟙_ (CompactificationReindexing.D Λ.X d.B.obj.left))
  C_spec : C.obj = (CompactificationReindexing.R Λ.X t.hom.left).obj
    (𝟙_ (CompactificationReindexing.D Λ.X d.B.obj.left))

/-- The tensor unit belongs to the localizing domain of the coherent compositor.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 1.
Proof: the constant rank-one coefficient module in degree zero is constructible and
has Tor amplitude [0,0]; the generating constructible finite-Tor subcategory lies
in its localizing closure.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
theorem unit_localizing (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    (B : SepFinType k) :
    AlgebraicGeometry.ProEtale.localizingClosureProEtale Λ.X B.obj.left
      (𝟙_ (CompactificationReindexing.D Λ.X B.obj.left)) := by
  letI : CompactSpace B.obj.left := QuasiCompact.compactSpace_of_compactSpace B.obj.hom
  letI : QuasiSeparatedSpace B.obj.left := quasiSeparatedSpace_of_quasiSeparated B.obj.hom
  intro P hP hS
  apply hS
  exact condensedCoefficientUnit_mem Λ.X B.obj.left

/-- The unit, bundled in the already defined localizing subcategory.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 1.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
def localizingUnit (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    (B : SepFinType k) :
    (localizingClosureProEtale Λ.X B.obj.left).FullSubcategory :=
  ⟨𝟙_ _, unit_localizing Λ B⟩

/-- Proper comparison for the identity-open compactification: remove the exact
extension by the identity, retaining the ordinary derived direct image.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Steps 3 and 5.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
def properModelIso (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] :
    CompactificationReindexing.F Λ.X (Compactification.ofIsProper f) ≅
      CompactificationReindexing.R Λ.X f :=
  Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ.X X) _ ≪≫
    Functor.leftUnitor _

/-- Proper comparison followed by the coherent compositor, compactification
comparison to the identity model, and the identity normalization. This fixes the
unit identification for a closed section; there is no chosen isomorphism.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 5.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
def sectionUnitIso (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    (H : CompactSupportComposition.CoherentData Λ.X k)
    {B X : SepFinType k} (s : B ⟶ X) (f : X ⟶ B)
    [IsProper s.hom.left] (c : Compactification f.hom.left)
    (hs : s.hom.left ≫ f.hom.left = 𝟙 _) :
    (CompactificationReindexing.F Λ.X c).obj
      ((CompactificationReindexing.R Λ.X s.hom.left).obj (𝟙_ _)) ≅ 𝟙_ _ := by
  letI : IsProper (s.hom.left ≫ f.hom.left) := by rw [hs]; infer_instance
  let cs := Compactification.ofIsProper s.hom.left
  let e := Compactification.ofIsProper (s.hom.left ≫ f.hom.left)
  let eId := (Compactification.ofIsProper (𝟙 B.obj.left)).copy hs
  exact (CompactificationReindexing.F Λ.X c).mapIso
      ((properModelIso Λ s.hom.left).symm.app (𝟙_ _)) ≪≫
    (H.comp s f cs c e).app (localizingUnit Λ B) ≪≫
    (H.comparison (s ≫ f) e eId).app (localizingUnit Λ B) ≪≫
    (CompactSupportComposition.identity Λ.X B.obj.left).app (𝟙_ _)

/-- The fixed identification for `fs=1`, including the equality specifying A.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 5.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
def c_f {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    (CompactificationReindexing.F I.Λ.X I.c.f).obj I.A.obj ≅ 𝟙_ _ := by
  letI : IsClosedImmersion I.s.hom.left := I.closed_s
  letI : IsProper I.s.hom.left := IsProper.of_isClosedImmersion _
  exact (CompactificationReindexing.F I.Λ.X I.c.f).mapIso (eqToIso I.A_spec) ≪≫
    sectionUnitIso I.Λ I.H I.s I.d.f I.c.f I.hs

/-- The fixed identification for `gt=1`, including the equality specifying C.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 5.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
def c_g {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    (CompactificationReindexing.F I.Λ.X I.c.g).obj I.C.obj ≅ 𝟙_ _ := by
  letI : IsClosedImmersion I.t.hom.left := I.closed_t
  letI : IsProper I.t.hom.left := IsProper.of_isClosedImmersion _
  exact (CompactificationReindexing.F I.Λ.X I.c.g).mapIso (eqToIso I.C_spec) ≪≫
    sectionUnitIso I.Λ I.H I.t I.d.g I.c.g I.ht

/-- The fixed identification for `hu=1`, with h represented by q followed by g.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 5.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
def c_h {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    (CompactificationReindexing.F I.Λ.X I.c.total).obj
      ((CompactificationReindexing.R I.Λ.X I.u.hom.left).obj (𝟙_ _)) ≅ 𝟙_ _ := by
  letI : IsClosedImmersion I.u.hom.left := I.closed_u
  letI : IsProper I.u.hom.left := IsProper.of_isClosedImmersion _
  exact sectionUnitIso I.Λ I.H I.u (I.d.q ≫ I.d.g) I.c.total
    (by
      change I.u.hom.left ≫ (I.d.q.hom.left ≫ I.d.g.hom.left) = _
      rw [← Category.assoc, I.hu_q, I.ht])

/-- The first coordinate of the Cartesian lift a is gs.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 1.
Proof: apply the first projection identity of the Cartesian lift.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
theorem sectionMap_p {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    (sectionMap I.d I.s I.t I.hs).hom.left ≫ I.d.p.hom.left =
      I.d.g.hom.left ≫ I.s.hom.left := by
  change I.d.cartesian.lift (I.d.g.hom.left ≫ I.s.hom.left) (𝟙 _) _ ≫
      I.d.p.hom.left = I.d.g.hom.left ≫ I.s.hom.left
  exact I.d.cartesian.lift_fst _ _ _

/-- The second coordinate of a is the identity.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 1.
Proof: apply the second projection identity of the Cartesian lift.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
theorem sectionMap_q {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    (sectionMap I.d I.s I.t I.hs).hom.left ≫ I.d.q.hom.left = 𝟙 _ := by
  change I.d.cartesian.lift (I.d.g.hom.left ≫ I.s.hom.left) (𝟙 _) _ ≫
      I.d.q.hom.left = 𝟙 _
  exact I.d.cartesian.lift_snd _ _ _

/-- The composite t followed by a is the specified product section u.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 1.
Proof: compare both projections into the Cartesian square. The p-coordinate is
`tgs=s` by ht, and the q-coordinate is t; use hu_p and hu_q and pullback uniqueness.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
theorem sectionMap_t {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    I.t.hom.left ≫ (sectionMap I.d I.s I.t I.hs).hom.left = I.u.hom.left := by
  apply I.d.cartesian.hom_ext
  · rw [Category.assoc, sectionMap_p]
    rw [← Category.assoc, I.ht, Category.id_comp, I.hu_p]
  · rw [Category.assoc, sectionMap_q, Category.comp_id, I.hu_q]

/-- The base-changed section is closed.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 1.
Proof: the square with sides g,a,s,p is Cartesian by pullback uniqueness, and a is
the base change of the closed immersion s. Closed immersions are stable under base change.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
theorem sectionMap_closed {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    IsClosedImmersion (sectionMap I.d I.s I.t I.hs).hom.left := by
  let a := sectionMap I.d I.s I.t I.hs
  have hsquare : a.hom.left ≫ I.d.p.hom.left = I.d.g.hom.left ≫ I.s.hom.left :=
    sectionMap_p I
  have hpb : IsPullback a.hom.left I.d.g.hom.left I.d.p.hom.left I.s.hom.left := by
    refine IsPullback.of_isLimit' (CommSq.mk hsquare) ?_
    refine PullbackCone.IsLimit.mk hsquare (fun c ↦ c.fst ≫ I.d.q.hom.left) ?_ ?_ ?_
    · intro c
      apply I.d.cartesian.hom_ext
      · rw [Category.assoc, sectionMap_p]
        calc
          ((c.fst ≫ I.d.q.hom.left) ≫ I.d.g.hom.left) ≫ I.s.hom.left =
              c.fst ≫ ((I.d.q.hom.left ≫ I.d.g.hom.left) ≫ I.s.hom.left) := by
            simp [Category.assoc]
          _ = c.fst ≫ ((I.d.p.hom.left ≫ I.d.f.hom.left) ≫ I.s.hom.left) := by
            rw [I.d.cartesian.w.symm]
          _ = (c.fst ≫ I.d.p.hom.left) ≫
              (I.d.f.hom.left ≫ I.s.hom.left) := by
            simp [Category.assoc]
          _ = (c.snd ≫ I.s.hom.left) ≫
              (I.d.f.hom.left ≫ I.s.hom.left) := by
            rw [c.condition]
          _ = c.snd ≫ I.s.hom.left := by
            have h := congrArg (fun z =>
              c.snd ≫ z ≫ I.s.hom.left) I.hs
            simpa [Category.assoc] using h
          _ = c.fst ≫ I.d.p.hom.left := by
            exact c.condition.symm
      · rw [Category.assoc, sectionMap_q, Category.comp_id]
    · intro c
      calc
        (c.fst ≫ I.d.q.hom.left) ≫ I.d.g.hom.left =
            c.fst ≫ (I.d.q.hom.left ≫ I.d.g.hom.left) := by simp [Category.assoc]
        _ = c.fst ≫ (I.d.p.hom.left ≫ I.d.f.hom.left) := by
          rw [I.d.cartesian.w.symm]
        _ = (c.fst ≫ I.d.p.hom.left) ≫ I.d.f.hom.left := by
          simp [Category.assoc]
        _ = (c.snd ≫ I.s.hom.left) ≫ I.d.f.hom.left := by
          rw [c.condition]
        _ = c.snd := by
          have h := congrArg (fun z => c.snd ≫ z) I.hs
          simpa [Category.assoc] using h
    · intro c m hm₁ hm₂
      calc
        m = m ≫ (a.hom.left ≫ I.d.q.hom.left) := by
          rw [sectionMap_q, Category.comp_id]
        _ = (m ≫ a.hom.left) ≫ I.d.q.hom.left := by simp [Category.assoc]
        _ = c.fst ≫ I.d.q.hom.left := by rw [hm₁]
  exact MorphismProperty.of_isPullback hpb.flip I.closed_s

/-- Proper-normalized H.comp identifies R_a R_t with R_u, using t a = u.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 3.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
def sectionDirectImageComp {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    (CompactificationReindexing.R I.Λ.X (sectionMap I.d I.s I.t I.hs).hom.left).obj
      ((CompactificationReindexing.R I.Λ.X I.t.hom.left).obj (𝟙_ _)) ≅
      (CompactificationReindexing.R I.Λ.X I.u.hom.left).obj (𝟙_ _) := by
  let a := sectionMap I.d I.s I.t I.hs
  letI : IsClosedImmersion a.hom.left := sectionMap_closed I
  letI : IsClosedImmersion I.t.hom.left := I.closed_t
  letI : IsClosedImmersion I.u.hom.left := I.closed_u
  letI : IsProper a.hom.left := IsProper.of_isClosedImmersion _
  letI : IsProper I.t.hom.left := IsProper.of_isClosedImmersion _
  letI : IsProper I.u.hom.left := IsProper.of_isClosedImmersion _
  let ct := Compactification.ofIsProper I.t.hom.left
  let ca := Compactification.ofIsProper a.hom.left
  let cu := Compactification.ofIsProper I.u.hom.left
  exact (CompactificationReindexing.R I.Λ.X a.hom.left).mapIso
      ((properModelIso I.Λ I.t.hom.left).symm.app (𝟙_ _)) ≪≫
    (properModelIso I.Λ a.hom.left).symm.app
      ((CompactificationReindexing.F I.Λ.X ct).obj (𝟙_ _)) ≪≫
    (I.H.comp I.t a ct ca (cu.copy (sectionMap_t I))).app (localizingUnit I.Λ I.d.B) ≪≫
    (properModelIso I.Λ I.u.hom.left).app (𝟙_ _)

/-- Actual closed direct-image exchange on the square with sides g,a,s,p,
followed by the pulled-back coefficient-unit comparison.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 3.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
def closedExchange {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    (CompactificationReindexing.P I.Λ.X I.d.p.hom.left).obj I.A.obj ⟶
      (CompactificationReindexing.R I.Λ.X (sectionMap I.d I.s I.t I.hs).hom.left).obj
        (𝟙_ _) :=
  (CompactificationReindexing.P I.Λ.X I.d.p.hom.left).map (eqToHom I.A_spec) ≫
    (baseChangeMap I.Λ.X (CommSq.mk (sectionMap_p I).symm)).app (𝟙_ _) ≫
    (CompactificationReindexing.R I.Λ.X (sectionMap I.d I.s I.t I.hs).hom.left).map
      (leftDerivedUpperStarUnitIso I.Λ.X I.d.g.hom.left).hom

/-- The displayed exterior-to-R_u composite: closed exchange tensor identity,
proper comparison, the projection formula for a, the tensor unitor, a*q*=1,
C=t_*1, and the proper-normalized compositor R_a R_t=R_u. Theta is its inverse.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 3.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
def exchangeProjection {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    RelativeKunneth.exterior I.Λ I.d I.A.obj I.C.obj ⟶
      (CompactificationReindexing.R I.Λ.X I.u.hom.left).obj (𝟙_ _) := by
  let a := sectionMap I.d I.s I.t I.hs
  letI : IsClosedImmersion a.hom.left := sectionMap_closed I
  letI : IsProper a.hom.left := IsProper.of_isClosedImmersion _
  let ca := Compactification.ofIsProper a.hom.left
  let L := (CompactificationReindexing.P I.Λ.X I.d.q.hom.left).obj I.C.obj
  let M := (CompactificationReindexing.P I.Λ.X a.hom.left).obj L
  exact (closedExchange I ⊗ₘ 𝟙 L) ≫
    ((properModelIso I.Λ a.hom.left).inv.app (𝟙_ _) ⊗ₘ 𝟙 L) ≫
    CompactificationReindexing.pf I.Λ.X ca (𝟙_ _) L ≫
    (properModelIso I.Λ a.hom.left).hom.app ((𝟙_ _) ⊗ M) ≫
    (CompactificationReindexing.R I.Λ.X a.hom.left).map
      ((λ_ M).hom ≫
        (leftDerivedUpperStarComp I.Λ.X a.hom.left I.d.q.hom.left).inv.app I.C.obj ≫
        eqToHom (congrArg (fun f ↦ (CompactificationReindexing.P I.Λ.X f).obj I.C.obj)
          (sectionMap_q I)) ≫
        (leftDerivedUpperStarId I.Λ.X I.d.Y.obj.left).hom.app I.C.obj ≫
        eqToHom I.C_spec) ≫
    (sectionDirectImageComp I).hom

/-- The canonical closed exchange/projection arrow is invertible.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 3.
Proof: proper base change for the closed immersion s makes closedExchange invertible.
The proper projection formula for the closed immersion a is invertible on the
constructible finite-Tor input q*C. All remaining factors are unit comparisons,
geometric equality transports, or the coherent proper compositor, hence isomorphisms.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
theorem exchangeProjection_isIso {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    IsIso (exchangeProjection I) := by
  sorry
/-- The exterior-to-source isomorphism; its inverse is the specified theta.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Steps 2--3.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
def sourceIso {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ} [Fact ell.Prime]
    (I : Input datum ell) :
    RelativeKunneth.exterior I.Λ I.d I.A.obj I.C.obj ≅
      (CompactificationReindexing.R I.Λ.X I.u.hom.left).obj (𝟙_ _) :=
  @asIso _ _ _ _ (exchangeProjection I) (exchangeProjection_isIso I)

/-- The two normalization clauses for the closed source and all supported arrows.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, Steps 6--8.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
structure Conclusion {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) where
  μ : 𝟙_ (CompactificationReindexing.D I.Λ.X I.d.B.obj.left) ⊗
      𝟙_ (CompactificationReindexing.D I.Λ.X I.d.B.obj.left) ≅
    𝟙_ (CompactificationReindexing.D I.Λ.X I.d.B.obj.left)
  μ_spec : μ = λ_ (𝟙_ _)
  clause_one :
    (c_h I).inv ≫
      (CompactificationReindexing.F I.Λ.X I.c.total).map
        (sourceIso I).inv ≫
      (I.family.iso I.d I.c I.A I.C).hom ≫
      ((c_f I).hom ⊗ₘ (c_g I).hom) = (λ_ (𝟙_ _)).inv
  clause_two : ∀
      (K : ConstantModelConstructibleFiniteTor I.Λ.X I.d.X.obj.left)
      (L : ConstantModelConstructibleFiniteTor I.Λ.X I.d.Y.obj.left)
      (a_s : I.A.obj ⟶ K.obj) (a_t : I.C.obj ⟶ L.obj),
    (c_h I).inv ≫
        (CompactificationReindexing.F I.Λ.X I.c.total).map
          ((sourceIso I).inv ≫
            ((CompactificationReindexing.P I.Λ.X I.d.p.hom.left).map a_s ⊗ₘ
              (CompactificationReindexing.P I.Λ.X I.d.q.hom.left).map a_t)) ≫
        (I.family.iso I.d I.c K L).hom =
      μ.inv ≫
        (((c_f I).inv ≫ (CompactificationReindexing.F I.Λ.X I.c.f).map a_s) ⊗ₘ
          ((c_g I).inv ≫ (CompactificationReindexing.F I.Λ.X I.c.g).map a_t))

/-- The compact Künneth comparison is normalized on closed sections.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-vector-bundle-thom.proof.md`, opening and Steps 1--2; the eight-step
expansion is recorded in the node's proof.
(blueprint: lem-pur-compact-kunneth-section-unit)

1. Identify Z_s with Y. The Cartesian lift a has qa=1, pa=gs, and ta=u.
It is the base change of the closed immersion s, hence closed and proper.
The coefficient unit has rank one in degree zero and Tor amplitude zero.
Constructible finite-Tor stability puts the exterior products and compact
images in the required domains over the algebraically closed base field.

2. Evaluate the specified projection map at its second unit input. Transposing
its proper factor along pullback/direct-image adjunction identifies it with
the composite r_(F_v M) followed by F_v(r_M.inv).
The open adjunct and strong monoidal unit axiom give the same normalization.
For the identity map, PF at first input the unit is the identity under unitors.

3. Let z be closedExchange, the actual baseChangeMap for the a-square followed
by the pullback unit comparison. For any D, tensor z with q*D, apply PF_a,
then the left unitor and a*q*=1. At D=C, the proper-normalized H.comp for
t followed by a identifies the target with R_u 1. This is exchangeProjection;
its inverse is theta. Proper base change and the closed projection formula
make these factors invertible for all the stated coefficient rings.

4. Let zeta:F_q(p*A)→1 be F_q(z) followed by the compositor for qa=1.
Let Gamma_D be F_q of the preceding composite with target D. PF naturality
and its composition pentagon for a,q give Gamma_D PF_q = lambda_D(zeta tensor 1).
Inverting at D=C identifies PF_q.inv Gamma_C.inv with
(zeta.inv tensor 1) lambda_C.inv.

5. Pull back s followed by f along g. The exchange/composition equation and
the identity-square normalization give zeta e_(g,f,A)=g*(c_f). The coefficient
unit comparison and proper comparison in this equation are exactly those
used in closedExchange and sectionUnitIso, by native adjunction coherence.

6. Read the first three factors of the six-arrow relative Künneth word.
Compositor associativity identifies its first factor after F_h(theta) with
F_g(Gamma_C.inv), using c_h and c_g. The second factor is simplified by Step 4;
the inverse exchange in the third factor cancels zeta.inv by Step 5.
Under c_f the result is F_g(lambda_C.inv).

7. The fourth factor, symmetry, changes this to F_g(r_C.inv); the unit lies
in degree zero, so the sign is +1. The inverse projection factor cancels by
Step 2, giving r_(F_g C).inv. The last symmetry gives lambda_(F_g C).inv.
Naturality of unitors with c_g gives lambda_1.inv=mu.inv, proving clause_one.

8. Apply naturality of the same six-arrow word to a_s and a_t, precompose
with F_h(theta), and substitute clause_one. This gives clause_two with its
displayed exterior supported arrow. For empty B all categories are zero;
for identity sections the equation is mu.inv=mu.inv. No shifts or twists
occur in this calculation. -/
theorem compact_kunneth_section_unit
    (datum : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ datum.p) (I : Input datum ell) : Nonempty (Conclusion I) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CompactKunnethSectionUnit
