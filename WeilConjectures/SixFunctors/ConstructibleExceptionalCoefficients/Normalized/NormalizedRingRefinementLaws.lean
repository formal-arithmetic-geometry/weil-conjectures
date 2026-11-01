/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingRefinementCoordinates
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.IntegralNormalizedRingRefinementLaws

/-! # Normalized coefficient comparisons: one component of the coherence argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem coordinate_transport {C : Type u} [Category.{v} C]
    {U V X Y P Q : C} (a : U ≅ X) (b : V ≅ Y) (p : X ≅ P) (q : Y ≅ Q)
    (r : U ⟶ V) (t : X ⟶ Y) (z : P ⟶ Q)
    (hn : a.inv ≫ r ≫ b.hom = t) (hc : t ≫ q.hom = p.hom ≫ z) :
    r ≫ (b ≪≫ q).hom = (a ≪≫ p).hom ≫ z := by
  have h := (Iso.inv_comp_eq a).mp hn
  change r ≫ b.hom ≫ q.hom = (a.hom ≫ p.hom) ≫ z
  rw [← Category.assoc, h, Category.assoc, hc, Category.assoc]

private theorem coordinate_identity {C : Type u} [Category.{v} C]
    {U X : C} (a : U ≅ X) (r : U ⟶ U)
    (h : r ≫ a.hom = a.hom ≫ 𝟙 X) : r = 𝟙 U := by
  apply (Iso.cancel_iso_hom_right _ _ a).1
  simpa only [Category.id_comp, Category.comp_id] using h

private theorem coordinate_composition {C : Type u} [Category.{v} C]
    {U V W X Y Z : C} (a : U ≅ X) (b : V ≅ Y) (c : W ≅ Z)
    (r : U ⟶ V) (s : V ⟶ W) (t : U ⟶ W)
    (x : X ⟶ Y) (y : Y ⟶ Z) (z : X ⟶ Z)
    (hr : r ≫ b.hom = a.hom ≫ x) (hs : s ≫ c.hom = b.hom ≫ y)
    (ht : t ≫ c.hom = a.hom ≫ z) (hz : z = x ≫ y) : t = r ≫ s := by
  apply (Iso.cancel_iso_hom_right _ _ c).1
  calc
    t ≫ c.hom = a.hom ≫ z := ht
    _ = a.hom ≫ x ≫ y := congrArg (fun m ↦ a.hom ≫ m) hz
    _ = (a.hom ≫ x) ≫ y := (Category.assoc _ _ _).symm
    _ = (r ≫ b.hom) ≫ y := congrArg (fun m ↦ m ≫ y) hr.symm
    _ = r ≫ b.hom ≫ y := Category.assoc _ _ _
    _ = r ≫ s ≫ c.hom := congrArg (fun m ↦ r ≫ m) hs.symm
    _ = (r ≫ s) ≫ c.hom := (Category.assoc _ _ _).symm

private theorem finite_refinement_laws
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (N : CoefficientConstructionRefinements.{u, v} l Ω D hl R F M)
    (E : FieldStage.{max u v} l) (n : ℕ) :
    (∀ c : Compactification f,
      (N.refinement (.id c) (.finite E ⟨n + 1, Nat.succ_pos n⟩)).left = Iso.refl _) ∧
    (∀ {a b c : Compactification f} (r : a.Refinement b) (t : b.Refinement c),
      (N.refinement (r.comp t) (.finite E ⟨n + 1, Nat.succ_pos n⟩)).left =
        (N.refinement r (.finite E ⟨n + 1, Nat.succ_pos n⟩)).left ≪≫
          (N.refinement t (.finite E ⟨n + 1, Nat.succ_pos n⟩)).left) := by
  classical
  let s : RingStage.{max u v} l := .finite E ⟨n + 1, Nat.succ_pos n⟩
  let A := Padic.coefficientExtensionRing l E.carrier (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E.carrier (n + 1)
    (Nat.succ_pos n)
  let JX : C.{u, v} l Ω X (s.stage l) ⥤ proEtaleDerivedCategory X A :=
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) X).ι
  let JY : C.{u, v} l Ω Y (s.stage l) ⥤ proEtaleDerivedCategory Y A :=
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).ι
  let : JY.Faithful := inferInstanceAs
    ((finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).ι.Faithful)
  let B (c : Compactification f) : (R.operation c (s.stage l)).F ⋙ JY ≅
      JX ⋙ sfAmbientCompactSupportCandidate A c := R.left c s ≪≫
    Functor.isoWhiskerLeft JX (PurCompactSupport.finiteImageIso l E.carrier n c)
  obtain ⟨θ, hθ, hid, hcomp, _⟩ := FrobeniusExchange.intrinsicCompactificationCoherence
    D.k l (PurCompactSupport.coefficientPrimeUnit l D hl) E.carrier (n + 1)
    (Nat.succ_pos n) f
  have origin (K : C.{u, v} l Ω X (s.stage l)) :
      ∃ L : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{max u v + 1} (ULift.{max u v + 1} A))),
        Nonempty ((FrobeniusExchange.origin A X).obj L.obj ≅ K.obj) := by
    have hK : intrinsicFiniteTorsionConstructible l E.carrier (n + 1)
        (Nat.succ_pos n) X K.obj := K.property.1
    obtain ⟨a, ha⟩ := hK.1.bddBelow
    obtain ⟨b, hb⟩ := hK.1.bddAbove
    have hz (i : ℤ) (hi : i < min a b ∨ max a b < i) :
        IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj) := by
      by_contra hn
      rcases hi with hi | hi
      · exact (not_lt_of_ge (le_trans (min_le_left _ _) (ha hn))) hi
      · exact (not_lt_of_ge (le_trans (hb hn) (le_max_right _ _))) hi
    obtain ⟨G, ⟨eG⟩⟩ := ((finiteRing_constructibleDerived_origin X A).2.2.1 K.obj).mpr
      ⟨hK.2, min a b, max a b, min_le_max, hz⟩
    obtain ⟨a', b', _, hvan⟩ := G.property.2
    exact ⟨⟨G.obj, a', (DerivedCategory.isGE_iff G.obj a').mpr
      (fun i hi ↦ hvan i (Or.inl hi))⟩, ⟨eG⟩⟩
  have coord {c d : Compactification f} (r : c.Refinement d)
      (K : C.{u, v} l Ω X (s.stage l))
      (L : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{max u v + 1} (ULift.{max u v + 1} A))))
      (α : (FrobeniusExchange.origin A X).obj L.obj ≅ K.obj) :
      JY.map ((N.refinement r (s.stage l)).left.hom.app K) ≫ (B d).hom.app K =
        (B c).hom.app K ≫ (θ c d r).hom.app ⟨K.obj, L, α⟩ := by
    let O : FrobeniusExchange.CompactOrigin A X := ⟨K.obj, L, α⟩
    obtain ⟨hi, hg, h⟩ := N.refinement_normalized r s
    obtain ⟨ε, hε, hρ⟩ := h K
    have hc := congrArg Iso.hom
      (finite_ring_refinement_coordinates l E.carrier n r O hi hg ε hε)
    rw [← hθ c d r O] at hc
    dsimp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom] at hc
    dsimp only [s, RingStage.coefficients, RingStage.inclusion, RingStage.stage] at hρ
    let T := ((PurCompactSupport.geometricPushComposition (s.coefficients l)
      r.hom d.g hg ≪≫ eqToIso (congrArg (fun h ↦
        PurCompactSupport.push (s.coefficients l) h) r.hom_g)).symm.app
          ((PurCompactSupport.openExtension (s.coefficients l) c.i).mapDerivedCategory.obj
            K.obj)).hom ≫ (PurCompactSupport.push (s.coefficients l) d.g).map ε.inv
    have hn : ((R.left c s).app K).inv ≫
        JY.map ((N.refinement r (s.stage l)).left.hom.app K) ≫
          ((R.left d s).app K).hom = T := hρ
    have ht : T ≫ ((PurCompactSupport.finiteImageIso l E.carrier n d).app K.obj).hom =
        ((PurCompactSupport.finiteImageIso l E.carrier n c).app K.obj).hom ≫
          (θ c d r).hom.app O := (Category.assoc _ _ _).trans hc
    have hu := coordinate_transport (C := proEtaleDerivedCategory Y A)
      ((R.left c s).app K) ((R.left d s).app K)
      ((PurCompactSupport.finiteImageIso l E.carrier n c).app K.obj)
      ((PurCompactSupport.finiteImageIso l E.carrier n d).app K.obj)
      (JY.map ((N.refinement r (s.stage l)).left.hom.app K)) T
      ((θ c d r).hom.app O) hn ht
    exact hu
  constructor
  · intro c
    apply Iso.ext
    apply NatTrans.ext
    funext K
    obtain ⟨L, ⟨α⟩⟩ := origin K
    apply JY.map_injective
    have hc := coord (.id c) K L α
    have hi : θ c c (.id c) = Iso.refl _ := hid c
    rw [hi] at hc
    have h := coordinate_identity ((B c).app K) _ hc
    exact h.trans (JY.map_id _).symm
  · intro a b c r t
    apply Iso.ext
    apply NatTrans.ext
    funext K
    obtain ⟨L, ⟨α⟩⟩ := origin K
    apply JY.map_injective
    let O : FrobeniusExchange.CompactOrigin A X := ⟨K.obj, L, α⟩
    have ht : θ a c (r.comp t) = θ a b r ≪≫ θ b c t := hcomp a b c r t
    have hθt : (θ a c (r.comp t)).hom.app O =
        (θ a b r).hom.app O ≫ (θ b c t).hom.app O :=
      congrArg (fun e ↦ e.hom.app O) ht
    have h := coordinate_composition ((B a).app K) ((B b).app K) ((B c).app K)
      _ _ _ _ _ _ (coord r K L α) (coord t K L α) (coord (r.comp t) K L α) hθt
    exact h.trans (JY.map_comp _ _).symm

/-- The proper/open-normalized ring refinement maps are unital and transitive.
Source: exceptional inverse-image compactification refinement paragraph; finite etale
origin compactification coherence and integral normalized refinement pasting
(blueprint: lem-sf-normalized-ring-refinement-laws).

Proof: at a finite coefficient level, choose the bounded etale-origin witness of each
constructible object. The canonical finite compactification comparison has the recorded
open-unit transpose. Uniqueness under the open adjunction identifies the proper/open
isomorphism in RingRefinementNormalized with this canonical one. Apply
compactification_coherence to its identity and composition. Conjugate by the supplied
left realizations and use faithfulness of the full inclusions.
For an integral coefficient field, use the same open transpose uniqueness to assemble
the pointwise open comparisons into a natural isomorphism on the finite-Tor domain.
The supplied integralLeft and its normalization give the compatible compact-support
realization. Apply integralRefinementDiagramAdmissibility to the finitely many words in
an identity or binary refinement diagram, using the input's uniform Tor interval.
The normalized integral refinement pasting theorem then gives identity and composition
for these actual maps. Full-inclusion faithfulness gives the asserted equations without
inferring equality from the individual finite evaluations. No absolute separatedness of
X or Y is needed: only the given proper/open compactifications and separated f are used.
The empty open and zero input are covered by the same adjunction equations. -/
theorem normalized_ring_refinement_laws (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (N : CoefficientConstructionRefinements.{u, v} l Ω D hl R F M) :
    (∀ (c : Compactification f) (s : RingStage.{max u v} l),
      (N.refinement (.id c) (s.stage l)).left = Iso.refl _) ∧
    (∀ {a b c : Compactification f} (r : a.Refinement b) (t : b.Refinement c)
      (s : RingStage.{max u v} l),
      (N.refinement (r.comp t) (s.stage l)).left =
        (N.refinement r (s.stage l)).left ≪≫ (N.refinement t (s.stage l)).left) := by
  have laws (s : RingStage.{max u v} l) :
      (∀ c : Compactification f,
        (N.refinement (.id c) (s.stage l)).left = Iso.refl _) ∧
      (∀ {a b c : Compactification f} (r : a.Refinement b) (t : b.Refinement c),
        (N.refinement (r.comp t) (s.stage l)).left =
          (N.refinement r (s.stage l)).left ≪≫ (N.refinement t (s.stage l)).left) := by
    cases s with
    | integral E => exact integral_normalized_ring_refinement_laws l Ω D hl R F M N E
    | finite E n =>
      rcases n with ⟨_ | n, hn⟩
      · omega
      · exact finite_refinement_laws l Ω D hl R F M N E n
  exact ⟨fun c s ↦ (laws s).1 c, fun {_ _ _} r t s ↦ (laws s).2 r t⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
