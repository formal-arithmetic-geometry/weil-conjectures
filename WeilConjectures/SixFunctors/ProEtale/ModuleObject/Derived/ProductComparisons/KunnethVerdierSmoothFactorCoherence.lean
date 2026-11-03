/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompComposition
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteProperLocalizing

/-! # Native exceptional Künneth composition and signed symmetry

Source: latest blueprint, sk-prop-tf-exceptional-external-kunneth.proof.md,
Constant and lisse coefficients (blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence).
The product presentations below retain their universal-property squares. Swapping a
presentation retains its representing scheme: the geometric swap is the identity
between these two presentations, and its coefficient comparison is the signed derived
braiding. No exceptional comparison is assumed invertible.

The compact-support compositor and model comparison are the specified maps of
sk-thm-sf-comp-composition (`sfCompComposition`, `sfCompComparison`); the Künneth map
alpha is the transpose of sk-def-sf-kv-maps (`ProductComparisons.alpha`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons
open CompactificationReindexing RelativeKunneth

/-- A chosen presentation of an absolute product over k, retaining the actual projections.
Source: product schemes in the composition equation
(blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence). -/
structure AbsoluteProduct (k : Type u) [Field k] where
  first : SepFinType k
  second : SepFinType k
  space : SepFinType k
  fst : space ⟶ first
  snd : space ⟶ second
  square : IsPullback fst.hom.left snd.hom.left first.obj.hom second.obj.hom

variable {k : Type u} [Field k]

/-- Reuse the existing relative-product interface over Spec k.
Source: absolute exterior products (blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence). -/
def AbsoluteProduct.diagram (P : AbsoluteProduct k) : Diagram k :=
  ⟨base k, P.first, P.second, P.space,
    ObjectProperty.homMk (Over.homMk P.first.obj.hom),
    ObjectProperty.homMk (Over.homMk P.second.obj.hom), P.fst, P.snd, P.square⟩

/-- Reverse the projections on the same representing product scheme.
Source: geometric factor swap (blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence). -/
def AbsoluteProduct.swap (P : AbsoluteProduct k) : AbsoluteProduct k :=
  ⟨P.second, P.first, P.space, P.snd, P.fst, P.square.flip⟩

/-- The canonical geometric swap between the two presentations of the same product.
Source: s in the swap equation
(blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence). -/
def AbsoluteProduct.swapMap (P : AbsoluteProduct k) :
    P.space.obj.left ⟶ P.swap.space.obj.left := 𝟙 _

/-- Cartesian auxiliary products specifying the canonical product of two morphisms.
These are precisely the squares required by the recorded native alpha construction.
Source: f1 times f2 (blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence). -/
structure ProductArrow (P Q : AbsoluteProduct k)
    (f₁ : P.first ⟶ Q.first) (f₂ : P.second ⟶ Q.second) where
  U : SepFinType k
  V : SepFinType k
  a₁ : U ⟶ P.first
  a₂ : V ⟶ P.second
  left : U ⟶ Q.space
  right : V ⟶ Q.space
  p : P.space ⟶ U
  q : P.space ⟶ V
  exchange₁ : IsPullback a₁.hom.left left.hom.left f₁.hom.left Q.fst.hom.left
  exchange₂ : IsPullback a₂.hom.left right.hom.left f₂.hom.left Q.snd.hom.left
  relative : IsPullback p.hom.left q.hom.left left.hom.left right.hom.left
  path₁ : p.hom.left ≫ a₁.hom.left = P.fst.hom.left
  path₂ : q.hom.left ≫ a₂.hom.left = P.snd.hom.left

/-- The recorded geometry, with definitionally shared source and target products.
Source: native alpha geometry (blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence). -/
def ProductArrow.geometry {P Q : AbsoluteProduct k}
    {f₁ : P.first ⟶ Q.first} {f₂ : P.second ⟶ Q.second}
    (a : ProductArrow P Q f₁ f₂) : Geometry k :=
  ⟨P.first, P.second, Q.first, Q.second, Q.space, a.U, a.V, P.space,
    f₁, f₂, Q.fst, Q.snd, a.a₁, a.a₂, a.left, a.right, a.p, a.q, P.fst, P.snd,
    P.square, Q.square, a.exchange₁, a.exchange₂, a.relative, a.path₁, a.path₂⟩

/-- The product morphism itself, as used by the native total compactification.
Source: f1 times f2 (blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence). -/
def ProductArrow.total {P Q : AbsoluteProduct k}
    {f₁ : P.first ⟶ Q.first} {f₂ : P.second ⟶ Q.second}
    (a : ProductArrow P Q f₁ f₂) : P.space ⟶ Q.space := a.q ≫ a.right

/-- The same product morphism with the factors reversed.
Source: both factor orders (blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence). -/
def ProductArrow.swap {P Q : AbsoluteProduct k}
    {f₁ : P.first ⟶ Q.first} {f₂ : P.second ⟶ Q.second}
    (a : ProductArrow P Q f₁ f₂) : ProductArrow P.swap Q.swap f₂ f₁ :=
  ⟨a.V, a.U, a.a₂, a.a₁, a.right, a.left, a.q, a.p,
    a.exchange₂, a.exchange₁, a.relative.flip, a.path₂, a.path₁⟩

/-- The product of composite pairs is the composite product morphism.
Source: h = g f in the full equation
(blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence).
Proof: compose with both projections and use the exchange-square equations and
path equations; the source and target product universal properties identify the maps. -/
theorem productArrow_total_comp (X Y Z : AbsoluteProduct k)
    (f₁ : X.first ⟶ Y.first) (f₂ : X.second ⟶ Y.second)
    (g₁ : Y.first ⟶ Z.first) (g₂ : Y.second ⟶ Z.second)
    (a : ProductArrow X Y f₁ f₂) (b : ProductArrow Y Z g₁ g₂)
    (c : ProductArrow X Z (f₁ ≫ g₁) (f₂ ≫ g₂)) :
    a.total.hom.left ≫ b.total.hom.left = c.total.hom.left := by
  have first {P Q : AbsoluteProduct k} {u : P.first ⟶ Q.first}
      {v : P.second ⟶ Q.second} (d : ProductArrow P Q u v) :
      d.total.hom.left ≫ Q.fst.hom.left = P.fst.hom.left ≫ u.hom.left := by
    change (d.q.hom.left ≫ d.right.hom.left) ≫ Q.fst.hom.left = _
    calc
      (d.q.hom.left ≫ d.right.hom.left) ≫ Q.fst.hom.left =
          (d.p.hom.left ≫ d.left.hom.left) ≫ Q.fst.hom.left := by rw [d.relative.w]
      _ = (d.p.hom.left ≫ d.a₁.hom.left) ≫ u.hom.left := by
        rw [Category.assoc, ← d.exchange₁.w, ← Category.assoc]
      _ = _ := by rw [d.path₁]
  have second {P Q : AbsoluteProduct k} {u : P.first ⟶ Q.first}
      {v : P.second ⟶ Q.second} (d : ProductArrow P Q u v) :
      d.total.hom.left ≫ Q.snd.hom.left = P.snd.hom.left ≫ v.hom.left := by
    change (d.q.hom.left ≫ d.right.hom.left) ≫ Q.snd.hom.left = _
    rw [Category.assoc, ← d.exchange₂.w, ← Category.assoc, d.path₂]
  apply Z.square.hom_ext
  · rw [Category.assoc, first b, ← Category.assoc, first a, first c]
    rfl
  · rw [Category.assoc, second b, ← Category.assoc, second a, second c]
    rfl

open scoped CategoryTheory.MonoidalClosed

/-- A finite discrete commutative ring killed by a power of ell is an admissible
condensed coefficient: its first clause, after a small discrete model of the ring.
Source: det-ctf-finite-proper-localizing, coefficient identification; sk-def-localizing-closure,
finite-coefficient convention (blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence).
Proof: shrink R to Type 0 by a ring equivalence; postcomposition gives an isomorphism of
continuous-map ring sheaves, hence of monoid objects, and the ell-power torsion transports
(this is the module-private `finiteDiscreteCoefficient_admissible` of FiniteProperLocalizing). -/
theorem finiteDiscreteCondensedCoefficient_isAdmissible (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Type u) [CommRing R] [Finite R] (_htors : ∃ n : ℕ, ∀ r : R, ℓ ^ n • r = 0) :
    IsLocalizingAdmissibleCoefficient ℓ (finiteDiscreteCondensedCoefficient R) := by
  classical
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let : IsTopologicalRing R := by infer_instance
  let B := Shrink.{0} R
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let : IsTopologicalRing B := by infer_instance
  let e : R ≃+* B := (Shrink.ringEquiv.{0} R).symm
  let h : Profinite.continuousMapRingSheafOfUniverse.{u, u} R ⟶
      Profinite.continuousMapRingSheaf.{u} B :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.toRingHom.compLeftContinuous S.unop (continuous_of_discreteTopology)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let v : Profinite.continuousMapRingSheaf.{u} B ⟶
      Profinite.continuousMapRingSheafOfUniverse.{u, u} R :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.symm.toRingHom.compLeftContinuous S.unop (continuous_of_discreteTopology)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let E : Profinite.continuousMapRingSheafOfUniverse.{u, u} R ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := h
      inv := v
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let E' := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso E
  let : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
  let eh := presheaf_enrichedHoms_exist
    (C := Profinite.{u}) (A := Ab.{u + 1})
  let : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}),
    Enriched.FunctorCategory.HasEnrichedHom Ab.{u + 1} F G := eh.1
  let : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}),
    Enriched.FunctorCategory.HasFunctorEnrichedHom Ab.{u + 1} F G := eh.2
  let : ((coherentTopology Profinite.{u}).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal
  let hmon : IsMonHom E'.hom := Sheaf.isMonHom_sheafCompose_map _ E.hom
  refine Or.inl ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ⟨Mon.mkIso' E'⟩⟩
  obtain ⟨n, hn⟩ := _htors
  refine ⟨n, fun b ↦ ?_⟩
  have hn' : (ℓ ^ n : ℕ) • (1 : B) = 0 := by
    simpa only [map_nsmul, map_one, map_zero] using congrArg e (hn 1)
  simpa only [nsmul_eq_mul, mul_one, zero_mul] using congrArg (fun x : B ↦ x * b) hn'

variable (Λ : ScalarSixRing.{u})

section SpecifiedComparisons

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ.X)

/-- Restriction to Dctf of the specified compact-support compositor of
sk-thm-sf-comp-composition, with no new choice.
Source: the comparison d of the proof, from [sk-thm-sf-comp-composition]
(blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence). -/
def constructibleSupportComp
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    {cf : Compactification f.hom.left} {cg : Compactification g.hom.left}
    {h : X ⟶ Z} (e : f.hom.left ≫ g.hom.left = h.hom.left)
    {ch : Compactification h.hom.left}
    (Sf : SixOperationsLocalizingAdjunction Λ.X cf)
    (Sg : SixOperationsLocalizingAdjunction Λ.X cg)
    (Sh : SixOperationsLocalizingAdjunction Λ.X ch) :
    lower Λ Sf ⋙ lower Λ Sg ≅ lower Λ Sh :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    ((sfCompComposition ℓ k Λ.X hΛ f g cf cg (ch.copy e)).app
      ⟨K.obj, Sf.source_mem K.obj K.property⟩))
    (by
      intro K L a
      ext
      exact (sfCompComposition ℓ k Λ.X hΛ f g cf cg (ch.copy e)).hom.naturality
        (show (⟨K.obj, Sf.source_mem K.obj K.property⟩ :
          (localizingClosureProEtale Λ.X X.obj.left).FullSubcategory) ⟶
          ⟨L.obj, Sf.source_mem L.obj L.property⟩ from ⟨a.hom⟩))

/-- Restriction to Dctf of the specified compactification comparison of
sk-thm-sf-comp-composition, also allowing equal total morphisms.
Source: canonical model identifications in the swap formula
(blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence). -/
def constructibleSupportComparison
    {X Y : SepFinType k} (f g : X ⟶ Y) (e : f.hom.left = g.hom.left)
    {cf : Compactification f.hom.left} {cg : Compactification g.hom.left}
    (Sf : SixOperationsLocalizingAdjunction Λ.X cf)
    (Sg : SixOperationsLocalizingAdjunction Λ.X cg) : lower Λ Sf ≅ lower Λ Sg :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    ((sfCompComparison ℓ k Λ.X hΛ f cf (cg.copy e)).app
      ⟨K.obj, Sf.source_mem K.obj K.property⟩))
    (by
      intro K L a
      ext
      exact (sfCompComparison ℓ k Λ.X hΛ f cf (cg.copy e)).hom.naturality
        (show (⟨K.obj, Sf.source_mem K.obj K.property⟩ :
          (localizingClosureProEtale Λ.X X.obj.left).FullSubcategory) ⟶
          ⟨L.obj, Sf.source_mem L.obj L.property⟩ from ⟨a.hom⟩))

/-- The counit mate r: (gf)! -> f!g! of the specified compact-support compositor.
Source: definition of r (blueprint: lem-sf-kunneth-verdier-smooth-factor-coherence). -/
def exceptionalComp
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    {cf : Compactification f.hom.left} {cg : Compactification g.hom.left}
    {h : X ⟶ Z} (e : f.hom.left ≫ g.hom.left = h.hom.left)
    {ch : Compactification h.hom.left}
    (Sf : SixOperationsLocalizingAdjunction Λ.X cf)
    (Sg : SixOperationsLocalizingAdjunction Λ.X cg)
    (Sh : SixOperationsLocalizingAdjunction Λ.X ch) :
    exceptional Λ Sh ≅ exceptional Λ Sg ⋙ exceptional Λ Sf :=
  conjugateIsoEquiv (adjunction Λ Sh) ((adjunction Λ Sf).comp (adjunction Λ Sg))
    (constructibleSupportComp Λ ℓ hΛ f g e Sf Sg Sh)

end SpecifiedComparisons

end AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons
