/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.Compactification.NagataCompactification
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDualProper
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-! # The double-dual morphism under proper direct image

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
order 2123 (blueprint: lem-weil-delta-proper-pushforward).

All constructions use ordinary unbounded etale module derived categories. Evaluation and
its transpose are normalized by tensor-Hom adjunction. The trace uses the mate of the
compactification composition comparison, and the exchange is the transpose of the
pushed-forward evaluation pairing.

## Main definitions and statement

* `ambientDualEvaluation` and `ambientDoubleDualMap`: signed evaluation and its transpose.
* `properAmbientShriekStarIso` and `ambientShriekCompIso`: canonical support comparisons.
* `properAmbientDualizingIso` and `properAmbientDualityTrace`: the adjoint mate and trace.
* `ambientDirectImageProduct`: direct-image product from projection and the counit.
* `properAmbientVerdierExchangeMap`: the transpose of evaluation followed by trace.
* `ProperAmbientDoubleDualCompatibility`: the natural exchange and double-dual square.
* `proper_ambient_double_dual_compatibility`: the proper pushforward assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace CategoryTheory.MonoidalClosed

-- These identities verify the normalizations before specialization to derived sheaves.
private theorem doubleDual_eq_transpose
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    (W K : C) :
    toIhomIhom W K = (internalHomAdjunction₂.adj ((ihom K).obj W)).homEquiv K W
      ((β_ ((ihom K).obj W) K).hom ≫
        ((internalHomAdjunction₂.adj K).homEquiv _ _).symm (𝟙 _)) := by
  rw [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem product_eq_laxProduct
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (p : F ⊣ G) [F.OplaxMonoidal] (U V : D) :
    letI := p.rightAdjointLaxMonoidal
    p.homEquiv _ _ (Functor.OplaxMonoidal.δ F (G.obj U) (G.obj V) ≫
      p.counit.app U ▷ F.obj (G.obj V)) ≫ G.map (U ◁ p.counit.app V) =
        Functor.LaxMonoidal.μ G U V := by
  let := p.rightAdjointLaxMonoidal
  rw [← p.homEquiv_naturality_right, Adjunction.rightAdjointLaxMonoidal_μ]
  congr 1
  exact (Category.assoc _ _ _).trans
    (congrArg (fun h ↦ Functor.OplaxMonoidal.δ F (G.obj U) (G.obj V) ≫ h)
      (MonoidalCategory.tensorHom_def (p.counit.app U) (p.counit.app V)).symm)

private theorem dualComparison_eq_curry
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.LaxBraided] {W : C} {W' : D} (e : G.obj W ⟶ W') (K : C) :
    curry ((β_ (G.obj ((ihom K).obj W)) (G.obj K)).inv ≫
      Functor.LaxMonoidal.μ G ((ihom K).obj W) K ≫
      G.map ((β_ ((ihom K).obj W) K).hom ≫ (ihom.ev K).app W) ≫ e) =
        dualComparison G e K := by
  apply uncurry_injective
  rw [uncurry_curry, G.map_comp]
  simp only [Category.assoc]
  rw [Functor.LaxBraided.braided_assoc, Iso.inv_hom_id_assoc]
  rw [dualComparison, uncurry_natural_right, uncurry_eq,
    Category.assoc, Functor.LaxMonoidal.ihomComparison_ev_assoc]

private theorem dualComparison_naturality
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.LaxBraided] {W : C} {W' : D} (e : G.obj W ⟶ W')
    {K L : C} (h : K ⟶ L) :
    G.map ((pre h).app W) ≫ dualComparison G e K =
      dualComparison G e L ≫ (pre (G.map h)).app W' := by
  rw [dualComparison, dualComparison, ← Category.assoc,
    Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app, Category.assoc,
    pre_comm_ihom_map, Category.assoc]

/-- Naturality, invertibility, and biduality compatibility of a traced dual comparison.
Source: blueprint order 2123 (blueprint: lem-weil-delta-proper-pushforward). -/
def TracedDualCompatibility
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.LaxBraided] {W : C} {W' : D} (t : G.obj W ⟶ W') : Prop :=
  (∀ (K L : C) (h : K ⟶ L),
    G.map ((pre h).app W) ≫ dualComparison G t K =
      dualComparison G t L ≫ (pre (G.map h)).app W') ∧
  (∀ K, IsIso (dualComparison G t K)) ∧
  (∀ K, G.map (toIhomIhom W K) ≫ dualComparison G t ((ihom K).obj W) =
    toIhomIhom W' (G.obj K) ≫ (pre (dualComparison G t K)).app W') ∧
  (∀ K, IsIso (toIhomIhom W' (G.obj K)) → IsIso (G.map (toIhomIhom W K)))

private theorem tracedDualCompatibility
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.LaxBraided] {W : C} {W' : D} (t : G.obj W ⟶ W')
    (hθ : ∀ K, IsIso (dualComparison G t K)) : TracedDualCompatibility G t := by
  refine ⟨fun _ _ h ↦ dualComparison_naturality G t h, hθ,
    fun K ↦ map_toIhomIhom_comp_dualComparison G t K, ?_⟩
  intro K hK
  have := hθ K
  have := hθ ((ihom K).obj W)
  exact (isIso_map_toIhomIhom_iff G t K).2 hK

end CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry.Etale

attribute [local instance] derivedBraidedCategory

section Evaluation

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  (X : Scheme.{u})

/-- The evaluation pairing in the order DK tensor K. Source: blueprint order 2123,
second proof paragraph (blueprint: lem-weil-delta-proper-pushforward).
This is the evaluation of lem-weil-duality-pairing: signed symmetry followed by the
inverse tensor-Hom transpose of the identity, so its normalization is fixed. -/
noncomputable def ambientDualEvaluation
    (W K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj (((derivedHom A X).obj (op K)).obj W)).obj K ⟶ W :=
  ((derivedTensorSymmetry A X).hom.app (((derivedHom A X).obj (op K)).obj W)).app K ≫
    ((derivedTensorHomAdjunction A K).homEquiv _ _).symm (𝟙 _)

/-- The canonical double-dual arrow, the transpose of evaluation in the preceding order.
Source: blueprint order 2123, third proof paragraph
(blueprint: lem-weil-delta-proper-pushforward). This fixes the Koszul signs by the existing
signed symmetry, and applies to every ambient object W and every unbounded K. -/
noncomputable def ambientDoubleDualMap
    (W K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ⟶ (ihom ((ihom K).obj W)).obj W :=
  MonoidalClosed.toIhomIhom W K

end Evaluation

/-- The canonical proper identification with direct image, through the identity
compactification and the proper/open comparison. Source: blueprint order 2123, first
proof paragraph (blueprint: lem-weil-delta-proper-pushforward).
No isomorphism is selected from a mere existence assertion. -/
noncomputable def properAmbientShriekStarIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ≅
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor := by
  let c := Compactification.ofIsProper f
  letI := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) c.i (c.isClopen_range_openImmersion inferInstance).isClosed
  let e := asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) c.i)
  letI : PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} Λ) c.i) :=
    preservesFiniteColimits_of_natIso e
  letI : PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} Λ) c.i) :=
    preservesFiniteLimits_of_natIso e
  exact (rightDerivedLowerShriekIso Λ c).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso e) _ ≪≫
    Functor.isoWhiskerRight
      ((lowerStar (ModuleCat.{u + 1} Λ) c.i).rightDerivedFunctorIsoMapDerivedCategory).symm _ ≪≫
    rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) c.i c.g ≪≫
    rightDerivedLowerStarCongr (ModuleCat.{u + 1} Λ) c.comm.symm

/-- The unbounded compact-support composition comparison, assembled from the existing
proper/open exchange and the canonical compactification comparisons.
Source: blueprint order 2123, first proof paragraph; Stacks 0F7H--0F7J
(blueprint: lem-weil-delta-proper-pushforward). This is the explicit construction underlying
nonempty_iso_rightDerivedLowerShriek_comp, with no choice from that theorem. -/
noncomputable def ambientShriekCompIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g := by
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  exact (rightDerivedLowerShriekIso Λ (d.comp e)).symm ≪≫
    (rightDerivedLowerShriekOfCompactificationCompIso Λ d e).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerShriekIso Λ e.restrict) _

/-- The canonical identification f-times omega-Y with omega-X, the right-adjoint mate of
compact-support composition after proper coincidence. Source: blueprint order 2123,
first proof paragraph (blueprint: lem-weil-delta-proper-pushforward). -/
noncomputable def properAmbientDualizingIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) g) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g) :=
  (conjugateIsoEquiv
    (((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).ofNatIsoLeft
      (properAmbientShriekStarIso Λ f)).comp
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) g))
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (f ≫ g))
    (ambientShriekCompIso Λ f g ≪≫
      Functor.isoWhiskerRight (properAmbientShriekStarIso Λ f)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g))).app (𝟙_ _)

/-- The trace F omega-X to omega-Y, transported from the exceptional counit by the
preceding canonical mate. Source: blueprint order 2123, first proof paragraph
(blueprint: lem-weil-delta-proper-pushforward). -/
noncomputable def properAmbientDualityTrace
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g)) ⟶
      dualizingComplex (ModuleCat.{u + 1} Λ) g :=
  (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
      (properAmbientDualizingIso Λ f g).inv ≫
    ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).ofNatIsoLeft
      (properAmbientShriekStarIso Λ f)).counit.app
        (dualizingComplex (ModuleCat.{u + 1} Λ) g)

section Product

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The symmetric product map FU tensor FV to F(U tensor V), using the ordinary
inverse-image/direct-image counit. Source: blueprint order 2123, second proof paragraph
(blueprint: lem-weil-delta-proper-pushforward). -/
noncomputable def ambientDirectImageProduct
    (U V : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A Y).obj ((lowerStar A f).rightDerivedFunctor.obj U)).obj
        ((lowerStar A f).rightDerivedFunctor.obj V) ⟶
      (lowerStar A f).rightDerivedFunctor.obj (((derivedTensor A X).obj U).obj V) :=
  ((rightDerivedLowerStarProjectionMap A f).app U).app
      ((lowerStar A f).rightDerivedFunctor.obj V) ≫
    (lowerStar A f).rightDerivedFunctor.map
      ((derivedTensor A X).obj U |>.map ((derivedUpperStarLowerStarAdjunction A f).counit.app V))

end Product

section Comparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical internal-Hom comparison for direct image with a specified trace.
Source: blueprint order 2123, pairing construction
(blueprint: lem-weil-delta-proper-pushforward). -/
noncomputable def ambientDirectImageDualComparison
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {W' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (t : (lowerStar A f).rightDerivedFunctor.obj W ⟶ W')
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (lowerStar A f).rightDerivedFunctor.obj (((derivedHom A X).obj (op K)).obj W) ⟶
      ((derivedHom A Y).obj (op ((lowerStar A f).rightDerivedFunctor.obj K))).obj W' :=
  letI := leftDerivedUpperStarMonoidal A f
  let p := derivedUpperStarLowerStarAdjunction A f
  letI := p.rightAdjointLaxBraidedOfδ (leftDerivedUpperStar_map_braiding_hom_δ A f)
  MonoidalClosed.dualComparison (lowerStar A f).rightDerivedFunctor t K

/-- Compatibility for direct image with any specified dualizing trace.
Source: blueprint order 2123 (blueprint: lem-weil-delta-proper-pushforward). -/
def AmbientDirectImageDoubleDualCompatibility
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {W' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (t : (lowerStar A f).rightDerivedFunctor.obj W ⟶ W') : Prop :=
  letI := leftDerivedUpperStarMonoidal A f
  let p := derivedUpperStarLowerStarAdjunction A f
  letI := p.rightAdjointLaxBraidedOfδ (leftDerivedUpperStar_map_braiding_hom_δ A f)
  MonoidalClosed.TracedDualCompatibility (lowerStar A f).rightDerivedFunctor t

private theorem ambientDirectImageDoubleDualCompatibility
    [IsIso (rightDerivedLowerStarProjectionMap A f)]
    {Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (q : (lowerStar A f).rightDerivedFunctor ⊣ Q)
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {W' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : W ≅ Q.obj W') :
    AmbientDirectImageDoubleDualCompatibility A f
      ((lowerStar A f).rightDerivedFunctor.map e.hom ≫ q.counit.app W') := by
  let := leftDerivedUpperStarMonoidal A f
  let p := derivedUpperStarLowerStarAdjunction A f
  let := p.rightAdjointLaxBraidedOfδ (leftDerivedUpperStar_map_braiding_hom_δ A f)
  apply MonoidalClosed.tracedDualCompatibility
  intro K
  exact p.isIso_dualComparison_of_isIso_projection
    (leftDerivedUpperStar_map_braiding_hom_δ A f) q e K
    (fun T ↦ inferInstanceAs (IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app T)))

end Comparison

/-- The ambient Verdier exchange, defined as the transpose of pushed-forward evaluation
followed by trace. Source: blueprint order 2123, second proof paragraph
(blueprint: lem-weil-delta-proper-pushforward). Its orientation is F DX to DY F. -/
noncomputable def properAmbientVerdierExchangeMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] (K : DerivedCategoryModule Λ X) :
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
        ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ g)).obj (op K)) ⟶
      (verdierDual (ModuleCat.{u + 1} Λ) g).obj
        (op ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K)) :=
  ambientDirectImageDualComparison (ModuleCat.{u + 1} Λ) f
    (properAmbientDualityTrace Λ f g) K

/-- Proper direct image carries the canonical double-dual arrow to the canonical
one under its ambient exchange. Source: blueprint order 2123, final displayed comparison
(blueprint: lem-weil-delta-proper-pushforward).
The middle equality is the comparison square before inverting either exchange map;
its two sides have target DY(F(DX K)). Thus it states the double-dual comparison
without assuming either double-dual arrow invertible. -/
def ProperAmbientDoubleDualCompatibility
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ S)
    [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] : Prop :=
  AmbientDirectImageDoubleDualCompatibility (ModuleCat.{u + 1} Λ) f
    (properAmbientDualityTrace Λ f g)

/-- The canonical ambient exchange for proper direct image identifies the two double-dual
arrows on arbitrary complexes; invertibility of delta after direct image implies
invertibility of the direct image of delta. Source: blueprint order 2123
(blueprint: lem-weil-delta-proper-pushforward).

Proof:
1. Transport the exceptional adjunction across properAmbientShriekStarIso. The
   canonical mate properAmbientDualizingIso identifies the two dualizing objects;
   its inverse followed by the exceptional counit is properAmbientDualityTrace.
2. Use the existing monoidal pullback and its compatibility with the descended
   braiding. Its right adjoint is lax braided. The product is the projection map
   followed by the ordinary counit, as verified by product_eq_laxProduct.
3. The generic dual comparison is the transpose of pushed-forward signed evaluation,
   by dualComparison_eq_curry. The double-dual normalization is verified before
   specialization by doubleDual_eq_transpose. Thus the canonical closed-category
   maps give the specified evaluation and exchange.
4. The unbounded finite-coefficient proper projection theorem makes every projection
   component invertible. Apply isIso_dualComparison_of_isIso_projection to the
   transported exceptional adjunction and the inverse dualizing isomorphism.
5. Naturality follows from the internal-Hom comparison and precomposition identities.
   Apply map_toIhomIhom_comp_dualComparison for the uninverted double-dual square.
   Apply isIso_map_toIhomIhom_iff using the comparisons at K and at its dual for the
   final implication. No geometric biduality or reflection of isomorphisms is used.
-/
theorem proper_ambient_double_dual_compatibility
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    ProperAmbientDoubleDualCompatibility Λ f aY := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ f
  change AmbientDirectImageDoubleDualCompatibility (ModuleCat.{u + 1} Λ) f
    (properAmbientDualityTrace Λ f aY)
  unfold properAmbientDualityTrace
  exact ambientDirectImageDoubleDualCompatibility (ModuleCat.{u + 1} Λ) f
    (Q := rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f)
    (W := dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ aY))
    (W' := dualizingComplex (ModuleCat.{u + 1} Λ) aY)
    ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).ofNatIsoLeft
      (properAmbientShriekStarIso Λ f)) (properAmbientDualizingIso Λ f aY).symm

end AlgebraicGeometry.Etale
