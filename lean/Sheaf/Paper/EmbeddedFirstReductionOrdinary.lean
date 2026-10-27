/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.EmbeddedFiniteCoefficientRealization
import all Sheaf.Paper.IntegralModelsEmbeddedCompletion
import all Sheaf.Paper.ConstantCompletionEquivalence
import all Sheaf.Paper.ConstantCompletionCore
import Sheaf.Paper.RingedTopoiTensorSections
import all Sheaf.Paper.IntegralModelsEmbeddedResidueSections
import all Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.Paper.EmbeddedFiniteScalarIsIso

/-! # Ordinary first reduction square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  IntegralModelsStacks.smallMap IntegralModelsStacks.smallModules ConstantCompletion.completed

private theorem small_map_comp (X : Scheme.{u})
    {R S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ T) [IsMonHom g] :
    IntegralModelsStacks.smallMap X (f ≫ g) =
      IntegralModelsStacks.smallMap X f ≫ IntegralModelsStacks.smallMap X g := by
  unfold IntegralModelsStacks.smallMap
  ext U x
  rfl

private def smallCoefficientIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S) :
    IntegralModelsStacks.smallRing X R ≅ IntegralModelsStacks.smallRing X S where
  hom := IntegralModelsStacks.smallMap X e.hom.hom
  inv := IntegralModelsStacks.smallMap X e.inv.hom
  hom_inv_id := by
    unfold IntegralModelsStacks.smallMap
    let i := (Mon.forget _).mapIso e
    ext U x
    change i.inv.hom.app (op (AsSmall.down.obj U.unop))
      (i.hom.hom.app (op (AsSmall.down.obj U.unop)) x) = x
    exact congrArg (fun f ↦ f.hom.app (op (AsSmall.down.obj U.unop)) x) i.hom_inv_id
  inv_hom_id := by
    unfold IntegralModelsStacks.smallMap
    let i := (Mon.forget _).mapIso e
    ext U x
    change i.hom.hom.app (op (AsSmall.down.obj U.unop))
      (i.inv.hom.app (op (AsSmall.down.obj U.unop)) x) = x
    exact congrArg (fun f ↦ f.hom.app (op (AsSmall.down.obj U.unop)) x) i.inv_hom_id

private theorem small_composite_surjective (X : Scheme.{u})
    {R S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
    (q : R ⟶ S) [IsMonHom q] (e : S ⟶ T) [IsMonHom e] [IsIso e]
    (hq : ∀ U, Function.Surjective ((IntegralModelsStacks.smallMap X q).hom.app U)) :
    ∀ U, Function.Surjective ((IntegralModelsStacks.smallMap X (q ≫ e)).hom.app U) := by
  let es := smallCoefficientIso X (Mon.mkIso' (asIso e))
  intro U
  rw [small_map_comp]
  let i := section_ring_equiv es U
  intro y
  obtain ⟨x, hx⟩ := hq U (i.symm y)
  refine ⟨x, ?_⟩
  change i ((IntegralModelsStacks.smallMap X q).hom.app U x) = y
  rw [hx, RingEquiv.apply_symm_apply]

private theorem small_composite_kernel (X : Scheme.{u})
    {R S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
    (q : R ⟶ S) [IsMonHom q] (e : S ⟶ T) [IsMonHom e] [IsIso e] (U) :
    RingHom.ker ((IntegralModelsStacks.smallMap X (q ≫ e)).hom.app U).hom =
      RingHom.ker ((IntegralModelsStacks.smallMap X q).hom.app U).hom := by
  let es := smallCoefficientIso X (Mon.mkIso' (asIso e))
  let i := section_ring_equiv es U
  rw [small_map_comp]
  ext x
  change i ((IntegralModelsStacks.smallMap X q).hom.app U x) = 0 ↔
    (IntegralModelsStacks.smallMap X q).hom.app U x = 0
  constructor
  · intro hx
    exact i.injective (hx.trans (map_zero i).symm)
  · intro hx
    rw [hx, map_zero]

private def smallExtensionIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    Mod.extendScalars f ⋙ IntegralModelsStacks.smallModules X S ≅
      IntegralModelsStacks.smallModules X R ⋙
        ConstantCompletion.change (IntegralModelsStacks.smallMap X f) := by
  have := smallModulesEquivalence X R
  have := smallModulesEquivalence X S
  let a := Mod.extendRestrictAdjunction f
  let b := SheafOfModules.RingedTensor.tensorAdjunction
    (IntegralModelsStacks.smallMap X f)
  let β := smallRestrictionIso X f
  let α := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β.hom)).natTrans
  have : IsIso α := InternalAbelianSheafModule.inverseMate_isIso a b β
  exact (asIso α).symm

private theorem smallQuotientComparison (X : Scheme.{u})
    {R B S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj B] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj B] [IsCommMonObj S]
    (φ : R ⟶ B) [IsMonHom φ] (q : R ⟶ S) [IsMonHom q]
    (p : B ⟶ S) [IsMonHom p] (h : φ ≫ p = q)
    (hq : ∀ U, Function.Surjective ((IntegralModelsStacks.smallMap X q).hom.app U))
    (hk : ∀ U, RingHom.ker ((IntegralModelsStacks.smallMap X p).hom.app U).hom =
      Ideal.span (((IntegralModelsStacks.smallMap X φ).hom.app U).hom ''
        (RingHom.ker ((IntegralModelsStacks.smallMap X q).hom.app U).hom : Set _))) :
    Nonempty (Mod.comap φ ⋙ Mod.extendScalars q ≅ Mod.extendScalars p) := by
  let φs := IntegralModelsStacks.smallMap X φ
  let qs := IntegralModelsStacks.smallMap X q
  let ps := IntegralModelsStacks.smallMap X p
  have hs : φs ≫ ps = qs := by
    dsimp only [φs, ps, qs]
    unfold IntegralModelsStacks.smallMap
    ext U x
    exact congrArg (fun f ↦ f.hom.app (op (AsSmall.down.obj U.unop)) x) h
  obtain ⟨e, _, _⟩ := ConstantCompletion.quotientTensorIso_exists φs qs ps hs hq hk
  let FB := IntegralModelsStacks.smallModules X B
  let FS := IntegralModelsStacks.smallModules X S
  have : FS.IsEquivalence := smallModulesEquivalence X S
  let α : (Mod.comap φ ⋙ Mod.extendScalars q) ⋙ FS ≅ Mod.extendScalars p ⋙ FS :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Mod.comap φ) (smallExtensionIso X q) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (smallRestrictionIso X φ) (ConstantCompletion.change qs) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft FB e ≪≫
      (smallExtensionIso X p).symm
  exact ⟨Functor.fullyFaithfulCancelRight FS α⟩

private theorem smallQuotientComparisonIso (X : Scheme.{u})
    {R B S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj B] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj B] [IsCommMonObj S] [IsCommMonObj T]
    (φ : R ⟶ B) [IsMonHom φ] (q : R ⟶ S) [IsMonHom q]
    (e : S ⟶ T) [IsMonHom e] [IsIso e] (p : B ⟶ T) [IsMonHom p]
    (h : φ ≫ p = q ≫ e)
    (hq : ∀ U, Function.Surjective ((IntegralModelsStacks.smallMap X q).hom.app U))
    (hk : ∀ U, RingHom.ker ((IntegralModelsStacks.smallMap X p).hom.app U).hom =
      Ideal.span (((IntegralModelsStacks.smallMap X φ).hom.app U).hom ''
        (RingHom.ker ((IntegralModelsStacks.smallMap X q).hom.app U).hom : Set _))) :
    Nonempty (Mod.comap φ ⋙ Mod.extendScalars (q ≫ e) ≅ Mod.extendScalars p) := by
  apply smallQuotientComparison X φ (q ≫ e) p h
    (small_composite_surjective X q e hq)
  intro U
  rw [small_composite_kernel X q e U]
  exact hk U

private theorem principal_kernels_image
    {R B S T : Type*} [CommRing R] [CommRing B] [CommRing S] [CommRing T]
    (φ : R →+* B) (q : R →+* S) (p : B →+* T) (r : R)
    (hR : RingHom.ker q = Ideal.span {r})
    (hB : RingHom.ker p = Ideal.span {φ r}) :
    RingHom.ker p = Ideal.span (φ '' (RingHom.ker q : Set R)) := by
  rw [hB, ← Ideal.map_span, Ideal.span_eq, hR, Ideal.map_span, Set.image_singleton]

private theorem quotient_section_data
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type v) [CommRing A] [IsNoetherianRing A] (t : A)
    {R B S T : Sheaf J CommRingCat.{v}} (φ : R ⟶ B) (q : R ⟶ S) (p : B ⟶ T)
    (h : ∃ (a : R ≅ ConstantCompletion.constant J A)
      (b : B ≅ ConstantCompletion.completed J A (Ideal.span {t}))
      (c : S ≅ ConstantCompletion.finite J A (Ideal.span {t}) 0)
      (d : T ≅ ConstantCompletion.finite J A (Ideal.span {t}) 0),
      φ ≫ b.hom = a.hom ≫ ConstantCompletion.coefficientMap J A (Ideal.span {t}) ∧
      q ≫ c.hom = a.hom ≫ ConstantCompletion.quotient J A (Ideal.span {t}) 0 ∧
      p ≫ d.hom = b.hom ≫ ConstantCompletion.projection J A (Ideal.span {t}) 0) :
    (∀ U, Function.Surjective (q.hom.app U)) ∧
      (∀ U, RingHom.ker (p.hom.app U).hom =
        Ideal.span ((φ.hom.app U).hom '' (RingHom.ker (q.hom.app U).hom : Set _))) := by
  obtain ⟨a, b, c, d, hφ, hq, hp⟩ := h
  constructor
  · intro U
    exact iso_square_surjective (q.hom.app U).hom
      ((ConstantCompletion.quotient J A (Ideal.span {t}) 0).hom.app U).hom
      (section_ring_equiv a U) (section_ring_equiv c U)
      (congrArg (fun f ↦ f.hom.app U) hq |> fun h ↦ ConcreteCategory.congr_hom h)
      (principal_completion_kernels J A t U.unop).1
  · obtain ⟨_, r, _, _, hR, hB⟩ :=
      residue_sections_of_completion J A t φ q p a b c d hφ hq hp
    intro U
    exact principal_kernels_image (φ.hom.app U).hom (q.hom.app U).hom
      (p.hom.app U).hom (r.val U) (hR U.unop) (hB U.unop)

private theorem adjunction_desc_naturality
    {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A B : C} {X Y : D} (f : A ⟶ B) (g : X ⟶ Y)
    (a : A ⟶ R.obj X) (b : B ⟶ R.obj Y) (h : f ≫ b = a ≫ R.map g) :
    L.map f ≫ (adj.homEquiv B Y).symm b = (adj.homEquiv A X).symm a ≫ g := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

private theorem constant_function_naturality
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf _ CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (f.comp ULift.ringEquiv.toRingHom))))) ≫ constantToContinuous B =
      constantToContinuous A ≫ Profinite.continuousMapRingSheafMap f hf := by
  let c := constantCommuteCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let f' := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.comp ULift.ringEquiv.toRingHom))
  have hc := c.hom.naturality f'
  unfold constantToContinuous
  rw [← Category.assoc]
  erw [hc]
  simp only [Category.assoc]
  apply (cancel_epi ((c.app (CommRingCat.of (ULift.{u + 1} A))).hom)).2
  apply adjunction_desc_naturality
    (sheafificationAdjunction (coherentTopology Profinite.{u}) RingCat.{u + 1})
  ext U x
  rfl

attribute [-instance] integralModel_coefficientMonObj in
private theorem first_reduction_square
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :
    scalarMap ℓ E X ≫ (integralModelReductionMap X ℓ E π 1).hom =
      residueMap ℓ E π X ≫ finiteScalarMap X (completedResidue ℓ E π 0) := by
  let F := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let f := Ideal.Quotient.mk ((Ideal.span {π}) ^ (0 + 1))
  have hp : scalarPointMap.{u} ℓ E ≫ F.map (completedReduction ℓ E π 0) =
      discreteMap f ≫ finiteScalarPointMap (completedResidue ℓ E π 0) := by
    have h := F.congr_map (constant_function_naturality f continuous_quot_mk).symm
    simpa only [scalarPointMap, discreteMap, finiteScalarPointMap,
      completedReduction, Functor.map_comp] using h
  change (upperStarFromPoint X).map (scalarPointMap ℓ E) ≫
      (upperStarFromPoint X).map (F.map (completedReduction ℓ E π 0)) =
    (upperStarFromPoint X).map (discreteMap f) ≫
      (upperStarFromPoint X).map (finiteScalarPointMap (completedResidue ℓ E π 0))
  exact ((upperStarFromPoint X).map_comp _ _).symm.trans
    (((upperStarFromPoint X).congr_map hp).trans ((upperStarFromPoint X).map_comp _ _))

set_option maxHeartbeats 1600000 in
-- Specializing the reconstructed coefficient diagrams requires extra definitional checks.
attribute [-instance] integralModel_coefficientMonObj in
/-- Ordinary reduction commutes with restriction of the actual embedded coefficient map.

Source: integral-models proof, first paragraph (1), the common uniformizer quotient;
Stacks Tags 093M, 03ET and 00YV.
(blueprint: lem-sfb-embedded-first-reduction-ordinary).

Proof: write R for constant integral coefficients, B for continuous integral
coefficients, S for the constant first residue ring, and T for the continuous first
residue ring. The constant-function map e : S -> T is an isomorphism because the
residue ring is finite and discrete. The actual quotient maps satisfy e q = p phi:
this is the equality on constant sections induced by the quotient ring homomorphism,
and sheafification and inverse image preserve it. Locally, q and p are surjective,
and their kernels are respectively pi R and pi B. Indeed the discrete quotient is
locally liftable to integer constants, and a continuous function to the finite
residue ring is locally constant; its zero fiber is precisely the ideal generated
by pi. These assertions are preserved by the exact inverse image from the point.

For a B-module M define S tensor_R M -> T tensor_B M by
s tensor m |-> e(s) tensor m. Its inverse is local: first identify T with S, then
send 1 tensor m to 1 tensor m in S tensor_R M. To check B-balancing, locally lift
the residue of b in B to a in R. Since b - phi(a) is in pi B, multiplication by
b on S tensor_R M agrees with multiplication by the residue of a. Thus the local
inverse respects b tensor m = 1 tensor bm. Different lifts differ by pi R and
produce the same tensor. The maps therefore glue after sheafification, are inverse
on local pure tensors, and commute with every map of M. Scalar extension along e
identifies S-modules with T-modules. Associativity of scalar extension gives the
stated natural isomorphism. No resolution or K-flatness is involved. Empty covers,
the zero module and unboundedness cause no additional condition. -/
theorem embeddedFirstReductionOrdinary
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X]
    [Finite (completedResidue ℓ E π 0)] [DiscreteTopology (completedResidue ℓ E π 0)] :
    Nonempty ((Mod.comap (scalarMap ℓ E X) ⋙ Mod.extendScalars (residueMap ℓ E π X)) ⋙
      Mod.extendScalars (finiteScalarMap X (completedResidue ℓ E π 0)) ≅
        Mod.extendScalars (integralModelReductionMap X ℓ E π 1).hom) := by
  let φ := scalarMap ℓ E X
  let q := residueMap ℓ E π X
  let e := finiteScalarMap X (completedResidue ℓ E π 0)
  let p := (integralModelReductionMap X ℓ E π 1).hom
  have : IsIso e := embeddedFiniteScalarIsIso X (completedResidue ℓ E π 0)
  let φs := IntegralModelsStacks.smallMap X φ
  let qs := IntegralModelsStacks.smallMap X q
  let ps := IntegralModelsStacks.smallMap X p
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let A := ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)
  let : IsNoetherianRing A :=
    isNoetherianRing_of_ringEquiv (PadicAlgCl.integers ℓ E.1) ULift.ringEquiv.symm
  have hd := quotient_section_data J A (ULift.up π) φs qs ps
    (integralModelsEmbeddedCompletionDiagram ℓ E π hπ X)
  obtain ⟨i⟩ := smallQuotientComparisonIso X φ q e p
    (first_reduction_square ℓ E π X) hd.1 hd.2
  exact ⟨Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Mod.comap φ) (Mod.extendScalarsComp q e).symm ≪≫ i⟩

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded
