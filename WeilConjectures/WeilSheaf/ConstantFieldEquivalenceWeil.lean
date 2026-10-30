/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCyclicTwist
public import WeilConjectures.WeilSheaf.ConstantFieldEquivalencePullback
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.Tensor

/-!
# Lisse Weil sheaves over a smaller base field

Let `k₀ ⊆ k'` be finite fields with `[k' : k₀] = m + 1` and `V` a `k'`-scheme, regarded also as a
`k₀`-scheme. The equivalence `ProEtaleWeilSheaf.constantFieldFunctor` (taking the first piece of
the decomposition of `V ⊗_{k₀} k̄` into the Frobenius conjugates of `V ⊗_{k'} k̄`) restricts to a
fully faithful functor `WeilSheaf.constantFieldFunctor` between Weil sheaves relative to `k₀` and
relative to `k'`, such that:

* it takes a constant twist by `b` to the constant twist by `b ^ (m + 1)`
  (`AlgebraicGeometry.WeilSheaf.constantFieldFunctorConstantTwistIso`);
* it takes `p₀^* H` to `p'^* H`
  (`AlgebraicGeometry.WeilSheaf.constantFieldFunctorGeometricFiberPullbackIso`);
* every lisse Weil sheaf relative to `k'` comes from a lisse Weil sheaf relative to `k₀`
  (`AlgebraicGeometry.WeilSheaf.exists_isLisse_constantFieldFunctor_obj_iso`), so that it
  preserves irreducible lisse sheaves
  (`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.constantFieldFunctor`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor Limits

noncomputable section

namespace AlgebraicGeometry

open ProEtale

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Finite k₀] [Finite k'] [Algebra k₀ k']
  {l : ℕ} [Fact l.Prime] {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
  [V.Over (Spec (CommRingCat.of k'))]
  (hc : (V ↘ Spec (CommRingCat.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) =
    V ↘ Spec (CommRingCat.of k₀))
  {m : ℕ} (hm : Module.finrank k₀ k' = m + 1)

namespace ProEtaleWeilSheaf

variable (l) in
/-- **The constant field equivalence takes a constant twist by `b` to the constant twist by
`b ^ (m + 1)`**: the first piece is reached after `m + 1` applications of the Frobenius. -/
def constantFieldFunctorObjTwistIso (K : ProEtaleWeilSheaf k₀ l V) (b : (PadicAlgCl l)ˣ) :
    (constantFieldFunctor l hc hm).obj
        (IsoAlgebra.mk K.carrier (K.str ≪≫ WeilCoefficients.smulIso b K.carrier)) ≅
      IsoAlgebra.mk ((constantFieldFunctor l hc hm).obj K).carrier
        (((constantFieldFunctor l hc hm).obj K).str ≪≫
          WeilCoefficients.smulIso (b ^ (m + 1)) ((constantFieldFunctor l hc hm).obj K).carrier) :=
  (cyclicDecomposition l hc hm).functorObjTwistIso K (fun X ↦ WeilCoefficients.smulIso b X)
    (fun n Y ↦ WeilCoefficients.smulIso (b ^ n) Y)
    (fun i X ↦ by
      rw [pow_one]
      exact AdicSheaf.adicUpperStar_map_smul _ _ _)
    (fun n Y ↦ by
      change AdicSheaf.smul _ Y = AdicSheaf.smul _ Y ≫ AdicSheaf.smul _ Y
      rw [AdicSheaf.smul_smul, pow_succ, Units.val_mul, pow_one]
      rfl)
    (fun n Y Y' f ↦ AdicSheaf.smul_comp _ f)
    (fun Y ↦ by
      change AdicSheaf.smul _ Y = _
      rw [pow_zero, Units.val_one]
      exact AdicSheaf.smul_one Y)

end ProEtaleWeilSheaf

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k' ≠ l)]

variable (l) in
/-- The constant field equivalence, on Weil sheaves: the first piece of a constructible Weil
sheaf relative to `k₀` is a constructible Weil sheaf relative to `k'`. -/
def constantFieldFunctor : WeilSheaf k₀ l V ⥤ WeilSheaf k' l V :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ ProEtaleWeilSheaf.constantFieldFunctor l hc hm)
    fun G ↦ G.property.upperStar _

/-- The constant field functor on Weil sheaves is fully faithful. -/
def constantFieldFunctorFullyFaithful : (constantFieldFunctor l hc hm).FullyFaithful :=
  have := (ObjectProperty.fullyFaithfulι (objectProperty k' l V)).faithful
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    (((ObjectProperty.fullyFaithfulι _).comp (.ofFullyFaithful _)).ofIso
      (ObjectProperty.liftCompιIso _ _ _).symm)

/-- The constant field functor preserves lisse sheaves. -/
lemma IsLisse.constantFieldFunctor {G : WeilSheaf k₀ l V} (hG : G.IsLisse) :
    ((WeilSheaf.constantFieldFunctor l hc hm).obj G).IsLisse :=
  hG.upperStar _

/-- **The constant field functor takes a constant twist by `b` to the constant twist by
`b ^ (m + 1)`.** -/
def constantFieldFunctorConstantTwistIso (G : WeilSheaf k₀ l V) (b : (PadicAlgCl l)ˣ) :
    (constantFieldFunctor l hc hm).obj (G.constantTwist b) ≅
      ((constantFieldFunctor l hc hm).obj G).constantTwist (b ^ (m + 1)) :=
  ObjectProperty.isoMk _ (ProEtaleWeilSheaf.constantFieldFunctorObjTwistIso l hc hm G.obj b)

/-- **The constant field functor takes `p₀^* H` to `p'^* H`**, with their canonical Weil
structures. -/
def constantFieldFunctorGeometricFiberPullbackIso {H : AdicSheaf l V} (hH : IsAdicLisseSheaf H) :
    (constantFieldFunctor l hc hm).obj (geometricFiberPullback (k₀ := k₀) hH) ≅
      geometricFiberPullback (k₀ := k') hH :=
  ObjectProperty.isoMk _
    (ProEtaleWeilSheaf.constantFieldFunctorObjGeometricFiberPullbackIso l hc hm H)

/-- A family of zero objects is a zero object of the product category. -/
lemma _root_.CategoryTheory.Limits.IsZero.pi {ι : Type*} {D : ι → Type*}
    [∀ i, Category (D i)] {X : ∀ i, D i} (h : ∀ i, IsZero (X i)) : IsZero X :=
  ⟨fun Y ↦ ⟨⟨fun i ↦ (h i).to_ (Y i)⟩, fun _ ↦ funext fun i ↦ (h i).eq_of_src _ _⟩,
    fun Y ↦ ⟨⟨fun i ↦ (h i).from_ (Y i)⟩, fun _ ↦ funext fun i ↦ (h i).eq_of_tgt _ _⟩⟩

/-- A Weil sheaf whose image under the constant field functor vanishes vanishes: all the pieces
of its underlying sheaf are isomorphic to the first one. -/
lemma isZero_of_isZero_constantFieldFunctor_obj {G : WeilSheaf k₀ l V}
    (h : IsZero ((constantFieldFunctor l hc hm).obj G)) : IsZero G := by
  set P := ProEtaleWeilSheaf.cyclicDecomposition l hc hm
  have h₀ : IsZero ((P.J 0).obj G.obj.carrier) := isZero_iff_isZero_carrier.1 h
  have := P.fullyFaithful.full
  have := P.fullyFaithful.faithful
  refine isZero_iff_isZero_carrier.2 (IsZero.of_full_of_faithful_of_isZero (Functor.pi' P.J) _
    (IsZero.pi fun i ↦ h₀.of_iso (P.chain G.obj i)))

/-- A zero Weil sheaf has zero image under the constant field functor. -/
lemma isZero_constantFieldFunctor_obj {G : WeilSheaf k₀ l V} (h : IsZero G) :
    IsZero ((constantFieldFunctor l hc hm).obj G) := by
  have := (adicUpperStarLowerStarAdjunction l
    (ProEtaleWeilSheaf.pieceMap (m := m) hc 0)).isLeftAdjoint
  exact isZero_iff_isZero_carrier.2
    (Functor.map_isZero ((ProEtaleWeilSheaf.pieceMap (m := m) hc 0)^*ᵃ[l])
      (isZero_iff_isZero_carrier.1 h))

/-- **Every lisse Weil sheaf relative to `k'` comes from a lisse Weil sheaf relative to `k₀`**:
its preimage under the constant field equivalence is lisse, all of its pieces being isomorphic
to the first one, and being lisse is local for the open cover by the pieces. -/
lemma exists_isLisse_constantFieldFunctor_obj_iso {G' : WeilSheaf k' l V} (hG' : G'.IsLisse) :
    ∃ G : WeilSheaf k₀ l V, G.IsLisse ∧ Nonempty ((constantFieldFunctor l hc hm).obj G ≅ G') := by
  set P := ProEtaleWeilSheaf.cyclicDecomposition l hc hm
  set K := (ProEtaleWeilSheaf.constantFieldFunctor l hc hm).objPreimage G'.obj
  let e := (ProEtaleWeilSheaf.constantFieldFunctor l hc hm).objObjPreimageIso G'.obj
  have hpiece (i : Fin (m + 1)) :
      IsAdicLisseSheaf ((ProEtaleWeilSheaf.pieceMap hc i)^*ᵃ[l].obj K.carrier) :=
    IsAdicLisseSheaf.of_iso (P.chain K i ≪≫ (IsoAlgebra.forget _).mapIso e).symm hG'
  have hcov : Presieve.ofArrows _ (ProEtaleWeilSheaf.pieceMap hc) ∈
      Scheme.proetalePrecoverage (V ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr
        ⟨fun x ↦ (ProEtaleWeilSheaf.existsUnique_mem_range_pieceMap hc hm x).exists,
          fun i ↦ inferInstance⟩)
  have hK : IsAdicLisseSheaf K.carrier := IsAdicLisseSheaf.of_cover _ hcov hpiece
  exact ⟨⟨K, hK.isAdicConstructibleSheaf⟩, hK, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **The constant field functor preserves irreducible lisse sheaves.** -/
lemma IsIrreducibleLisse.constantFieldFunctor {G : WeilSheaf k₀ l V}
    (hG : G.IsIrreducibleLisse) :
    ((WeilSheaf.constantFieldFunctor l hc hm).obj G).IsIrreducibleLisse := by
  refine ⟨hG.1.constantFieldFunctor hc hm,
    fun h ↦ hG.2.1 (isZero_of_isZero_constantFieldFunctor_obj hc hm h), fun G'' i hi hG'' ↦ ?_⟩
  obtain ⟨Q, hQ, ⟨e⟩⟩ := exists_isLisse_constantFieldFunctor_obj_iso hc hm hG''
  set ff := constantFieldFunctorFullyFaithful (l := l) hc hm
  have := ff.faithful
  have hj : Mono (ff.preimage (e.hom ≫ i)) := ⟨fun g h hgh ↦ ff.map_injective
    ((cancel_mono (e.hom ≫ i)).1 (by
      rw [← ff.map_preimage (e.hom ≫ i), ← Functor.map_comp, ← Functor.map_comp, hgh]))⟩
  rcases hG.2.2 Q _ hj hQ with hz | hiso
  · exact Or.inl ((isZero_constantFieldFunctor_obj hc hm hz).of_iso e.symm)
  · refine Or.inr ?_
    have : IsIso (e.hom ≫ i) := by
      rw [← ff.map_preimage (e.hom ≫ i)]
      infer_instance
    exact IsIso.of_isIso_comp_left e.hom i

end WeilSheaf

end AlgebraicGeometry
