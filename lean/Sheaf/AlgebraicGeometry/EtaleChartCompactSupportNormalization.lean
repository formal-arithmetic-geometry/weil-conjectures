/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Unbounded compact-support normalization on a closed affine chart

Source: main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Locality and Charts, closed-chart supplement;
Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-pur-etale-chart-compact-support-normalization).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The consequences and the specified normalization on the entire derived categories.
The universally quantified instances in the last clause install consequences asserted
in the preceding clauses; they are not additional geometric or coefficient hypotheses.
The two adjunction equalities fix the ordinary extension-by-zero evaluation counits.
The isomorphism equality specifies every factor, so the refinement-independent
comparisons of the dependency determine the isomorphism, rather than an arbitrary choice.
Source: main-20261015, exceptional-reduction Locality and Charts, closed-chart supplement,
Steps 1--2; Stacks Tags 0F7B and 0F7J
(blueprint: lem-pur-etale-chart-compact-support-normalization). -/
def EtaleChartCompactSupportNormalization
    (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (k : Type u) [Field k] {X Y U V W : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) (u : U ⟶ X) (v : V ⟶ Y) (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V)
    (j : W ⟶ AffineSpace (ULift.{u} (Fin r)) V)
    [IsOpenImmersion u] [IsOpenImmersion v] [IsClosedImmersion i]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) : Prop :=
  Finite A ∧ (N : A) = 0 ∧
  (∀ s ∈ ([⟨X, X ↘ Spec (.of k)⟩, ⟨Y, Y ↘ Spec (.of k)⟩,
      ⟨U, u ≫ (X ↘ Spec (.of k))⟩, ⟨V, v ≫ (Y ↘ Spec (.of k))⟩,
      ⟨AffineSpace (ULift.{u} (Fin r)) V,
        (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ≫ v ≫ (Y ↘ Spec (.of k))⟩,
      ⟨W, j ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ≫ v ≫ (Y ↘ Spec (.of k))⟩] :
        List (Σ S : Scheme.{u}, S ⟶ Spec (.of k))),
    IsNoetherian s.1 ∧ LocallyOfFiniteType s.2 ∧ QuasiCompact s.2 ∧
      IsUnit (N : Γ(s.1, ⊤))) ∧
  (∀ a ∈ ([⟨U, X, u⟩, ⟨V, Y, v⟩,
      ⟨W, AffineSpace (ULift.{u} (Fin r)) V, j⟩,
      ⟨X, Y, f⟩, ⟨U, AffineSpace (ULift.{u} (Fin r)) V, i⟩,
      ⟨AffineSpace (ULift.{u} (Fin r)) V, V,
        AffineSpace (ULift.{u} (Fin r)) V ↘ V⟩,
      ⟨U, Y, u ≫ f⟩,
      ⟨U, V, i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)⟩,
      ⟨U, Y, (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v⟩,
      ⟨AffineSpace (ULift.{u} (Fin r)) V, Y,
        (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ≫ v⟩,
      ⟨W, V, j ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)⟩,
      ⟨W, Y, (j ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v⟩,
      ⟨X, Spec (.of k), X ↘ Spec (.of k)⟩,
      ⟨Y, Spec (.of k), Y ↘ Spec (.of k)⟩,
      ⟨U, Spec (.of k), u ≫ (X ↘ Spec (.of k))⟩,
      ⟨V, Spec (.of k), v ≫ (Y ↘ Spec (.of k))⟩,
      ⟨AffineSpace (ULift.{u} (Fin r)) V, Spec (.of k),
        ((AffineSpace (ULift.{u} (Fin r)) V ↘ V) ≫ v) ≫ (Y ↘ Spec (.of k))⟩,
      ⟨W, Spec (.of k),
        ((j ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) ≫ (Y ↘ Spec (.of k))⟩] :
        List (Σ S T : Scheme.{u}, S ⟶ T)),
    IsSeparated a.2.2 ∧ LocallyOfFiniteType a.2.2 ∧ QuasiCompact a.2.2 ∧
      HasCompactification a.2.2) ∧
  PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} A) i) ∧
  PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i) ∧
  (∀ [Finite A] [QuasiCompact u] [QuasiCompact v] [QuasiCompact f]
      [QuasiCompact (u ≫ f)]
      [HasCompactification u] [HasCompactification v] [HasCompactification f]
      [HasCompactification (u ≫ f)]
      [HasCompactification (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V))]
      [HasCompactification ((i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v)],
    ∃ (au : (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory ⊣
        (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory)
      (av : (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory ⊣
        (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory),
      au = derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u ∧
      av = derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v ∧
      ∃ e : (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
        ((lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} A)
            (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ⋙
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory,
        e =
          Functor.isoWhiskerRight (rightDerivedLowerShriekIsoOfIsOpenImmersion A u).symm _ ≪≫
          unboundedEtaleLowerShriekCompIso A u f ≪≫
          unboundedEtaleLowerShriekCongr A h ≪≫
          (unboundedEtaleLowerShriekCompIso A
            (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) v).symm ≪≫
          Functor.isoWhiskerRight
            (unboundedEtaleLowerShriekCompIso A i
              (AffineSpace (ULift.{u} (Fin r)) V ↘ V)).symm _ ≪≫
          Functor.isoWhiskerRight
            (Functor.isoWhiskerRight
              (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) i ≪≫
                rightDerivedFunctorLowerStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i)
              _) _ ≪≫
          Functor.isoWhiskerLeft _ (rightDerivedLowerShriekIsoOfIsOpenImmersion A v) ∧
        ∃ μ : ∀ (cf : Compactification f)
            (cp : Compactification (AffineSpace (ULift.{u} (Fin r)) V ↘ V)),
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory ⋙
              rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ≅
            ((lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory ⋙
              rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cp) ⋙
              (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory,
          (∀ cf cp, μ cf cp =
            Functor.isoWhiskerLeft
                (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory
                (rightDerivedLowerShriekIso A cf) ≪≫ e ≪≫
              Functor.isoWhiskerRight
                (Functor.isoWhiskerLeft
                  (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory
                  (rightDerivedLowerShriekIso A cp).symm)
                (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory) ∧
          ∀ cf cf' cp cp',
            Functor.isoWhiskerLeft
                (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory
                (rightDerivedLowerShriekOfCompactificationIso A cf cf') ≪≫ μ cf' cp' =
              μ cf cp ≪≫
                Functor.isoWhiskerRight
                  (Functor.isoWhiskerLeft
                    (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory
                    (rightDerivedLowerShriekOfCompactificationIso A cp cp'))
                  (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory)

/-- The finite coefficient, geometric and normalized unbounded compact-support assertions
on a closed affine chart, including the complementary open.
Source: main-20261015, exceptional-reduction Locality and Charts, closed-chart supplement;
Stacks Tags 0F7B and 0F7J
(blueprint: lem-pur-etale-chart-compact-support-normalization).

Proof:
1. The valuation-ring DVR theorem and finite quotient theorem make A finite.
   Since ell is in the uniformizer ideal, its nth power vanishes in A. The nonzero
   element ell^n of k is invertible, and remains invertible on every k-scheme.
2. Finite type over the Noetherian field gives Noetherian X,Y. Their affine opens
   U,V are Noetherian; opens of a Noetherian space are quasi-compact, so u,v are
   quasi-compact and finite type.
3. The polynomial presentation of the affine space makes its projection finite type.
   Hence P is Noetherian, as is W; the same open argument gives j quasi-compact and
   finite type. This includes r=0 and empty charts.
4. Separated cancellation and finite-type cancellation make every displayed arrow
   and composite separated of finite type. Their targets are qcqs. Apply Nagata
   to obtain the compactifications.
5. Exact extension by zero and exact inverse image give the ordinary open adjunctions.
   Descend their termwise units and evaluation counits through homotopy localization;
   the triangle identities descend by faithfulness of localization.
6. The closed immersion is proper, finite and quasi-finite. The quasi-finite
   proper-support comparison identifies its compact support with exact termwise i_*.
7. The identity-proper compactifications of the open factors give their canonical
   identifications with exact extension by zero. Use precisely the source-open
   composition formula of lem-amb-compact-support-open-source-composition.
8. Compose alpha(f,u), transport along the chart equality, inverse alpha(v,pi i),
   inverse alpha(pi,i), then the proper closed and open identifications. Coherence
   and refinement compatibility of lem-amb-unbounded-compact-support-comparisons
   give refinement independence. Every factor is unbounded. -/
theorem etaleChartCompactSupportNormalization
    (ell : ℕ) [Fact ell.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hell : ell ≠ p)
    {X Y U V W : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsAffine U] [IsAffine V] (u : U ⟶ X) (v : V ⟶ Y)
    [IsOpenImmersion u] [IsOpenImmersion v] (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V) [IsClosedImmersion i]
    (j : W ⟶ AffineSpace (ULift.{u} (Fin r)) V) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) :
    EtaleChartCompactSupportNormalization (Padic.coefficientExtensionRing ell E n)
      (ell ^ n) k f u v r i j h := by
  classical
  have _ := hp
  have _ := hij
  let A := Padic.coefficientExtensionRing ell E n
  have hfin : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
  have hdvr := (Padic.extension_integers_dvr ell E
    (Padic.coefficientExtensionAbsoluteValue ell E)
    (spectralNorm_extends (K := Padic ell) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ell E} :
      Set (Padic.coefficientExtensionIntegers ell E)) =
      Padic.coefficientExtensionMaximalIdeal ell E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hmem : (ell : Padic.coefficientExtensionIntegers ell E) ∈
      Padic.coefficientExtensionMaximalIdeal ell E := by
    apply hdvr.2.1 _ |>.2
    change Padic.coefficientExtensionAbsoluteValue ell E (ell : E) < 1
    rw [← map_natCast (algebraMap (Padic ell) E) ell]
    exact (spectralNorm_extends (K := Padic ell) (L := E) (ell : Padic ell)).trans_lt
      (Padic.norm_p_lt_one)
  have hzero : ((ell ^ n : ℕ) : A) = 0 := by
    change ((ell ^ n : ℕ) : Padic.coefficientExtensionIntegers ell E ⧸
      Padic.coefficientExtensionIdeal ell E n) = 0
    rw [← map_natCast (Ideal.Quotient.mk _) (ell ^ n), Ideal.Quotient.eq_zero_iff_mem]
    change ((ell ^ n : ℕ) : Padic.coefficientExtensionIntegers ell E) ∈ _
    rw [Nat.cast_pow]
    apply Ideal.pow_mem_pow
    rwa [hgen]
  have hellk : (ell : k) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff k p]
    intro hd
    rcases (Fact.out : ell.Prime).eq_one_or_self_of_dvd p hd with h | h
    · exact (CharP.char_ne_one k p) h
    · exact hell h.symm
  have hunit (S : Scheme.{u}) (a : S ⟶ Spec (.of k)) :
      IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤)) := by
    let φ : k →+* Γ(S, ⊤) := a.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
    have hk : IsUnit ((ell ^ n : ℕ) : k) := by
      rw [Nat.cast_pow]
      exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hellk)
    simpa only [map_natCast] using hk.map φ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian u
  have : IsNoetherian U := ⟨⟩
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian v
  have : IsNoetherian V := ⟨⟩
  let P := AffineSpace (ULift.{u} (Fin r)) V
  let π : P ⟶ V := P ↘ V
  have : LocallyOfFiniteType π := inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian P := ⟨⟩
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian j
  have : TopologicalSpace.NoetherianSpace W :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : CompactSpace W := inferInstance
  have : IsNoetherian W := ⟨⟩
  have : IsSeparated (f ≫ (Y ↘ Spec (.of k))) := by
    rw [comp_over]; infer_instance
  have : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of k))
  have : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))) := by
    rw [comp_over]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  unfold EtaleChartCompactSupportNormalization
  refine ⟨hfin, hzero, ?_, ?_, inferInstance, inferInstance, ?_⟩
  · intro s hs
    have hu := hunit s.1 s.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨inferInstance, inferInstance, inferInstance, hu⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  · intro _ _ _ _ _ _ _ _ _ _ _
    refine ⟨derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) u,
      derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) v,
      rfl, rfl, ?_⟩
    let e :=
      Functor.isoWhiskerRight (rightDerivedLowerShriekIsoOfIsOpenImmersion A u).symm _ ≪≫
      unboundedEtaleLowerShriekCompIso A u f ≪≫
      unboundedEtaleLowerShriekCongr A h ≪≫
      (unboundedEtaleLowerShriekCompIso A (i ≫ π) v).symm ≪≫
      Functor.isoWhiskerRight (unboundedEtaleLowerShriekCompIso A i π).symm _ ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight
          (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat A) i ≪≫
            rightDerivedFunctorLowerStarIsoMapDerivedCategory (ModuleCat A) i) _) _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerShriekIsoOfIsOpenImmersion A v)
    refine ⟨e, rfl, ?_⟩
    refine ⟨fun cf cp ↦
      Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat A) u).mapDerivedCategory
        (rightDerivedLowerShriekIso A cf) ≪≫ e ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (lowerStar (ModuleCat A) i).mapDerivedCategory
          (rightDerivedLowerShriekIso A cp).symm)
        (openImmersionLowerShriek (ModuleCat A) v).mapDerivedCategory,
      fun _ _ ↦ rfl, ?_⟩
    intro cf cf' cp cp'
    have hf := (unboundedEtaleCompactSupport_comparison_coherence A f).2
    have hp := (unboundedEtaleCompactSupport_comparison_coherence A π).2
    have hf' := hf cf cf' (HasCompactification.compactification f)
    have hp' := hp cp cp' (HasCompactification.compactification π)
    change rightDerivedLowerShriekOfCompactificationIso A cf cf' ≪≫
      rightDerivedLowerShriekIso A cf' = rightDerivedLowerShriekIso A cf at hf'
    change rightDerivedLowerShriekOfCompactificationIso A cp cp' ≪≫
      rightDerivedLowerShriekIso A cp' = rightDerivedLowerShriekIso A cp at hp'
    have hp'' : (rightDerivedLowerShriekIso A cp).symm ≪≫
        rightDerivedLowerShriekOfCompactificationIso A cp cp' =
        (rightDerivedLowerShriekIso A cp').symm := by
      rw [← hp']
      simp
    apply Iso.ext
    apply NatTrans.ext
    funext K
    have hfK := congrArg (fun e ↦ e.hom.app
      ((openImmersionLowerShriek (ModuleCat A) u).mapDerivedCategory.obj K)) hf'
    have hpK := congrArg (fun e ↦
      (openImmersionLowerShriek (ModuleCat A) v).mapDerivedCategory.map
        (e.hom.app ((lowerStar (ModuleCat A) i).mapDerivedCategory.obj K))) hp''
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp] at hfK hpK
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    simp only [Category.assoc] at hfK hpK ⊢
    rw [← Category.assoc, hfK]
    rw [hpK]

end AlgebraicGeometry.Etale
