/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.RealWeilSheaves
public import Sheaf.Paper.NormalizedClassicalWeilRealization
public import Sheaf.Paper.EtaleWeilFundamentalRepresentation
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import WeilConjectures.RepresentationTheory.CompositionSeries
import Sheaf.Paper.EtaleWeilRealization

/-! # Geometric quotient filtrations and Weil composition series

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, paragraph 2.
(blueprint: lem-zl-geometric-quotient-weil-composition-series).

The finite diagram is the prescribed filtration, and the supplied cokernel maps
are its prescribed quotients. All quotient comparisons retain those maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace RealSheaves

private theorem quotientOfImage
    {k G A V B : Type*} [Field k] [Group G]
    [AddCommGroup A] [Module k A] [AddCommGroup V] [Module k V]
    [AddCommGroup B] [Module k B]
    {σ : Representation k G A} {ρ : Representation k G V} {τ : Representation k G B}
    (f : σ.IntertwiningMap ρ) (hf : Function.Injective f)
    (N : Subrepresentation ρ) (q : σ.IntertwiningMap τ)
    (hq : Function.Surjective q) (hker : ∀ x, q x = 0 ↔ f x ∈ N) :
    ∃ a : (f.range.subquotient N).Equiv τ,
      ∀ x, a (Submodule.Quotient.mk (LinearEquiv.ofInjective f.toLinearMap hf x)) = q x := by
  let e : A ≃ₗ[k] f.range.toSubmodule := LinearEquiv.ofInjective f.toLinearMap hf
  have he (x : f.range.toSubmodule) : f (e.symm x) = x :=
    LinearEquiv.ofInjective_symm_apply f.toLinearMap x
  -- Transport the prescribed quotient map to the image of its source.
  let p : f.range.toSubmodule →ₗ[k] B := q.toLinearMap.comp e.symm.toLinearMap
  have hp : Function.Surjective p := hq.comp e.symm.surjective
  have hk : N.toSubmodule.comap f.range.toSubmodule.subtype = p.ker := by
    ext x
    change (x : V) ∈ N ↔ q (e.symm x) = 0
    rw [hker, he]
  -- The first isomorphism theorem keeps the prescribed map on quotient representatives.
  let a : (f.range.toSubmodule ⧸ N.toSubmodule.comap f.range.toSubmodule.subtype) ≃ₗ[k] B :=
    (Submodule.quotEquivOfEq _ _ hk).trans (p.quotKerEquivOfSurjective hp)
  have ha (x : f.range.toSubmodule) : a (Submodule.Quotient.mk x) = q (e.symm x) := by
    simp [a, p]
  refine ⟨Representation.Equiv.mk a (fun g ↦ ?_), fun x ↦ ?_⟩
  · apply Submodule.linearMap_qext
    ext x
    change a (Submodule.Quotient.mk _) = τ g (a (Submodule.Quotient.mk x))
    rw [ha, ha]
    calc
      _ = q (σ g (e.symm x)) := congrArg q (by
        apply hf
        rw [he, f.isIntertwining, he]
        rfl)
      _ = _ := q.isIntertwining _ _ g _
  · change a (Submodule.Quotient.mk (e x)) = q x
    rw [ha, e.symm_apply_apply]

variable (S : Setup.{u, u + 1}) (C₀ : Scheme.{u}) [C₀.Over (Spec (.of S.k₀))]
  [hC : Fact (S.IsCurve C₀)]

/-- Inherited finite type, a projection of the chapter curve hypothesis.
Source: d-real-setup (blueprint: lem-zl-geometric-quotient-weil-composition-series). -/
instance geometricQuotientCurve_lft : LocallyOfFiniteType (C₀ ↘ Spec (.of S.k₀)) :=
  hC.out.2.2.2.1

/-- Inherited quasi-compactness, a projection of the chapter curve hypothesis.
Source: d-real-setup (blueprint: lem-zl-geometric-quotient-weil-composition-series). -/
instance geometricQuotientCurve_qc : QuasiCompact (C₀ ↘ Spec (.of S.k₀)) :=
  hC.out.2.2.2.2.1

/-- Inherited separatedness, a projection of the chapter curve hypothesis.
Source: d-real-setup (blueprint: lem-zl-geometric-quotient-weil-composition-series). -/
instance geometricQuotientCurve_separated : IsSeparated (C₀ ↘ Spec (.of S.k₀)) :=
  hC.out.2.1

/-- The existing noetherian base-change structure on the chosen geometric curve.
Source: d-real-setup (blueprint: lem-zl-geometric-quotient-weil-composition-series). -/
instance geometricQuotientCurve_noetherian : IsNoetherian (S.geometricCurve C₀) :=
  @WeilConjectures.zlClassicalNoetherian S.weilFieldDatum
    (Over.mk (C₀ ↘ Spec (.of S.k₀))) hC.out.2.2.2.1 hC.out.2.2.2.2.1

/-- The existing separated base-change structure on the chosen geometric curve.
Source: d-real-setup (blueprint: lem-zl-geometric-quotient-weil-composition-series). -/
instance geometricQuotientCurve_geometricSeparated : (S.geometricCurve C₀).IsSeparated :=
  @WeilConjectures.zlClassicalSeparated S.weilFieldDatum
    (Over.mk (C₀ ↘ Spec (.of S.k₀))) hC.out.2.2.2.1 hC.out.2.2.2.2.1 hC.out.2.1

/-- The coefficient prime is invertible by the existing finite-field coefficient interface.
Source: d-real-setup (blueprint: lem-zl-geometric-quotient-weil-composition-series). -/
instance geometricQuotientCurve_invertible (x : S.geometricCurve C₀) :
    Invertible (S.l : (S.geometricCurve C₀).residueField x) :=
  @WeilConjectures.sfWeilPrimeInvertible S.weilFieldDatum S.l S.l_prime S.l_ne_p
    (Over.mk (C₀ ↘ Spec (.of S.k₀))) hC.out.2.2.2.1 hC.out.2.2.2.2.1 x

/-- The actual classical lisse Weil category on this curve with the fixed coefficients.
Source: def-wf-fundamental-representation
(blueprint: lem-zl-geometric-quotient-weil-composition-series). -/
abbrev curveQuotientWeilSheaf :=
  Scheme.EtaleLisseWeilSheaf S.l S.Qbar (S.weilFrobenius C₀ hC.out)

variable {κ : Type u} [Field κ] [IsAlgClosed κ]
  (t : Spec (.of κ) ⟶ S.geometricCurve C₀)

/-- The actual geometric stalk, with no coordinate replacement.
Source: def-pod-lisse-l-adic-sheaves
(blueprint: lem-zl-geometric-quotient-weil-composition-series). -/
abbrev curveQuotientStalk (F : curveQuotientWeilSheaf S C₀) :=
  Scheme.lisseAlgebraicFiber S.l (S.geometricCurve C₀) S.Qbar t F.carrier

/-- The actual linear stalk map of the prescribed Weil morphism.
Source: def-wf-fundamental-representation
(blueprint: lem-zl-geometric-quotient-weil-composition-series). -/
abbrev curveQuotientStalkMap {F H : curveQuotientWeilSheaf S C₀} (a : F ⟶ H) :=
  (Scheme.etaleAlgebraicFiberMap S.l S.Qbar t a.hom.f).hom

variable {W : Type v} [Group W] (d : Monodromy.DegreeDatum W)
  (D : Scheme.EtaleWeilDegreeData (S.weilFrobenius C₀ hC.out) t W d)

/-- Exactly the prescribed Weil fundamental representation on the actual geometric stalk.
The degree datum and normalized path are the presentation data of the recorded interface.
Source: def-wf-fundamental-representation
(blueprint: lem-zl-geometric-quotient-weil-composition-series). -/
abbrev curveQuotientWeilRep (F : curveQuotientWeilSheaf S C₀) :=
  Scheme.etaleFundamentalRep S.l S.Qbar (S.weilFrobenius C₀ hC.out) t d D F

include d D in
private theorem curveQuotientStalk_isZero_iff (F : curveQuotientWeilSheaf S C₀) :
    IsZero F ↔ Subsingleton (curveQuotientStalk S C₀ t F) := by
  let : ConnectedSpace (S.geometricCurve C₀) := hC.out.2.2.2.2.2.2
  let R := Scheme.etaleWeilRealization S.l S.Qbar (S.weilFrobenius C₀ hC.out) t d D
  let : R.Full :=
    (Scheme.etaleWeilRealization_fullyFaithful S.l S.Qbar
      (S.weilFrobenius C₀ hC.out) t d D).full
  let : R.Faithful :=
    (Scheme.etaleWeilRealization_fullyFaithful S.l S.Qbar
      (S.weilFrobenius C₀ hC.out) t d D).faithful
  let K := R ⋙ ObjectProperty.ι _
  constructor
  · intro hz
    have hh : (𝟙 (K.obj F)) = 0 := by
      calc
        _ = K.map (𝟙 F) := (K.map_id F).symm
        _ = K.map (K.preimage 0) := congrArg K.map (hz.eq_of_src _ _)
        _ = 0 := K.map_preimage 0
    exact ⟨fun x y ↦ by
      have hx : x = 0 := congrArg (fun a : K.obj F ⟶ K.obj F ↦ a.hom x) hh
      have hy : y = 0 := congrArg (fun a : K.obj F ⟶ K.obj F ↦ a.hom y) hh
      exact hx.trans hy.symm⟩
  · intro hs
    exact IsZero.of_full_of_faithful_of_isZero K F ((Rep.isZero_iff S.Qbar W _).2 hs)

private def curveQuotientIntertwiner {F H : curveQuotientWeilSheaf S C₀} (a : F ⟶ H) :
    (curveQuotientWeilRep S C₀ t d D F).IntertwiningMap
      (curveQuotientWeilRep S C₀ t d D H) where
  toLinearMap := curveQuotientStalkMap S C₀ t a
  isIntertwining' g := by
    let : ConnectedSpace (S.geometricCurve C₀) := hC.out.2.2.2.2.2.2
    obtain ⟨e, he⟩ := Scheme.etaleWeilFiberHom S.l S.Qbar
      (S.weilFrobenius C₀ hC.out) t d D F H
    simpa only [he a, curveQuotientStalkMap, curveQuotientWeilRep,
      Endofunctor.IsoAlgebra.forget_map] using (e a).isIntertwining' g

private theorem curveQuotientWeil_irreducible (F : curveQuotientWeilSheaf S C₀)
    (hn : ¬ IsZero F)
    (hi : ∀ A : Subrepresentation (Scheme.etaleGeometricRep S.l S.Qbar F.carrier t),
      A = ⊥ ∨ A = ⊤) : (curveQuotientWeilRep S C₀ t d D F).IsIrreducible := by
  refine Representation.isIrreducible_iff.2 ⟨?_, fun U hU ↦ ?_⟩
  · exact not_subsingleton_iff_nontrivial.1 fun hs ↦
      hn ((curveQuotientStalk_isZero_iff S C₀ t d D F).2 hs)
  · let A : Subrepresentation (Scheme.etaleGeometricRep S.l S.Qbar F.carrier t) :=
      ⟨U, fun g x hx ↦ by
        have hg := (Scheme.etaleFundamentalRep_exists S.l S.Qbar
          (S.weilFrobenius C₀ hC.out) t d D F).exists.choose_spec.1 g
        rw [← hg]
        exact hU (D.geom g) x hx⟩
    exact (hi A).imp (congrArg Subrepresentation.toSubmodule)
      (congrArg Subrepresentation.toSubmodule)

set_option linter.unusedVariables false in
/-- The given finite lisse Weil filtration is a composition series of its actual stalk.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 2
(blueprint: lem-zl-geometric-quotient-weil-composition-series).

Proof: The normalized realization new-p6-etale-weil-realization and its Hom dictionary
new-p6-etale-weil-fiber-hom make the prescribed stalk maps equivariant and functorial.
The supplied stalk exactness, at the chosen point, makes the inclusions injective;
by reverse induction every map to the final stalk is injective. Identify each term
with its image in the final stalk. The zero and final terms give the endpoints.
For each prescribed quotient map q, exactness says that its kernel is the preceding
term and that q is surjective. Hence [v] maps to q(v) by a unique linear isomorphism
of the successive quotient with the prescribed quotient stalk; equivariance of q
makes this an isomorphism of Weil representations with its prescribed action.
A Weil-stable subspace of that stalk is stable under the geometric subgroup, since
its action is the restriction specified by def-wf-fundamental-representation.
Geometric irreducibility forces it to be zero or the whole stalk. The nonzero
quotient sheaf has nonzero stalk, since the fully faithful realization reflects zero objects.
Thus all steps are strict covers, giving Representation.CompositionSeries, and
the prescribed quotients are constituents by def-real-weil-representation-operations.
When r=0 the endpoints force the sheaf and its stalk to be zero, and the singleton
chain has no factors. No splitting or semisimplicity is used. -/
theorem geometricQuotientWeilCompositionSeries
    (hgeneric : IsGenericPoint (t (IsLocalRing.closedPoint κ)) Set.univ)
    (r : ℕ) (J : Fin (r + 1) ⥤ curveQuotientWeilSheaf S C₀)
    (T : Fin r → curveQuotientWeilSheaf S C₀)
    (q : ∀ j : Fin r, J.obj j.succ ⟶ T j)
    (hzero : IsZero (J.obj 0))
    (hmono : ∀ j : Fin r, Mono (J.map (homOfLE j.castSucc_le_succ)))
    (hexact : ∀ (κ' : Type u) [Field κ'] [IsAlgClosed κ']
      (x : Spec (.of κ') ⟶ S.geometricCurve C₀) (j : Fin r),
      Function.Injective (curveQuotientStalkMap S C₀ x
        (J.map (homOfLE j.castSucc_le_succ))) ∧
      Function.Exact (curveQuotientStalkMap S C₀ x
        (J.map (homOfLE j.castSucc_le_succ))) (curveQuotientStalkMap S C₀ x (q j)) ∧
      Function.Surjective (curveQuotientStalkMap S C₀ x (q j)))
    (hnonzero : ∀ j : Fin r, ¬ IsZero (T j))
    (hirr : ∀ (j : Fin r)
      (A : Subrepresentation (Scheme.etaleGeometricRep S.l S.Qbar (T j).carrier t)),
      A = ⊥ ∨ A = ⊤) :
    FiniteDimensional S.Qbar (curveQuotientStalk S C₀ t (J.obj (Fin.last r))) ∧
    ∃ (s : (curveQuotientWeilRep S C₀ t d D (J.obj (Fin.last r))).CompositionSeries)
      (hlen : s.length = r)
      (e : ∀ i : Fin (s.length + 1),
        curveQuotientStalk S C₀ t (J.obj (Fin.cast (congrArg Nat.succ hlen) i)) ≃ₗ[S.Qbar]
          (s.series i).toSubmodule),
      (∀ (i : Fin (s.length + 1))
        (v : curveQuotientStalk S C₀ t (J.obj (Fin.cast (congrArg Nat.succ hlen) i))),
        (e i v : curveQuotientStalk S C₀ t (J.obj (Fin.last r))) =
          curveQuotientStalkMap S C₀ t
            (J.map (homOfLE (Fin.le_last (Fin.cast (congrArg Nat.succ hlen) i)))) v) ∧
      (∀ j : Fin s.length,
        ∃ a : (s.factor j).Equiv (curveQuotientWeilRep S C₀ t d D (T (Fin.cast hlen j))),
          ∀ v : curveQuotientStalk S C₀ t (J.obj (Fin.cast hlen j).succ),
            a (Submodule.Quotient.mk (e j.succ v)) =
              curveQuotientStalkMap S C₀ t (q (Fin.cast hlen j)) v) ∧
      ∀ j : Fin r,
        (curveQuotientWeilRep S C₀ t d D (T j)).IsIrreducible ∧
        (curveQuotientWeilRep S C₀ t d D (T j)).IsConstituent
          (curveQuotientWeilRep S C₀ t d D (J.obj (Fin.last r))) := by
  classical
  have fd (F : curveQuotientWeilSheaf S C₀) :
      FiniteDimensional S.Qbar (curveQuotientStalk S C₀ t F) :=
    (Scheme.etaleFundamentalRep_isLAdic S.l S.Qbar
      (S.weilFrobenius C₀ hC.out) t d D F).1
  refine ⟨fd _, ?_⟩
  let ρ := curveQuotientWeilRep S C₀ t d D (J.obj (Fin.last r))
  let f (i : Fin (r + 1)) :=
    curveQuotientIntertwiner S C₀ t d D (J.map (homOfLE i.le_last))
  let F (i : Fin (r + 1)) : Subrepresentation ρ := (f i).range
  let : ConnectedSpace (S.geometricCurve C₀) := hC.out.2.2.2.2.2.2
  let R := Scheme.etaleWeilRealization S.l S.Qbar (S.weilFrobenius C₀ hC.out) t d D
  have map_eq {A B : curveQuotientWeilSheaf S C₀} (a : A ⟶ B) :
      (R.map a).hom.hom.toLinearMap = curveQuotientStalkMap S C₀ t a := by
    simpa only [curveQuotientStalkMap, Endofunctor.IsoAlgebra.forget_map] using
      Scheme.etaleWeilRealization_map S.l S.Qbar (S.weilFrobenius C₀ hC.out) t d D a
  have comp (i j k : Fin (r + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
      (curveQuotientStalkMap S C₀ t (J.map (homOfLE hjk))).comp
        (curveQuotientStalkMap S C₀ t (J.map (homOfLE hij))) =
      curveQuotientStalkMap S C₀ t (J.map (homOfLE (hij.trans hjk))) := by
    have hh : J.map (homOfLE (hij.trans hjk)) =
        J.map (homOfLE hij) ≫ J.map (homOfLE hjk) :=
      J.map_comp (homOfLE hij) (homOfLE hjk)
    rw [← map_eq, ← map_eq, ← map_eq, hh, R.map_comp]
    rfl
  have fid : (f (Fin.last r)).toLinearMap = LinearMap.id := by
    change curveQuotientStalkMap S C₀ t (J.map (homOfLE (Fin.last r).le_last)) = _
    rw [← map_eq]
    have hh : homOfLE (Fin.last r).le_last = 𝟙 (Fin.last r) := Subsingleton.elim _ _
    rw [hh, J.map_id, R.map_id]
    rfl
  -- Every composite inclusion is injective, including the identity at the last term.
  have hf (i : Fin (r + 1)) : Function.Injective (f i) := by
    refine Fin.reverseInduction ?_ (fun j ih ↦ ?_) i
    · change Function.Injective (f (Fin.last r)).toLinearMap
      rw [fid]
      exact Function.injective_id
    · have hh : (f j.succ).toLinearMap.comp
          (curveQuotientStalkMap S C₀ t (J.map (homOfLE j.castSucc_le_succ))) =
          (f j.castSucc).toLinearMap :=
        comp j.castSucc j.succ (Fin.last r) j.castSucc_le_succ j.succ.le_last
      change Function.Injective (f j.castSucc).toLinearMap
      rw [← hh]
      exact ih.comp (hexact κ t j).1
  let e (i : Fin (r + 1)) :
      curveQuotientStalk S C₀ t (J.obj i) ≃ₗ[S.Qbar] (F i).toSubmodule :=
    LinearEquiv.ofInjective (f i).toLinearMap (hf i)
  have hF : Monotone F := by
    intro i j hij x hx
    obtain ⟨v, rfl⟩ := hx
    refine ⟨curveQuotientStalkMap S C₀ t (J.map (homOfLE hij)) v, ?_⟩
    exact LinearMap.congr_fun (comp i j (Fin.last r) hij j.le_last) v
  have hzero' : F 0 = ⊥ := by
    have := (curveQuotientStalk_isZero_iff S C₀ t d D (J.obj 0)).1 hzero
    ext x
    change (∃ v, f 0 v = x) ↔ x = 0
    constructor
    · rintro ⟨v, rfl⟩
      rw [Subsingleton.elim v 0, map_zero]
    · rintro rfl
      exact ⟨0, map_zero _⟩
  have hlast : F (Fin.last r) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    change LinearMap.range (f (Fin.last r)).toLinearMap = ⊤
    rw [fid, LinearMap.range_id]
  have hirr' (j : Fin r) : (curveQuotientWeilRep S C₀ t d D (T j)).IsIrreducible :=
    curveQuotientWeil_irreducible S C₀ t d D (T j) (hnonzero j) (hirr j)
  have hfactor (j : Fin r) :
      ∃ a : ((F j.succ).subquotient (F j.castSucc)).Equiv
          (curveQuotientWeilRep S C₀ t d D (T j)),
        ∀ v, a (Submodule.Quotient.mk (e j.succ v)) =
          curveQuotientStalkMap S C₀ t (q j) v := by
    apply quotientOfImage (f j.succ) (hf j.succ) (F j.castSucc)
      (curveQuotientIntertwiner S C₀ t d D (q j)) (hexact κ t j).2.2
    intro x
    change curveQuotientStalkMap S C₀ t (q j) x = 0 ↔
      ∃ y, f j.castSucc y = f j.succ x
    rw [(hexact κ t j).2.1 x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (LinearMap.congr_fun
        (comp j.castSucc j.succ (Fin.last r) j.castSucc_le_succ j.succ.le_last) y).symm⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, hf j.succ ?_⟩
      exact (LinearMap.congr_fun
        (comp j.castSucc j.succ (Fin.last r) j.castSucc_le_succ j.succ.le_last) y).trans hy
  -- Simple successive quotients give exactly the covers of the prescribed image chain.
  let s : ρ.CompositionSeries :=
    { series :=
        { length := r
          toFun := F
          step := by
            intro j
            exact (Subrepresentation.isIrreducible_subquotient_iff
              (hF j.castSucc_le_succ)).1 ((hfactor j).choose.isIrreducible_iff.2 (hirr' j)) }
      head_eq := hzero'
      last_eq := hlast }
  refine ⟨s, rfl, e, fun _ _ ↦ rfl, hfactor, fun j ↦ ⟨hirr' j, ?_⟩⟩
  exact Representation.isConstituent_of_equiv_subquotient (hirr' j)
    (hF j.castSucc_le_succ) (hfactor j).choose.symm

end RealSheaves
