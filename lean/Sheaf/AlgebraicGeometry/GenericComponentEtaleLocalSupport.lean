module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Sheaf.AlgebraicGeometry.FiniteIntersectionEtaleStalkModel
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.Etale.LocalDimension

/-!
# Étale local support above a component generic point

Source: Stacks Project, More on Algebra, Tag 07QP, and Properties, Tags 02IZ and 0BA9
(blueprint: lem-trf-generic-component-etale-local-support).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The extension to `𝒪_{W,w}` of the kernel of `𝒪_{X,i η} → 𝒪_{Z,η}`.
The equality `hw` transports the source stalk of `v.stalkMap w`; the map is the actual
stalk map, and the ideal is its ordinary ideal-theoretic extension.
Source: Stacks Project, More on Algebra, Tag 07QP, on the quotient affine chart
(blueprint: lem-trf-generic-component-etale-local-support). -/
noncomputable def genericComponentEtaleLocalIdeal {X Z W : Scheme.{u}}
    (i : Z ⟶ X) (η : Z) (v : W ⟶ X) (w : W) (hw : v w = i η) :
    Ideal (W.presheaf.stalk w) :=
  Ideal.map ((X.presheaf.stalkCongr (.of_eq hw.symm)).hom ≫ v.stalkMap w).hom
    (RingHom.ker (i.stalkMap η).hom)

private theorem etale_stalk_dimension {U W : Scheme.{u}} (e : W ⟶ U) [Etale e]
    (w : W) : ringKrullDim (U.presheaf.stalk (e w)) =
      ringKrullDim (W.presheaf.stalk w) := by
  obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    U.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (e w))
  obtain ⟨T, hT, hw, hTV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    W.isBasis_affineOpens (show w ∈ e ⁻¹ᵁ V from hx)
  let a := IsAffineOpen.arrowStalkMapIso e V hV T hT hTV hw
  have hd := RingHom.Etale.ringKrullDim_localization_eq
    (e.appLE V T hTV).hom (e.etale_appLE hV hT hTV)
    (hT.primeIdealOf ⟨w, hw⟩).asIdeal
  have hp := IsAffineOpen.comap_primeIdealOf_appLE V hV T hT hTV hw
  have hd' : ringKrullDim
      (Localization.AtPrime (hV.primeIdealOf ⟨e w, hTV hw⟩).asIdeal) =
      ringKrullDim (Localization.AtPrime (hT.primeIdealOf ⟨w, hw⟩).asIdeal) := by
    have hh := congrArg (fun p : PrimeSpectrum Γ(U, V) ↦
      ringKrullDim (Localization.AtPrime p.asIdeal)) hp
    exact hh.symm.trans hd
  exact (ringKrullDim_eq_of_ringEquiv
    (Arrow.leftFunc.mapIso a).commRingCatIsoToRingEquiv).trans
    (hd'.trans (ringKrullDim_eq_of_ringEquiv
      (Arrow.rightFunc.mapIso a).commRingCatIsoToRingEquiv).symm)

/-- Étale localization above a generic point of a component of a closed subscheme has
zero-dimensional singleton support, and preserves the ambient local dimension.
`Order.coheight` on a scheme is the supremum of generalization-chain lengths from the
point. Under the generic-point correspondence with irreducible closed subsets this is
the codimension convention of the statement. In the last clause the point is closed.
Source: Stacks Project, More on Algebra, Tag 07QP; Properties, Tags 02IZ and 0BA9
(blueprint: lem-trf-generic-component-etale-local-support).

Proof:
1. Apply the scheme-stalk dimension/generalization-chain formula to `Z` at `η`.
   The closure of `η` is the maximal irreducible subset `C`, so its codimension is zero.
2. The one-member finite-intersection étale stalk model identifies `𝒪_{Z,η}` with
   `A/I` and the pullback with `Spec (B/IB)` over `Spec B`. The quotient is nonzero
   local, with maximal ideal the image of the maximal ideal of `B`.
3. Choose an étale affine chart `R → S` of `v` at `w`. The stalks are `R_p` and `S_q`.
   Tag 07QP gives their equal dimensions. This uses the chart map, without asserting
   finite presentation for the map between the stalks themselves.
4. Write the closed subscheme on this chart as `Spec (R/K)`. Its base change is
   `Spec (S/KS)`, with an étale quotient chart map. Apply 07QP to this map, then
   commute localization and quotient: `dim (B/IB) = dim (A/I) = 0`.
5. Every prime of the nonzero local ring `B/IB` lies in its maximal ideal. A strict
   inclusion would be a chain of length one, contradicting dimension zero. Thus its
   spectrum has exactly one point. Its image is the maximal ideal of `B`, and a
   singleton space has exactly its singleton as irreducible component.
6. By 02IZ the codimension of the closed point of `Spec B` is the dimension of its
   stalk. This stalk is `B` localized at its maximal ideal, hence isomorphic to `B`.
The DAG steps use `lem-sc-scheme-stalk-dimension-generalization-chains`,
`lem-trf-finite-intersection-etale-stalk-model`, `lem-weil-pbc-quotient-local-structure`,
`lem-weil-pbc-etale-ring-map-iff-etale-affine`, `lem-weil-pbc-affine-open-stalk-localization`,
`lem-sc-etale-local-dimension`, `lem-weil-pbc-etale-ring-base-change`, and
`lem-weil-pbc-localization-at-prime-of-quotient`, together with the recorded definitions.
No reduction of a scheme or quotient ring is used. -/
theorem genericComponent_etale_local_support {X Z W : Scheme.{u}}
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (η : Z) (C : Set Z) (hC : C ∈ irreducibleComponents Z) (hη : IsGenericPoint η C)
    (v : W ⟶ X) [Etale v] (w : W) (hw : v w = i η) :
    ringKrullDim (Z.presheaf.stalk η) = 0 ∧
      ringKrullDim (W.presheaf.stalk w ⧸ genericComponentEtaleLocalIdeal i η v w hw) = 0 ∧
      (∃ e : pullback i (W.fromSpecStalk w ≫ v) ≅
          Spec (CommRingCat.of
            (W.presheaf.stalk w ⧸ genericComponentEtaleLocalIdeal i η v w hw)),
        e.hom ≫ Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (genericComponentEtaleLocalIdeal i η v w hw))) =
          pullback.snd i (W.fromSpecStalk w ≫ v) ∧
        ∃ t : (pullback i (W.fromSpecStalk w ≫ v) : Scheme.{u}),
          (∀ p : (pullback i (W.fromSpecStalk w ≫ v) : Scheme.{u}), p = t) ∧
          (pullback.snd i (W.fromSpecStalk w ≫ v)) t =
            IsLocalRing.closedPoint (W.presheaf.stalk w) ∧
          irreducibleComponents (pullback i (W.fromSpecStalk w ≫ v) : Scheme.{u}) = {{t}}) ∧
      ringKrullDim (W.presheaf.stalk w) = ringKrullDim (X.presheaf.stalk (i η)) ∧
      (Order.coheight (@id (Spec (W.presheaf.stalk w))
          (IsLocalRing.closedPoint (W.presheaf.stalk w))) : WithBot ℕ∞) =
        ringKrullDim (W.presheaf.stalk w) := by
  classical
  have hdimZ : ringKrullDim (Z.presheaf.stalk η) = 0 := by
    have hmax : IsMax η := by
      intro y hηy
      change y ⤳ η at hηy
      have hsub : closure {y} ⊆ C := hC.2 isIrreducible_singleton.closure
        (hη.symm.trans_subset hηy.closure_subset)
      change η ⤳ y
      exact specializes_iff_closure_subset.mpr (hsub.trans_eq hη.symm)
    rw [ringKrullDim_stalk_eq_coheight, Order.IsMax.coheight_eq_zero hmax]
    rfl
  let J : Finset (Fin 1) := Finset.univ
  let j₀ : J := ⟨0, Finset.mem_univ _⟩
  let c : WidePullbackCone (fun _ : J ↦ i) :=
    WidePullbackCone.mk i (fun _ ↦ 𝟙 Z) (fun _ ↦ Category.id_comp i)
  have hc : IsLimit c := WidePullbackCone.IsLimit.mk c (fun t ↦ t.π j₀)
    (fun t ↦ t.condition j₀)
    (fun t j ↦ by
      have : j = j₀ := Subsingleton.elim _ _
      subst j
      change t.π j₀ ≫ 𝟙 Z = t.π j₀
      exact Category.comp_id _)
    (fun t m _ hm ↦ by
      have hh : m ≫ 𝟙 Z = t.π j₀ := hm j₀
      exact (Category.comp_id m).symm.trans hh)
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : X.Opens)) (x := i η) (by simp)
  have hK : i.ker.ideal ⟨U, hU⟩ = ⨆ _ : J, i.ker.ideal ⟨U, hU⟩ := by
    let : Nonempty J := ⟨j₀⟩
    simp
  have hI := i.ker_stalkMap ⟨U, hU⟩ η hx
  have hmodel := (finiteIntersection_etale_stalk_model (fun _ : Fin 1 ↦ Z)
    (fun _ ↦ i) (fun _ ↦ inferInstance) J c hc).2.2.2 η U hU hx
    (i.ker.ideal ⟨U, hU⟩) hK (RingHom.ker (i.stalkMap η).hom) hI
  dsimp only [c, WidePullbackCone.mk_base] at hmodel
  obtain ⟨_, _, _, hm⟩ := hmodel
  let φ := ((X.presheaf.stalkCongr (.of_eq hw.symm)).hom ≫ v.stalkMap w).hom
  have hφ : φ = (v.stalkMap w).hom.comp
      (X.presheaf.stalkCongr (.of_eq hw)).inv.hom := by
    rfl
  obtain ⟨_, _, hnt, _, hl, ⟨e, he⟩, p, hp, _, hz, eB, _⟩ :=
    hm W v inferInstance w hw φ hφ (genericComponentEtaleLocalIdeal i η v w hw) rfl
  let := hnt
  let := hl
  have hdimD :
      ringKrullDim (W.presheaf.stalk w ⧸ genericComponentEtaleLocalIdeal i η v w hw) =
        0 := by
    have hdη : ringKrullDim (Z.presheaf.stalk ((pullback.fst i v) p)) =
        ringKrullDim (Z.presheaf.stalk η) :=
      ringKrullDim_eq_of_ringEquiv
        (Z.presheaf.stalkCongr (.of_eq hz)).commRingCatIsoToRingEquiv
    exact (ringKrullDim_eq_of_ringEquiv eB).trans
      ((etale_stalk_dimension (pullback.fst i v) p).symm.trans (hdη.trans hdimZ))
  let : Ring.KrullDimLE 0
      (W.presheaf.stalk w ⧸ genericComponentEtaleLocalIdeal i η v w hw) :=
    Ring.krullDimLE_iff.mpr hdimD.le
  let : Subsingleton (Spec (CommRingCat.of
      (W.presheaf.stalk w ⧸ genericComponentEtaleLocalIdeal i η v w hw))) := by
    change Subsingleton (PrimeSpectrum
      (W.presheaf.stalk w ⧸ genericComponentEtaleLocalIdeal i η v w hw))
    infer_instance
  let t := e.inv (IsLocalRing.closedPoint
    (W.presheaf.stalk w ⧸ genericComponentEtaleLocalIdeal i η v w hw))
  have ht (q : (pullback i (W.fromSpecStalk w ≫ v) : Scheme.{u})) : q = t := by
    apply e.hom.homeomorph.injective
    exact Subsingleton.elim _ _
  have htimage : (pullback.snd i (W.fromSpecStalk w ≫ v)) t =
      IsLocalRing.closedPoint (W.presheaf.stalk w) := by
    rw [← he, Scheme.Hom.comp_apply]
    have heq : e.hom t = IsLocalRing.closedPoint
        (W.presheaf.stalk w ⧸ genericComponentEtaleLocalIdeal i η v w hw) := by
      change e.hom (e.inv _) = _
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
      rfl
    rw [heq]
    have : IsLocalHom
        (Ideal.Quotient.mk (genericComponentEtaleLocalIdeal i η v w hw)) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    exact Spec_closedPoint
  have hcomponents :
      irreducibleComponents (pullback i (W.fromSpecStalk w ≫ v) : Scheme.{u}) =
        {{t}} := by
    apply Set.ext
    intro S
    constructor
    · intro hS
      have hsub : S ⊆ {t} := fun q _ ↦ ht q
      have hsup : {t} ⊆ S := hS.2 isIrreducible_singleton hsub
      exact Set.mem_singleton_iff.mpr (le_antisymm hsub hsup)
    · rintro rfl
      exact ⟨isIrreducible_singleton, fun T _ _ q _ ↦ ht q⟩
  refine ⟨hdimZ, hdimD, ⟨e, he, t, ht, htimage, hcomponents⟩, ?_, ?_⟩
  · rw [← etale_stalk_dimension v w, hw]
  · rw [← ringKrullDim_stalk_eq_coheight]
    exact ringKrullDim_eq_of_ringEquiv
      (stalkClosedPointIso (W.presheaf.stalk w)).commRingCatIsoToRingEquiv

end AlgebraicGeometry
