/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Sheaf.RingTheory.FiniteTypeLocalClosedFibreApproximation
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.LocalizationLocalization
import WeilConjectures.RingTheory.FlatOfFlatClosedFiber
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Pointwise fibre criterion for flatness

Source: Stacks Project, More on Morphisms, Tag 039C,
`theorem-criterion-flatness-fibre`, implication (1) to (2) for the structure sheaf.
(blueprint: lem-sfb-fibrewise-flatness-criterion)

The fibre morphism is the canonical pullback map over the residue field at `p x`.
Flatness at a point is flatness of its actual local-ring homomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_fp_model {X S : Scheme.{u}} (p : X ⟶ S)
    [LocallyOfFinitePresentation p] (x : X) :
    let R := S.presheaf.stalk (p x)
    let C := X.presheaf.stalk x
    let : Algebra R C := (p.stalkMap x).hom.toAlgebra
    ∃ (P : CommRingCat.{u}) (_ : Algebra R P) (_ : Algebra P C),
      IsScalarTower R P C ∧ Algebra.FinitePresentation R P ∧
        ∃ W : Submonoid P, IsLocalization W C := by
  -- Localize a finite-presentation affine chart at the contracted base prime.
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show p x ∈ (⊤ : S.Opens) by simp)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ p ⁻¹ᵁ U from hxU)
  let R := S.presheaf.stalk (p x)
  let C := X.presheaf.stalk x
  let : Algebra R C := (p.stalkMap x).hom.toAlgebra
  let A := Γ(S, U)
  let D := Γ(X, V)
  let : Algebra A R := S.presheaf.algebra_section_stalk ⟨p x, hxU⟩
  let : Algebra D C := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  let a := hU.primeIdealOf ⟨p x, hxU⟩
  let c := hV.primeIdealOf ⟨x, hxV⟩
  have : IsLocalization.AtPrime R a.asIdeal := hU.isLocalization_stalk ⟨p x, hxU⟩
  have : IsLocalization.AtPrime C c.asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  let φ : A →+* D := (p.appLE U V hVU).hom
  let M := a.asIdeal.primeCompl.map φ
  have hM : M ≤ c.asIdeal.primeCompl := by
    rintro b ⟨z, hz, rfl⟩
    change φ z ∉ c.asIdeal
    change z ∉ a.asIdeal at hz
    have heq : Ideal.comap φ c.asIdeal = a.asIdeal :=
      congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV)
    exact fun hb ↦ hz (heq ▸ hb)
  let P := Localization M
  let ψ : R →+* P := IsLocalization.map P φ (Submonoid.le_comap_map a.asIdeal.primeCompl)
  let : Algebra R P := ψ.toAlgebra
  let : Algebra P C := IsLocalization.localizationAlgebraOfSubmonoidLe P C M
    c.asIdeal.primeCompl hM
  have : IsScalarTower D P C :=
    IsLocalization.localization_isScalarTower_of_submonoid_le P C M c.asIdeal.primeCompl hM
  have ht : IsScalarTower R P C := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext a.asIdeal.primeCompl
    ext z
    change (p.stalkMap x).hom (algebraMap A R z) =
      algebraMap P C (ψ (algebraMap A R z))
    rw [show ψ (algebraMap A R z) = algebraMap D P (φ z) from
      IsLocalization.map_eq (Submonoid.le_comap_map a.asIdeal.primeCompl) z]
    rw [← IsScalarTower.algebraMap_apply D P C]
    change (p.stalkMap x) (S.presheaf.germ U (p x) hxU z) =
      X.presheaf.germ V x hxV ((p.appLE U V hVU) z)
    rw [p.germ_stalkMap_apply]
    exact (X.presheaf.germ_res_apply (homOfLE hVU) x hxV (p.app U z)).symm
  have hfp : Algebra.FinitePresentation R P :=
    RingHom.finitePresentation_localizationPreserves φ a.asIdeal.primeCompl R P
      (p.finitePresentation_appLE hU hV hVU)
  exact ⟨CommRingCat.of P, inferInstance, inferInstance, ht, hfp,
    c.asIdeal.primeCompl.map (algebraMap D P),
    IsLocalization.isLocalization_of_submonoid_le P C M c.asIdeal.primeCompl hM⟩

set_option backward.isDefEq.respectTransparency false in
private theorem local_criterion (R B C : Type u)
    [CommRing R] [CommRing B] [CommRing C]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing C]
    (α : R →+* B) (β : B →+* C) [IsLocalHom α] [IsLocalHom β]
    (hft : α.EssFiniteType) (hp : (β.comp α).Flat)
    (hmodel : letI : Algebra R C := (β.comp α).toAlgebra
      ∃ (Q : CommRingCat.{u}) (_ : Algebra R Q) (_ : Algebra Q C),
        IsScalarTower R Q C ∧ Algebra.FinitePresentation R Q ∧
          ∃ V : Submonoid Q, IsLocalization V C)
    (hclosed : (Ideal.quotientMap
      ((IsLocalRing.maximalIdeal R).map (β.comp α)) β
      (by simpa only [← Ideal.map_map] using
        (Ideal.le_comap_map : (IsLocalRing.maximalIdeal R).map α ≤
          (((IsLocalRing.maximalIdeal R).map α).map β).comap β))).Flat) :
    β.Flat ∧ α.Flat := by
  let : Algebra R B := α.toAlgebra
  let : Algebra B C := β.toAlgebra
  let : Algebra R C := (β.comp α).toAlgebra
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.EssFiniteType R B := hft
  have : Module.Flat R C := hp
  obtain ⟨Q, algRQ, algQC, towerRQC, fpQ, V, locC⟩ := hmodel
  let : Algebra R Q := algRQ
  let : Algebra Q C := algQC
  have : IsScalarTower R Q C := towerRQC
  have : Algebra.FinitePresentation R Q := fpQ
  have : IsLocalization V C := locC
  -- The approximation preserves the actual quotient map, hence its scalar action.
  obtain ⟨T, ringT, localT, algRT, f, localRT, localf, hsurj, hmodelT, e, he⟩ :=
    Algebra.exists_finitePresentation_local_approximation_closedFibre R B
  let : CommRing T := ringT
  have : IsLocalRing T := localT
  let : Algebra R T := algRT
  have : IsLocalHom (algebraMap R T) := localRT
  have : IsLocalHom f.toRingHom := localf
  let : Algebra T C := (β.comp f.toRingHom).toAlgebra
  have : IsLocalHom (algebraMap T C) := RingHom.isLocalHom_comp β f.toRingHom
  have : IsScalarTower R T C := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change β (α r) = β (f (algebraMap R T r))
    rw [f.commutes]
    rfl
  obtain ⟨P, ringP, algRP, fpP, W, ⟨eT⟩⟩ := hmodelT
  let : CommRing P := ringP
  let : Algebra R P := algRP
  have : Algebra.FinitePresentation R P := fpP
  let : Algebra P T := (eT.symm.toRingHom.comp (algebraMap P (Localization W))).toAlgebra
  have : IsLocalization W T :=
    (IsLocalization.isLocalization_iff_of_ringEquiv W eT.symm.toRingEquiv).mp
      (inferInstance : IsLocalization W (Localization W))
  have : IsScalarTower R P T := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R T r = eT.symm (algebraMap P (Localization W) (algebraMap R P r))
    rw [← IsScalarTower.algebraMap_apply R P (Localization W), eT.symm.commutes]
  let m := IsLocalRing.maximalIdeal R
  let IT := m.map (algebraMap R T)
  let IB := m.map α
  let IC := m.map (β.comp α)
  have hTC : IT ≤ IC.comap (algebraMap T C) := by
    dsimp only [IT, IC]
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
    exact le_of_eq (congrArg (fun g : R →+* C ↦ m.map g)
      (IsScalarTower.algebraMap_eq R T C).symm)
  have hquot : (Ideal.quotientMap IC (algebraMap T C) hTC).Flat := by
    have hcomp : Ideal.quotientMap IC (algebraMap T C) hTC =
        (Ideal.quotientMap IC β
          (by dsimp only [IB, IC]; rw [← Ideal.map_map];
              exact Ideal.le_comap_map)).comp e.toRingHom := by
      apply Ideal.Quotient.ringHom_ext
      ext t
      change Ideal.Quotient.mk IC (β (f t)) =
        (Ideal.quotientMap IC β
          (by dsimp only [IC]; rw [← Ideal.map_map]; exact Ideal.le_comap_map))
          (e (Ideal.Quotient.mk IT t))
      rw [he]
      rfl
    rw [hcomp]
    exact (RingHom.Flat.of_bijective e.bijective).comp hclosed
  have hIC : IT.map (algebraMap T C) = IC := by
    dsimp only [IT, IC]
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R T C]
    rfl
  have hfibre : Module.Flat (T ⧸ IT) (TensorProduct T (T ⧸ IT) C) := by
    have hquot' : (Ideal.quotientMap (IT.map (algebraMap T C))
        (algebraMap T C) Ideal.le_comap_map).Flat := by
      have heq : Ideal.quotientMap (IT.map (algebraMap T C))
          (algebraMap T C) Ideal.le_comap_map =
          (Ideal.quotEquivOfEq hIC.symm).toRingHom.comp
            (Ideal.quotientMap IC (algebraMap T C) hTC) := by
        apply Ideal.Quotient.ringHom_ext
        ext t
        rfl
      rw [heq]
      exact hquot.comp (RingHom.Flat.of_bijective (Ideal.quotEquivOfEq hIC.symm).bijective)
    have : Module.Flat (T ⧸ IT) (C ⧸ IT.map (algebraMap T C)) :=
      RingHom.flat_algebraMap_iff.mp hquot'
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C IT).symm.toLinearEquiv
  -- Apply the known criterion to R → T → C with the rank-one C-module C.
  obtain ⟨hT, hC⟩ := Module.flat_of_flat_closedFiber R T C C P Q W V hfibre
  have : Module.Flat T C := hC
  have : Module.FaithfullyFlat T C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  -- Faithful flatness makes T → C injective, and this map factors through f.
  have hinj : Function.Injective f := by
    intro t t' h
    apply FaithfulSMul.algebraMap_injective T C
    change β (f t) = β (f t')
    rw [h]
  have hflatTC : (β.comp f.toRingHom).Flat := hC
  have hflatRT : (algebraMap R T).Flat := RingHom.flat_algebraMap_iff.mpr hT
  have hflatRB : α.Flat := by
    have hc : f.toRingHom.comp (algebraMap R T) = α := by ext r; exact f.commutes r
    rw [← hc]
    exact hflatRT.comp (RingHom.Flat.of_bijective ⟨hinj, hsurj⟩)
  exact ⟨(RingHom.Flat.comp_iff_of_bijective_right ⟨hinj, hsurj⟩).mp hflatTC, hflatRB⟩

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_quotient {X S : Scheme.{u}} (p : X ⟶ S) (x : X)
    (s : S) (hs : p x = s) (z : p.fiber s) (hz : p.fiberι s z = x) :
    let ρ := (X.presheaf.stalkCongr (.of_eq hz.symm)).hom ≫ (p.fiberι s).stalkMap z
    Function.Surjective ρ.hom ∧
      RingHom.ker ρ.hom = (IsLocalRing.maximalIdeal (S.presheaf.stalk (p x))).map
        (p.stalkMap x).hom := by
  subst s
  have heq : z = p.asFiber x :=
    (p.fiberι (p x)).isEmbedding.injective (hz.trans (p.fiberι_asFiber x).symm)
  subst z
  exact ⟨(p.fiberStalkMap_surjective_ker_quotientEquiv x).1,
    (p.fiberStalkMap_surjective_ker_quotientEquiv x).2.1⟩

set_option backward.isDefEq.respectTransparency false in
/-- A commuting square of locally ringed spaces induces the corresponding stalk square.
The point congruences are explicit; no scheme or fibre hypotheses are needed. -/
private theorem fibre_square_stalk_commutes
    {E A Z W : LocallyRingedSpace.{u}} (e : E ⟶ A) (i : Z ⟶ E) (j : W ⟶ A) (m : Z ⟶ W)
    (h : m ≫ j = i ≫ e) (z : Z) (x : E) (hx : i.base z = x) (hw : j.base (m.base z) = e.base x) :
    (A.presheaf.stalkCongr (.of_eq hw.symm)).hom ≫ j.stalkMap (m.base z) ≫ m.stalkMap z =
      e.stalkMap x ≫ (E.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫ i.stalkMap z := by
  rw [← LocallyRingedSpace.stalkMap_comp,
    LocallyRingedSpace.stalkMap_congr_hom (m ≫ j) (i ≫ e) h z, LocallyRingedSpace.stalkMap_comp]
  rw [← Category.assoc, ← Category.assoc]
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_comp]
  have hh := LocallyRingedSpace.stalkMap_congr_point e x (i.base z) hx.symm
  simpa only [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc] using
    congrArg (fun k ↦ k ≫ i.stalkMap z) hh.symm

private theorem flat_quotientMap_of_square
    {A B Af Bf : Type u} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bf]
    (β : A →+* B) (ρA : A →+* Af) (ρB : B →+* Bf) (ψ : Af →+* Bf)
    (I : Ideal A) (J : Ideal B) (hIJ : I ≤ J.comap β)
    (hA : Function.Surjective ρA) (hB : Function.Surjective ρB)
    (hkerA : RingHom.ker ρA = I) (hkerB : RingHom.ker ρB = J)
    (hc : ψ.comp ρA = ρB.comp β) (hψ : ψ.Flat) :
    (Ideal.quotientMap J β hIJ).Flat := by
  let eA := (Ideal.quotEquivOfEq hkerA.symm).trans (ρA.quotientKerEquivOfSurjective hA)
  let eB := (Ideal.quotEquivOfEq hkerB.symm).trans (ρB.quotientKerEquivOfSurjective hB)
  have heA (a : A) : eA (Ideal.Quotient.mk I a) = ρA a := by simp [eA]
  have heB (b : B) : eB (Ideal.Quotient.mk J b) = ρB b := by simp [eB]
  have heq : Ideal.quotientMap J β hIJ =
      eB.symm.toRingHom.comp (ψ.comp eA.toRingHom) := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    apply eB.injective
    change eB (Ideal.Quotient.mk J (β a)) = eB (eB.symm (ψ (eA (Ideal.Quotient.mk I a))))
    rw [RingEquiv.apply_symm_apply, heA, heB]
    exact (congrArg (fun k : A →+* Bf ↦ k a) hc).symm
  rw [heq]
  exact ((RingHom.Flat.of_bijective eA.bijective).comp hψ).comp
    (RingHom.Flat.of_bijective eB.symm.bijective)

set_option backward.isDefEq.respectTransparency false in
/-- If the finitely presented source is flat over the base at `x`, and the induced
fibre map is flat at the corresponding fibre point, then both the original map
at `x` and the target's structure map at `f x` are flat.

Source: Stacks Project, More on Morphisms, Tag 039C,
`theorem-criterion-flatness-fibre`, implication (1) to (2), with the structure sheaf.
(blueprint: lem-sfb-fibrewise-flatness-criterion)

Proof:
1. Put R = O_{S,p(x)}, B = O_{Y,f(x)}, and C = O_{X,x}. These are nonzero local
   rings. Their local stalk maps form R -> B -> C, with composite the stalk map
   of p, by lem-weil-pbc-scheme-stalk-map-composition. Thus C is flat over R.
2. Apply lem-sbc-scheme-fibre-stalk-quotient to p and q. The actual fibre-projection
   stalk maps identify the fibre stalks with C/m_R C and B/m_R B. The pullback-map
   projection equations (def-pc-fibre-product), and stalk-map composition, show
   that the fibre map sends [b] to [f-sharp(b)]. The fibre-flatness hypothesis
   therefore gives C/m_R C flat over B/m_R B with precisely the quotient action.
3. Choose affine charts Spec D around x and Spec A around p(x) on which p is
   finitely presented (def-sbc-locally-finite-presentation). By
   lem-weil-pbc-affine-open-stalk-localization, compatibly with the germ formulas,
   R = A_a and C = D_c. Base change gives P = R tensor_A D finitely presented
   over R (lem-weil-pbc-finite-presentation-base-change-composition). This tensor
   product is the localization of D at A minus a, via r tensor d -> rd and
   d/a -> (1/a) tensor d. As this set avoids c, localization transitivity
   (lem-weil-pbc-localization-of-localization) makes C a localization of P.
4. On the same affine base choose a finite-type chart Spec E around f(x), using
   def-weil-finite-type-morphism. The same affine stalk and germ formulas give
   B = E_b. Generators of E over A also generate R tensor_A E over R; this tensor
   product is the localization at A minus a. Localization transitivity therefore
   makes B essentially of finite type over R. No finite presentation of B is used.
5. Apply lem-sfb-finite-type-local-closed-fibre-approximation to R -> B. It gives
   local R -> T ->> B, with T essentially finitely presented over R and
   T/m_R T -> B/m_R B an isomorphism induced by the surjection u. Composing with
   B -> C is local. Relabelling coefficients along that quotient isomorphism
   transports step 2 to flatness of C/m_R C over T/m_R T.
6. Apply lem-weil-pbc-criterion-flatness-fibre to R -> T -> C and M = C. Both T
   and C are essentially finitely presented over R; C is finitely presented over
   itself, being free of rank one, and nonzero as a stalk local ring. Its two
   flatness hypotheses are steps 1 and 5. Thus T is R-flat and C is T-flat.
7. The flat local map T -> C is faithfully flat by
   lem-pc-local-flat-faithful-flat-reflects-surjective. Apply
   lem-weil-pbc-faithfully-flat-universally-injective with N = T. Under
   T tensor_T C = C, the injective map t -> t tensor 1 is T -> C, so this map is
   injective. Since it factors through u, u is injective as well as surjective,
   hence an R-algebra isomorphism T -> B.
8. Transport step 6 along this isomorphism. The action on C agrees with its
   original B-action by the factorization through u, giving B R-flat and C
   B-flat. The pointwise definition def-weil-flat-morphism gives both conclusions.
-/
theorem Scheme.Hom.flatAt_and_base_flatAt_of_fiber_flatAt {S X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ q = p)
    [LocallyOfFinitePresentation p] [LocallyOfFiniteType q]
    (x : X) (hp : (p.stalkMap x).hom.Flat)
    (hfs : ((pullback.map p (S.fromSpecResidueField (p x))
      q (S.fromSpecResidueField (p x)) f (𝟙 _) (𝟙 S)
      (by simpa only [Category.comp_id] using hf.symm) (by simp)).stalkMap
        (p.asFiber x)).hom.Flat) :
    (f.stalkMap x).hom.Flat ∧ (q.stalkMap (f x)).hom.Flat := by
  subst p
  let R := S.presheaf.stalk (q (f x))
  let B := Y.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  let α : R →+* B := (q.stalkMap (f x)).hom
  let β : B →+* C := (f.stalkMap x).hom
  have hbase : (β.comp α).Flat := by
    simpa only [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] using hp
  have hmodel := stalk_fp_model (f ≫ q) x
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hmodel
  apply local_criterion R B C α β (LocallyOfFiniteType.stalkMap q (f x)) hbase hmodel
  let s := (f ≫ q) x
  let z := (f ≫ q).asFiber x
  let i := (f ≫ q).fiberι s
  let j := q.fiberι s
  let m : (f ≫ q).fiber s ⟶ q.fiber s := pullback.map (f ≫ q) (S.fromSpecResidueField s)
    q (S.fromSpecResidueField s) f (𝟙 _) (𝟙 S)
    (by simp) (by simp)
  have hx : i z = x := (f ≫ q).fiberι_asFiber x
  have hsquare : m ≫ j = i ≫ f := by
    simp [m, j, i, Scheme.Hom.fiberι]
  have hw : j (m z) = f x := by
    rw [← Scheme.Hom.comp_apply, hsquare, Scheme.Hom.comp_apply, hx]
  let ρB := (Y.presheaf.stalkCongr (.of_eq hw.symm)).hom ≫ j.stalkMap (m z)
  let ρC := (X.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫ i.stalkMap z
  let I := (IsLocalRing.maximalIdeal R).map α
  let J := (IsLocalRing.maximalIdeal R).map (β.comp α)
  have hB : Function.Surjective ρB.hom ∧ RingHom.ker ρB.hom = I :=
    fibre_quotient q (f x) s rfl (m z) hw
  have hC : Function.Surjective ρC.hom ∧ RingHom.ker ρC.hom = J := by
    have hh := fibre_quotient (f ≫ q) x s rfl z hx
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hh
    exact hh
  have hc : (m.stalkMap z).hom.comp ρB.hom = ρC.hom.comp β :=
    congrArg CommRingCat.Hom.hom
      (fibre_square_stalk_commutes f.toLRSHom i.toLRSHom j.toLRSHom m.toLRSHom
        (congrArg Scheme.Hom.toLRSHom hsquare) z x hx hw)
  exact flat_quotientMap_of_square β ρB.hom ρC.hom (m.stalkMap z).hom I J _
    hB.1 hC.1 hB.2 hC.2 hc hfs

end AlgebraicGeometry
