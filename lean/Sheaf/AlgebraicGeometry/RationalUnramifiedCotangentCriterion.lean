module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.Morphisms.FormallyUnramifiedStalkNeighbourhood

/-!
# Rational-point cotangent criterion for unramified morphisms

Source: `literature/stacks-project/varieties.tex`, lemma-injective-tangent-spaces-unramified,
together with the local characterization by vanishing relative differentials
(blueprint: lem-sc-rational-unramified-cotangent-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

private theorem local_unramified_iff_cotangent_surjective
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ]
    (hfin : φ.EssFiniteType)
    (hres : Function.Surjective ((IsLocalRing.residue S).comp φ)) :
    φ.FormallyUnramified ↔ Function.Surjective
      (Ideal.mapCotangent (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) φ.toIntAlgHom
        (Ideal.map_le_iff_le_comap.mp (IsLocalRing.map_maximalIdeal_le φ))) := by
  let := φ.toAlgebra
  have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom φ)
  have : Algebra.EssFiniteType R S := hfin
  constructor
  · intro hu
    have : Algebra.FormallyUnramified R S := hu
    have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)
    let F := Ideal.mapCotangent (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal S) φ.toIntAlgHom
      (Ideal.map_le_iff_le_comap.mp (IsLocalRing.map_maximalIdeal_le φ))
    have hsmul (a : R) (w : IsLocalRing.CotangentSpace R) : F (a • w) = φ a • F w := by
      obtain ⟨w, rfl⟩ := Ideal.toCotangent_surjective _ w
      change (IsLocalRing.maximalIdeal S).toCotangent ⟨φ (a * w.1), _⟩ =
        φ a • (IsLocalRing.maximalIdeal S).toCotangent ⟨φ w.1, _⟩
      rw [← map_smul]
      congr 1
      exact Subtype.ext (map_mul φ a w.1)
    intro w
    obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ w
    have hx' : x ∈ (IsLocalRing.maximalIdeal R).map φ := hm.symm ▸ hx
    suffices H : ∀ x (hx : x ∈ (IsLocalRing.maximalIdeal R).map φ),
        ∃ a, F a = (IsLocalRing.maximalIdeal S).toCotangent ⟨x, hm ▸ hx⟩ by
      exact H x hx'
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨(IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩, rfl⟩
    | zero => exact ⟨0, by change F 0 = (IsLocalRing.maximalIdeal S).toCotangent 0; simp⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a + b, ?_⟩
      change F (a + b) = (IsLocalRing.maximalIdeal S).toCotangent
        ((⟨x, hm ▸ hx⟩ : IsLocalRing.maximalIdeal S) + ⟨y, hm ▸ hy⟩)
      simp only [map_add, ha, hb]
    | smul b x hx ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨r, hr⟩ := hres (IsLocalRing.residue S b)
      refine ⟨r • a, ?_⟩
      rw [hsmul, ha, ← map_smul]
      apply (IsLocalRing.maximalIdeal S).toCotangent_eq.mpr
      change φ r * x - b * x ∈ IsLocalRing.maximalIdeal S ^ 2
      rw [← sub_mul, pow_two]
      apply Ideal.mul_mem_mul _ (hm ▸ hx)
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      simpa only [map_sub, RingHom.comp_apply, sub_eq_zero] using hr
  · intro hsurj
    have : Subsingleton (KaehlerDifferential R (IsLocalRing.ResidueField S)) :=
      KaehlerDifferential.subsingleton_of_surjective R (IsLocalRing.ResidueField S) hres
    let e := Ideal.Cotangent.equivOfEq (IsLocalRing.maximalIdeal S)
      (RingHom.ker (algebraMap S (IsLocalRing.ResidueField S)))
      (IsLocalRing.ker_residue (R := S)).symm
    let δ := (KaehlerDifferential.kerCotangentToTensor R S (IsLocalRing.ResidueField S)).comp
      e.toLinearMap
    have hδ : Function.Surjective δ := by
      apply Function.Surjective.comp _ e.surjective
      intro t
      exact (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S
        (IsLocalRing.ResidueField S) IsLocalRing.residue_surjective t).mp (Subsingleton.elim _ _)
    have hδc (c : IsLocalRing.maximalIdeal S) :
        δ ((IsLocalRing.maximalIdeal S).toCotangent c) =
          TensorProduct.tmul S 1 (KaehlerDifferential.D R S c.1) := by
      simp only [δ, e, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Ideal.Cotangent.equivOfEq_toCotangent,
        KaehlerDifferential.kerCotangentToTensor_toCotangent]
      rfl
    have hz : ∀ c, δ c = 0 := by
      intro c
      obtain ⟨a, rfl⟩ := hsurj c
      obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ a
      rw [Ideal.mapCotangent_toCotangent, hδc]
      change TensorProduct.tmul S 1 (KaehlerDifferential.D R S (algebraMap R S a.1)) = 0
      simp
    have : Subsingleton
        (TensorProduct S (IsLocalRing.ResidueField S) (KaehlerDifferential R S)) :=
      subsingleton_of_forall_eq 0 fun t ↦ by
        obtain ⟨c, rfl⟩ := hδ t
        exact hz c
    have : Subsingleton (KaehlerDifferential R S) :=
      (IsLocalRing.subsingleton_tensorProduct (R := S)).mp inferInstance
    exact ⟨inferInstance⟩

namespace AlgebraicGeometry

-- Keep the original hypotheses although the proof works under weaker assumptions.
set_option linter.unusedVariables false in
/-- Let `f : X ⟶ Y` be a morphism locally of finite type between schemes over a field `k`
(`hf : f ≫ pY = pX`), and let `x` and `y = f x` be closed points with residue fields equal
to `k` (`hκx`, `hκy`: the structure maps `k → κ(x)`, `k → κ(y)` are bijective). Then `f` is
unramified at `x` (some open `U ∋ x` with `U.ι ≫ f` locally of finite type with open-immersion
diagonal, def-weil-unramified-morphism) if and only if the map
`m_y/m_y² → m_x/m_x²` induced by the local ring map `f.stalkMap x` (Mathlib's
`Ideal.mapCotangent`) is surjective.

Source: literature/stacks-project/varieties.tex, lemma-injective-tangent-spaces-unramified
(blueprint: lem-sc-rational-unramified-cotangent-criterion).
Proof: choose affine opens `Spec B ∋ x` over `Spec R ∋ y` with `R → B` of finite type, and
let `A → C` be the induced local map of local rings; then `Ω_{C/A} = (Ω_{B/R})_q`. Since
`Ω_{B/R}` is finite, `f` is unramified at `x` iff `Ω_{C/A} = 0` (localize at some `g ∉ q`
and use the affine criterion for unramified ring maps). As `κ(y) = κ(x) = k`, the
Jacobi–Zariski sequence identifies `Ω_{C/A} ⊗ κ(x)` with the cokernel of
`m_y/m_y² → m_x/m_x²`; by Nakayama `Ω_{C/A} = 0` iff this cokernel vanishes. -/
theorem rational_unramified_iff_cotangent_surjective
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ pY = pX) (x : X)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({f x} : Set Y))
    (hκx : Function.Bijective (pX.residueFieldMap x).hom)
    (hκy : Function.Bijective (pY.residueFieldMap (f x)).hom) :
    (∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧
        IsOpenImmersion (pullback.diagonal (U.ι ≫ f))) ↔
      Function.Surjective
        (Ideal.mapCotangent (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (f.stalkMap x).hom.toIntAlgHom
          (Ideal.map_le_iff_le_comap.mp
            (IsLocalRing.map_maximalIdeal_le (f.stalkMap x).hom)) :
          IsLocalRing.CotangentSpace (Y.presheaf.stalk (f x)) →ₗ[ℤ]
            IsLocalRing.CotangentSpace (X.presheaf.stalk x)) := by
  have hr : Function.Surjective ((IsLocalRing.residue (X.presheaf.stalk x)).comp
      (f.stalkMap x).hom) := by
    have he : Function.Surjective (f.residueFieldMap x).hom := by
      subst pX
      rw [Scheme.residueFieldMap_comp] at hκx
      exact Function.Surjective.of_comp hκx.2
    exact he.comp (IsLocalRing.residue_surjective (R := Y.presheaf.stalk (f x)))
  rw [← local_unramified_iff_cotangent_surjective (f.stalkMap x).hom
    (LocallyOfFiniteType.stalkMap f x) hr]
  constructor
  · rintro ⟨U, hxU, hft, hd⟩
    let := hft
    let := hd
    have h := FormallyUnramified.stalkMap (U.ι ≫ f) ⟨x, hxU⟩
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.FormallyUnramified.respectsIso.cancel_right_isIso] at h
    exact h
  · intro h
    obtain ⟨U, hxU, hu⟩ := FormallyUnramified.exists_neighbourhood_of_stalkMap f x h
    let := hu
    exact ⟨U, hxU, inferInstance, inferInstance⟩

end AlgebraicGeometry
