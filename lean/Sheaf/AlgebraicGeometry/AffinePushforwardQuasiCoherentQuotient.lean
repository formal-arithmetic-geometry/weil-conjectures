module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affine pushforward of quasi-coherent quotients

Source: Stacks Project, Divisors, Tag 080G, final sentence of the proof;
Schemes, Tags 01IB, 01IC and 01LC
(blueprint: lem-trf-affine-pushforward-quasi-coherent-quotient).

A subsheaf is represented by a monomorphism. Its quotient is any cokernel cofork,
so the result does not depend on a chosen realization of the sheafified quotient.
The quotient after pushforward is Mathlib's categorical cokernel. Naturality is
expressed for the induced quotient arrows, characterized by their commuting squares.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem ker_eq_range_of_exact {Z : Scheme.{u}} (S : ShortComplex Z.Modules)
    (hS : S.Exact) [Mono S.f] (U : Z.Opens) :
    LinearMap.ker (S.g.val.app (op U)).hom =
      LinearMap.range (S.f.val.app (op U)).hom := by
  let E := SheafOfModules.evaluation Z.ringCatSheaf (op U)
  have : E.Additive := { map_add := rfl }
  have : PreservesFiniteLimits E :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have hE := hS.map_of_mono_of_preservesKernel E inferInstance inferInstance
  exact hE.moduleCat_range_eq_ker.symm

/-- Affine pushforward preserves a quasi-coherent quotient, including its sectionwise
kernel, affine section surjectivity, and unique natural quotient isomorphism.

Source: Stacks Project, Divisors, Tag 080G, final sentence of the proof;
Schemes, Tags 01IB, 01IC and 01LC
(blueprint: lem-trf-affine-pushforward-quasi-coherent-quotient).

Proof:
1. Apply `lem-weil-pbc-quasi-coherent-module-cokernel-image` to the inclusion.
Its cokernel is the specified sheafified quotient and is quasi-coherent. Its local
image is the original subsheaf: local lifts agree because the inclusion is mono,
and glue by the sheaf axiom. Thus the kernel on every open is the subsheaf's sections;
on affine opens the quotient map is surjective.
2. By `lem-weil-pbc-affine-morphism-permanence`, an affine morphism is quasi-compact
and quasi-separated. Apply `pqf-lem-pushforward-qcoh` to all three modules. Pushforward
is evaluation on inverse images, giving sectionwise injectivity and the kernel formula
on every open. An affine open has affine inverse image, giving affine surjectivity.
3. The pushed quotient map kills the pushed inclusion. The cokernel universal property
(`def-weil-pbc-sheafification`) gives the unique comparison factoring this map through
the quotient projection. Apply `lem-weil-pbc-quasi-coherent-module-cokernel-image` to
the pushed inclusion. On every affine open both quotient projections are surjective
with the same kernel, so the comparison is bijective on those sections.
4. Apply `lem-weil-pbc-quasi-coherent-iso-on-affine-cover` to obtain an isomorphism.
The pushed quotient map is epi, since it is a quotient projection followed by this
isomorphism. Together with the kernel formula and the pushed monomorphism, this
proves short exactness in `def-weil-sheaf-of-modules-category`.
5. For a morphism of pairs, precompose the desired naturality equation with the
quotient projection. The defining equations for the induced quotient arrows and
both comparison maps make the two composites equal. Cancel the epimorphic quotient
projection. The same cancellation proves uniqueness of the comparison isomorphism. -/
theorem affine_pushforward_quasiCoherent_quotient
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {K H Q : X.Modules} (i : K ⟶ H) [Mono i]
    [K.IsQuasicoherent] [H.IsQuasicoherent]
    (q : H ⟶ Q) (hiq : i ≫ q = 0)
    (_hq : IsColimit (CokernelCofork.ofπ q hiq)) :
    Q.IsQuasicoherent ∧
    ((pushforward f).obj K).IsQuasicoherent ∧
    ((pushforward f).obj H).IsQuasicoherent ∧
    ((pushforward f).obj Q).IsQuasicoherent ∧
    ((ShortComplex.mk i q hiq).map (pushforward f)).ShortExact ∧
    (∀ U : Y.Opens, IsAffineOpen U →
      Function.Surjective (q.app (f ⁻¹ᵁ U)) ∧
      LinearMap.ker (q.val.app (op (f ⁻¹ᵁ U))).hom =
        LinearMap.range (i.val.app (op (f ⁻¹ᵁ U))).hom) ∧
    (∀ U : Y.Opens,
      LinearMap.ker (((pushforward f).map q).val.app (op U)).hom =
        LinearMap.range (((pushforward f).map i).val.app (op U)).hom) ∧
    (∃ θ : cokernel ((pushforward f).map i) ≅ (pushforward f).obj Q,
      cokernel.π ((pushforward f).map i) ≫ θ.hom = (pushforward f).map q ∧
      (∀ θ' : cokernel ((pushforward f).map i) ≅ (pushforward f).obj Q,
        cokernel.π ((pushforward f).map i) ≫ θ'.hom = (pushforward f).map q →
          θ' = θ) ∧
      ∀ (K' H' Q' : X.Modules) (i' : K' ⟶ H') (_hi' : Mono i')
        (_hK' : K'.IsQuasicoherent) (_hH' : H'.IsQuasicoherent)
        (q' : H' ⟶ Q') (hi'q' : i' ≫ q' = 0)
        (_hq' : IsColimit (CokernelCofork.ofπ q' hi'q'))
        (a : H ⟶ H') (b : K ⟶ K') (_hab : i ≫ a = b ≫ i')
        (aQ : Q ⟶ Q') (_haQ : q ≫ aQ = a ≫ q')
        (aP : cokernel ((pushforward f).map i) ⟶ cokernel ((pushforward f).map i'))
        (_haP : cokernel.π ((pushforward f).map i) ≫ aP =
          (pushforward f).map a ≫ cokernel.π ((pushforward f).map i'))
        (θ' : cokernel ((pushforward f).map i') ≅ (pushforward f).obj Q')
        (_hθ' : cokernel.π ((pushforward f).map i') ≫ θ'.hom = (pushforward f).map q'),
        aP ≫ θ'.hom = θ.hom ≫ (pushforward f).map aQ) := by
  let S := ShortComplex.mk i q hiq
  have hS : S.Exact := S.exact_of_g_is_cokernel _hq
  let e : cokernel i ≅ Q :=
    (cokernelIsCokernel i).coconePointUniqueUpToIso _hq
  have he : cokernel.π i ≫ e.hom = q :=
    (cokernelIsCokernel i).comp_coconePointUniqueUpToIso_hom _hq WalkingParallelPair.one
  have hci := quasiCoherent_cokernel_image i
  have : (cokernel i).IsQuasicoherent := hci.2.2.2.2.2.2.1
  have hQ : Q.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e inferInstance
  have hKp := isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f K
  have hHp := isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f H
  have hQp := isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f Q
  have hsurj (U : X.Opens) (hU : IsAffineOpen U) : Function.Surjective (q.app U) := by
    have hπ := (hci.2.2.2.2.2.2.2.2 ⟨U, hU⟩).2.1
    have heU : Function.Bijective (e.hom.app U) :=
      ConcreteCategory.bijective_of_isIso
        ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map e.hom)
    have hc := heU.surjective.comp hπ
    simpa only [← he, Hom.comp_app, ConcreteCategory.coe_comp] using hc
  have hmonop : Mono ((pushforward f).map i) := inferInstance
  have hmonoS : Mono (S.map (pushforward f)).f := hmonop
  have hSp : (S.map (pushforward f)).Exact :=
    hS.map_of_mono_of_preservesKernel (pushforward f) inferInstance inferInstance
  have hw : (pushforward f).map i ≫ (pushforward f).map q = 0 := by
    rw [← Functor.map_comp, hiq, Functor.map_zero]
  let t := cokernel.desc ((pushforward f).map i) ((pushforward f).map q) hw
  have ht : cokernel.π ((pushforward f).map i) ≫ t = (pushforward f).map q :=
    cokernel.π_desc _ _ _
  have hcp := quasiCoherent_cokernel_image ((pushforward f).map i)
  have : (cokernel ((pushforward f).map i)).IsQuasicoherent :=
    hcp.2.2.2.2.2.2.1
  have htbij (U : Y.affineOpens) : Function.Bijective (t.app U.1) := by
    have hπ := (hcp.2.2.2.2.2.2.2.2 U).2.1
    have hkπ := (hcp.2.2.2.2.2.2.2.2 U).2.2.1
    have hkq : LinearMap.ker (((pushforward f).map q).val.app (op U.1)).hom =
        LinearMap.range (((pushforward f).map i).val.app (op U.1)).hom :=
      ker_eq_range_of_exact (S.map (pushforward f)) hSp U.1
    have htu (x : Γ((pushforward f).obj H, U.1)) :
        t.app U.1 ((cokernel.π ((pushforward f).map i)).app U.1 x) =
          ((pushforward f).map q).app U.1 x :=
      ConcreteCategory.congr_hom (congrArg (fun a ↦ a.app U.1) ht) x
    constructor
    · apply (injective_iff_map_eq_zero (t.app U.1).hom).mpr
      intro y hy
      obtain ⟨x, rfl⟩ := hπ y
      have hx : x ∈ LinearMap.ker (((pushforward f).map q).val.app (op U.1)).hom := by
        change ((pushforward f).map q).app U.1 x = 0
        rw [← htu, hy]
      exact hkπ.ge (hkq.le hx)
    · intro y
      obtain ⟨x, hx⟩ := hsurj (f ⁻¹ᵁ U.1) (U.2.preimage f) y
      exact ⟨(cokernel.π ((pushforward f).map i)).app U.1 x, (htu x).trans hx⟩
  have : IsIso t := Hom.isIso_of_bijective_on_affine_open_cover t
    (fun U : Y.affineOpens ↦ U.1) (iSup_affineOpens_eq_top Y) (fun U ↦ U.2) htbij
  let θ := asIso t
  have hepip : Epi ((pushforward f).map q) := by
    rw [← ht]
    infer_instance
  refine ⟨hQ, hKp, hHp, hQp, ?_, ?_, ?_, θ, ht, ?_, ?_⟩
  · exact { exact := hSp, mono_f := hmonop, epi_g := hepip }
  · intro U hU
    exact ⟨hsurj _ (hU.preimage f), ker_eq_range_of_exact S hS _⟩
  · exact ker_eq_range_of_exact (S.map (pushforward f)) hSp
  · intro θ' hθ'
    apply Iso.ext
    apply (cancel_epi (cokernel.π ((pushforward f).map i))).mp
    exact hθ'.trans ht.symm
  · intro K' H' Q' i' hi' hK' hH' q' hi'q' hq' a b hab aQ haQ aP haP θ' hθ'
    apply (cancel_epi (cokernel.π ((pushforward f).map i))).mp
    calc
      cokernel.π ((pushforward f).map i) ≫ aP ≫ θ'.hom =
          (pushforward f).map a ≫ (pushforward f).map q' := by
        rw [← Category.assoc, haP, Category.assoc, hθ']
      _ = (pushforward f).map q ≫ (pushforward f).map aQ := by
        rw [← Functor.map_comp, ← haQ, Functor.map_comp]
      _ = cokernel.π ((pushforward f).map i) ≫ θ.hom ≫
          (pushforward f).map aQ := by
        simpa only [θ, asIso_hom, Category.assoc] using
          congrArg (fun z ↦ z ≫ (pushforward f).map aQ) ht.symm

end AlgebraicGeometry.Scheme.Modules
