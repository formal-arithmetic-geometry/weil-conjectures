module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation

/-!
# Compatible finite affine coproduct maps for locally finitely presented composites

Source: Stacks Project, Descent, Tag 02KL, proof of
`lemma-flat-finitely-presented-permanence`; Morphisms, Tag 01TQ,
`lemma-locally-finite-presentation-characterize`
(blueprint: lem-trf-finite-affine-composite-presentation).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem sigma_desc_spec
    {J : Type u} [Finite J] {Y : Scheme.{u}} (A : J → Scheme.{u})
    (g : ∀ j, A j ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)
    (T : ∀ j, (A j).Opens) (hT : ∀ j, IsAffineOpen (T j))
    (hTV : ∀ j, T j ≤ g j ⁻¹ᵁ V) :
    (Sigma.mapIso (fun j ↦ (hT j).isoSpec) ≪≫
      asIso (sigmaSpec (fun j ↦ Γ(A j, T j)))).inv ≫
      Sigma.desc (fun j ↦ (g j).resLE V (T j) (hTV j)) ≫ hV.isoSpec.hom =
      Spec.map (CommRingCat.ofHom
        (RingHom.pi (fun j ↦ ((g j).appLE V (T j) (hTV j)).hom))) := by
  let e := Sigma.mapIso (fun j ↦ (hT j).isoSpec) ≪≫
    asIso (sigmaSpec (fun j ↦ Γ(A j, T j)))
  change e.inv ≫ _ ≫ _ = _
  rw [← cancel_epi e.hom, e.hom_inv_id_assoc]
  apply Sigma.hom_ext
  intro j
  simp only [e, Iso.trans_hom, asIso_hom, Category.assoc,
    Sigma.ι_desc_assoc, Sigma.ι_mapIso_hom_assoc, ι_sigmaSpec_assoc]
  rw [← Spec.map_comp]
  have hproj : CommRingCat.ofHom
      (RingHom.pi (fun j ↦ ((g j).appLE V (T j) (hTV j)).hom)) ≫
      CommRingCat.ofHom (Pi.evalRingHom _ j) = (g j).appLE V (T j) (hTV j) := by
    ext r
    rfl
  rw [hproj]
  exact (Scheme.Opens.toSpecΓ_SpecMap_appLE (g j) V (T j) (hTV j)).symm

/-- The finite affine coproduct reduction, including compatibility of both scheme maps and
both coordinate maps. Source: Stacks Project, Descent, Tag 02KL, proof of
`lemma-flat-finitely-presented-permanence`; Morphisms, Tag 01TQ
(blueprint: lem-trf-finite-affine-composite-presentation).

Here `R = Γ(S, V)`, `A = Γ(X, W)`, and `B j = Γ(U (i j), T j)`. The witnesses `q`, `p`
are characterized by their component restrictions, `e` is the canonical finite affine
coproduct isomorphism, and `β`, `γ` are the componentwise maps to the product ring.

Proof (the DAG proof, with its dependencies):
1. Restrict each `h (i j)` to `T j → W` and each composite to `T j → V`. Restriction of
structure-sheaf maps respects composition, so the latter is the former followed by
`f.resLE V W hWV`. The coproduct universal property constructs `q` and `p`, and uniqueness
of the descended map proves their compatibility
(`lem-weil-pbc-scheme-coproduct-family`, `def-pc-scheme`).
2. Identify each affine open with its spectrum and use `sigmaSpec` for the finite
coproduct. Its composite with a coprojection is the spectrum of the product projection.
Functoriality and faithfulness of `Spec` identify the ring maps of `q` and `p` with the
componentwise `β` and `γ`. Equality in the product is coordinatewise, so `γ` factors through
`f.appLE V W hWV` and `β`
(`lem-weil-pbc-finite-affine-coproduct-spectrum`, `def-weil-affine-spectrum`).
3. Apply the affine-open finite-presentation criterion (Tag 01TQ) to `h (i j) ≫ f`,
using `T j`, `V`, and the composite of the two given inclusions. Each component ring map
is finitely presented (`lem-weil-pbc-lfp-affine-opens-finite-presentation`).
4. The coprojections are open immersions covering the coproduct. At each point the
component from step 3 gives an affine neighbourhood over `V` with a finitely presented
ring map. Thus `p` is locally of finite presentation
(`lem-weil-pbc-scheme-coproduct-family`, `def-sbc-locally-finite-presentation`).
5. The coproduct is affine by step 2. Apply the affine-open criterion to `p`, with the
whole source and target, to deduce finite presentation of `γ`
(`lem-weil-pbc-lfp-affine-opens-finite-presentation`).
6. For empty `J`, the coproduct is empty and the product ring is zero. The map equalities
follow from the empty universal property, local finite presentation is vacuous, and the
zero algebra has the presentation `R/(1)`. A zero factor is an empty component with this
same presentation (`def-weil-pbc-finitely-presented-algebra`). No flatness, covering,
separation or Noetherian assumption is used. -/
theorem finite_affine_composite_presentation
    {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v} (U : I → Scheme.{u})
    (h : ∀ k : I, U k ⟶ X) [∀ k : I, LocallyOfFinitePresentation (h k ≫ f)]
    (V : S.Opens) (hV : IsAffineOpen V) (W : X.Opens) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) {J : Type u} [Finite J] (i : J → I)
    (T : ∀ j : J, (U (i j)).Opens) (hT : ∀ j : J, IsAffineOpen (T j))
    (hTW : ∀ j : J, T j ≤ h (i j) ⁻¹ᵁ W) :
    ∃ (q : (∐ fun j : J ↦ (T j).toScheme) ⟶ W.toScheme)
      (p : (∐ fun j : J ↦ (T j).toScheme) ⟶ V.toScheme)
      (e : (∐ fun j : J ↦ (T j).toScheme) ≅
        Spec (CommRingCat.of (∀ j : J, Γ(U (i j), T j))))
      (β : Γ(X, W) →+* (∀ j : J, Γ(U (i j), T j)))
      (γ : Γ(S, V) →+* (∀ j : J, Γ(U (i j), T j))),
      (∀ j : J, Sigma.ι (fun j : J ↦ (T j).toScheme) j ≫ q =
        (h (i j)).resLE W (T j) (hTW j)) ∧
      (∀ j : J, Sigma.ι (fun j : J ↦ (T j).toScheme) j ≫ p =
        (h (i j) ≫ f).resLE V (T j) (fun _ hx ↦ hWV (hTW j hx))) ∧
      p = q ≫ f.resLE V W hWV ∧
      e = Sigma.mapIso (fun j : J ↦ (hT j).isoSpec) ≪≫
        asIso (sigmaSpec (fun j : J ↦ Γ(U (i j), T j))) ∧
      β = RingHom.pi (fun j : J ↦ ((h (i j)).appLE W (T j) (hTW j)).hom) ∧
      γ = RingHom.pi (fun j : J ↦
        ((h (i j) ≫ f).appLE V (T j) (fun _ hx ↦ hWV (hTW j hx))).hom) ∧
      e.inv ≫ q ≫ hW.isoSpec.hom = Spec.map (CommRingCat.ofHom β) ∧
      e.inv ≫ p ≫ hV.isoSpec.hom = Spec.map (CommRingCat.ofHom γ) ∧
      γ = β.comp (f.appLE V W hWV).hom ∧
      (∀ j : J,
        ((h (i j) ≫ f).appLE V (T j) (fun _ hx ↦ hWV (hTW j hx))).hom.FinitePresentation) ∧
      LocallyOfFinitePresentation p ∧ γ.FinitePresentation := by
  let q := Sigma.desc (fun j ↦ (h (i j)).resLE W (T j) (hTW j))
  let p := Sigma.desc (fun j ↦
    (h (i j) ≫ f).resLE V (T j) (fun _ hx ↦ hWV (hTW j hx)))
  let e := Sigma.mapIso (fun j ↦ (hT j).isoSpec) ≪≫
    asIso (sigmaSpec (fun j ↦ Γ(U (i j), T j)))
  let β := RingHom.pi (fun j ↦ ((h (i j)).appLE W (T j) (hTW j)).hom)
  let γ := RingHom.pi (fun j ↦
    ((h (i j) ≫ f).appLE V (T j) (fun _ hx ↦ hWV (hTW j hx))).hom)
  have hq : e.inv ≫ q ≫ hW.isoSpec.hom = Spec.map (CommRingCat.ofHom β) :=
    sigma_desc_spec (fun j ↦ U (i j)) (fun j ↦ h (i j)) W hW T hT hTW
  have hp : e.inv ≫ p ≫ hV.isoSpec.hom = Spec.map (CommRingCat.ofHom γ) :=
    sigma_desc_spec (fun j ↦ U (i j)) (fun j ↦ h (i j) ≫ f) V hV T hT
      (fun j _ hx ↦ hWV (hTW j hx))
  have hlfp : LocallyOfFinitePresentation p :=
    IsZariskiLocalAtSource.sigmaDesc (fun j ↦ inferInstance)
  have hγ : γ.FinitePresentation := by
    apply (LocallyOfFinitePresentation.SpecMap_iff (CommRingCat.ofHom γ)).mp
    rw [← hp]
    have := hlfp
    infer_instance
  refine ⟨q, p, e, β, γ, ?_, ?_, ?_, rfl, rfl, rfl, hq, hp, ?_, ?_, hlfp, hγ⟩
  · intro j
    exact Sigma.ι_desc _ j
  · intro j
    exact Sigma.ι_desc _ j
  · apply Sigma.hom_ext
    intro j
    simp only [p, q, Sigma.ι_desc, Sigma.ι_desc_assoc]
    exact (Scheme.Hom.resLE_comp_resLE (h (i j)) (hTW j) f hWV).symm
  · ext r j
    exact (congrArg (fun a : Γ(S, V) ⟶ Γ(U (i j), T j) ↦ a.hom r)
      (Scheme.Hom.appLE_comp_appLE (h (i j)) f V W (T j) hWV (hTW j))).symm
  · intro j
    exact (h (i j) ≫ f).finitePresentation_appLE hV (hT j) _

end AlgebraicGeometry
