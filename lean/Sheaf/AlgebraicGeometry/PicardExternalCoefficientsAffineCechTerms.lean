/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.Topology.Sheaves.CechComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorAffine

/-! # Normalized affine-right Cech term comparisons

Source: Stacks Project, Tag 0BED, lemma-kunneth, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms).
-/

@[expose] public section

set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type w} [Field k] {X Y : Scheme.{w}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
variable (F : X.Modules) (G : Y.Modules) {ι : Type w} (U : ι → X.Opens) (V : Y.Opens)

/-- The additive-group complex on the inverse image of V.
Source: Stacks Project, Tag 0BED, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
abbrev picardAffineCechLeft : CochainComplex AddCommGrpCat.{w} ℕ :=
  let W := (pullback.snd f g) ⁻¹ᵁ V
  let E := (externalCupCoefficients f g F G).restrict W.ι
  let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
  ((forget₂ (ModuleCat.{w} Γ(W.toScheme, ⊤)) AddCommGrpCat.{w}).mapHomologicalComplex
    (.up ℕ)).obj ((cechComplexFunctor U').obj E.presheafModuleCat)

/-- The field-linear Cech complex with scalars restricted along f.
Source: Stacks Project, Tag 0BED, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
abbrev picardAffineCechBase : CochainComplex (ModuleCat.{w} k) ℕ :=
  ((ModuleCat.restrictScalars (scalarMap f ⊤)).mapHomologicalComplex (.up ℕ)).obj
    ((cechComplexFunctor U).obj F.presheafModuleCat)

/-- The fixed right tensor factor.
Source: Stacks Project, Tag 0BED, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
abbrev picardAffineCechFactor : ModuleCat.{w} k :=
  scalarObj (V.ι ≫ g) (G.restrict V.ι) (op ⊤)

/-- The additive-group complex obtained by termwise tensoring with G(V).
Source: Stacks Project, Tag 0BED, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
abbrev picardAffineCechRight : CochainComplex AddCommGrpCat.{w} ℕ :=
  ((forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w}).mapHomologicalComplex (.up ℕ)).obj
    (((tensorRight (picardAffineCechFactor g G V)).mapHomologicalComplex (.up ℕ)).obj
      (picardAffineCechBase f F U))

/-- The pure external section on one intersection, constructed from the two
pullback units and the tensor section operation. No affine hypothesis is needed.
Source: Stacks Project, Tag 0BED, maps preceding equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
def picardAffineCechPureSection (n : ℕ) (y : Fin (n + 1) → ι)
    (a : (picardAffineCechBase f F U).X n) (t : picardAffineCechFactor g G V) :
    let W := (pullback.snd f g) ⁻¹ᵁ V
    let E := (externalCupCoefficients f g F G).restrict W.ι
    let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
    Γ(E, ⨅ l, U' (y l)) := by
  let W := (pullback.snd f g) ⁻¹ᵁ V
  let E := externalCupCoefficients f g F G
  let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
  let J : W.toScheme.Opens := ⨅ l, U' (y l)
  let A : X.Opens := ⨅ l, U (y l)
  let K : (Limits.pullback f g).Opens := W.ι ''ᵁ J
  have hK : K ≤ (pullback.fst f g) ⁻¹ᵁ A := by
    apply (W.ι.image_mono ?_).trans (W.ι.image_preimage_le _)
    change (⨅ l, U' (y l)) ≤ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ (⨅ l, U (y l)))
    apply le_of_eq
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_iInf, Scheme.Hom.coe_preimage,
      Set.preimage_iInter]
    rfl
  have hKV : K ≤ (pullback.snd f g) ⁻¹ᵁ V := by
    exact (W.ι.image_mono le_top).trans_eq W.ι_image_top
  let s : Γ(F, A) := TopCat.Presheaf.cechComplexFunctorXAddEquiv
    U F.presheafModuleCat n a y
  let t' : Γ(G, V) := G.presheaf.map (eqToHom V.ι_image_top.symm).op
    ((G.restrictAppIso V.ι ⊤).hom t)
  let ηF := (Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).unit.app F
  let ηG := (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app G
  let s' : Γ((tensorPullback (pullback.fst f g)).obj F, K) :=
    ((tensorPullback (pullback.fst f g)).obj F).presheaf.map (homOfLE hK).op
      (ηF.val.app (op A) s)
  let t'' : Γ((tensorPullback (pullback.snd f g)).obj G, K) :=
    ((tensorPullback (pullback.snd f g)).obj G).presheaf.map (homOfLE hKV).op
      (ηG.val.app (op V) t')
  exact (E.restrictAppIso W.ι J).inv (tmulSection s' t'')

/-- Normalization of degreewise maps on pure tensors, coordinate by coordinate.
Source: Stacks Project, Tag 0BED, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
def PicardAffineCechNormalized
    (e : ∀ n, (picardAffineCechRight f g F G U V).X n ≅
      (picardAffineCechLeft f g F G U V).X n) : Prop :=
  let W := (pullback.snd f g) ⁻¹ᵁ V
  let E := (externalCupCoefficients f g F G).restrict W.ι
  let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
  ∀ (n : ℕ) (a : (picardAffineCechBase f F U).X n)
    (t : picardAffineCechFactor g G V) (y : Fin (n + 1) → ι),
      TopCat.Presheaf.cechComplexFunctorXAddEquiv U' E.presheafModuleCat n
        ((e n).hom (a ⊗ₜ[k] t)) y = picardAffineCechPureSection f g F G U V n y a t

/-- The affine-right external section comparison is a normalized isomorphism
in each degree. This assertion has no differential or cohomology condition.
Source: Stacks Project, Tag 0BED, lemma-kunneth, affine-open paragraph;
Tags 01I9 and 01CD for affine pullback and tensor sections.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms).

Proof: Each intersection in the inverse image of V is the product of an affine
intersection of U with V. Restriction versus open-immersion pullback and pullback
composition identify its coefficient with the external coefficient of the two
restricted modules. Affine pullback sections and tensor sections identify the
section module with M tensor_k N. This chart calculation is already proved by
externalGlobalSectionsTensor_bijective_of_isAffine in
Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorAffine: apply it to the two
restricted affine schemes instead of rebuilding the balanced tensor equivalence.
The normalized open-immersion and pullback-composition comparisons transport its
canonical pure-tensor formula to the two original pullback units followed by
tmulSection. In degree n the tuple set is finite. Use TensorProduct.piRight from
Mathlib.LinearAlgebra.TensorProduct.Pi, conjugated by tensor commutativity, for the
map (product M_y) tensor N to product (M_y tensor N). Its pure-tensor formula sends
a tensor of a tuple to its coordinate tensors, including the empty tuple set.
Compose this comparison with the chart comparisons and the native Cech product
coordinate isomorphisms. This gives the asserted normalized degreewise maps.
Empty tuple sets, empty intersections, empty V and zero coefficients give zero
terms and obey the same formulas. No covering or differential condition is used. -/
theorem picardAffineCech_normalized_terms [F.IsQuasicoherent] [G.IsQuasicoherent]
    [Finite ι]
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hV : IsAffineOpen V) :
    ∃ e : ∀ n, (picardAffineCechRight f g F G U V).X n ≅
      (picardAffineCechLeft f g F G U V).X n,
      PicardAffineCechNormalized f g F G U V e := by sorry

end
end AlgebraicGeometry.Scheme.Modules
