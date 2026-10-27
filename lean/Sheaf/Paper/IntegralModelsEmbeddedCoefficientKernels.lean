/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.Paper.IntegralModelsEmbedded
import all Sheaf.Paper.ConstantCompletionEquivalence
import all Sheaf.Paper.ConstantCompletionCore
import Sheaf.Paper.IntegralModelsEmbeddedScalarFlat
import Sheaf.Paper.IntegralModelsEmbeddedResidueSections

/-! # Underived embedded integral coefficient comparison

Source: Stacks Project, Tags 099L and 099I.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  IntegralModelsStacks.smallMap

section ResidueKernels

universe v
variable {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
  {R B S T : Sheaf J CommRingCat.{v}}

private theorem image_span_generator (f : R ⟶ B) (K : RingedSiteIdeal R)
    (U : C) (r : R.obj.obj (op U)) (hK : K.sections U = Ideal.span {r}) :
    Ideal.span (Set.range (fun a : K.sections U ↦ f.hom.app (op U) a)) =
      Ideal.span {f.hom.app (op U) r} := by
  have he : Set.range (fun a : K.sections U ↦ f.hom.app (op U) a) =
      (f.hom.app (op U)).hom '' (K.sections U : Set (R.obj.obj (op U))) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [he]
  change Ideal.map (f.hom.app (op U)).hom (K.sections U) = _
  rw [hK, Ideal.map_span, Set.image_singleton]

private theorem residue_kernel_comparison (φ : R ⟶ B) (q : R ⟶ S) (p : B ⟶ T)
    (e : S ≅ T) (r : (R.obj ⋙ forget CommRingCat).sections)
    (hq : Presheaf.IsLocallySurjective J q.hom)
    (hw : φ ≫ p = q ≫ e.hom)
    (hR : ∀ U : C, RingHom.ker (q.hom.app (op U)).hom =
      Ideal.span {r.val (op U)})
    (hB : ∀ U : C, RingHom.ker (p.hom.app (op U)).hom =
      Ideal.span {φ.hom.app (op U) (r.val (op U))}) :
    SheafOfModules.IsFiniteType.{v, v, v} (ConstantCompletion.kernelIdeal q).module ∧
      (ConstantCompletion.kernelIdeal q).IsQuotientIso φ ∧
      (ConstantCompletion.kernelIdeal q).extension φ = ConstantCompletion.kernelIdeal p := by
  let K := ConstantCompletion.kernelIdeal q
  let L := ConstantCompletion.kernelIdeal p
  have hK (U : C) : K.sections U = RingHom.ker (q.hom.app (op U)).hom :=
    (ConstantCompletion.kernelIdeal_existsUnique q).exists.choose_spec U
  have hL (U : C) : L.sections U = RingHom.ker (p.hom.app (op U)).hom :=
    (ConstantCompletion.kernelIdeal_existsUnique p).exists.choose_spec U
  have hext : K.extension φ = L := by
    apply ConstantCompletion.extension_eq_of_span φ K L
    intro U
    rw [hL, hB U]
    exact (image_span_generator φ K U (r.val (op U)) ((hK U).trans (hR U))).symm
  have hc (U : C) (a : R.obj.obj (op U)) :
      p.hom.app (op U) (φ.hom.app (op U) a) =
        e.hom.hom.app (op U) (q.hom.app (op U) a) :=
    congrArg (fun f ↦ f.hom.app (op U) a) hw
  refine ⟨?_, ?_, hext⟩
  · apply ConstantCompletion.ideal_finiteType_of_span K 1 (fun _ ↦ r)
    intro U
    rw [hK, hR]
    simp only [Set.range_const]
  · constructor
    · intro U a
      rw [hext, hL, hK]
      change p.hom.app (op U) (φ.hom.app (op U) a) = 0 ↔
        q.hom.app (op U) a = 0
      rw [hc]
      constructor
      · intro ha
        have hz := congrArg (fun b ↦ e.inv.hom.app (op U) b) ha
        have hi := congrArg (fun f ↦ f.hom.app (op U)
          (q.hom.app (op U) a)) e.hom_inv_id
        change e.inv.hom.app (op U) (e.hom.hom.app (op U)
          (q.hom.app (op U) a)) = q.hom.app (op U) a at hi
        rw [hi, map_zero] at hz
        exact hz
      · intro ha
        rw [ha, map_zero]
    · intro U b
      let s := e.inv.hom.app (op U) (p.hom.app (op U) b)
      let := hq
      refine ⟨Presheaf.imageSieve q.hom s, Presheaf.imageSieve_mem J q.hom s, ?_⟩
      intro V g hg
      obtain ⟨a, ha⟩ := hg
      refine ⟨a, ?_⟩
      rw [hext, hL]
      change p.hom.app (op V) (B.obj.map g.op b - φ.hom.app (op V) a) = 0
      rw [map_sub, hc, ha]
      have hn := ConcreteCategory.congr_hom (e.inv.hom.naturality g.op)
        (p.hom.app (op U) b)
      change e.inv.hom.app (op V) (T.obj.map g.op (p.hom.app (op U) b)) =
        S.obj.map g.op s at hn
      rw [← hn]
      have hn' := ConcreteCategory.congr_hom (p.hom.naturality g.op) b
      change p.hom.app (op V) (B.obj.map g.op b) =
        T.obj.map g.op (p.hom.app (op U) b) at hn'
      rw [hn']
      have hi := congrArg (fun f ↦ f.hom.app (op V)
        (T.obj.map g.op (p.hom.app (op U) b))) e.inv_hom_id
      change e.hom.hom.app (op V)
        (e.inv.hom.app (op V) (T.obj.map g.op (p.hom.app (op U) b))) =
          T.obj.map g.op (p.hom.app (op U) b) at hi
      rw [hi, sub_self]

end ResidueKernels

set_option maxHeartbeats 800000 in
-- The reconstructed coefficient-map types require additional definitional-equality checks.
attribute [-instance] integralModel_coefficientMonObj in
/-- The embedded scalar map is flat and identifies the residue quotient, and extension
of the constant residue kernel is exactly the completed residue kernel.

Source: integral-models proof, paragraph (1); Stacks Tags 093M, 099L, 099I and 0A07
(blueprint: lem-sfb-embedded-integral-coefficient-kernels).

Proof: obtain flatness of the specified scalar map from the scalar-flatness lemma.
For the ideal assertions use the residue-section presentation: its global generator
r cuts out the constant kernel, its scalar image cuts out the completed kernel, and
the two quotient maps commute with an isomorphism of their residue rings. The named
kernel ideals have exactly the sectionwise kernels. The finite-generator ideal
lemma applied to the single section r proves finite type. The image of the principal
ideal (r) is generated by the image of r, by Ideal.map_span; local saturation
therefore identifies its extension with the completed kernel. The commuting square
and the inverse residue isomorphism prove that scalar preimages of that kernel are
exactly the constant kernel. To lift a completed section modulo this kernel, apply
local surjectivity of the constant residue map to the inverse residue image of its
completed reduction. On that covering image sieve choose a residue lift a. Naturality
and the square show that the difference from phi(a) has zero completed reduction,
hence belongs to the extended ideal. These are precisely the two local conditions
of IsQuotientIso. This works on empty covering sieves as well. -/
theorem integralModelsEmbeddedCoefficientKernels
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X] :
    let φ := IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.scalarMap ℓ E X)
    let q := IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.residueMap ℓ E π X)
    let qB := IntegralModelsStacks.smallMap X
      (completedCoefficientMap X (completedReduction ℓ E π 0)).hom
    let I := ConstantCompletion.kernelIdeal q
    SheafOfModules.IsFiniteType.{u + 1, u + 1, u + 1} I.module ∧
      SheafOfModules.IsFlat.{u + 1}
        ((SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (Scheme.coefficientProEtaleModelTopology.{u, u} X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)).obj
            (SheafOfModules.unit (siteModuleRings _))) ∧
      I.IsQuotientIso φ ∧ I.extension φ = ConstantCompletion.kernelIdeal qB := by
  obtain ⟨e, r, hq, hw, hR, hB⟩ := integralModelsEmbeddedResidueSections ℓ E π hπ X
  let φ := IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.scalarMap ℓ E X)
  let q := IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.residueMap ℓ E π X)
  let qB := IntegralModelsStacks.smallMap X
    (completedCoefficientMap X (completedReduction ℓ E π 0)).hom
  have h := residue_kernel_comparison φ q qB e r hq hw hR hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.1
  · exact integralModelsEmbeddedScalarFlat ℓ E π hπ X
  · exact h.2.1
  · exact h.2.2

end AlgebraicGeometry.ProEtale
