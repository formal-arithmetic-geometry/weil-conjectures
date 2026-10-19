/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Sheaf.Algebra.Category.ModuleCat.RingScalarExtension
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.ConstructibleSheaf.MonoidalParts
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import Mathlib.CategoryTheory.Sites.Adjunction

/-! # Tensor products, scalar extension and stalks of lisse sheaves

Source: Stacks Project, sites-modules, 093V, 03EL; etale-cohomology, 095D, 04FM,
03PN (blueprint: lem-pod-lisse-tensor-and-scalar-extension).

Lisse sheaves of `Λ`-modules are the sheaves satisfying the source predicate
`Scheme.IsFiniteLocallyConstantSheaf` at `A = ModuleCat Λ`. Geometric points have
algebraically closed fields. Stalks are the fibres of the lifted point
`(pointSmallEtale y).ulift`, as in lem-pod-etale-stalk-tensor-scalar.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}

/-- The constant-module stalk map is an isomorphism, without finiteness or commutativity.
Source: Stacks, 03PT (2), 040R (blueprint: lem-pod-lisse-tensor-and-scalar-extension).
Proof: apply lem-weil-pbc-constant-sheaf-geometric-stalk to the underlying abelian group.
Sheafification of modules has the underlying abelian sheafification. The global constant
section gives the indicated germ; its scalar linearity follows from the restriction maps. -/
theorem constant_module_stalk_isIso (R : Type (u + 1)) [Ring R]
    (M : ModuleCat.{u + 1} R) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    IsIso (((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} R)).app
      ((Functor.const Y.Etaleᵒᵖ).obj M)).app (op (⊤_ Y.Etale)) ≫
        (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber (⊤_ Y.Etale)
          ((pointSmallEtale y).ulift.{u + 1}.uniqueFiberObj _ terminalIsTerminal).default
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M).obj) := by
  let p := (pointSmallEtale y).ulift.{u + 1}
  let U : Y.Etale := ⊤_ Y.Etale
  let x := (p.uniqueFiberObj U terminalIsTerminal).default
  have h₁ : (p.presheafFiberConstIso M).inv =
      p.toPresheafFiber U x ((Functor.const Y.Etaleᵒᵖ).obj M) := by
    have h := p.toPresheafFiber_presheafFiberConstIso_hom M U x
    calc
      (p.presheafFiberConstIso M).inv = 𝟙 _ ≫ (p.presheafFiberConstIso M).inv :=
        (Category.id_comp _).symm
      _ = _ := by rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcomp : (p.presheafFiberConstIso M).inv ≫
      p.presheafFiber.map (toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj M)) =
      (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
        (op U) ≫ p.toPresheafFiber U x
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M).obj := by
    rw [h₁, p.toPresheafFiber_naturality]
    rfl
  rw [← hcomp]
  infer_instance

section Tensor

variable {R : Type (u + 1)} [CommRing R]

attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
attribute [local instance] CategoryTheory.Sheaf.braidedCategory

private def tensorSheafifyIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{u + 1} R)]
    (F G : Sheaf J (ModuleCat.{u + 1} R)) :
    F ⊗ G ≅ (presheafToSheaf J (ModuleCat.{u + 1} R)).obj (F.obj ⊗ G.obj) :=
  tensorIso (asIso ((sheafificationAdjunction J _).counit.app F)).symm
      (asIso ((sheafificationAdjunction J _).counit.app G)).symm ≪≫
    Functor.Monoidal.μIso (presheafToSheaf J _) F.obj G.obj

private def constantTensorIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{u + 1} R)]
    (M N : ModuleCat.{u + 1} R) :
    (constantSheaf J _).obj M ⊗ (constantSheaf J _).obj N ≅
      (constantSheaf J _).obj (M ⊗ N) :=
  Functor.Monoidal.μIso (presheafToSheaf J _)
      ((Functor.const Cᵒᵖ).obj M) ((Functor.const Cᵒᵖ).obj N) ≪≫
    (presheafToSheaf J _).mapIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp))

/-- Tensor preserves lissity. Source: Stacks, 093V and 095D
(blueprint: lem-pod-lisse-tensor-and-scalar-extension).
Proof: refine the two finite-value trivializing covers by their fibre products
(def-weil-pbc-etale-site). Restriction commutes with sheafification; tensor of the two
constant sheaves sheafifies to the constant tensor module. This module is finite over a
finite ring, giving the finite local values. The existing finite locally constant predicate
expresses the same property via local constancy and finite generation of geometric stalks. -/
theorem lisse_tensor_and_scalar_extension [Finite R]
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F) (hG : IsFiniteLocallyConstantSheaf G) :
    IsFiniteLocallyConstantSheaf (F ⊗ G) := by
  exact
    { toIsLocallyConstantSheaf :=
        IsLocallyConstantSheaf.tensorObj_part
          hF.toIsLocallyConstantSheaf hG.toIsLocallyConstantSheaf
      toIsFiniteSheaf := IsFiniteSheaf.tensorObj_part hF.toIsFiniteSheaf hG.toIsFiniteSheaf }

/-- The local tensor formula holds on every common trivializing etale neighbourhood.
Source: Stacks, 093V and 095D (blueprint: lem-pod-lisse-tensor-and-scalar-extension).
Proof: restriction commutes with sheafification. Apply the sectionwise tensor maps to the
local constant identifications. Their sheafification is the constant tensor product.
This is the local calculation in step 2 of the node's proof. -/
theorem lisse_tensor_local_iso [Finite R]
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F) (hG : IsFiniteLocallyConstantSheaf G)
    (U : Y.Etale) (M N : ModuleCat.{u + 1} R)
    (eF : Nonempty (F.over U ≅ (constantSheaf (Y.smallEtaleTopology.over U) _).obj M))
    (eG : Nonempty (G.over U ≅ (constantSheaf (Y.smallEtaleTopology.over U) _).obj N)) :
    Nonempty ((F ⊗ G).over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) _).obj (M ⊗ N)) := by
  have _ := hF
  have _ := hG
  obtain ⟨eF⟩ := eF
  obtain ⟨eG⟩ := eG
  let J := Y.smallEtaleTopology
  let A := ModuleCat.{u + 1} R
  let e := ((Over.forget U).pushforwardContinuousSheafificationCompatibility
    A (J.over U) J).app (F.obj ⊗ G.obj)
  refine ⟨(J.overPullback A U).mapIso (tensorSheafifyIso J F G) ≪≫ e.symm ≪≫ ?_⟩
  exact (tensorSheafifyIso (J.over U) (F.over U) (G.over U)).symm ≪≫
    tensorIso eF eG ≪≫ constantTensorIso (J.over U) M N

/-- The stalk comparison of a tensor product of lisse sheaves is the unique linear map
sending `s_y ⊗ t_y` to `(s ⊗ t)_y`, and it is an isomorphism.
Source: Stacks, 03EL, 04FM (blueprint: lem-pod-lisse-tensor-and-scalar-extension).
Proof: apply clause (1) of lem-pod-etale-stalk-tensor-scalar to `F` and `G`. Stalks and
sheafification commute with filtered colimits, as do tensor products; the comparison sends
the tensor of two germs to the germ of the sectionwise tensor, and pure germs generate.
This is step 3 of the node's proof. -/
theorem tensor_stalk_iso [Finite R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F) (hG : IsFiniteLocallyConstantSheaf G) :
    (let p := (pointSmallEtale y).ulift.{u + 1}
    let T := p.sheafFiber (A := ModuleCat.{u + 1} R)
    letI : T.Monoidal := inferInstanceAs
      ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).Monoidal
    letI := (sheafificationAdjunction Y.smallEtaleTopology
      (ModuleCat.{u + 1} R)).rightAdjointLaxMonoidal
    let P := fun f : T.obj F ⊗ T.obj G ⟶ T.obj (F ⊗ G) ↦
      ∀ (U : Y.Etale) (x : p.fiber.obj U),
        (p.toPresheafFiber U x F.obj ⊗ₘ p.toPresheafFiber U x G.obj) ≫ f =
          (Functor.LaxMonoidal.μ
            (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) F G).app (op U) ≫
            p.toPresheafFiber U x (F ⊗ G).obj
    (∃! f, P f) ∧ P (Functor.LaxMonoidal.μ T F G) ∧
      IsIso (Functor.LaxMonoidal.μ T F G)) := by
  have _ := hF
  have _ := hG
  exact etale_stalk_tensor_unique y F G

/-- The tensor stalk comparison is natural in lisse `F` and `G`.
Source: Stacks 008B and 03EL (blueprint: lem-pod-lisse-tensor-and-scalar-extension).
Proof: clause (1) of lem-pod-etale-stalk-tensor-scalar; both composites send pure germs
to the germ of the tensor of their images, and these generate. Step 4 of the proof. -/
theorem tensor_stalk_natural [Finite R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) {F F' G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (hF : IsFiniteLocallyConstantSheaf F) (hF' : IsFiniteLocallyConstantSheaf F')
    (hG : IsFiniteLocallyConstantSheaf G) (hG' : IsFiniteLocallyConstantSheaf G')
    (f : F ⟶ F') (g : G ⟶ G') :
    (let p := (pointSmallEtale y).ulift.{u + 1}
    let T := p.sheafFiber (A := ModuleCat.{u + 1} R)
    letI : T.Monoidal := inferInstanceAs
      ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).Monoidal
    (T.map f ⊗ₘ T.map g) ≫ Functor.LaxMonoidal.μ T F' G' =
      Functor.LaxMonoidal.μ T F G ≫ T.map (f ⊗ₘ g)) := by
  have _ := hF
  have _ := hF'
  have _ := hG
  have _ := hG'
  exact etale_stalk_tensor_natural y f g

/-- The tensor stalk comparison is compatible with the associativity, commutativity and
unit isomorphisms on both sides, for lisse `F`, `G`, `H`.
Source: Stacks 008B and 03EL (blueprint: lem-pod-lisse-tensor-and-scalar-extension).
Proof: clause (1) of lem-pod-etale-stalk-tensor-scalar; evaluate each diagram on pure
germs and use the corresponding module identities. Step 4 of the node's proof. -/
theorem tensor_stalk_coherence [Finite R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (F G H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F) (hG : IsFiniteLocallyConstantSheaf G)
    (hH : IsFiniteLocallyConstantSheaf H) :
    (let p := (pointSmallEtale y).ulift.{u + 1}
    let T := p.sheafFiber (A := ModuleCat.{u + 1} R)
    letI : T.Monoidal := inferInstanceAs
      ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).Monoidal
    ((Functor.LaxMonoidal.μ T F G ▷ T.obj H) ≫
        Functor.LaxMonoidal.μ T (F ⊗ G) H ≫ T.map (α_ F G H).hom =
      (α_ (T.obj F) (T.obj G) (T.obj H)).hom ≫
        (T.obj F ◁ Functor.LaxMonoidal.μ T G H) ≫
          Functor.LaxMonoidal.μ T F (G ⊗ H)) ∧
    ((β_ (T.obj F) (T.obj G)).hom ≫ Functor.LaxMonoidal.μ T G F =
      Functor.LaxMonoidal.μ T F G ≫ T.map (β_ F G).hom) ∧
    ((Functor.LaxMonoidal.ε T ▷ T.obj F) ≫
        Functor.LaxMonoidal.μ T (𝟙_ _) F ≫ T.map (λ_ F).hom =
      (λ_ (T.obj F)).hom) ∧
    ((T.obj F ◁ Functor.LaxMonoidal.ε T) ≫
        Functor.LaxMonoidal.μ T F (𝟙_ _) ≫ T.map (ρ_ F).hom =
      (ρ_ (T.obj F)).hom)) := by
  have _ := hF
  have _ := hG
  have _ := hH
  exact (etale_stalk_tensor_coherence y F G H).2

end Tensor

section Scalars

variable {R S : Type (u + 1)} [Ring R] [Ring S]

private def scalarOverIso (f : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (U : Y.Etale) :
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F).over U ≅
      (Sheaf.ringExtendScalars.{u + 1, u + 1} (Y.smallEtaleTopology.over U) f).obj
        (F.over U) :=
  (((Over.forget U).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} S) (Y.smallEtaleTopology.over U) Y.smallEtaleTopology).app
      (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).symm

private def scalarConstantIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{u + 1} R)]
    [HasWeakSheafify J (ModuleCat.{u + 1} S)] (f : R →+* S)
    (M : ModuleCat.{u + 1} R) :
    (Sheaf.ringExtendScalars.{u + 1, u + 1} J f).obj ((constantSheaf J _).obj M) ≅
      (constantSheaf J _).obj ((ModuleCat.ringExtendScalars.{u + 1, u + 1} f).obj M) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  exact (presheafToSheafCompComposeAndSheafifyIso J E).app
      ((Functor.const Cᵒᵖ).obj M) ≪≫
    (presheafToSheaf J _).mapIso (NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (by intros; simp))

private theorem scalarFinite (f : R →+* S) (M : ModuleCat.{u + 1} R)
    (hM : ConcreteCategory.IsFinitelyGenerated M) :
    ConcreteCategory.IsFinitelyGenerated
      ((ModuleCat.ringExtendScalars.{u + 1, u + 1} f).obj M) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f
  let η := adj.unit.app M
  obtain ⟨s, hs, h⟩ := hM
  refine ⟨η '' s, hs.image _, ?_⟩
  intro N m hm hsm
  let mR := (ModuleCat.restrictScalars f).map m
  have : Mono mR := inferInstance
  have hi : IsIso (pullback.snd mR η) := h _ inferInstance fun x hx ↦ by
    obtain ⟨n, hn⟩ := hsm ⟨x, hx, rfl⟩
    exact ⟨Concrete.pullbackMk mR η n x hn, Concrete.pullbackMk_snd mR η n x hn⟩
  let ℓ := inv (pullback.snd mR η) ≫ pullback.fst mR η
  have hℓ : ℓ ≫ mR = η := by
    dsimp only [ℓ]
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  let k := (adj.homEquiv M N).symm ℓ
  have hk : k ≫ m = 𝟙 (E.obj M) := by
    apply (adj.homEquiv M (E.obj M)).injective
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    simpa [Adjunction.homEquiv_unit] using! hℓ
  have : IsSplitEpi m := ⟨⟨⟨k, hk⟩⟩⟩
  exact isIso_of_mono_of_epi m

/-- Scalar extension preserves lissity over arbitrary finite rings.
Source: Stacks, Section 6.3 and 093V (blueprint: lem-pod-lisse-tensor-and-scalar-extension).
Proof: on a trivializing cover, sheafify the sectionwise balanced tensor to obtain the
constant sheaf of S tensor_R M. Its finite generating set and the finiteness of S give
finite local values. This is step 2 of the node's proof for scalar extension. -/
theorem lisse_ring_scalar_extension [Finite R] [Finite S] (f : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F) :
    IsFiniteLocallyConstantSheaf
      ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  refine { toIsLocallyConstantSheaf := ?_, toIsFiniteSheaf := ?_ }
  · obtain ⟨⟨𝒰, h𝒰⟩⟩ := hF.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
    refine ⟨⟨⟨𝒰, fun i ↦ ?_⟩⟩⟩
    have := h𝒰 i
    obtain ⟨M, ⟨e⟩⟩ := (F.over (𝒰.etalePrecoverageToEtale i)).mem_essImage_of_isConstant
    exact Sheaf.isConstant_of_iso _
      (scalarOverIso f F _ ≪≫
        (Sheaf.ringExtendScalars.{u + 1, u + 1} _ f).mapIso e.symm ≪≫
        scalarConstantIso _ f M)
  · constructor
    intro Ω _ _ y
    let p := (pointSmallEtale y).ulift.{u + 1}
    have hM := (hF.isFinitelyGenerated_sheafFiber Ω y).of_iso
      (((pointSmallEtale y).uliftSheafFiberIso.{u + 1}
        (ModuleCat.{u + 1} R)).app F).symm
    exact (scalarFinite f _ hM).of_iso
      ((p.presheafFiberCompIso E).symm.app F.obj ≪≫
        (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)).symm.app (F.obj ⋙ E) ≪≫
        ((pointSmallEtale y).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} S)).app _)

/-- The scalar-extension formula on every trivializing etale neighbourhood.
Source: Stacks, Section 6.3 (blueprint: lem-pod-lisse-tensor-and-scalar-extension).
Proof: restrict the sectionwise balanced tensor and sheafify; restriction commutes with
sheafification. The resulting constant value is S tensor_R M, as in proof step 2. -/
theorem lisse_ring_scalar_extension_local_iso [Finite R] [Finite S] (f : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F) (U : Y.Etale) (M : ModuleCat.{u + 1} R)
    (eF : Nonempty (F.over U ≅ (constantSheaf (Y.smallEtaleTopology.over U) _).obj M)) :
    Nonempty (((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F).over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) _).obj
        ((ModuleCat.ringExtendScalars.{u + 1, u + 1} f).obj M)) := by
  have _ := hF
  obtain ⟨eF⟩ := eF
  exact ⟨scalarOverIso f F U ≪≫
    (Sheaf.ringExtendScalars.{u + 1, u + 1} (Y.smallEtaleTopology.over U) f).mapIso eF ≪≫
    scalarConstantIso (Y.smallEtaleTopology.over U) f M⟩

/-- For a lisse sheaf `F`, the canonical stalk comparison
`S ⊗_R F_y → (S ⊗_R F)_y` (the inverse of the fibre comparisons of the left adjoint
`S ⊗_R -` and of sheafification) sends `b ⊗ a_y` to `(b ⊗ a)_y` and is an isomorphism.
Source: Stacks, 03EL, 04FM, 008B (blueprint: lem-pod-lisse-tensor-and-scalar-extension).
Proof: apply clause (2) of lem-pod-etale-stalk-tensor-scalar with
`E = ModuleCat.ringExtendScalars f`. The balanced tensor, a left adjoint, commutes with the
filtered colimit of pointed neighbourhoods; sheafification leaves this stalk unchanged.
The comparison is S-linear and sends b tensor a_y to the germ of b tensor a. This is proof
step 5. -/
theorem ring_scalar_extension_stalk_iso [Finite R] [Finite S] (f : R →+* S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F) :
    (letI := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
    let p := (pointSmallEtale y).ulift.{u + 1}
    let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
    let J := Y.smallEtaleTopology
    let c := (p.presheafFiberCompIso E).inv.app F.obj ≫
      (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)).inv.app (F.obj ⋙ E)
    (∀ (U : Y.Etale) (x : p.fiber.obj U) (b : S) (a : F.obj.obj (op U)),
      c (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ b (p.toPresheafFiber U x F.obj a)) =
        p.toPresheafFiber U x ((Sheaf.ringExtendScalars.{u + 1, u + 1} J f).obj F).obj
          (((toSheafification J (ModuleCat.{u + 1} S)).app (F.obj ⋙ E)).app (op U)
            (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ b a))) ∧
      IsIso c) := by
  have _ := hF
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f
  let := adj.isLeftAdjoint
  let p := (pointSmallEtale y).ulift.{u + 1}
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let Q := (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F
  let c := (p.presheafFiberCompIso E).inv.app F.obj ≫
    (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)).inv.app (F.obj ⋙ E)
  have h := etale_stalk_scalar_component_unique y f E adj F
  dsimp only at h ⊢
  refine ⟨?_, h.2.2⟩
  intro U x b a
  have he := congrArg (fun k ↦ k a) (h.2.1 U x)
  change c (adj.unit.app _ (p.toPresheafFiber U x F.obj a)) =
    p.toPresheafFiber U x Q.obj
      ((toSheafify Y.smallEtaleTopology (F.obj ⋙ E)).app (op U) (adj.unit.app _ a)) at he
  change c (b • (show E.obj _ from
      adj.unit.app _ (p.toPresheafFiber U x F.obj a))) =
    p.toPresheafFiber U x Q.obj
      ((toSheafify Y.smallEtaleTopology (F.obj ⋙ E)).app (op U)
        (b • (show E.obj _ from adj.unit.app _ a)))
  simpa only [map_smul] using! congrArg (fun z ↦ b • z) he

/-- The scalar stalk comparison is natural in lisse `F`.
Source: Stacks, 03EL, 04FM, 008B (blueprint: lem-pod-lisse-tensor-and-scalar-extension).
Proof: clause (2) of lem-pod-etale-stalk-tensor-scalar; both composites send `b ⊗ a_y` to
the germ of `b ⊗ φ(a)`, and these generate. Proof step 5. -/
theorem ring_scalar_extension_stalk_natural [Finite R] [Finite S] (f : R →+* S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (hF : IsFiniteLocallyConstantSheaf F) (hF' : IsFiniteLocallyConstantSheaf F')
    (φ : F ⟶ F') :
    (letI := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
    let p := (pointSmallEtale y).ulift.{u + 1}
    let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
    let c := fun G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ↦
      (p.presheafFiberCompIso E).inv.app G.obj ≫
        (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)).inv.app (G.obj ⋙ E)
    E.map (p.sheafFiber.map φ) ≫ c F' =
      c F ≫ p.sheafFiber.map
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).map φ)) := by
  have _ := hF
  have _ := hF'
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  let p := (pointSmallEtale y).ulift.{u + 1}
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  have h₁ := (p.presheafFiberCompIso E).inv.naturality φ.hom
  have h₂ := (p.presheafToSheafCompSheafFiberIso
    (ModuleCat.{u + 1} S)).inv.naturality ((Functor.whiskeringRight _ _ _).obj E |>.map φ.hom)
  dsimp only [Functor.comp_map] at h₁ h₂
  change E.map (p.presheafFiber.map φ.hom) ≫
      ((p.presheafFiberCompIso E).inv.app F'.obj ≫
        (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)).inv.app (F'.obj ⋙ E)) =
    ((p.presheafFiberCompIso E).inv.app F.obj ≫
      (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)).inv.app (F.obj ⋙ E)) ≫ _
  erw [← Category.assoc, h₁, Category.assoc, h₂]
  rfl

private theorem scalarCompIso_eq {T : Type (u + 1)} [Ring T]
    (f : R →+* S) (g : S →+* T) :
    (((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).comp
      (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} g)).ofNatIsoRight
        (ModuleCat.restrictScalarsComp f g).symm).leftAdjointUniq
          (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} (g.comp f)) =
      ModuleCat.ringExtensionComp.{u + 1, u + 1} f g := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let adj := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).comp
    (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} g)
  let adj' := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} (g.comp f)
  let e := ModuleCat.restrictScalarsComp.{u + 1} f g
  apply (adj.homEquiv M _).injective
  have h := (adj.ofNatIsoRight e.symm).homEquiv_leftAdjointUniq_hom_app adj' M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have h' := adj.homEquiv_leftAdjointUniq_hom_app (adj'.ofNatIsoRight e) M
  change adj.homEquiv M _ (((adj.ofNatIsoRight e.symm).leftAdjointUniq adj').hom.app M) =
    adj.homEquiv M _ ((adj.leftAdjointUniq (adj'.ofNatIsoRight e)).hom.app M)
  rw [h']
  apply (cancel_mono (e.inv.app _)).1
  simpa [Adjunction.ofNatIsoRight_unit] using h

private theorem scalarMapTmul (f : R →+* S)
    {M N : ModuleCat.{u + 1} R} (φ : M ⟶ N) (b : S) (m : M) :
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).map φ
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f M b m) =
      ModuleCat.ringExtensionTmul.{u + 1, u + 1} f N b (φ m) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f
  have h := congrArg (fun k ↦ k m) (adj.unit.naturality φ)
  change adj.unit.app N (φ m) = E.map φ (adj.unit.app M m) at h
  have h' : (E.map φ) (show E.obj M from adj.unit.app M m) =
      (show E.obj N from adj.unit.app N (φ m)) := h.symm
  simpa only [ModuleCat.ringExtensionTmul, map_smul] using! congrArg (fun z ↦ b • z) h'

private theorem scalarCompTmul {T : Type (u + 1)} [Ring T]
    (f : R →+* S) (g : S →+* T) (M : ModuleCat.{u + 1} R)
    (s : S) (d : T) (m : M) :
    (ModuleCat.ringExtensionComp.{u + 1, u + 1} f g).hom.app M
      (ModuleCat.ringExtensionTmul.{u + 1, u + 1} g _ d
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f M s m)) =
      ModuleCat.ringExtensionTmul.{u + 1, u + 1} (g.comp f) M (d * g s) m := by
  let adj₁ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f
  let adj₂ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} g
  let adj₃ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} (g.comp f)
  let a := ModuleCat.ringExtensionComp.{u + 1, u + 1} f g
  have h := congrArg (fun k ↦ k m)
    ((adj₁.comp adj₂).unit_leftAdjointUniq_hom_app
      (adj₃.ofNatIsoRight (ModuleCat.restrictScalarsComp f g)) M)
  change a.hom.app M (adj₂.unit.app _ (adj₁.unit.app M m)) = adj₃.unit.app M m at h
  simp only [ModuleCat.ringExtensionTmul, map_smul]
  change d • a.hom.app M
      (g s • (show (ModuleCat.ringExtendScalars.{u + 1, u + 1} g).obj _ from
        adj₂.unit.app _ (adj₁.unit.app M m))) =
    (d * g s) • (show (ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f)).obj M from
      adj₃.unit.app M m)
  rw [map_smul, h, mul_smul]

/-- The scalar comparisons commute with composite extensions, for lisse `F`.
Source: Stacks, Section 6.3, 03EL and 04FM
(blueprint: lem-pod-lisse-tensor-and-scalar-extension).
Proof: the module associativity comparison `ringExtensionComp` is adjoint uniqueness and
sends c tensor (b tensor a) to cb tensor a. Sheafify that comparison after the first
sheafification, obtaining the same sectionwise formula. Both composites in the stalk square
send this generator to the germ of cb tensor a; pure tensors generate. This is the
composite calculation of proof step 4. -/
theorem ring_scalar_extension_stalk_comp [Finite R] [Finite S]
    {T : Type (u + 1)} [Ring T] [Finite T] (f : R →+* S) (g : S →+* T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F) :
    (letI := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
    letI := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} g).isLeftAdjoint
    letI := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} (g.comp f)).isLeftAdjoint
    let J := Y.smallEtaleTopology
    let p := (pointSmallEtale y).ulift.{u + 1}
    let L₁ := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
    let L₂ := ModuleCat.ringExtendScalars.{u + 1, u + 1} g
    let L₃ := ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f)
    let F₁ := (Sheaf.ringExtendScalars.{u + 1, u + 1} J f).obj F
    let F₁₂ := (Sheaf.ringExtendScalars.{u + 1, u + 1} J g).obj F₁
    let F₃ := (Sheaf.ringExtendScalars.{u + 1, u + 1} J (g.comp f)).obj F
    let c₁ := (p.presheafFiberCompIso L₁).inv.app F.obj ≫
      (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)).inv.app (F.obj ⋙ L₁)
    let c₂ := (p.presheafFiberCompIso L₂).inv.app F₁.obj ≫
      (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} T)).inv.app (F₁.obj ⋙ L₂)
    let c₃ := (p.presheafFiberCompIso L₃).inv.app F.obj ≫
      (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} T)).inv.app (F.obj ⋙ L₃)
    let a := ModuleCat.ringExtensionComp.{u + 1, u + 1} f g
    ∃ b : F₁₂ ≅ F₃,
      (∀ (U : Y.Etale) (s : S) (d : T) (m : F.obj.obj (op U)),
        let j₁ := ((toSheafification J (ModuleCat.{u + 1} S)).app (F.obj ⋙ L₁)).app (op U)
        let j₂ := ((toSheafification J (ModuleCat.{u + 1} T)).app (F₁.obj ⋙ L₂)).app (op U)
        let j₃ := ((toSheafification J (ModuleCat.{u + 1} T)).app (F.obj ⋙ L₃)).app (op U)
        b.hom.hom.app (op U)
          (j₂ (ModuleCat.ringExtensionTmul.{u + 1, u + 1} g _ d
            (j₁ (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ s m)))) =
          j₃ (ModuleCat.ringExtensionTmul.{u + 1, u + 1} (g.comp f) _ (d * g s) m)) ∧
      L₂.map c₁ ≫ c₂ ≫ p.sheafFiber.map b.hom =
        a.hom.app (p.sheafFiber.obj F) ≫ c₃) := by
  have _ := hF
  have h := etale_stalk_scalar_iteration y f g
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f)
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} g)
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f))
    (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f)
    (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} g)
    (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} (g.comp f)) F
  dsimp only at h ⊢
  obtain ⟨b, hb, hc⟩ := h
  refine ⟨b, ?_, ?_⟩
  · intro U s d m
    have he := congrArg (fun k ↦ k
      (ModuleCat.ringExtensionTmul.{u + 1, u + 1} g _ d
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ s m))) (hb U)
    rw [scalarCompIso_eq] at he
    simp only [ModuleCat.comp_apply] at he
    erw [scalarMapTmul, scalarCompTmul] at he
    exact he
  · simpa only [scalarCompIso_eq] using! hc

end Scalars

end AlgebraicGeometry.Scheme
