/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Sites.Point.Monoidal
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Sheaf.Algebra.Category.ModuleCat.RingScalarExtension

/-! # Tensor products, scalar extension and stalks of lisse sheaves

Source: Stacks Project, sites-modules, 093V, 03EL; etale-cohomology, 095D, 04FM,
03PN (blueprint: lem-pod-lisse-tensor-and-scalar-extension).

Lisse sheaves of `Λ`-modules are the sheaves satisfying the source predicate
`Scheme.IsFiniteLocallyConstantSheaf` at `A = ModuleCat Λ`. Geometric points have
algebraically closed fields. Stalks are the fibres of the lifted point
`(pointSmallEtale y).ulift`, as in lem-pod-etale-stalk-tensor-scalar.
-/

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
  sorry

section Tensor

variable {R : Type (u + 1)} [CommRing R]

attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
attribute [local instance] CategoryTheory.Sheaf.braidedCategory

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Tensor

section Scalars

variable {R S : Type (u + 1)} [Ring R] [Ring S]

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Scalars

end AlgebraicGeometry.Scheme
