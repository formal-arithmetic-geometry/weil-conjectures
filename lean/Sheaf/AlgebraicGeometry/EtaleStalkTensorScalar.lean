/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal

/-!
# Tensor products and scalar extension at geometric étale stalks

Source: Stacks Project, Tags 007K, 008B, 03EL and 04FM
(blueprint: lem-pod-etale-stalk-tensor-scalar).

Scalar extension is expressed by its universal property: a left adjoint to restriction
of scalars. Its adjunction unit sends `m` to `1 ⊗ m`; consequently `a • unit m`
is `a ⊗ m`. This formulation includes noncommutative coefficient rings.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
attribute [local instance] CategoryTheory.Sheaf.braidedCategory

section Tensor

variable {R : Type (u + 1)} [CommRing R]


/-- Source: Stacks 007K, 008B, 03EL, 04FM
(blueprint: lem-pod-etale-stalk-tensor-scalar), clause 1.
Step 1 uses `lem-weil-pbc-sheafification-geometric-stalk` to identify the tensor
presheaf stalk with the tensor sheaf stalk. Step 2 uses
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`: represent two germs on a common
refinement and tensor their sections; further refinements prove independence of choices.
The inverse sends a pure tensor section to the tensor of its germs, and the two composites
are identities on generators. Step 3 checks uniqueness on those generators. -/
theorem etale_stalk_tensor_unique
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
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

/-- Source: Stacks 008B and 03EL (blueprint: lem-pod-etale-stalk-tensor-scalar),
clause 1 naturality. Step 3: both composites send pure germs to the germ of the tensor
of their images; these generate the source. -/
theorem etale_stalk_tensor_natural
    {F F' G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    (let p := (pointSmallEtale y).ulift.{u + 1}
    let T := p.sheafFiber (A := ModuleCat.{u + 1} R)
    letI : T.Monoidal := inferInstanceAs
      ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).Monoidal
    (T.map f ⊗ₘ T.map g) ≫ Functor.LaxMonoidal.μ T F' G' =
      Functor.LaxMonoidal.μ T F G ≫ T.map (f ⊗ₘ g)) := by
  sorry

/-- Source: Stacks 008B and 03EL (blueprint: lem-pod-etale-stalk-tensor-scalar),
clause 1 coherence. Step 3 evaluates associativity, symmetry and the two unit diagrams
on pure germs and uses the corresponding module identities. The unit sheaf here is
`constantSheaf` applied to the module unit, by the sheaf monoidal structure. -/
theorem etale_stalk_tensor_coherence
    (F G H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (let p := (pointSmallEtale y).ulift.{u + 1}
    let T := p.sheafFiber (A := ModuleCat.{u + 1} R)
    letI : T.Monoidal := inferInstanceAs
      ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).Monoidal
    ((𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))) =
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
        (ModuleCat.of R R)) ∧
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

section Scalar

variable {R S : Type (u + 1)} [Ring R] [Ring S] (f : R →+* S)

/-- Source: Stacks 008B, change-of-rings construction
(blueprint: lem-pod-etale-stalk-tensor-scalar), clause 2's tensor object.
The balanced tensor `S ⊗[R] M`, with left action on its first factor, represents
`R`-linear maps from `M` to the restriction of an `S`-module. Thus tensoring defines
a left adjoint. This universal property, including the unit `m ↦ 1 ⊗ m`, specifies
scalar extension without imposing commutativity. -/
theorem etale_scalar_extension_exists :
    ∃ E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S,
      Nonempty (E ⊣ ModuleCat.restrictScalars f) := by
  sorry

/-- Source: Stacks 007K, 008B and 04FM
(blueprint: lem-pod-etale-stalk-tensor-scalar), clause 2.
Step 4 uses `lem-weil-pbc-sheafification-geometric-stalk` and
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`. The balanced maps on sections
to `S ⊗[R] F_y` induce the comparison inverse. A tensor of a germ is sent to the germ
of its tensor section; equality of representatives follows on a refinement. Both
composites are identities on pure tensors. Naturality and uniqueness follow by the
same calculation. The displayed equation is the pure-germ formula at `1 ⊗ s`;
`S`-linearity gives it at every `a ⊗ s`. -/
theorem etale_stalk_scalar_unique
    (E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
    (adj : E ⊣ ModuleCat.restrictScalars f) :
    (let p := (pointSmallEtale y).ulift.{u + 1}
    let J := Y.smallEtaleTopology
    let A := ModuleCat.{u + 1} R
    let B := ModuleCat.{u + 1} S
    let P := fun c : p.sheafFiber ⋙ E ⟶
        sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj E ⋙
          presheafToSheaf J B ⋙ p.sheafFiber ↦
      ∀ (F : Sheaf J A) (U : Y.Etale) (x : p.fiber.obj U),
        p.toPresheafFiber U x F.obj ≫ adj.unit.app (p.sheafFiber.obj F) ≫
          (ModuleCat.restrictScalars f).map (c.app F) =
        adj.unit.app (F.obj.obj (op U)) ≫
          (ModuleCat.restrictScalars f).map
            ((toSheafify J (F.obj ⋙ E)).app (op U) ≫
              p.toPresheafFiber U x ((presheafToSheaf J B).obj (F.obj ⋙ E)).obj)
    (∃! c, P c) ∧ ∀ c, P c → ∀ F : Sheaf J A, IsIso (c.app F)) := by
  sorry

/-- Source: Stacks 007K, 008B and 04FM
(blueprint: lem-pod-etale-stalk-tensor-scalar), clause 2, individual-map uniqueness.
Step 4: form balanced maps on sections and pass to the filtered neighborhood colimit
using `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`. A tensor of a germ maps
to the class of its tensor section, independently of the representative. The inverse
maps that section class to its tensor of germs. The composites fix generators.
`lem-weil-pbc-sheafification-geometric-stalk` then identifies the target with the
sheafified stalk. Uniqueness follows on generators, including every `a ⊗ s` by
left `S`-linearity. The two existing comparison isomorphisms define that same map. -/
theorem etale_stalk_scalar_component_unique
    (E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
    (adj : E ⊣ ModuleCat.restrictScalars f)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (letI := adj.isLeftAdjoint
    let p := (pointSmallEtale y).ulift.{u + 1}
    let J := Y.smallEtaleTopology
    let B := ModuleCat.{u + 1} S
    let Q := (presheafToSheaf J B).obj (F.obj ⋙ E)
    let c₀ := (p.presheafFiberCompIso E).inv.app F.obj ≫
      (p.presheafToSheafCompSheafFiberIso B).inv.app (F.obj ⋙ E)
    let P := fun c : E.obj (p.sheafFiber.obj F) ⟶ p.sheafFiber.obj Q ↦
      ∀ (U : Y.Etale) (x : p.fiber.obj U),
        p.toPresheafFiber U x F.obj ≫ adj.unit.app (p.sheafFiber.obj F) ≫
          (ModuleCat.restrictScalars f).map c =
        adj.unit.app (F.obj.obj (op U)) ≫
          (ModuleCat.restrictScalars f).map
            ((toSheafify J (F.obj ⋙ E)).app (op U) ≫
              p.toPresheafFiber U x Q.obj)
    (∃! c, P c) ∧ P c₀ ∧ IsIso c₀) := by
  sorry

end Scalar

/-- Source: Stacks, Modules on Sites, scalar-extension associativity (Section 6.3),
with Tags 008B and 04FM (blueprint: lem-pod-etale-stalk-tensor-scalar), clause 2,
successive extension. Step 5 evaluates the two composites on
`a'' ⊗ a' ⊗ s_y`. They give the germ of `a'' ⊗ a' ⊗ s`, so are equal on
all generators. The sheaf identification is induced by the same sectionwise
associativity map, followed by sheafification; the displayed section equation
specifies this identification. `a` is the canonical uniqueness-of-left-adjoints
identification, hence the module tensor associativity identification. -/
theorem etale_stalk_scalar_iteration {R S V : Type (u + 1)} [Ring R] [Ring S] [Ring V]
    (f : R →+* S) (g : S →+* V)
    (E₁₂ : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
    (E₂₃ : ModuleCat.{u + 1} S ⥤ ModuleCat.{u + 1} V)
    (E₁₃ : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} V)
    (adj₁₂ : E₁₂ ⊣ ModuleCat.restrictScalars f)
    (adj₂₃ : E₂₃ ⊣ ModuleCat.restrictScalars g)
    (adj₁₃ : E₁₃ ⊣ ModuleCat.restrictScalars (g.comp f))
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (letI := adj₁₂.isLeftAdjoint
    letI := adj₂₃.isLeftAdjoint
    letI := adj₁₃.isLeftAdjoint
    let J := Y.smallEtaleTopology
    let p := (pointSmallEtale y).ulift.{u + 1}
    let B := ModuleCat.{u + 1} S
    let D := ModuleCat.{u + 1} V
    let F₁₂ := (presheafToSheaf J B).obj (F.obj ⋙ E₁₂)
    let F₁₂₃ := (presheafToSheaf J D).obj (F₁₂.obj ⋙ E₂₃)
    let F₁₃ := (presheafToSheaf J D).obj (F.obj ⋙ E₁₃)
    let a := ((adj₁₂.comp adj₂₃).ofNatIsoRight
      (ModuleCat.restrictScalarsComp f g).symm).leftAdjointUniq adj₁₃
    let c₁₂ := (p.presheafFiberCompIso E₁₂).inv.app F.obj ≫
      (p.presheafToSheafCompSheafFiberIso B).inv.app (F.obj ⋙ E₁₂)
    let c₂₃ := (p.presheafFiberCompIso E₂₃).inv.app F₁₂.obj ≫
      (p.presheafToSheafCompSheafFiberIso D).inv.app (F₁₂.obj ⋙ E₂₃)
    let c₁₃ := (p.presheafFiberCompIso E₁₃).inv.app F.obj ≫
      (p.presheafToSheafCompSheafFiberIso D).inv.app (F.obj ⋙ E₁₃)
    ∃ b : F₁₂₃ ≅ F₁₃,
      (∀ U : Y.Etale,
        E₂₃.map ((toSheafify J (F.obj ⋙ E₁₂)).app (op U)) ≫
          (toSheafify J (F₁₂.obj ⋙ E₂₃)).app (op U) ≫ b.hom.hom.app (op U) =
        a.hom.app (F.obj.obj (op U)) ≫ (toSheafify J (F.obj ⋙ E₁₃)).app (op U)) ∧
      E₂₃.map c₁₂ ≫ c₂₃ ≫ p.sheafFiber.map b.hom =
        a.hom.app (p.sheafFiber.obj F) ≫ c₁₃) := by
  sorry

end AlgebraicGeometry.Scheme
