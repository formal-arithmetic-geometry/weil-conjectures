/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Topology.Sheaves.PUnit
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The fibre of a sheaf of modules: tensor products, inverses and rank one

Let `X` be a scheme and `x` a point of `X`. The fibre functor
`AlgebraicGeometry.Scheme.Modules.fiberFunctor X x` sends an `𝒪ₓ`-module `F` to the
`κ(x)`-vector space `F(x)`, obtained by pulling `F` back along `Spec κ(x) ⟶ X` and taking global
sections. We show that this functor is monoidal, so that `(F ⊗ G)(x)` is `F(x) ⊗_{κ(x)} G(x)`
and the fibre of the structure sheaf is `κ(x)`.

The pullback of `𝒪ₓ`-modules is monoidal, see
`WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal`, so the content is that the global
sections functor on `Spec κ(x)` is monoidal. This holds because `Spec κ(x)` has a single point:
on a scheme with at most one point every presheaf of modules is already a sheaf, the
sheafification is therefore an equivalence of categories, and the sections over `⊤` of a
presheaf tensor product are the tensor product of the sections.

As a consequence, if `L` is an invertible `𝒪ₓ`-module with tensor inverse `N`, then `L(x)` and
`N(x)` are inverse invertible `κ(x)`-modules — they pair to `κ(x)`, and `N(x)` is the dual of
`L(x)` — and `L(x)` is a one-dimensional `κ(x)`-vector space. All of this is compatible with
pullback, in particular with restriction to a scheme-theoretic fibre.

## Main declarations

- `AlgebraicGeometry.Scheme.Modules.fiberFunctorMonoidal`: the fibre functor is monoidal, with
  the isomorphisms `AlgebraicGeometry.Scheme.Modules.fiberTensorIso` for a tensor product and
  `AlgebraicGeometry.Scheme.Modules.fiberTensorUnitIso` for the structure sheaf.
- `AlgebraicGeometry.Scheme.Modules.fiberTensorIsoTensorUnit` and
  `AlgebraicGeometry.Scheme.Modules.fiberLinearEquivDual`: the fibres of an invertible sheaf and
  of its inverse pair to `κ(x)`, and the second is the dual of the first.
- `AlgebraicGeometry.Scheme.Modules.finrank_fiber_eq_one`: the fibre of an invertible sheaf of
  modules is a one-dimensional `κ(x)`-vector space.
- `AlgebraicGeometry.Scheme.Modules.pullbackTensorIsoTensorUnit` and
  `AlgebraicGeometry.Scheme.Modules.restrictToFiberTensorIsoTensorUnit`: pullback, and in
  particular restriction to a scheme-theoretic fibre, takes the inverse of an invertible sheaf
  to the inverse of its image.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

section Subsingleton

variable (P : _root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))

/-- On a scheme with at most one point, every presheaf of `𝒪ₓ`-modules is a sheaf: the only open
subsets are `⊥` and `⊤`, and the sections over `⊥` form the zero module. -/
theorem isSheaf_presheaf_of_subsingleton [Subsingleton X] :
    TopCat.Presheaf.IsSheaf (X := X) P.presheaf := by
  refine TopCat.Presheaf.isSheaf_of_isTerminal_of_indiscrete (IndiscreteTopology.eq_top _) _ ?_
  have h : Subsingleton (P.obj (op ⊥)) := Module.subsingleton Γ(X, ⊥) _
  exact (@AddCommGrpCat.isZero_of_subsingleton _ h).isTerminal

/-- On a scheme with at most one point, the unit of the sheafification adjunction for presheaves
of modules is an isomorphism. -/
theorem isIso_sheafificationAdjunction_unit_app [Subsingleton X] :
    IsIso ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P) := by
  have h₁ : IsIso (toSheafify (Opens.grothendieckTopology X) P.presheaf) :=
    isIso_toSheafify _ (isSheaf_presheaf_of_subsingleton P)
  have h₂ : IsIso ((_root_.PresheafOfModules.toPresheaf _).map
      ((_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P)) := by
    rw [_root_.PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact h₁
  exact isIso_of_reflects_iso _ (_root_.PresheafOfModules.toPresheaf _)

variable (X) in
/-- On a scheme with at most one point, the sheafification functor from presheaves of
`𝒪ₓ`-modules to `𝒪ₓ`-modules is an equivalence of categories: every presheaf of modules is
already a sheaf. -/
noncomputable def sheafificationEquivalence [Subsingleton X] :
    _root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}) ≌ X.Modules :=
  have := fun P ↦ isIso_sheafificationAdjunction_unit_app (X := X) P
  (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).toEquivalence

variable (X) in
/-- On a scheme with at most one point, the functor of sections over `⊤` from `𝒪ₓ`-modules to
`Γ(X, ⊤)`-modules is monoidal: it is the inverse of the sheafification, which is an equivalence,
followed by the evaluation of presheaves of modules over `⊤`. -/
noncomputable instance evaluationTopMonoidal [Subsingleton X] :
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).Monoidal :=
  letI : (sheafificationEquivalence X).functor.Monoidal :=
    inferInstanceAs (SheafOfModules.sheafification X.sheaf).Monoidal
  letI := (sheafificationEquivalence X).inverseMonoidal
  letI : ((sheafificationEquivalence X).inverse ⋙
      _root_.PresheafOfModules.evaluation
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}) (op ⊤)).Monoidal :=
    Functor.Monoidal.instComp (F := (sheafificationEquivalence X).inverse)
      (G := _root_.PresheafOfModules.evaluation _ (op ⊤))
  Functor.Monoidal.transport (F := (sheafificationEquivalence X).inverse ⋙
      _root_.PresheafOfModules.evaluation
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}) (op ⊤))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

section SpecMonoidal

variable (R : CommRingCat.{u}) [Subsingleton (Spec R)]

/-- On the spectrum of a ring with a unique prime ideal, for instance on the spectrum of a
field, the global sections functor `(Spec R).Modules ⥤ ModuleCat R` is monoidal: the global
sections of a tensor product are the tensor product of the global sections. -/
noncomputable instance moduleSpecΓFunctorMonoidal :
    @Functor.Monoidal (Spec R).Modules _ _ (ModuleCat R) _ _ (moduleSpecΓFunctor (R := R)) :=
  letI := ModuleCat.restrictScalarsMonoidal (Scheme.ΓSpecIso R).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)
  letI : (SheafOfModules.evaluation (Spec R).ringCatSheaf (op ⊤) ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).Monoidal :=
    Functor.Monoidal.instComp
      (F := SheafOfModules.evaluation (Spec R).ringCatSheaf (op ⊤))
      (G := ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom)
  Functor.Monoidal.transport
    (F := SheafOfModules.evaluation (Spec R).ringCatSheaf (op ⊤) ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

end SpecMonoidal

end Subsingleton

section Fiber

/-- **The fibre functor is monoidal.** It is the pullback along `Spec κ(x) ⟶ X`, which is
monoidal, followed by the global sections functor on `Spec κ(x)`, which is monoidal because
`Spec κ(x)` has a single point. -/
noncomputable instance fiberFunctorMonoidal (X : Scheme.{u}) (x : X) :
    (fiberFunctor X x).Monoidal :=
  Functor.Monoidal.instComp (F := Modules.pullback (X.fromSpecResidueField x))
    (G := moduleSpecΓFunctor (R := X.residueField x))

/-- **The fibre of a tensor product** of sheaves of `𝒪ₓ`-modules is the tensor product over
`κ(x)` of the fibres. -/
noncomputable def fiberTensorIso (F G : X.Modules) (x : X) :
    (F ⊗ G).fiber x ≅ F.fiber x ⊗ G.fiber x :=
  (Functor.Monoidal.μIso (fiberFunctor X x) F G).symm

/-- **The fibre of the tensor unit** is `κ(x)`. -/
noncomputable def fiberTensorUnitIso (X : Scheme.{u}) (x : X) :
    (𝟙_ X.Modules).fiber x ≅ 𝟙_ (ModuleCat (X.residueField x)) :=
  (Functor.Monoidal.εIso (fiberFunctor X x)).symm

/-- The fibre of the structure sheaf at `x` is the residue field `κ(x)`. -/
noncomputable def fiberUnitIso (X : Scheme.{u}) (x : X) :
    fiber (X := X) (SheafOfModules.unit X.ringCatSheaf) x ≅
      ModuleCat.of (X.residueField x) (X.residueField x) :=
  (fiberFunctor X x).mapIso (SheafOfModules.tensorUnitIso X.sheaf).symm ≪≫
    fiberTensorUnitIso X x

/-- **The pairing between the fibres of an invertible sheaf and of its inverse.** If `L ⊗ N` is
isomorphic to the structure sheaf, then `L(x) ⊗ N(x)` is isomorphic to `κ(x)`. -/
noncomputable def fiberTensorIsoTensorUnit {L N : X.Modules} (e : L ⊗ N ≅ 𝟙_ X.Modules) (x : X) :
    L.fiber x ⊗ N.fiber x ≅ 𝟙_ (ModuleCat (X.residueField x)) :=
  (fiberTensorIso L N x).symm ≪≫ (fiberFunctor X x).mapIso e ≪≫ fiberTensorUnitIso X x

/-- **The fibre of the inverse of an invertible sheaf is the dual of the fibre.** If `L ⊗ N` is
isomorphic to the structure sheaf, then `N(x)` is the `κ(x)`-linear dual of `L(x)`. -/
noncomputable def fiberLinearEquivDual {L N : X.Modules} (e : L ⊗ N ≅ 𝟙_ X.Modules) (x : X) :
    N.fiber x ≃ₗ[X.residueField x] Module.Dual (X.residueField x) (L.fiber x) :=
  Module.Invertible.linearEquivDual
    ((β_ (N.fiber x) (L.fiber x) ≪≫ fiberTensorIsoTensorUnit e x).toLinearEquiv)

/-- **The fibre of an invertible sheaf of modules is an invertible `κ(x)`-vector space.** -/
theorem module_invertible_fiber {L : X.Modules} (hL : L.Invertible) (x : X) :
    Module.Invertible (X.residueField x) (L.fiber x) := by
  obtain ⟨N, ⟨e⟩⟩ := (SheafOfModules.invertible_iff_exists (R := X.sheaf)).1 hL
  exact .left (fiberTensorIsoTensorUnit e x).toLinearEquiv

/-- **The fibre of an invertible sheaf of modules is a one-dimensional `κ(x)`-vector space.** -/
theorem finrank_fiber_eq_one {L : X.Modules} (hL : L.Invertible) (x : X) :
    Module.finrank (X.residueField x) (L.fiber x) = 1 :=
  have := module_invertible_fiber hL x
  Module.Invertible.finrank_eq_one _ _

/-- The fibre of an invertible sheaf of modules is a one-dimensional `κ(x)`-vector space. -/
theorem rank_fiber_eq_one {L : X.Modules} (hL : L.Invertible) (x : X) :
    Module.rank (X.residueField x) (L.fiber x) = 1 :=
  have := module_invertible_fiber hL x
  Module.Invertible.rank_eq_one _ _

/-- **Pullback preserves tensor inverses.** If `L ⊗ N` is isomorphic to the structure sheaf of
`Y`, then `f^* L ⊗ f^* N` is isomorphic to the structure sheaf of `X`. -/
noncomputable def pullbackTensorIsoTensorUnit (f : X ⟶ Y) {L N : Y.Modules}
    (e : L ⊗ N ≅ 𝟙_ Y.Modules) :
    (Modules.pullback f).obj L ⊗ (Modules.pullback f).obj N ≅ 𝟙_ X.Modules :=
  Functor.Monoidal.μIso (Modules.pullback f) L N ≪≫ (Modules.pullback f).mapIso e ≪≫
    (Functor.Monoidal.εIso (Modules.pullback f)).symm

/-- **Restriction to a scheme-theoretic fibre preserves tensor inverses.** If `L ⊗ N` is
isomorphic to the structure sheaf of `X`, then `L_y ⊗ N_y` is isomorphic to the structure sheaf
of the fibre of `f : X ⟶ Y` over `y`. -/
noncomputable def restrictToFiberTensorIsoTensorUnit (f : X ⟶ Y) (y : Y) {L N : X.Modules}
    (e : L ⊗ N ≅ 𝟙_ X.Modules) :
    (restrictToFiber f y).obj L ⊗ (restrictToFiber f y).obj N ≅ 𝟙_ (f.fiber y).Modules :=
  pullbackTensorIsoTensorUnit (f.fiberι y) e

/-- The fibre at a point `x` of the scheme-theoretic fibre of `f : X ⟶ Y` over `y` of the
restriction `L_y` of an invertible `𝒪ₓ`-module `L` is a one-dimensional vector space. -/
theorem finrank_fiber_restrictToFiber_eq_one (f : X ⟶ Y) (y : Y) {L : X.Modules}
    (hL : L.Invertible) (x : f.fiber y) :
    Module.finrank ((f.fiber y).residueField x) (((restrictToFiber f y).obj L).fiber x) = 1 :=
  finrank_fiber_eq_one (hL.pullback (f.fiberι y)) x

end Fiber

end AlgebraicGeometry.Scheme.Modules
