/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.Monoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Mathlib.Topology.Sheaves.PUnit

/-!
# Sections of sheaves of modules on a space with at most one point are monoidal

The tensor product of two sheaves of modules is the *sheafification* of the sectionwise tensor
product, so the functor of sections over an open subset is in general only lax monoidal. It is
monoidal as soon as the sheafification of presheaves of modules is an equivalence of categories,
which happens over a topological space with at most one point: there every presheaf of modules
is already a sheaf.

The case of interest is the spectrum of a ring with at most one prime ideal, for instance the
spectrum of a field, or of the residue field of a point of a scheme: the global sections functor
`Γ : (Spec R).Modules ⥤ ModuleCat R` is then monoidal. This is what makes the fibre functor of
`WeilConjectures.AlgebraicGeometry.Modules.Fiber` monoidal.

## Main declarations

- `SheafOfModules.evaluationMonoidalOfIsSheaf`: if every presheaf of `R`-modules is a sheaf,
  evaluation of sheaves of `R`-modules at an object is monoidal.
- `AlgebraicGeometry.Scheme.Modules.evaluationMonoidal`: on a scheme with at most one point,
  the sections of `𝒪ₓ`-modules over an open subset are monoidal.
- `AlgebraicGeometry.moduleSpecΓFunctorMonoidal`: on the spectrum of a ring with at most one
  prime ideal, the global sections functor `(Spec R).Modules ⥤ ModuleCat R` is monoidal.

-/

@[expose] public section

universe v₁ u₁ u

open CategoryTheory Opposite TopologicalSpace

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})
  (h : ∀ P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u}),
    Presheaf.IsSheaf J P.presheaf)

/-- The sheafification equivalence between presheaves of `R`-modules and sheaves of `R`-modules
over a site on which every presheaf of modules is a sheaf. This is
`PresheafOfModules.sheafificationEquivalenceOfIsSheaf` spelled so that the monoidal structures
of `SheafOfModules.sheafification` are found by instance resolution. -/
noncomputable abbrev sheafificationEquivalence :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u}) ≌
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) :=
  PresheafOfModules.sheafificationEquivalenceOfIsSheaf (𝟙 _) h

/-- **If every presheaf of `R`-modules is a sheaf, evaluation at an object `X` is monoidal**: it
is the inverse of the sheafification, which is then a monoidal equivalence, followed by the
evaluation of presheaves of modules at `X`, whose tensor product is computed sectionwise.

```
  PresheafOfModules R ── sheafification ──≌──> SheafOfModules R
           │                                          │
   PresheafOfModules.evaluation X       SheafOfModules.evaluation X
           ↓                                          ↓
      ModuleCat R(X) ═════════════════════════ ModuleCat R(X)
```
-/
@[instance_reducible]
noncomputable def evaluationMonoidalOfIsSheaf (X : Cᵒᵖ) :
    (evaluation ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) X).Monoidal :=
  letI : (sheafificationEquivalence R h).functor.Monoidal :=
    inferInstanceAs (SheafOfModules.sheafification R).Monoidal
  letI : (sheafificationEquivalence R h).inverse.Monoidal :=
    (sheafificationEquivalence R h).inverseMonoidal
  inferInstanceAs ((sheafificationEquivalence R h).inverse ⋙ PresheafOfModules.evaluation
    (R.obj ⋙ forget₂ CommRingCat RingCat.{u}) X).Monoidal

end SheafOfModules

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [Subsingleton X]

/-- **On a scheme with at most one point, the sections of `𝒪ₓ`-modules over an open subset are
monoidal**: every presheaf of `𝒪ₓ`-modules is already a sheaf, so the tensor product of sheaves
of modules is computed sectionwise. -/
noncomputable instance Scheme.Modules.evaluationMonoidal (U : (Opens X)ᵒᵖ) :
    (SheafOfModules.evaluation X.ringCatSheaf U).Monoidal :=
  SheafOfModules.evaluationMonoidalOfIsSheaf X.sheaf
    (PresheafOfModules.isSheaf_of_subsingleton X.sheaf) U

variable (R : CommRingCat.{u}) [Subsingleton (Spec R)]

/-- **On the spectrum of a ring with at most one prime ideal**, for instance on the spectrum of a
field, **the global sections functor `(Spec R).Modules ⥤ ModuleCat R` is monoidal**: the global
sections of a tensor product are the tensor product of the global sections.

```
  (Spec R).Modules ── evaluation (op ⊤) ──> ModuleCat Γ(Spec R, ⊤)
           │                                          │
  moduleSpecΓFunctor              restrictScalars (ΓSpecIso R).inv
           ↓                                          ↓
     ModuleCat R ═════════════════════════════ ModuleCat R
```

The source category is given explicitly: `moduleSpecΓFunctor (R := R)` has source spelled
`(Spec (CommRingCat.of ↑R)).Modules`, whereas at the use sites it is composed with a functor
landing in `(Spec R).Modules`. The two monoidal structures are definitionally equal but not
syntactically so, and instance resolution needs the second spelling. -/
@[instance_reducible]
noncomputable instance moduleSpecΓFunctorMonoidal :
    Functor.Monoidal (C := (Spec R).Modules) (moduleSpecΓFunctor (R := R)) :=
  letI := ModuleCat.restrictScalarsMonoidalOfBijective (Scheme.ΓSpecIso R).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)
  inferInstanceAs (SheafOfModules.evaluation (Spec R).ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).Monoidal

end AlgebraicGeometry
