/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Sheaf.Paper.RingedTopoiTensorSections
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Compatible central scalars and derived ringed-topos pullback

Source: Stacks Project, Cohomology on Sites, Tag 06YY (lemma-derived-base-change),
Modules on Sites, Tag 03D6 (definition-pushforward), and Conventions, section-algebra.
The compatible-central-scalar refinement is the agent-supplied prerequisite implicit
in the K-flat computation (blueprint: lem-pur-ringed-derived-pullback-linear).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Restrict the existing global-section action on module-sheaf Hom groups along `s`.
On a morphism `f`, its value at `U,x` is `(s r).val U • f.val.app U x`.
This is the actual sectionwise action, with Mathlib's existing preadditive structure.

Source: Stacks Project, Modules on Sites, Tag 03D6; Conventions, section-algebra
(blueprint: lem-pur-ringed-derived-pullback-linear). -/
@[instance_reducible]
noncomputable def scalarSectionLinear
    (R : Type v) [CommRing R] {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J CommRingCat.{u})
    (s : R →+* RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    Linear R (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A)) := by
  letI : Linear (RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf A)) :=
    homLinear A.obj (RingedTensor.ringSheaf A).property
  exact
    { homModule := fun M N ↦ Module.compHom (M ⟶ N) s
      smul_comp := fun M N P r f g ↦ Linear.smul_comp M N P (s r) f g
      comp_smul := fun M N P f r g ↦ Linear.comp_smul M N P f (s r) g }

/-- Canonical K-flat derived pullback is linear over compatible actual scalar sections.
The two module-category structures are the explicitly constructed sectionwise actions;
the derived structures are Mathlib's induced localization structures. The universal
property on `LF,epsilon` specifies the left derived functor, not an arbitrary functor
with objectwise comparison isomorphisms. It includes the canonical K-flat construction
of `ringedTopoiDerivedPullback` and every realization canonically isomorphic to it.
The generalized-element form of `hs` says exactly that the structural map sends the
inverse image of each global scalar section to the specified target scalar section.

Source: Stacks Project, Cohomology on Sites, Tag 06YY (lemma-derived-base-change),
Modules on Sites, Tag 03D6, and Conventions, section-algebra. The scalar refinement
is agent supplied (blueprint: lem-pur-ringed-derived-pullback-linear).

Proof:
1. Global scalar sections act on module-sheaf morphisms sectionwise, and commutativity
makes these maps module-linear. Ring-homomorphism laws and bilinearity of composition
are the existing Hom-module construction (def-weil-linear-category).
2. Algebraic inverse image transports scalar multiplication by `sA r` to multiplication
by its inverse image (def-weil-pbc-algebraic-inverse-image). Tensor balancing and `hs`
give `b tensor (sA r * x) = (sB r * b) tensor x`. Finite sums and sheafification give
ordinary pullback preservation of scalar identity maps (def-pur-sheaf-tensor-product).
3. The natural K-flat comparison of lem-weil-pbc-ringed-topoi-derived-pullback is
invertible on flat-term K-flat complexes. Naturality at the degreewise scalar chain
map, and linearity of localization (lem-weil-linear-abelian-derived-category), imply
preservation of scalar identities on these complexes by cancellation.
4. Resolve every complex by a flat-term K-flat complex (lem-pc-kflat-resolution).
Conjugation by the localized resolution isomorphism extends step 3 to every object.
For the supplied realization `LF`, first use uniqueness of the left derived functor
to transport the canonical comparison and exactness along its natural isomorphism.
5. For every morphism f, write r*f as f followed by the scalar identity. Functoriality
and step 4 imply scalar preservation. Exactness implies additivity
(def-weil-triangulated-category), giving def-weil-linear-functor and the displayed
scalar-identity clause. Tensor balancing required no flatness of the structural map. -/
theorem ringedDerivedPullback_linear
    (R : Type v) [CommRing R]
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (A : Sheaf JC CommRingCat.{u}) (B : Sheaf JD CommRingCat.{u})
    (u : RingedToposMorphism
      (RingedTensor.ringSheaf B)
      (RingedTensor.ringSheaf A))
    (AI : Sheaf JD CommRingCat.{u}) (I : AlgebraicInverseImage u.inverse A AI)
    (c : AI ⟶ B)
    (hstruct : I.ringUnderlying.hom ≫
      (sheafCompose JD (CategoryTheory.forget CommRingCat)).map c = u.ringMap)
    (sA : R →+* RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat RingCat))
    (sB : R →+* RingCat.sectionsSubring (B.obj ⋙ forget₂ CommRingCat RingCat))
    (hs : ∀ (r : R) (T : Sheaf JC (Type u))
      (a : T ⟶ (sheafCompose JC (CategoryTheory.forget CommRingCat)).obj A),
      (∀ (U : Cᵒᵖ) (x : T.obj.obj U), a.hom.app U x = (sA r).val U) →
      ∀ (V : Dᵒᵖ) (x : (u.inverse.obj T).obj.obj V),
        ((u.inverse.map a) ≫ u.ringMap).hom.app V x = (sB r).val V)
    (uStar : ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A) ⥤
      ringedSiteModules.{u, u, u, u} (RingedTensor.ringSheaf B))
    (hobj : ∀ M : ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A)} (f : M ⟶ N),
      uStar.map f = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf B))]
    (LF : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf B)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf A)) (ComplexShape.up ℤ))] :
    (fun [_lA : Linear R (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf A))]
      [_lB : Linear R (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf B))] ↦
      LF.Additive ∧ Functor.Linear R LF ∧
        ∀ (X : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
          (RingedTensor.ringSheaf A))) (r : R),
          LF.map (r • (𝟙 X : X ⟶ X)) =
            r • (𝟙 (LF.obj X) : LF.obj X ⟶ LF.obj X))
      (_lA := scalarSectionLinear R A sA) (_lB := scalarSectionLinear R B sB) := by
  sorry

end SheafOfModules
