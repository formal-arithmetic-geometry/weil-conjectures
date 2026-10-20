/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NC
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Strict-perfect coefficient packages

Source: the Weil conjectures blueprint, proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).

## Main definitions

- `SheafOfModules.StrictPerfectCoefficientPackage`: the chosen degreewise splittings.
- `SheafOfModules.StrictPerfectCoefficientRepresentation`: a bounded localized model.
- `SheafOfModules.IsLocallyStrictPerfectComplex` and `SheafOfModules.IsPerfectOnRingedSite`:
  local perfectness of complexes and perfectness of derived objects.
- `ModuleCat.StrictPerfectCoefficientPackage`: the global ring-module version.
- `ModuleCat.StrictPerfectCoefficientPackage.constant`: its associated constant sheaf package.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- Chosen degreewise finite-free splittings, with no chain-map condition.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
structure StrictPerfectCoefficientPackage (R : Sheaf J RingCat.{u})
    (F : CochainComplex (SheafOfModules.{u} R) ℤ) where
  /-- Rank of the finite free term in each degree. -/
  N : ℤ → ℕ
  /-- Inclusion into a finite tuple sheaf. -/
  i (r : ℤ) : F.X r ⟶ ∏ᶜ fun _ : Fin (N r) => SheafOfModules.unit R
  /-- Retraction from the same finite tuple sheaf. -/
  p (r : ℤ) : (∏ᶜ fun _ : Fin (N r) => SheafOfModules.unit R) ⟶ F.X r
  /-- Splitting relation, in diagrammatic composition order. -/
  splitting (r : ℤ) : i r ≫ p r = 𝟙 (F.X r)

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- The degreewise idempotent associated to the chosen splitting.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def StrictPerfectCoefficientPackage.e {R : Sheaf J RingCat.{u}}
    {F : CochainComplex (SheafOfModules.{u} R) ℤ}
    (P : StrictPerfectCoefficientPackage R F) (r : ℤ) := P.p r ≫ P.i r

attribute [instance] CategoryTheory.module_overFunctor_preservesZero

/-- Local perfectness: covering sieves admit bounded, finite-free retract models mapping
quasi-isomorphically to the restricted complex. Bounds and ranks vary with the cover member.
Source: Stacks, Tag 08G5, and proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def IsLocallyStrictPerfectComplex (R : Sheaf J CommRingCat.{u})
    (K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
    ∀ (U : C) (f : U ⟶ V), S f →
      ∃ F : CochainComplex (SheafOfModules.{u}
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ℤ,
        (∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) ∧
        Nonempty (StrictPerfectCoefficientPackage _ F) ∧
        ∃ α : F ⟶ ((SheafOfModules.overFunctor _ U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K, QuasiIso α

/-- Perfect objects are exactly the objects represented by locally perfect complexes.
Source: Stacks, Tag 08G5, and proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def IsPerfectOnRingedSite (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (E : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) : Prop :=
  ∃ K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ,
    IsLocallyStrictPerfectComplex R K ∧ Nonempty (E ≅ DerivedCategory.Q.obj K)

/-- A bounded representative of a localized derived object, with its chosen package.
The coefficient sheaf is the restriction of a commutative ring sheaf to `C/U`.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
structure StrictPerfectCoefficientRepresentation (R : Sheaf J CommRingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (Q : DerivedCategory (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))) where
  /-- The representative complex. -/
  F : CochainComplex (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ℤ
  /-- Terms vanish outside a finite interval. -/
  bounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)
  /-- The representation of the derived object. -/
  represents : Q ≅ DerivedCategory.Q.obj F
  /-- Chosen degreewise splittings. -/
  package : StrictPerfectCoefficientPackage _ F

end SheafOfModules

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ]

/-- A global coefficient package for a fixed representative. The standard finite free
module is the module of finite tuples, with its standard basis.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
structure StrictPerfectCoefficientPackage (F : CochainComplex (ModuleCat.{u} Λ) ℤ) where
  /-- Finite ranks, allowed to be zero. -/
  N : ℤ → ℕ
  /-- Degreewise inclusions. -/
  i (r : ℤ) : F.X r ⟶ ModuleCat.of Λ (Fin (N r) → Λ)
  /-- Degreewise projections. -/
  p (r : ℤ) : ModuleCat.of Λ (Fin (N r) → Λ) ⟶ F.X r
  /-- The projections split the inclusions. -/
  splitting (r : ℤ) : i r ≫ p r = 𝟙 (F.X r)

/-- A bounded finite-projective representative of a perfect ring complex, with a global package.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
structure StrictPerfectCoefficientRepresentation
    [HasDerivedCategory.{u} (ModuleCat.{u} Λ)]
    (Q : DerivedCategory (ModuleCat.{u} Λ)) (hQ : DerivedCategory.IsPerfect Q) where
  /-- The chosen representative. -/
  F : CochainComplex (ModuleCat.{u} Λ) ℤ
  /-- Strict boundedness of the representative. -/
  bounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)
  /-- Every term is finitely generated and projective. -/
  finite_projective : ∀ r : ℤ, Module.Finite Λ (F.X r) ∧ Module.Projective Λ (F.X r)
  /-- The isomorphism to the represented object. -/
  represents : Q ≅ DerivedCategory.Q.obj F
  /-- The global package. -/
  package : StrictPerfectCoefficientPackage F

end ModuleCat

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

/-- Constant presheaves of modules, with identity restriction maps.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def strictPerfectConstantPresheaf :
    ModuleCat.{u} Λ ⥤ PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj M := { obj := fun _ => M, map := fun _ => ModuleCat.ofHom (LinearMap.id) }
  map f := { app := fun _ => f }

/-- Constant presheaves preserve addition componentwise.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: evaluate the two maps at any object; both are the original sum of linear maps. -/
theorem strictPerfectConstantPresheaf_additive :
    (strictPerfectConstantPresheaf (C := C) Λ).Additive := sorry

attribute [instance] strictPerfectConstantPresheaf_additive

/-- The associated constant sheaf of modules over the constant ring sheaf. This applies
module sheafification to the constant presheaf, using the ring-sheafification unit.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def strictPerfectConstantSheaf :
    ModuleCat.{u} Λ ⥤ SheafOfModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) :=
  strictPerfectConstantPresheaf (C := C) Λ ⋙
    PresheafOfModules.sheafification
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))

/-- The constant module sheaf functor is additive.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: the constant presheaf functor is additive componentwise. Module sheafification
preserves finite products and the zero object, so it is additive; compose these functors. -/
theorem strictPerfectConstantSheaf_additive : (strictPerfectConstantSheaf J Λ).Additive := sorry

attribute [instance] strictPerfectConstantSheaf_additive

/-- Termwise sheafification, including the differential.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def strictPerfectConstantComplex (F : CochainComplex (ModuleCat.{u} Λ) ℤ) :=
  ((strictPerfectConstantSheaf J Λ).mapHomologicalComplex (ComplexShape.up ℤ)).obj F

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

/-- Coordinate evaluation followed by the coefficient-ring sheafification unit is additive.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: addition of tuples is pointwise, so evaluation at `k` sends the sum to
`v k + w k`. Apply preservation of addition by the ring sheafification unit at `X`. -/
theorem strictPerfectConstantCoordinateComponent_map_add (n : ℕ) (k : Fin n)
    (X : Cᵒᵖ) (v w : Fin n → Λ) :
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X ((v + w) k) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X (v k) +
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X (w k) := sorry

/-- Coordinate evaluation followed by the coefficient-ring unit respects scalar multiplication.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: scalar multiplication of tuples is pointwise multiplication by `r`.
The unit preserves multiplication, and restriction of scalars makes the target action
multiplication by the image of `r` under that same unit. -/
theorem strictPerfectConstantCoordinateComponent_map_smul (n : ℕ) (k : Fin n)
    (X : Cᵒᵖ) (r : Λ) (v : Fin n → Λ) :
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X ((r • v) k) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X r *
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X (v k) := sorry

/-- A coordinate component, linear for the sheafification unit on coefficient rings.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def strictPerfectConstantCoordinateComponent (n : ℕ) (k : Fin n) (X : Cᵒᵖ) :
    ModuleCat.of Λ (Fin n → Λ) ⟶
      ((PresheafOfModules.restrictScalars
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj
          (SheafOfModules.unit ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))).val).obj X :=
  ModuleCat.ofHom
    (Y := ((PresheafOfModules.restrictScalars
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj
        (SheafOfModules.unit ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))).val).obj X)
    { toFun := fun v => (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X (v k)
      map_add' := strictPerfectConstantCoordinateComponent_map_add J Λ n k X
      map_smul' := strictPerfectConstantCoordinateComponent_map_smul J Λ n k X }

/-- The coordinate components are natural.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: evaluate at a tuple `v`. The left side is the image of `v k` under the ring
sheafification unit at `Y`; the right side is its image at `X` followed by restriction.
These agree by naturality of the ring sheafification unit. -/
theorem strictPerfectConstantCoordinate_naturality (n : ℕ) (k : Fin n)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((strictPerfectConstantPresheaf (C := C) Λ).obj
        (ModuleCat.of Λ (Fin n → Λ))).map f ≫
      (ModuleCat.restrictScalars
        (((Functor.const Cᵒᵖ).obj (RingCat.of Λ)).map f).hom).map
          (strictPerfectConstantCoordinateComponent J Λ n k Y) =
    strictPerfectConstantCoordinateComponent J Λ n k X ≫
      ((PresheafOfModules.restrictScalars
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj
          (SheafOfModules.unit ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))).val).map f :=
  sorry

/-- A coordinate map, obtained from the constant presheaf coordinate by module sheafification.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def strictPerfectConstantCoordinate (n : ℕ) (k : Fin n) :
    (strictPerfectConstantSheaf J Λ).obj (ModuleCat.of Λ (Fin n → Λ)) ⟶
      SheafOfModules.unit ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) :=
  (PresheafOfModules.sheafificationHomEquiv
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).symm
    { app := strictPerfectConstantCoordinateComponent J Λ n k
      naturality := strictPerfectConstantCoordinate_naturality J Λ n k }

/-- The canonical finite-product comparison, with coordinates the sheafified projections.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def strictPerfectConstantFiniteFreeComparison (n : ℕ) :
    (strictPerfectConstantSheaf J Λ).obj (ModuleCat.of Λ (Fin n → Λ)) ⟶
      ∏ᶜ fun _ : Fin n =>
        SheafOfModules.unit ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) :=
  Pi.lift (strictPerfectConstantCoordinate J Λ n)

/-- The canonical finite-product comparison is invertible, also in rank zero.
Source: finite-product preservation of sheafification and proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: before sheafification the finite tuple module is the product of `n` copies of the
coefficient ring. Sheafification preserves finite products (including the empty product),
and sheafifying the coefficient ring gives the constant ring sheaf. The displayed map is
precisely the comparison induced by these projections. Thus it is an isomorphism. -/
theorem strictPerfectConstantFiniteFreeComparison_isIso (n : ℕ) :
    IsIso (strictPerfectConstantFiniteFreeComparison J Λ n) := sorry

attribute [instance] strictPerfectConstantFiniteFreeComparison_isIso

/-- Transport of a degreewise splitting through sheafification and the finite-free comparison.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: cancel the adjacent comparison and its inverse. The remaining composite is the
image of `i_r ≫ p_r`; use the original splitting and preservation of identity maps. -/
theorem strictPerfectConstant_splitting {F : CochainComplex (ModuleCat.{u} Λ) ℤ}
    (P : ModuleCat.StrictPerfectCoefficientPackage F) (r : ℤ) :
    ((strictPerfectConstantSheaf J Λ).map (P.i r) ≫
      strictPerfectConstantFiniteFreeComparison J Λ (P.N r)) ≫
      (inv (strictPerfectConstantFiniteFreeComparison J Λ (P.N r)) ≫
        (strictPerfectConstantSheaf J Λ).map (P.p r)) =
      𝟙 ((strictPerfectConstantComplex J Λ F).X r) := sorry

/-- The associated constant package: sheafify the complex and both splitting maps termwise,
then identify the constant finite tuples with finite tuples of the constant ring sheaf.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def _root_.ModuleCat.StrictPerfectCoefficientPackage.constant
    {F : CochainComplex (ModuleCat.{u} Λ) ℤ} (P : ModuleCat.StrictPerfectCoefficientPackage F) :
    SheafOfModules.StrictPerfectCoefficientPackage _ (strictPerfectConstantComplex J Λ F) where
  N := P.N
  i r := (strictPerfectConstantSheaf J Λ).map (P.i r) ≫
    strictPerfectConstantFiniteFreeComparison J Λ (P.N r)
  p r := inv (strictPerfectConstantFiniteFreeComparison J Λ (P.N r)) ≫
    (strictPerfectConstantSheaf J Λ).map (P.p r)
  splitting := strictPerfectConstant_splitting J Λ P

/-- The idempotent identities of a sheaf coefficient package.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: reassociate each composite and substitute `i_r ≫ p_r = 1`. The three results
are respectively `p_r ≫ i_r`, `p_r` and `i_r`. -/
theorem StrictPerfectCoefficientPackage.identities {R : Sheaf J RingCat.{u}}
    {F : CochainComplex (SheafOfModules.{u} R) ℤ}
    (P : StrictPerfectCoefficientPackage R F) (r : ℤ) :
    P.e r ≫ P.e r = P.e r ∧ P.e r ≫ P.p r = P.p r ∧ P.i r ≫ P.e r = P.i r := sorry

end SheafOfModules

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ]

/-- The degreewise idempotent of a global coefficient package.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def StrictPerfectCoefficientPackage.e {F : CochainComplex (ModuleCat.{u} Λ) ℤ}
    (P : StrictPerfectCoefficientPackage F) (r : ℤ) := P.p r ≫ P.i r

/-- The idempotent identities of a global coefficient package.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: reassociate each composite, replace the middle `i_r ≫ p_r` by the identity,
and remove the identity. -/
theorem StrictPerfectCoefficientPackage.identities {F : CochainComplex (ModuleCat.{u} Λ) ℤ}
    (P : StrictPerfectCoefficientPackage F) (r : ℤ) :
    P.e r ≫ P.e r = P.e r ∧ P.e r ≫ P.p r = P.p r ∧ P.i r ≫ P.e r = P.i r := sorry

end ModuleCat
