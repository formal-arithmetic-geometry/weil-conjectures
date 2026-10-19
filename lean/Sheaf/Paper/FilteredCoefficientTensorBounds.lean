/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.ProEtaleConstructibleSheaf
import Sheaf.Paper.SfCommonStageWeilCohomology

/-!
# Finite coefficient filtrations preserve constructibility and cohomological bounds

Source: Stacks Project, proetale.tex, Tag 09B5, lemma-constructible-serre;
agent-written finite-filtration application
(blueprint: lem-sf-filtered-coefficient-tensor-bounds).

The coefficient tensor is constructed as `(B_Y ⊗_R P) ⊗_{B_Y} U_Y`.
The canonical balanced identification sends `(b ⊗ p) ⊗ v` to `p ⊗ bv`;
its inverse sends `p ⊗ v` to `(1 ⊗ p) ⊗ v`. Thus this is precisely
`P ⊗_R U_Y`, with its B_Y-action, including its differential.

## Main declarations

* `filteredCoefficientTensorFunctor` and `filteredCoefficientTensorDifferential`:
  the termwise tensor functor and its actual differential.
* `filteredCoefficientTensorComplex_laws`: the shape and square-zero proof obligations.
* `filteredCoefficientTensorComplex`: the resulting cochain complex.
* `filteredCoefficientTensor_constructible_bounds`: finite coefficient devissage.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (ρ : R ⟶ adicLisseConstantRing Y B)
  (P : CochainComplex (pbcModules Y R) ℤ)

/-- Tensoring constant B-modules on the pro-etale site.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-sf-filtered-coefficient-tensor-bounds). -/
noncomputable def filteredCoefficientTensorFunctor (U : ModuleCat.{u + 1} B) :
    pbcModules Y (adicLisseConstantRing Y B) ⥤ pbcModules Y (adicLisseConstantRing Y B) :=
  SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
    (C := Y.ProEt) (J := ProEt.topology Y)
    (A := adicLisseConstantRing Y B) ((adicLisseConstantModules Y B).obj U)

/-- Differential obtained by extending scalars and tensoring with the constant module.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-sf-filtered-coefficient-tensor-bounds). -/
noncomputable def filteredCoefficientTensorDifferential
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (ρ : R ⟶ adicLisseConstantRing Y B) (P : CochainComplex (pbcModules Y R) ℤ)
    (U : ModuleCat.{u + 1} B) (i j : ℤ) :
    (filteredCoefficientTensorFunctor Y B U).obj
        (SheafOfModules.changeOfRings.{u, u + 1, u + 1} ρ (P.X i)) ⟶
      (filteredCoefficientTensorFunctor Y B U).obj
        (SheafOfModules.changeOfRings.{u, u + 1, u + 1} ρ (P.X j)) :=
  (filteredCoefficientTensorFunctor Y B U).map
    (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} ρ (P.X i) (P.d i j))

/-- Well-definedness of the termwise coefficient tensor differential.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-sf-filtered-coefficient-tensor-bounds).
Proof: sectionwise change of rings sends d to 1 tensor d, preserves composition
and zero, and sheafification is additive. Tensoring with U_Y again preserves
composition and zero, as can be checked on pure tensors before sheafification.
Consequently the shape and square-zero equations follow from those of P.
These are only the proof fields needed by the displayed tensor construction. -/
theorem filteredCoefficientTensorComplex_laws (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (ρ : R ⟶ adicLisseConstantRing Y B) (P : CochainComplex (pbcModules Y R) ℤ)
    (U : ModuleCat.{u + 1} B) :
    (∀ (i j : ℤ), ¬ (ComplexShape.up ℤ).Rel i j →
      filteredCoefficientTensorDifferential Y B R ρ P U i j = 0) ∧
    (∀ i j k : ℤ,
      filteredCoefficientTensorDifferential Y B R ρ P U i j ≫
        filteredCoefficientTensorDifferential Y B R ρ P U j k = 0) := by
  constructor
  · intro i j hij
    unfold filteredCoefficientTensorDifferential
    rw [SheafOfModules.changeOfRingsComplex_shape ρ P i j hij]
    exact
      (SheafOfModules.siteSheafTensorRight_preservesZeroMorphisms
        ((adicLisseConstantModules Y B).obj U)).map_zero _ _
  · intro i j k
    unfold filteredCoefficientTensorDifferential
    rw [← Functor.map_comp]
    rw [SheafOfModules.changeOfRingsComplex_comp ρ P i j k]
    exact
      (SheafOfModules.siteSheafTensorRight_preservesZeroMorphisms
        ((adicLisseConstantModules Y B).obj U)).map_zero _ _

/-- The actual B_Y-complex P tensor_R U_Y, formed by ordinary sheaf tensors.
Its associative presentation first extends P to B_Y and then tensors with U_Y.
The balanced mutually inverse formulas in the module documentation identify
this with the direct R-tensor, and commute with d_P tensor 1.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-sf-filtered-coefficient-tensor-bounds). -/
def filteredCoefficientTensorComplex (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (ρ : R ⟶ adicLisseConstantRing Y B) (P : CochainComplex (pbcModules Y R) ℤ)
    (U : ModuleCat.{u + 1} B) :
    CochainComplex (pbcModules Y (adicLisseConstantRing Y B)) ℤ where
  X i := (filteredCoefficientTensorFunctor Y B U).obj
    (SheafOfModules.changeOfRings.{u, u + 1, u + 1} ρ (P.X i))
  d i j := filteredCoefficientTensorDifferential Y B R ρ P U i j
  shape := (filteredCoefficientTensorComplex_laws Y B R ρ P U).1
  d_comp_d' i j k _ _ := by
    exact (filteredCoefficientTensorComplex_laws Y B R ρ P U).2 i j k

/-- Finite coefficient devissage keeps exactly the common cohomological interval.
Source: Stacks Project, proetale.tex, Tag 09B5; finite-filtration application
(blueprint: lem-sf-filtered-coefficient-tensor-bounds).

Proof:
1. For j<t, take the quotient sequence 0→V_(j+1)→V_j→W_j→0.
Constant presheaves are sectionwise exact; exact module sheafification
(lem-weil-pbc-site-r-module-presheaf-sheafification-exact) gives the constant
B_Y-module sequence. Restriction through rho retains its underlying additive
sheaves and exactness (def-pc-sheaf-restrict-scalars).
2. Flatness of each P^q gives a short exact sequence after tensoring with P^q
(def-pc-flat-sheaf-modules). The maps commute with d_P tensor 1 and are B_Y-linear,
as verified on pure tensors (def-pur-sheaf-tensor-product). Thus the sequence
of coefficient complexes is degreewise short exact in Mod(B_Y).
3. Descend from j=t. The zero coefficient gives the zero complex and zero
cohomology, constructible using a single stratum, even for the empty scheme.
This also handles t=0. At each step use the assertion for V_(j+1) and the
assumed assertion for W_j.
4. The long exact cohomology sequence
(lem-weil-pbc-complex-ses-homology-long-exact) gives exactness of the same-degree
segment. Outside [r,s] both outer cohomology sheaves vanish, hence the middle
one vanishes. Neither endpoint moves.
5. The short exact complex sequence gives a distinguished triangle
(lem-weil-pbc-complex-ses-triangle). Derived cohomology agrees with cohomology
of these representatives (def-weil-derived-cohomology-sheaves and
 def-weil-abstract-derived-category). The middle-vertex clause of
lem-weil-proetale-dbc-triangulated preserves constructibility and boundedness
for the finite ring B on arbitrary Y. Descending induction proves every V_j;
V_0=V proves the final assertion. The interval is independent of t. -/
theorem filteredCoefficientTensor_constructible_bounds [Finite B]
    (hP : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (C := Y.ProEt)
      (J := ProEt.topology Y) (R := R)
      (P.X q : SheafOfModules.{u + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (V : Type (u + 1)) [AddCommGroup V] [Module B V] [Finite V]
    (t : ℕ) (F : Fin (t + 1) → Submodule B V) (hF : Antitone F)
    (hF₀ : F 0 = ⊤) (hFt : F (Fin.last t) = ⊥)
    (r s : ℤ) (hrs : r ≤ s)
    (hW : ∀ (j : Fin t) (n : ℤ),
      IsConstructibleProEtaleCoefficientModuleSheaf Y B
        ((filteredCoefficientTensorComplex Y B R ρ P
          (ModuleCat.of B ((F j.castSucc) ⧸
            (F j.succ).comap (F j.castSucc).subtype))).homology n) ∧
      ((n < r ∨ s < n) → IsZero
        ((filteredCoefficientTensorComplex Y B R ρ P
          (ModuleCat.of B ((F j.castSucc) ⧸
            (F j.succ).comap (F j.castSucc).subtype))).homology n))) :
    (∀ (j : Fin (t + 1)) (n : ℤ),
      IsConstructibleProEtaleCoefficientModuleSheaf Y B
        ((filteredCoefficientTensorComplex Y B R ρ P (ModuleCat.of B (F j))).homology n) ∧
      ((n < r ∨ s < n) → IsZero
        ((filteredCoefficientTensorComplex Y B R ρ P (ModuleCat.of B (F j))).homology n))) ∧
    (∀ n : ℤ,
      IsConstructibleProEtaleCoefficientModuleSheaf Y B
        ((filteredCoefficientTensorComplex Y B R ρ P (ModuleCat.of B V)).homology n) ∧
      ((n < r ∨ s < n) → IsZero
        ((filteredCoefficientTensorComplex Y B R ρ P (ModuleCat.of B V)).homology n))) := by
  sorry

end AlgebraicGeometry.Scheme
