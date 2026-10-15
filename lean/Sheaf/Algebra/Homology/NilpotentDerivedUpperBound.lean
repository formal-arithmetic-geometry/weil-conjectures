/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.KFlatClosure
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.AcyclicKFlatTensor
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Nilpotent derived reduction detects an upper cohomological bound

Source: Stacks Project, More on Algebra, Tag 0H75,
lemma-check-tor-dimension-modulo-nilpotent, upper-bound-only adaptation used by Tag 09AR
(blueprint: lem-weil-pbc-nilpotent-derived-upper-bound).

Ordinary modules are encoded on the existing one-object site with bottom topology.
The additive scalar-extension functor and its left derived functor are specified by
exactly the object formula, morphism formula and universal property supplied by
`SheafOfModules.derivedChangeOfRings`; no choice of a particular model is required.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Reduction modulo a nilpotent ideal detects vanishing above the same integer.
Source: Stacks Project, More on Algebra, Tag 0H75,
lemma-check-tor-dimension-modulo-nilpotent, upper-bound-only adaptation used by Tag 09AR
(blueprint: lem-weil-pbc-nilpotent-derived-upper-bound).

Proof:
1. Represent `C` by a complex and take a termwise flat K-flat resolution `P`
   (lem-pc-kflat-resolution). Derived change of rings (lem-pur-derived-change-of-rings)
   identifies its reduction `Q` with `LF.obj C`. It is termwise flat and K-flat over
   `A/I` by lem-pur-kflat-change-of-rings.
2. Good truncation at `b` is quasi-isomorphic to `Q`. Replace that truncation by a
   flat complex `F` zero above `b` (lem-pc-kflat-bounded-flat-replacement).
   It is K-flat by lem-pc-module-bounded-flat-kflat. Thus `F → Q` is a
   quasi-isomorphism between K-flat complexes.
3. Its cone is acyclic and K-flat (lem-pur-quasi-iso-cone-acyclic,
   lem-pc-kflat-cone-direct-sum). Tensoring with any `A/I`-module preserves its
   acyclicity (lem-pur-acyclic-kflat-tensor-arbitrary). Swap the degree-zero module
   factor by the ordinary balanced symmetry, and identify the tensor of the cone
   with the cone of the tensor map by its differential block matrix. Therefore
   `F ⊗ M → Q ⊗ M` is a quasi-isomorphism. The source is zero above `b`.
4. If `IM = 0`, the inverse balanced formulas `p ⊗ m ↦ (p ⊗ 1) ⊗ m` and
   `(p ⊗ a) ⊗ m ↦ p ⊗ am` identify `P ⊗_A M` with `Q ⊗_(A/I) M`.
   Hence it has no cohomology above `b`.
5. Induct on `t ≥ 1` for modules killed by `I^t`, using `0 → IM → M → M/IM → 0`.
   Termwise flatness (def-pc-flat-sheaf-modules) makes its tensor with `P`
   degreewise exact. For a cocycle `z` above `b`, its quotient image is a boundary;
   lift a primitive `y`. Then `z-dy` comes from a cocycle `x` in the first complex
   by injectivity in the next degree. There `x=dw`, so `z=d(y+w)`.
6. Apply this to `M=A` and `t=N`. The balanced isomorphism `P ⊗_A A ≅ P`,
   given by `p ⊗ a ↦ ap`, and the resolution identify this vanishing with that of `C`.
-/
theorem isZero_homology_of_nilpotent_derived_reduction
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ)
    (hN : 1 ≤ N) (hI : I ^ N = ⊥)
    [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules (A ⧸ I))]
    (E : RingSiteModules A ⥤ RingSiteModules (A ⧸ I))
    (hobjects : ∀ M : RingSiteModules A,
      E.obj M = SheafOfModules.changeOfRings (ringSiteMap (Ideal.Quotient.mk I)) M)
    (hmaps : ∀ {M M' : RingSiteModules A} (f : M ⟶ M'),
      E.map f = eqToHom (hobjects M) ≫
        SheafOfModules.changeOfRingsHom (ringSiteMap (Ideal.Quotient.mk I)) M f ≫
          eqToHom (hobjects M').symm)
    [E.Additive]
    (LF : DerivedCategory (RingSiteModules A) ⥤ DerivedCategory (RingSiteModules (A ⧸ I)))
    (ε : Qh ⋙ LF ⟶ E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (RingSiteModules A) (ComplexShape.up ℤ)))
    (C : DerivedCategory (RingSiteModules A)) (b : ℤ)
    (hred : ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (RingSiteModules (A ⧸ I)) i).obj (LF.obj C))) :
    ∀ i : ℤ, b < i → IsZero ((homologyFunctor (RingSiteModules A) i).obj C) := by
  sorry

end DerivedCategory
