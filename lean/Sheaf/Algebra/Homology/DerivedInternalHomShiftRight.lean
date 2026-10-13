/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom

/-! # Right-argument shift comparison for internal derived Hom
Source: Stacks Project, Cohomology on Sites, Section 21.34 (Tag 0A8X)
and Section 21.35 (Tag 08JA); the signed shift calculation is written here.
(blueprint: lem-pur-derived-internal-hom-shift-right).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace CategoryTheory

/-- Shifting the target argument by n shifts internal Hom by n.
Proof: Represent P by L and the target by a K-injective I. The shifted complex
I[n] remains K-injective, since shifting an acyclic test complex by -n
transports the null-homotopy criterion. Reindex the degree of the internal Hom
complex to identify Hom(L,I)[n] with Hom(L,I[n]); no source reindexing sign is
needed. Its differential has the same postcomposition and precomposition
signs on both sides. This comparison commutes with postcomposition and with
homotopies. Localize and transport using the representative comparisons;
quasi-isomorphism invariance makes it independent of the representative and
natural for all derived morphisms. All integers n are allowed, including zero,
and the construction preserves zero complexes.
Source: Stacks Project, sites-cohomology.tex, Sections 21.34 and 21.35,
Tags 0A8X and 08JA.
(blueprint: lem-pur-derived-internal-hom-shift-right) -/
theorem derivedInternalHom_shift_right
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (P : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) (n : ℤ) :
    Nonempty (
      ((Functor.curry.obj (derivedInternalHom.{u, w} (C := C) J R)).obj (op P) ⋙
        shiftFunctor _ (n)) ≅
      (shiftFunctor _ n ⋙
        (Functor.curry.obj (derivedInternalHom.{u, w} (C := C) J R)).obj (op P))) := by sorry

end CategoryTheory
