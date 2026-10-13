/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom

/-! # Left-argument shift comparison for internal derived Hom
Source: Stacks Project, Cohomology on Sites, Section 21.34 (Tag 0A8X)
and Section 21.35 (Tag 08JA); the signed shift calculation is written here.
(blueprint: lem-pur-derived-internal-hom-shift-left).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace CategoryTheory

/-- Shifting the source argument by m shifts internal Hom by -m.
Proof: Represent P by L and the second variable by a functorial K-injective I.
The signed reindexing of Hom(L,I)[-m] to Hom(L[m],I) sends the component in
index p and degree k to (-1)^(m*k) times the component in index p+m.
The inverse reindexes backwards with the same sign. The differential identity
follows by comparing the postcomposition and precomposition terms: their
relative sign is (-1)^m, canceled by the adjacent-degree scalar ratio.
Postcomposition commutes with reindexing and scalar multiplication. Localize
this natural chain isomorphism and use the representative comparison for
internal derived Hom. Quasi-isomorphism invariance descends the comparison
and its naturality to the derived category. The construction also works for
negative m and zero objects; m=0 has identity reindexing and signs.
Source: Stacks Project, sites-cohomology.tex, Sections 21.34 and 21.35,
Tags 0A8X and 08JA.
(blueprint: lem-pur-derived-internal-hom-shift-left) -/
theorem derivedInternalHom_shift_left
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (P : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) (m : ℤ) :
    Nonempty (
      ((Functor.curry.obj (derivedInternalHom.{u, w} (C := C) J R)).obj (op P) ⋙
        shiftFunctor _ (-m)) ≅
      ((Functor.curry.obj (derivedInternalHom.{u, w} (C := C) J R)).obj (op (P⟦m⟧)))) := by sorry

end CategoryTheory
