/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom

/-! # Shift comparison for derived internal Hom
Source: Stacks Project, Cohomology on Sites, Sections 21.34 and 21.35, Tag 08JA.
(blueprint: lem-pur-derived-internal-hom-shift-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace CategoryTheory

/-- Shifting the two arguments of internal derived Hom shifts its value by their
relative degree, naturally in the second argument. This is a comparison in the
sheaf derived category; no global-section or cohomology functor occurs here.
Source: Stacks Project, Cohomology on Sites, Sections 21.34 and 21.35, Tag 08JA.
(blueprint: lem-pur-derived-internal-hom-shift-comparison).

Proof: Represent P by a complex L and Q by a K-injective complex I. Shifting I by n
preserves K-injectivity: shift an acyclic test complex by -n in the null-homotopy
criterion. The representative comparison for internal derived Hom therefore
computes the two values by Hom(L,I) and Hom(L[m],I[n]). In degree k, send a family
with components a_r : L^r → I^(r+k+n-m) to the family with p-th component
(-1)^(m*k) a_(p+m). This is an invertible reindexing of the product of internal
Hom sheaves. The source differential has the overall shift sign (-1)^(n-m);
the target differential has signs (-1)^n on postcomposition and (-1)^(k+m)
on precomposition. The ratio is (-1)^m, compensated by the adjacent-degree
factors (-1)^(m*k) and (-1)^(m*(k+1)). Thus it is a chain isomorphism.
Postcomposition commutes with the reindexing and scalar factors, so it is natural
in I. Apply the derived localization and the representative comparisons. A
morphism between K-injective representatives is represented by a chain map up
to homotopy; both constructions preserve homotopy, giving the displayed
naturality for arbitrary derived q. This works in every integer degree and for
unbounded complexes. At m=n=0 the reindexing and signs are the identity; for zero
arguments both complexes vanish. No K-flatness assumption is needed. -/
theorem derivedInternalHom_shift_comparison
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    ∃ e : ∀ (P Q : DerivedCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) (m n : ℤ),
      ((derivedInternalHom J R).obj (op P, Q))⟦n - m⟧ ≅
        (derivedInternalHom J R).obj (op (P⟦m⟧), Q⟦n⟧),
      ∀ (P Q Q' : DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
        (m n : ℤ) (q : Q ⟶ Q'),
        ((derivedInternalHom J R).map ((𝟙 P).op, q))⟦n - m⟧' ≫
            (e P Q' m n).hom =
          (e P Q m n).hom ≫
            (derivedInternalHom J R).map ((𝟙 (P⟦m⟧)).op, q⟦n⟧') := by sorry

end CategoryTheory
