/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Maps from ind-étale algebras into henselian local rings
Source: Stacks Project, Algebra, Lemmas Tags 08HQ and 08HR
(blueprint: lem-weil-pbc-map-into-henselian-colimit).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- Source: Stacks Project, Algebra, Lemmas Tags 08HQ and 08HR
(blueprint: lem-weil-pbc-map-into-henselian-colimit).

Proof (the nine steps of the node):
1. In the single étale case put `k = S / m` and `B = A ⊗[R] S`. Base change preserves
   étaleness (`lem-weil-pbc-etale-ring-base-change`).
2. The residue map from `A` and the quotient map from `S` agree over `R` by `hτ`, hence
   define `φ : B → k`. It is surjective; its kernel `q'` lies over `m` with residue field `k`
   (`def-weil-residue-field`).
3. Apply `lem-weil-pbc-henselian-etale-retraction` to obtain the unique retraction
   `σ : B → S` over `S` with inverse image `q'`, and restrict it to `f : A → S`.
4. The residue of `σ` is `φ`: both maps factor through `B / q'` and agree on the
   surjective image of `S`. Therefore `f` induces `τ`; injectivity of `τ` gives the
   required inverse-image ideal.
5. Any other such `f'` extends to an `S`-algebra retraction `σ'` by the tensor-product
   universal property. Its residue is `φ`, so its inverse-image ideal is `q'`.
   Uniqueness in `lem-weil-pbc-henselian-etale-retraction` gives `σ' = σ` and `f' = f`.
6. For the filtered diagram pull `q` back to `qᵢ` and compose `τ` with the induced
   residue-field map. Apply the single étale case to obtain the unique `fᵢ` at each stage
   (`def-weil-pbc-category-colimit`, `def-weil-residue-field`). A singleton diagram
   includes the single étale case.
7. Along every transition map the composite with `fⱼ` satisfies the conditions defining
   `fᵢ`, so uniqueness makes the family compatible. The colimit universal property
   defines `f` (`def-weil-pbc-category-colimit`).
8. Every element comes from a stage (`lem-weil-pbc-filtered-colimit-algebras-elementwise`);
   checking there gives the inverse-image ideal and prescribed residue map for `f`.
9. Any other map restricts to `fᵢ` at every stage by the single étale uniqueness.
   Colimit uniqueness then makes it equal to `f` (`def-weil-pbc-category-colimit`).
-/
theorem map_into_henselian_colimit
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] [HenselianLocalRing S]
    (A : Type w) [CommRing A] [Algebra R A]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{w} R) [HasColimit F]
    (hA : Nonempty (colimit F ≅ CommAlgCat.of R A))
    (hEtale : ∀ i : I, Algebra.Etale R (F.obj i))
    (q : Ideal A) [q.IsPrime]
    (p : Ideal R) [p.IsPrime]
    (hp : p = q.comap (algebraMap R A))
    (hm : p = (IsLocalRing.maximalIdeal S).comap (algebraMap R S))
    (τ : q.ResidueField →+* (IsLocalRing.maximalIdeal S).ResidueField)
    (hτ : τ.comp (Ideal.ResidueField.map p q (algebraMap R A) hp) =
      Ideal.ResidueField.map p (IsLocalRing.maximalIdeal S) (algebraMap R S) hm) :
    ∃! f : A →ₐ[R] S,
      ∃ hf : q = (IsLocalRing.maximalIdeal S).comap f.toRingHom,
        Ideal.ResidueField.map q (IsLocalRing.maximalIdeal S) f.toRingHom hf = τ := by
  sorry

end Algebra
