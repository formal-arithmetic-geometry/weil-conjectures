/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap

/-! # Lower support bound for double derived Hom

Source: Stacks Project, more-algebra.tex, Tag 0A69,
lemma-internal-hom-evaluate-isomorphism-technical, proof, second tail object;
sites-cohomology.tex, Tags 0A8X, 08J7 and 0A95
(blueprint: lem-trf-double-derived-hom-lower-bound).

Ordinary modules use the shared one-object bottom-topology ringed site.
The conclusion records the actual Hom complexes, their derived comparisons,
and the resulting uniform cohomological bound.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Double derived Hom into bounded injective targets has a uniform lower bound,
with the specified actual Hom-complex models.
Source: Stacks Project, Tag 0A69, final sentence of proof, second tail object;
Tags 070J, 0A8X, 08J7 and 0A95
(blueprint: lem-trf-double-derived-hom-lower-bound).

Proof:
1. The vanishing of E below q gives a representative zero below q by the standard
   t-structure (def-sbc-standard-tstructure-derived-category). Fix any such B.
2. Boundedness of J supplies a lower bound, and I is zero below v. Their terms are
   injective, so both targets are K-injective by
   lem-weil-pbc-bounded-below-injectives-kinjective (Stacks 070J).
3. The K-injective model comparison for def-pur-derived-internal-hom, justified by
   lem-pur-rhom-well-defined, identifies Q Hom(B,J) with RHom(E,L). Apply it again
   to Hom(Hom(B,J),I), then transport the first argument along the first isomorphism.
4. In degree s, Hom(B,J) is the product over p of Hom(B^p,J^(p+s)), by
   def-pur-hom-complex. If s>u-q, then p<q kills the source, while p>=q implies
   p+s>u and kills the target. Every factor, and hence the product, is zero.
5. In degree t<q+v-u, each factor Hom(C^s,I^(s+t)) is zero: either s>u-q and
   C^s=0 by step 4, or s<=u-q and s+t<v. Thus the second actual complex is zero.
6. A zero term has zero cohomology. Apply the cohomology functor to the derived
   comparison in step 3 to obtain the asserted vanishing. The t-structure supplies
   B even when none was chosen beforehand. Only the fixed u,v and the varying q
   enter these calculations, so the same u,v work for every eligible E,q and B.
-/
theorem double_derived_hom_lower_bound
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (RingSiteModules R)]
    (L M : DerivedCategory (RingSiteModules R))
    (J I : CochainComplex (RingSiteModules R) ℤ) (uBound vBound : ℤ)
    (_hJ : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (J.X r))
    (_hI : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (I.X r))
    (_hJinj : ∀ r : ℤ, Injective (J.X r))
    (_hIinj : ∀ r : ℤ, Injective (I.X r))
    (_eJ : Q.obj J ≅ L) (_eI : Q.obj I ≅ M)
    (_hJu : ∀ r : ℤ, uBound < r → IsZero (J.X r))
    (_hIv : ∀ r : ℤ, r < vBound → IsZero (I.X r)) :
    ∀ (E : DerivedCategory (RingSiteModules R)) (q : ℤ),
      (∀ r : ℤ, r < q → IsZero ((homologyFunctor (RingSiteModules R) r).obj E)) →
      (∀ (B : CochainComplex (RingSiteModules R) ℤ) (_eB : Q.obj B ≅ E)
        (_hB : ∀ r : ℤ, r < q → IsZero (B.X r)),
        Nonempty (Q.obj (homComplex (R := CochainComplex.onePointRingSheaf R) B J) ≅
          (derivedInternalHomOfUniverses.{u, u, u, w} ⊥
            (CochainComplex.onePointRingSheaf R)).obj (op E, L)) ∧
        Nonempty (Q.obj (homComplex (R := CochainComplex.onePointRingSheaf R)
          (homComplex (R := CochainComplex.onePointRingSheaf R) B J) I) ≅
          (derivedInternalHomOfUniverses.{u, u, u, w} ⊥
            (CochainComplex.onePointRingSheaf R)).obj
              (op ((derivedInternalHomOfUniverses.{u, u, u, w} ⊥
                (CochainComplex.onePointRingSheaf R)).obj (op E, L)), M)) ∧
        (∀ s : ℤ, uBound - q < s →
          IsZero ((homComplex (R := CochainComplex.onePointRingSheaf R) B J).X s)) ∧
        (∀ t : ℤ, t < q + vBound - uBound →
          IsZero ((homComplex (R := CochainComplex.onePointRingSheaf R)
            (homComplex (R := CochainComplex.onePointRingSheaf R) B J) I).X t))) ∧
      (∀ t : ℤ, t < q + vBound - uBound →
        IsZero ((homologyFunctor (RingSiteModules R) t).obj
          ((derivedInternalHomOfUniverses.{u, u, u, w} ⊥
            (CochainComplex.onePointRingSheaf R)).obj
              (op ((derivedInternalHomOfUniverses.{u, u, u, w} ⊥
                (CochainComplex.onePointRingSheaf R)).obj (op E, L)), M)))) := by
  sorry

end DerivedCategory
