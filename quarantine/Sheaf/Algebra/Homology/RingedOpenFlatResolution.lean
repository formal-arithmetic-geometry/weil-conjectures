/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Flat resolutions under ringed slice extension

Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0E8I
(lemma-j-shriek-and-tensor); the cochain and strict-tower refinement is agent-written
(blueprint: lem-cbc-ringed-open-flat-resolution).

Extension is the existing direct-sum presheaf followed by module sheafification.
All complexes are integer-indexed and may be unbounded. Strict inverse sequences
are functors from the opposite natural-number order, indexed starting at zero;
reindexing by n + 1 gives the convention of towers starting at one.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe c v r

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {S : Type c} [Category.{v} S] {J : GrothendieckTopology S}
  (R : Sheaf J CommRingCat.{max c v r}) (U : S)

/-- The existing quasi-isomorphism predicate with canonical small-site sheafification
witnesses supplied explicitly. No homology theory or notion of quasi-isomorphism is changed.
Source: Stacks Project, Modules on Sites, Tags 03DI--03DJ, and Homology, Tag 010N
(blueprint: lem-cbc-ringed-open-flat-resolution). -/
abbrev ringedOpenQuasiIso {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r})
    {P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ}
    (f : P ⟶ Q) : Prop :=
  letI : HasSheafify K AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := K)
  letI : K.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := K)
  QuasiIso f

/-- Ringed slice extension preserves K-flatness, flat terms, and termwise epimorphic
quasi-isomorphisms, without a boundedness assumption.

Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0E8I
(lemma-j-shriek-and-tensor); agent-written resolution refinement
(blueprint: lem-cbc-ringed-open-flat-resolution).

Proof:
1. Both restriction and extension are exact by
   lem-pur-site-restriction-module-adjunction-exact. Apply either functor to
   0 -> Z^i X -> X^i -> B^(i+1) X -> 0 and
   0 -> B^i X -> Z^i X -> H^i X -> 0. This identifies the homology of the
   image with the image of homology naturally in chain maps, in every integer degree
   (def-pc-acyclic-complex-modules). In particular acyclic complexes stay acyclic.
2. For acyclic A, restriction makes j^* A acyclic. The unbounded total-tensor
   comparison of lem-sf-ringed-open-total-tensor-kflat identifies
   Tot(e_! P tensor A) with e_! Tot(P tensor j^* A). The inner complex is acyclic
   by def-pc-kflat-complex, and exact extension preserves acyclicity. Interchanging
   the tensor factors uses the signed swap (-1)^(pq) on the (p,q) summand; its square
   is the identity and it commutes with d_P tensor 1 + (-1)^p 1 tensor d_A.
3. Restrict a short exact sequence, tensor with a flat P^i, and extend. Exactness
   of both functors and the natural module projection isomorphism of
   lem-weil-pbc-ringed-slice-extension-tensor identify this exact sequence with its
   tensor by e_!(P^i). This is def-pc-flat-sheaf-modules for each image term.
4. Apply exact extension to the kernel short exact sequence of each epimorphic q^i.
   Thus every image component is epimorphic. Step 1 identifies H^i(e_! q) with
   e_! H^i(q), an isomorphism, proving def-pc-quasi-iso-modules for the image map.
   Combining steps 2--4 gives preservation of flat-term K-flat replacements.
5. For strict towers apply these arguments at every level. The tower assertion
   below retains exactly the image transition maps, without choosing new lifts. -/
theorem ringedOpen_preserves_flat_resolution :
    (∀ P : CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{max c v, v, max c v r}
        (J := J.over U) (R := R.over U) P →
        CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
          (J := J) (R := R)
          ((ringedOpenExtensionOnComplexes.{c, v, r} R U).obj P)) ∧
    (∀ P : CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ,
      (∀ i : ℤ, @IsFlatOnSite.{max c v, v, max c v r, max c v r}
          (Over U) _ (J.over U) _
          (wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r}
            (J := J.over U))
          (hasSheafify_coefficientUniverse.{max c v, v, max c v r}
            (J := J.over U)).isRightAdjoint (R.over U) (P.X i)) →
        ∀ i : ℤ, @IsFlatOnSite.{c, v, max c v r, max c v r} S _ J _
          (wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J))
          (hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)).isRightAdjoint R
          (((ringedOpenExtensionOnComplexes.{c, v, r} R U).obj P).X i)) ∧
    (∀ (P C : CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ)
        (q : P ⟶ C),
      (∀ i : ℤ, Epi (q.f i)) → ringedOpenQuasiIso.{max c v, v, r} (R.over U) q →
        (∀ i : ℤ, Epi (((ringedOpenExtensionOnComplexes.{c, v, r} R U).map q).f i)) ∧
          ringedOpenQuasiIso.{c, v, r} R
            ((ringedOpenExtensionOnComplexes.{c, v, r} R U).map q)) := by
  sorry

/-- The same three preservation assertions hold objectwise for strict inverse sequences.
The extended tower is the actual composite functor, and its resolution map is
`whiskerRight q`, so its transitions and their commutation equations are retained.

Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0E8I
(lemma-j-shriek-and-tensor); agent-written strict-tower refinement
(blueprint: lem-cbc-ringed-open-flat-resolution).

Proof:
1. Exact restriction and extension give the natural homology comparison using the
   two cycle/boundary short exact sequences as in the preceding assertion
   (lem-pur-site-restriction-module-adjunction-exact,
   def-pc-acyclic-complex-modules).
2. At every level use lem-sf-ringed-open-total-tensor-kflat and the signed tensor swap
   to apply def-pc-kflat-complex to the restricted acyclic test complex.
3. At every level use the exact module projection isomorphism of
   lem-weil-pbc-ringed-slice-extension-tensor to test def-pc-flat-sheaf-modules.
4. Exact extension preserves the kernel short exact sequence of each resolution
   component, hence its epimorphism. The natural homology comparison preserves
   its quasi-isomorphism (def-pc-quasi-iso-modules).
5. Postcompose the original strict tower with the existing complex extension
   functor and whisker its resolution map. Functoriality preserves the chain-map
   and tower equations with precisely e_!(t_n) as transitions. Kernels, cokernels,
   epimorphisms and homology in the tower category are detected levelwise by
   lem-weil-tower-category-levelwise-abelian. The three conclusions together say
   that every objectwise flat-term K-flat replacement remains one. -/
theorem ringedOpen_tower_preserves_flat_resolution :
    (∀ P : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ,
      (∀ n : ℕᵒᵖ, CochainComplex.IsKFlatIndependentCoefficients.{max c v, v, max c v r}
        (J := J.over U) (R := R.over U) (P.obj n)) →
        ∀ n : ℕᵒᵖ, CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
          (J := J) (R := R)
          ((P ⋙ ringedOpenExtensionOnComplexes.{c, v, r} R U).obj n)) ∧
    (∀ P : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ,
      (∀ (n : ℕᵒᵖ) (i : ℤ), @IsFlatOnSite.{max c v, v, max c v r, max c v r}
          (Over U) _ (J.over U) _
          (wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r}
            (J := J.over U))
          (hasSheafify_coefficientUniverse.{max c v, v, max c v r}
            (J := J.over U)).isRightAdjoint (R.over U) ((P.obj n).X i)) →
        ∀ (n : ℕᵒᵖ) (i : ℤ), @IsFlatOnSite.{c, v, max c v r, max c v r} S _ J _
          (wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J))
          (hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)).isRightAdjoint R
          (((P ⋙ ringedOpenExtensionOnComplexes.{c, v, r} R U).obj n).X i)) ∧
    (∀ (P C : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ)
        (q : P ⟶ C),
      (∀ (n : ℕᵒᵖ) (i : ℤ), Epi ((q.app n).f i)) →
      (∀ n : ℕᵒᵖ, ringedOpenQuasiIso.{max c v, v, r} (R.over U) (q.app n)) →
        (∀ (n : ℕᵒᵖ) (i : ℤ),
          Epi (((Functor.whiskerRight q
            (ringedOpenExtensionOnComplexes.{c, v, r} R U)).app n).f i)) ∧
        (∀ n : ℕᵒᵖ,
          ringedOpenQuasiIso.{c, v, r} R ((Functor.whiskerRight q
            (ringedOpenExtensionOnComplexes.{c, v, r} R U)).app n))) := by
  sorry

end SheafOfModules
