/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat

/-!
# Functorial bounded-above flat replacement on the small etale site

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`,
`lem-kun-bounded-flat-replacement`; Stacks Project, Tag 05T7 (1), with sectionwise
free covers and exact sheafification (Tags 00WJ and 03ET).
(blueprint: lem-kun-bounded-flat-replacement).

The full subcategory defined by `IsStrictlyLE N` retains every chain map between
complexes vanishing above `N`. A natural augmentation expresses compatibility of the
replacement maps with all these chain maps. Surjectivity means epimorphy of module
sheaves, not surjectivity on sections over every object of the site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- At every fixed upper bound, complexes of modules over the constant ring sheaf
admit a functorial flat replacement and a termwise epimorphic quasi-isomorphism.
The output has the same upper bound; functor laws are those of `Φ`, and compatibility
with the augmentation is naturality of `ε`.
Source: blueprint `lem-kun-bounded-flat-replacement`; Stacks Project, Tag 05T7 (1).
(blueprint: lem-kun-bounded-flat-replacement).

Proof:
1. Restrict scalars to the constant presheaf ring and take the sectionwise free cover
   B(M)(U) with basis the sections of M(U). Evaluation is natural and surjective
   (def-weil-pbc-free-module, def-weil-pbc-constant-sheaf, def-weil-size-convention).
2. Descend from N. Set C above N to zero, and in degree i take the free cover of
   F^i times_{Z^(i+1)F} Z^(i+1)C. Evaluation and the two projections define q and d.
   Using cycles makes d squared zero and makes q a chain map
   (def-weil-abstract-derived-category). This is the cycle-pullback construction of
   05T7, correcting the full-next-term pullback in the imported blueprint proof.
3. Inductively, q is sectionwise onto both terms and cycles: lift d(x) to a cycle
   for a term lift, and use the pair (x,0) for a cycle lift.
4. The resulting map is a sectionwise cohomology isomorphism. Cycle lifts give
   surjectivity; if q(c)=d(a), the basis vector [(a,c)] has differential c, proving
   injectivity (lem-weil-pbc-site-module-presheaf-sheafification-exact).
5. Sheafify termwise. Exact sheafification preserves the upper bound, epimorphisms
   and cohomology. Sheafify the scalar action using preservation of finite products
   to obtain the constant-sheaf module action; the augmentation and cohomology
   comparison are linear (def-weil-pbc-sheafification,
   lem-weil-pbc-sheafification-sets-exact).
6. The presheaf terms are sectionwise free, hence flat, so sectionwise tensor
   preserves finite limits (lem-weil-pbc-projective-module-flat,
   lem-weil-pbc-flat-tensor-exact). Sheafification gives flat module sheaves by
   lem-pc-sites-modules-sheafification-flat, with flatness as in
   def-pc-flat-sheaf-modules.
7. A chain map acts on each cycle pullback by (x,z) mapping to (f(x),h(z)), and
   then on its free cover. Descending induction proves identity and composition,
   the chain equation and augmentation compatibility. Sheafification retains
   these identities. No additivity of the replacement functor is asserted. -/
theorem exists_functorial_bounded_flat_replacement
    (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] (N : ℤ) :
    ∃ (Φ : ObjectProperty.FullSubcategory
        (fun K : CochainComplex (SheafOfModules.{u + 1}
          ((sheafCompose T.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
                (CommRingCat.of Λ)))) ℤ ↦ K.IsStrictlyLE N) ⥤
        CochainComplex (SheafOfModules.{u + 1}
          ((sheafCompose T.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
                (CommRingCat.of Λ)))) ℤ)
      (ε : Φ ⟶ ObjectProperty.ι _),
      ∀ F, (Φ.obj F).IsStrictlyLE N ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := T.smallEtaleTopology)
          (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)) ((Φ.obj F).X i)) ∧
        QuasiIso (ε.app F) ∧ (∀ i : ℤ, Epi ((ε.app F).f i)) := by
  sorry

/-- Every bounded-above complex of Z/nZ-module sheaves has a bounded-above flat
replacement, for every integer n, including zero and negative n. The coefficient
ring is `ZMod n.natAbs`, the canonical presentation of Z/(n); `ULift` only places
this ring in the site's coefficient universe.
Source: blueprint `lem-kun-bounded-flat-replacement`, final assertion.
(blueprint: lem-kun-bounded-flat-replacement).

Proof: specialize exists_functorial_bounded_flat_replacement to the commutative
ring `ULift (ZMod n.natAbs)` and the supplied bound N, evaluate its augmentation
at F, and retain the bound, flatness and quasi-isomorphism (step 7 of the node).
There is no invertibility, finiteness or properness assumption. -/
theorem exists_bounded_flat_replacement_zmod
    (T : Scheme.{u}) (n : ℤ) (N : ℤ)
    (F : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} (ZMod n.natAbs)))))) ℤ)
    [F.IsStrictlyLE N] :
    ∃ (P : CochainComplex (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
              (CommRingCat.of (ULift.{u + 1} (ZMod n.natAbs)))))) ℤ)
      (q : P ⟶ F), P.IsStrictlyLE N ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := T.smallEtaleTopology)
          (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} (ZMod n.natAbs)))) (P.X i)) ∧ QuasiIso q := by
  sorry

end AlgebraicGeometry.Scheme
