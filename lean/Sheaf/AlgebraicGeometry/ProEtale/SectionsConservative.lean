/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible

/-!
# Evaluation on affine weakly contractible objects is conservative

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-cor-pe-sections/det-pe-sections-conservative.md` (blueprint: det-pe-sections-conservative).
-/

@[expose] public section

set_option autoImplicit false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{t}}

/-- The module-sheaf category is abelian in the common site/coefficient universe.
Source: Stacks Project, Tag 03DA; `def-weil-sheaf-of-modules-category`
(blueprint: det-pe-sections-conservative). -/
noncomputable instance sections_module_abelian (R : Sheaf (topology X) RingCat.{u}) :
    Abelian (ringedSiteModules.{max u (t + 1)} R) := by
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses (topology X) R
  infer_instance

/-- Evaluation of module sheaves on a site object is additive.
Source: Stacks Project, Tag 03DA; `def-weil-sheaf-of-modules-category`
(blueprint: det-pe-sections-conservative). -/
noncomputable instance sections_evaluation_additive
    (R : Sheaf (topology X) RingCat.{u}) (W : X.ProEt) :
    (SheafOfModules.evaluation.{max u (t + 1)} R (op W)).Additive :=
  inferInstanceAs ((SheafOfModules.forget R ⋙
    PresheafOfModules.evaluation R.obj (op W)).Additive)

/-- Evaluation on affine weakly contractible objects detects exact sequences, acyclic
complexes, isomorphisms, and quasi-isomorphisms of modules on the small pro-etale site.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-cor-pe-sections/det-pe-sections-conservative.md`, clauses 1--3;
Stacks Project, Tags 0946, 0947, 05RT, and 0115
(blueprint: det-pe-sections-conservative).

Clause 1 is Proposition 0947(1); clauses 2--3 are its degreewise and cone
consequences, as expanded in the blueprint proof.

Proof:
1. Put `Z = ker g` and let `u : A ⟶ Z` be induced by `f`; its existence follows from
`f ≫ g = 0`.
The sequence is exact at `B` precisely when `coker u = Z / im f` is zero. The underlying
abelian sheaf of this cokernel is the abelian cokernel of `u`, by
`lem-weil-pbc-module-sheaves-colimits-forgetful`; faithfulness reflects the zero object.
Thus exactness is equivalent to the underlying abelian map `u` being epic. By
`lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`, this is equivalent to local lifting
of each section of `Z`. The equality `Z(V) = ker (g(V))` is the sectionwise kernel statement
from `def-weil-sheaf-of-modules-category`, yielding the local lifting formulation.
2. By `det-pe-wcb-cover`, every site object has a covering by affine objects `Spec D` with
`D` w-contractible. The final assertion of `det-pe-weak-contractible-equivalences` makes
each such affine weakly contractible, so every object has a covering by the class used here.
3. If the sequence is exact, the underlying abelian map `u` is locally surjective. The set
sheaf criterion `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective` makes it epic, and
clause 3 of `det-pe-weak-contractible-equivalences` makes `A(W) ⟶ Z(W)` surjective for every
weakly contractible affine `W`. The sectionwise kernel equality gives exactness after
evaluation; the reverse inclusion follows from `f ≫ g = 0`.
4. Conversely, exactness on every affine weakly contractible member of a covering gives,
for a section in `ker (g(V))`, local lifts through `f`; these lifts need not agree on
overlaps, which is exactly local surjectivity and hence exactness of the sheaf sequence.
5. For every cochain complex `K`, its degree-`q` cohomology is `ker d^q / im d^(q-1)` by
`def-weil-abstract-derived-category`. It vanishes exactly when the adjacent maps are exact.
Apply clause 1 degreewise and exchange the quantifiers over `q` and `W`; no boundedness is
used.
6. An isomorphism of module sheaves has bijective components by evaluating its inverse.
Conversely, componentwise bijectivity on all affine weakly contractible objects gives
injectivity by the sheaf condition and surjectivity by gluing the unique local lifts from a
covering. The glued inverse is linear and natural because applying the original morphism
verifies both properties.
7. For a morphism `v : K ⟶ L`, use the cone with degree `q` equal to
`L^q ⊞ K^(q+1)` and differential `(l,k) ↦ (d_L l + v k, -d_K k)`. The cone criterion
`lem-pur-quasi-iso-cone-acyclic` identifies quasi-isomorphisms with acyclic cones. Finite
biproducts and sectionwise limits from `lem-weil-pbc-module-sheaves-limits-sectionwise`,
together with additivity, identify the evaluated cone with the cone of `v(W)`. Clause 2
therefore gives the quasi-isomorphism equivalence.
-/
theorem sections_conservative
    (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) :
    (∀ (A B C : ringedSiteModules.{max u (t + 1)} R)
        (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0),
      (ShortComplex.mk f g h).Exact ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            ((ShortComplex.mk f g h).map
              (SheafOfModules.evaluation.{max u (t + 1)} R (op W))).Exact) ∧
    (∀ (K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ),
      K.Acyclic ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            HomologicalComplex.Acyclic
              ((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj K)) ∧
    (∀ (A B : ringedSiteModules.{max u (t + 1)} R) (f : A ⟶ B),
      IsIso f ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            Function.Bijective
              ((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).map f).hom) ∧
    (∀ (K L : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ)
        (f : K ⟶ L),
      QuasiIso f ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            QuasiIso
              (((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
