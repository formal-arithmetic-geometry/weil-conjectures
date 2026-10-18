/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import Sheaf.RingTheory.WContractibleGeometricCriterion
import Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exact sections at an algebraically closed pro-etale point

Source: Stacks Project, `proetale.tex`, Tags 0982 and 098H;
`sites-cohomology.tex`, Tag 0946; `derived.tex`, Tags 015F and 014X
(blueprint: lem-weil-point-proetale-sections-exact).
-/

@[expose] public section

universe u w w'

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- Sections of module sheaves at the final small pro-etale object, with their actual
section-ring action. This is exactly Mathlib evaluation, after forgetting commutativity
of the coefficient sheaf; it introduces no different module category or section functor.

Source: Stacks Project, `sites-modules.tex`, Tag 03CW
(blueprint: lem-weil-point-proetale-sections-exact). -/
noncomputable abbrev pointModuleSections (k : Type u) [Field k]
    (A : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :
    ringedSiteModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) ⥤
      ModuleCat.{u + 1}
        (((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj.obj
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) :=
  SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))

/-- Sections at an algebraically closed pro-etale point are exact, and their termwise
extension induces the specified unbounded derived functor with natural cohomology comparison.

Source: Stacks Project, `proetale.tex`, Tags 0982 and 098H; `sites-cohomology.tex`,
Tag 0946; `homology.tex`, Tag 010N; `derived.tex`, Tags 015F and 014X
(blueprint: lem-weil-point-proetale-sections-exact).

Proof (the seven steps of the node):
1. Spec k and its component space are singletons, hence w-local and extremally
   disconnected. The sole maximal localization is k. Idempotent lifting modulo its zero
   maximal ideal is the identity, so k is henselian. Algebraic closedness implies that
   every irreducible polynomial has degree one; the residue field k is separably closed,
   so the localization is strictly henselian.
2. Apply `lem-weil-pbc-wcontractible-geometric-criterion`: every faithfully flat weakly
   etale k-algebra has a ring retraction, without any finite-presentation condition.
3. Apply `lem-weil-pbc-wcontractible-affine-weakly-contractible` to X = T = Spec k and
   its identity structural map. This gives surjectivity on sections of epimorphisms of
   set sheaves on the full small site, without assuming big-site restriction of sheaves.
4. Apply `lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits` to every
   commutative ring sheaf A and W = Spec k. Use its exactness clause for module evaluation,
   with the ordinary sectionwise action, including nonconstant and zero coefficient rings.
5. Abelian sheaves are modules over the constant sheaf of integers: integer multiplication
   extends uniquely across sheafification. Compatible local endomorphisms glue by applying
   them to sections on pullback covers; uniqueness makes the glued maps additive and natural.
   This constructs the endomorphism sheaf and the extended action. The action is forced
   by unitality and all abelian-sheaf maps respect it. Kernels and images remain the same
   underlying subgroups after forgetting this action, giving abelian-section surjectivity.
6. Apply `lem-sp-exact-functor-preserves-homology` to three consecutive complex terms.
   Evaluation preserves cycles, boundaries and their quotient, naturally in complex maps.
   Thus it preserves quasi-isomorphisms in every integer degree, without boundedness.
7. Apply `lem-weil-pbc-exact-functor-derived-factorization` to this exact additive functor.
   `mapDerivedCategory` is its termwise descent, with the standard shift and triangle
   structures. Its localization comparison identifies every representative with the
   section complex; step 6 descends naturally, giving the stated cohomology isomorphism.

The localization instances are arbitrary chosen presentations of the derived categories,
not restrictions on A. The final clause quantifies exactness proof instances only to
make the canonical `mapDerivedCategory` construction available; exactness is asserted
before that clause. Its shift structure is the one supplied by this construction. -/
theorem point_proEtale_sections_exact (k : Type u) [Field k] [IsAlgClosed k] :
    (∀ (F G : Sheaf (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1})
      (f : F ⟶ G), Epi f →
      Function.Surjective
        ((((sheafSections (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))).map f).hom)) ∧
    (∀ A : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
      PreservesFiniteLimits (pointModuleSections k A) ∧
      PreservesFiniteColimits (pointModuleSections k A) ∧
      (∀ (K L : CochainComplex (ringedSiteModules.{u + 1}
          ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ)
        (f : K ⟶ L), QuasiIso f →
        QuasiIso (((pointModuleSections k A).mapHomologicalComplex (.up ℤ)).map f)) ∧
      (∀ [HasDerivedCategory.{w} (ringedSiteModules.{u + 1}
          ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))]
        [HasDerivedCategory.{w'}
          (ModuleCat.{u + 1}
            (((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj.obj
                (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))))]
        [PreservesFiniteLimits (pointModuleSections k A)]
        [PreservesFiniteColimits (pointModuleSections k A)],
        Nonempty (Functor.CommShift (pointModuleSections k A).mapDerivedCategory ℤ) ∧
        Functor.IsTriangulated (pointModuleSections k A).mapDerivedCategory ∧
        Nonempty
          (DerivedCategory.Q ⋙ (pointModuleSections k A).mapDerivedCategory ≅
            (pointModuleSections k A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ∧
        ∀ i : ℤ, Nonempty
          ((pointModuleSections k A).mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ i ≅
            DerivedCategory.homologyFunctor _ i ⋙ pointModuleSections k A))) := by
  sorry

end AlgebraicGeometry.ProEtale
