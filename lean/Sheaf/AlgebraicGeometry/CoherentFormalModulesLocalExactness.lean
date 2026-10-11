/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Restriction and local exactness of coherent formal modules

Source: Stacks Project, Cohomology of Schemes, Lemma 087X, parts (2) and (3)
(blueprint: lem-weil-pbc-coherent-formal-modules-local-exactness).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Restriction is the additive functor whose underlying inverse systems and maps are
termwise restrictions. It preserves short exact sequences, and exactness and short
exactness are detected on every open covering. The auxiliary `hz` supplies the proof
of zero preservation needed to form the mapped short complexes, without any new hypothesis.
The witness `hN` states that every open subscheme is Noetherian; `I.comap U.ι` is the restricted
quasi-coherent ideal. The abelian structure is supplied by `coherentFormalModule_abelian`.
Source: Stacks Project, Lemma 087X (2)--(3)
(blueprint: lem-weil-pbc-coherent-formal-modules-local-exactness).

Proof:
1. Opens of a Noetherian scheme are Noetherian (pqf-def-locnoeth). Restriction preserves
coherence, ideal powers and their quotient maps by module-restriction-open-immersion-colimits,
coherent-module-local-on-open-cover and ideal-times-quasi-coherent-affine-sections.
Thus restricting objects and compatible maps gives the indicated additive functors.
2. Cokernels are termwise by coherent-formal-modules-abelian and commute with restriction.
For kernels use coherent-formal-module-kernel: sectionwise kernels, locally generated
images and ideal products commute with restriction, as do quotients. The stabilization
bound on X works on every open; any alternative bound gives the same eventual system.
3. Consequently restriction preserves kernel and cokernel universal properties, and
therefore short exactness and exactness at the middle object (def-weil-pbc-exact-sequence).
4. Conversely factor the first arrow through the kernel of the second. Local exactness
makes these factors epi by abelian-exact-iff-epi-kernel-lift. Their cokernel restricts to
zero everywhere, hence is zero by coherent-formal-modules-isomorphism-local. The factor
is epi globally, giving exactness by the same abelian criterion.
5. Apply locality also at the two ends of the five-term sequence, where exactness is
respectively monicity and epicity, to obtain the short exactness equivalence. -/
theorem coherentFormalModules_local_exactness (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) :
    ∃ (hN : ∀ U : X.Opens, IsNoetherian U.toScheme)
      (ρ : ∀ U : X.Opens,
        CoherentFormalModule X I ⥤
          @CoherentFormalModule U.toScheme (hN U) (I.comap U.ι))
      (hz : ∀ U : X.Opens, (ρ U).PreservesZeroMorphisms),
      (∀ U : X.Opens, (ρ U).Additive ∧
        ρ U ⋙ (IsCoherentFormalModule (I.comap U.ι)).ι =
          (IsCoherentFormalModule I).ι ⋙
            (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
              (Scheme.Modules.restrictFunctor U.ι) ∧
        ∀ S : ShortComplex (CoherentFormalModule X I), S.ShortExact →
          (@ShortComplex.map _ _ _ _ _ _ S (ρ U) (hz U)).ShortExact) ∧
      (∀ (J : Type v) (U : J → X.Opens), iSup U = ⊤ →
        ∀ S : ShortComplex (CoherentFormalModule X I),
          (S.Exact ↔ ∀ j : J,
            (@ShortComplex.map _ _ _ _ _ _ S (ρ (U j)) (hz (U j))).Exact) ∧
          (S.ShortExact ↔ ∀ j : J,
            (@ShortComplex.map _ _ _ _ _ _ S (ρ (U j)) (hz (U j))).ShortExact)) := by
  sorry

end AlgebraicGeometry
