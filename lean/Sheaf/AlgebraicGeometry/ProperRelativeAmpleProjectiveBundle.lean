/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple
import Sheaf.TraceFormula.ProjectiveBundleSeparated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Proper relatively ample morphisms are projective in the projective-bundle sense

Source: Stacks Project, Morphisms, Tag 0BCL(1), with Definitions 01VH, 01VW(1), 01W8(1)
(blueprint: lem-sfb-proper-relative-ample-projective-bundle).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper morphism to a quasi-compact quasi-separated scheme that admits a relatively
ample invertible module is projective in the finite-type quasi-coherent projective-bundle
sense. Relative ampleness means quasi-compactness and absolute ampleness after restriction
to the inverse image of every affine open of the base. The existential proof of
invertibility of each restriction only supplies the proof argument of `IsAmple`.

Source: Stacks Project, Morphisms, Tag 0BCL(1), Definitions 01VH, 01VW(1), 01W8(1)
(blueprint: lem-sfb-proper-relative-ample-projective-bundle).

Proof, following the five steps of the node:
1. Properness includes local finite type, and universal closedness gives quasi-compactness
   (def-weil-proper-morphism, def-weil-finite-type-morphism). Thus h is of finite type.
2. Apply lem-trf-relative-ample-very-ample over the quasi-compact base to obtain n >= 1
   with N = L.tensorPow n relatively very ample. By def-trf-relatively-very-ample, N is
   invertible. This step imposes no finite-type condition on the ambient module.
3. Apply lem-sfb-very-ample-finite-type-realization, using finite type of h and the qcqs
   base, to obtain a finite-type quasi-coherent module E and an immersion r into P(E)
   over S. This is finite-type approximation, without a Noetherian or local-freeness
   hypothesis.
4. By lem-trf-projective-bundle-separated, the structure morphism pi_E is separated.
   Since r followed by pi_E is the proper morphism h,
   lemma-nagata-proper-to-separated-target makes r proper.
5. By lem-weil-pbc-proper-immersion-closed, the proper immersion r is a closed immersion.
   Its factorization of h through P(E) is precisely def-trf-projective-bundle-morphism. -/
theorem isProjectiveBundle_of_isProper_of_relative_ample
    {X S : Scheme.{u}} (h : X ⟶ S) [IsProper h]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (hample : ∃ L : X.Modules, L.IsInvertible ∧ QuasiCompact h ∧
      ∀ V : S.Opens, IsAffineOpen V →
        ∃ hL : ((Scheme.Modules.tensorPullback (h ⁻¹ᵁ V).ι).obj L).IsInvertible,
          @Scheme.Modules.IsAmple (h ⁻¹ᵁ V).toScheme
            ((Scheme.Modules.tensorPullback (h ⁻¹ᵁ V).ι).obj L) hL) :
    IsProjectiveBundle h := by
  obtain ⟨L, hL, hqc, hample⟩ := hample
  have : L.IsInvertible := hL
  obtain ⟨n, _, hn⟩ :=
    (Scheme.Modules.relative_ample_very_ample h L).1.1.mp ⟨hqc, hample⟩
  obtain ⟨E, hE, hfinite, D, r, hr, hcomp, _⟩ :=
    Scheme.Modules.veryAmple_finiteType_realization h (L.tensorPow n) hn
  have : E.IsQuasicoherent := hE
  have : IsImmersion r := hr
  have : IsSeparated
      (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom :=
    isSeparated_projectiveBundle E
  have : IsProper
      (r ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom) := by
    rw [hcomp]
    infer_instance
  have : IsProper r := IsProper.of_comp r
    (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom
  exact ⟨E, hE, hfinite, r,
    IsClosedImmersion.of_isPreimmersion r r.isClosedMap.isClosed_range, hcomp⟩

end AlgebraicGeometry
