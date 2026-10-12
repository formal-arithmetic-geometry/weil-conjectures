/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Subobject.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.CategoryTheory.FiniteFiltrationRefinement

/-! # A filtration with unresolved factors of smaller support

Source: Stacks Project, Tag 01YF, proof before applying support minimality.
(blueprint: lem-pc-s3-support-reduction-filtration)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The geometric step of support induction: leave smaller-support factors unresolved.
This does not assert integral-ideal filtrations for those factors.

Source: Stacks Project, Tag 01YF (`coherent.tex`, `lemma-coherent-filter`), proof,
reducible support, the J-adic filtration, and the generic ideal inclusion of Tag 01YE.
(blueprint: lem-pc-s3-support-reduction-filtration)

Proof: Finite presentation on a Noetherian scheme gives coherence and closed support S.
If S is empty, the sheaf is zero by stalk detection and use the empty chain. If S is
reducible, choose two proper closed subsets covering S. The support-union exact sequence
of Tag 01YD gives a coherent submodule and quotient supported in these two subsets.
Use the resulting two-step chain; both factors have strictly smaller closed support.
If S is irreducible, let J be the ideal of its reduced induced integral closed subscheme.
Tag 01Y9 gives J^n F = 0. The ascending chain of J-adic powers has coherent quotients Q
annihilated by J. Each Q has support contained in S. Keep a Q with proper support as an
unresolved factor. For each Q with support S, the stalk J at the generic point of S is
the ambient maximal ideal: a function vanishing at the generic point vanishes on S by
closedness of its zero locus. Tag 01YE therefore gives a monomorphism from the pushforward
of a finite direct sum of a coherent ideal on this integral closed subscheme into Q,
isomorphic near that generic point. Filter its image by the images of the partial sums.
Each quotient of this image chain is the pushforward of the ideal. Append its cokernel;
this is coherent, is supported in S, and has zero generic stalk, so has proper support.
Lift each of these chains through the epimorphism from the corresponding J-adic power
to Q and concatenate them. The abelian quotient identifications show the resulting
quotients are exactly the ideal factors or the unresolved proper-support cokernels.
All unresolved factors are finitely presented by coherence on a Noetherian scheme.
Their supports are closed, so the asserted strict inclusion also holds for closures.
This construction never filters a proper-support factor by induction. -/
theorem exists_finitePresentation_support_reduction_filtration
    (X : Scheme.{u}) [IsNoetherian X] (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c),
      c 0 = ⊥ ∧ c (Fin.last m) = ⊤ ∧
      ∀ j : Fin m,
        let Q := cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
          (hc j.castSucc_le_succ))
        (∃ (Z : Scheme.{u}) (i : Z ⟶ X),
          IsClosedImmersion i ∧ IsIntegral Z ∧
          ∃ I : Z.IdealSheafData, Nonempty (Q ≅ (pushforward i).obj I.toModules)) ∨
        (Q.IsFinitePresentation ∧
          closure {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} ⊂
            closure {x : X | ¬ Subsingleton (F.presheaf.stalk x)}) := by sorry

end AlgebraicGeometry.Scheme.Modules
