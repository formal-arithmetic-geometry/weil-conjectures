/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.Coherent

/-! # Global lifting in an affine extension

Source: Stacks Project, Schemes, Lemma 01IE, ideal and principal-open lifting argument.
(blueprint: lem-pc-affine-extension-section-surjectivity).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The quotient map of an affine extension with quasi-coherent ends is surjective on
 global sections.
Source: Stacks Project, Schemes, Lemma 01IE (lemma-extension-quasi-coherent),
from "Pick m" to the end of its proof.
(blueprint: lem-pc-affine-extension-section-surjectivity).

Proof: For a section m of the quotient, let I be the ideal of scalars a such that a*m
lifts globally. At each prime p, local surjectivity gives a lift s on D(f) with f
outside p. At each point of V(f), choose a lift s' on D(g). The difference on D(fg)
is a section of the quasi-coherent kernel, hence a fraction in its section module.
Clear its f denominator: f^n*s glues with f^n*s' plus a kernel section on D(g).
Compactness of V(f) gives finitely many g and a common n. The differences of these
extended lifts on D(g_j*g_k) are kernel sections vanishing on D(f*g_j*g_k).
The localization description of the kernel kills all differences by a common
power of f. The corrected lifts then glue over X to a lift of f^N*m. Thus I is
contained in no prime ideal, so I is the unit ideal and m itself lifts. This proves
surjectivity, which is equivalent to being epi in ModuleCat. The zero ring and zero
end terms cause no exception: the same ideal argument or the zero-section argument
applies. No quasi-coherence of the middle term is assumed.
-/
theorem epi_globalSections_of_shortExact {R : CommRingCat.{u}}
    (S : ShortComplex (Spec R).Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    Epi ((moduleSpecΓFunctor (R := R)).map S.g) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
