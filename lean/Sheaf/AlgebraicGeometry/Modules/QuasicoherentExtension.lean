/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Extensions of quasi-coherent modules

Source: Stacks Project, Schemes, Lemma 01IE, applied on an affine open cover
(blueprint: lem-pc-quasi-coherent-extension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- In a short exact sequence of modules on a scheme, quasi-coherence of both end terms
implies quasi-coherence of the middle term.
Source: Stacks Project, Schemes, Lemma 01IE, and locality of quasi-coherence
(blueprint: lem-pc-quasi-coherent-extension).

Proof:
1. Restrict to an affine open cover. Restriction preserves short exact sequences and
   quasi-coherence of the end terms (lem-weil-pbc-module-restriction-open-immersion-colimits).
   Write the end terms as associated modules using the affine quasi-coherent equivalence
   (lem-weil-pbc-affine-tilde-gamma-adjunction).
2. On an affine open, let M₂ be the sections of the middle term. For a section m of M₃,
   the elements a for which a*m lifts to M₂ form an ideal. Around each prime m lifts on
   a principal open D(f). Quasi-compactness of V(f) and localization of the first term
   supply a common power of f killing the differences of local lifts, which then glue.
   Thus a power of f lies in the ideal; the ideal lies in no prime and is the unit ideal.
   This proves exactness on global sections. Form the adjunction map from the associated
   module of M₂ to the middle term. Repeat the argument on each principal open, use
   exactness of localization and the five lemma to show this map is bijective there.
   Since principal opens form a basis, it is an isomorphism. Associated modules are
   quasi-coherent (lem-weil-pbc-spec-module-tilde-sections).
3. Quasi-coherence on the affine open cover implies quasi-coherence on the scheme
   (pqf-def-coherent). -/
theorem isQuasicoherent_of_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.IsQuasicoherent := by
  sorry

end AlgebraicGeometry.Scheme.Modules
