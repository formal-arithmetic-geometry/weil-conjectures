/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Concatenating coherent integral-ideal filtrations

Source: Stacks Project, Cohomology of Schemes, Lemma 01YF, induced-filtration step.
(blueprint: lem-weil-pbc-coherent-integral-filtration-extension)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Coherent integral-ideal filtrations are closed under coherent extensions.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YF, proof, the induced
filtration in the reducible-support paragraph and the last sentence.
(blueprint: lem-weil-pbc-coherent-integral-filtration-extension)

Proof: take a filtration A_0 <= ... <= A_a of S.X₁ and a filtration B_0 <= ... <= B_b
of S.X₃. Map the first chain into S.X₂ along the monomorphism S.f. Append the inverse
images of B_k under the epimorphism S.g. The two chains meet at ker S.g = im S.f.
The inverse image of B_k is the kernel of S.X₂ -> S.X₃ -> S.X₃/B_k, so is coherent
by coherent kernels and cokernels on a locally Noetherian scheme. The mapped first
chain is isomorphic to the original chain and hence coherent. Monotonicity is inherited
from the two chains; the endpoints are zero and S.X₂. Quotients in the first part are
isomorphic to A_{j+1}/A_j. Quotients in the second part are isomorphic to B_{k+1}/B_k:
the induced map is injective on stalks by the kernel description and surjective on
stalks because S.g is an epimorphism. Stalk exactness and detection of isomorphisms
identify these quotients. Compose with the given integral-ideal quotient isomorphisms.
This also works if either filtration has length zero. -/
theorem coherentIntegralFiltration_of_shortExact
    (X : Scheme.{u}) [IsLocallyNoetherian X] (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (h₁ : RingedSpace.IsCoherent X.toRingedSpace S.X₁)
    (h₂ : RingedSpace.IsCoherent X.toRingedSpace S.X₂)
    (h₃ : RingedSpace.IsCoherent X.toRingedSpace S.X₃)
    (hA : HasCoherentIntegralFiltration S.X₁)
    (hB : HasCoherentIntegralFiltration S.X₃) :
    HasCoherentIntegralFiltration S.X₂ := by sorry

end AlgebraicGeometry.Scheme.Modules
