/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleMorphism
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import WeilConjectures.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra

/-!
# Finite morphisms are projective in the projective-bundle sense

Source: Stacks Project, Morphisms, Lemma 29.43.2 (Tag 0B3I) and
Definition 29.43.1 (Tag 01W8), clause (1)
(blueprint: lem-trf-finite-projective-bundle).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every finite morphism is projective in the projective-bundle convention.
Source: Stacks Project, Morphisms, Lemma 29.43.2 (Tag 0B3I), with projectivity as in
Definition 29.43.1 (Tag 01W8), clause (1)
(blueprint: lem-trf-finite-projective-bundle).

Proof:
1. Set E = h_* O_T, a finite-type quasi-coherent O_S-algebra by
   [def-weil-finite-integral-morphism]. On every affine Spec R in S its inverse image
   is Spec A, with A finite over R. We seek the closed immersion into P_S(E) required
   by [def-trf-projective-bundle-morphism].
2. Form the graded sheaf algebra B with B_0 = O_S and B_n = E for n positive.
   Positive-degree multiplication is a[m] b[n] = (ab)[m+n]; degree zero acts by the
   algebra structure. The algebra axioms and restriction compatibility follow from E
   [def-weil-pbc-graded-sheaf-structures]. Its underlying module is the coproduct of O_S
   and the positive copies of E, hence is quasi-coherent by
   [lem-weil-pbc-quasi-coherent-module-coproduct-closure]. The affine tilde equivalence
   [lem-weil-pbc-affine-tilde-gamma-adjunction] identifies its affine sections with
   C = R plus the sum of A[n] for n positive. Let t = 1_A[1].
3. The identity E to B_1 extends to a graded surjection Sym(E) to B by
   [lem-weil-pbc-quasi-coherent-symmetric-algebra] and
   [lem-weil-pbc-symmetric-algebra-graded]. Degree zero is the identity, and a[n] is
   the image of j(a) j(1)^(n-1) for n positive. Both are quasi-coherent algebras
   [def-weil-pbc-quasi-coherent-algebra], so their relative Proj schemes are defined
   [def-nagata-relative-proj]. The surjective-map clause of
   [prop-nagata-relative-proj-functoriality] gives a closed immersion Proj_S(B) into P_S(E).
4. On an affine base, every positive homogeneous element satisfies
   a[n]^2 = t (a^2)[2n-1]. A homogeneous prime containing t therefore contains every
   positive-degree element, hence the irrelevant ideal, and is excluded by
   [def-pc-proj]. Thus Proj(C) is the single standard open D_+(t), which is the spectrum
   of its degree-zero homogeneous localization by [prop-nagata-proj-standard-open].
5. Using [def-nagata-homogeneous-localization-degree-zero], every degree-zero fraction
   has the form a[m]/t^m for m positive: multiply a degree-zero numerator by t first.
   Send this fraction to a. Multiplication by t on positive degrees preserves its
   coefficient, so equality of fractions is exactly equality of coefficients. The
   inverse sends a to a[1]/t. The sum and product formulas give inverse R-algebra maps;
   the structure map is R to A. By [def-weil-affine-spectrum] this chart is Spec A
   over Spec R. The same calculation includes A = 0 and the empty spectra.
6. The affine identifications respect restriction, by the coefficient formula and
   [prop-nagata-relative-proj-functoriality]. Glue them and their inverses using
   [lem-weil-pbc-scheme-morphism-gluing]; uniqueness shows their composites are identities.
   This gives T isomorphic over S to Proj_S(B). Compose with Step 3's closed immersion;
   closed immersions remain closed immersions after precomposition with an isomorphism
   [def-weil-closed-immersion]. The finite-type quasi-coherent E from Step 1 is the
   witness in [def-trf-projective-bundle-morphism]. -/
theorem isProjectiveBundle_of_isFinite {T S : Scheme.{u}} (h : T ⟶ S) [IsFinite h] :
    IsProjectiveBundle h := by
  sorry

end AlgebraicGeometry
