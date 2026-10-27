module

public import Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
import Sheaf.AlgebraicGeometry.StackQcqsMorphism
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit

/-! # Adequate algebra maps and adequately affine direct image

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Lemma 4.1.7, proof of (2) implies (1), printed pp. 17--18
(blueprint: lem-sfb-adequate-algebra-pushforward).

Universal adequacy of the input algebra map is the existing direct-image predicate
for the identity of the source stack. Its value at T → X is the compatible-section
ring on X ×_X T, canonically the section ring of the algebra on T. This uses the
same smooth tests, étale covers and positive exponents as the conclusion.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- An adequately affine morphism preserves universal adequacy of arbitrary
quasi-coherent algebra maps. No surjectivity, injectivity, finite generation or
Noetherian hypothesis is imposed on the input map or stacks.

Source: Alper, Lemma 4.1.7, implication (2) implies (1), printed pp. 17--18
(blueprint: lem-sfb-adequate-algebra-pushforward).

Proof: factor the algebra map through its smooth-test image C using
lem-sfb-stack-algebra-smooth-image, as a surjection q followed by an injection j.
Universal adequacy passes from the composite to j by applying q to each power
lift. Adequate affineness gives universal adequacy of f_*q. For f_*j, work first
over an affine smooth test V of the target. The stack X ×_Y V is algebraic and
quasi-compact, by lem-sfb-algebraic-stack-fibre-products and the quasi-compactness
clause of def-sfb-stack-qcqs-morphism. Choose a quasi-compact smooth scheme atlas
using lem-sfb-algebraic-stack-quasicompact-surjection. Its composite to X is smooth
by lem-sfb-stack-smooth-permanence. Lift powers on this atlas by adequacy of j.
Use lem-weil-pbc-etale-covering-sieve-finite-affine-refinement to replace the
resulting étale covering by a finite affine refinement. Multiply its positive
exponents and raise the local lifts to obtain one exponent on all members. If
the cover is empty, take exponent one. On every overlap the two lifts have the
same image, so smooth-test injectivity of j makes them equal. Smoothness of these
overlaps follows from lem-sfb-stack-smooth-permanence and the étale-implies-smooth
clause of def-sbc-smooth-morphisms. Descend the lifts by
lem-sfb-smooth-cover-section-descent. The direct-image section formula identifies
the descended lift with a power lift over V. Cover arbitrary smooth tests by
affine opens. Finally compose the étale local lifts for f_*j and f_*q, multiplying
their positive exponents; def-weil-pbc-sites-and-cohomology supplies composition
of the covering families. This is the required universal adequacy of f_*u. -/
theorem isUniversallyAdequateModuliDirectImage_of_isAdequatelyAffine
    {k : Type u} [Field k]
    {X : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {Y : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    (f : BasedFunctor X Y) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y)
    (hf : IsAdequatelyAffineMorphism f hX hY)
    {A B : ModuliAlgebraSheaf X hX.1.1} (u : A ⟶ B)
    (hA : IsQuasicoherentModuliAlgebra A) (hB : IsQuasicoherentModuliAlgebra B)
    (hu : IsUniversallyAdequateModuliDirectImage (BasedFunctor.id X) u) :
    IsUniversallyAdequateModuliDirectImage f u := by
  sorry

end CategoryTheory
