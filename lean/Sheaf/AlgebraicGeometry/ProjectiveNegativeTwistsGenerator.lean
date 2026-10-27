module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDerivedHom
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import WeilConjectures.AlgebraicGeometry.GlobalHomShiftedHypercohomology
import WeilConjectures.AlgebraicGeometry.Ample

/-! # A finite sum of negative twists generates the projective-space derived category

Source: Stacks Project, perfect.tex, Tag 0A9V, lemma-generator-P1
(blueprint: lem-sfb-projective-negative-twists-generator).

The generator is the degree-zero finite coproduct of the twists O(-i), 0 <= i <= n.
The weak-generator criterion is stated in the ambient derived category, restricting
its test objects to the full subcategory with quasi-coherent cohomology. This avoids
requiring a separate triangulated-category structure on that full subcategory.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace

/-- The finite sum O + O(-1) + ... + O(-n), placed in degree zero.
Source: Stacks Project, perfect.tex, Tag 0A9V, lemma-generator-P1
(blueprint: lem-sfb-projective-negative-twists-generator).
The homogeneous coordinate type is `ULift (Fin (n + 1))`, so the underlying scheme
is projective n-space over A, in the shared base-change model of projective space. -/
noncomputable def negativeTwistsGenerator (A : Type u) [CommRing A] (n : ℕ)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))).toRingedSpace))] :
    schemeDerivedCategory (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))) :=
  (DerivedCategory.singleFunctor (SheafOfModules.{u}
    (moduleRings (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))).toRingedSpace)) 0).obj
      (∐ fun i : Fin (n + 1) ↦
        (twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)) (-(i.val : ℤ)) :
          SheafOfModules.{u}
            (moduleRings (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))).toRingedSpace)))

/-- The finite negative-twist sum detects zero among all unbounded complexes with
quasi-coherent cohomology, the weak-generator criterion of `IsWeakTriangulatedGenerator`
restricted to the full quasi-coherent subcategory.
Source: Stacks Project, perfect.tex, Tag 0A9V, lemma-generator-P1
(blueprint: lem-sfb-projective-negative-twists-generator).

Proof: Each twist is invertible, hence quasi-coherent; finite direct sums preserve
quasi-coherence, and a degree-zero single has only that sheaf as nonzero cohomology.
This puts the finite sum in the quasi-coherent derived subcategory.
Fix K orthogonal to every shift of the finite sum. The shift-stable left
orthogonal is strictly full and triangulated (lem-sf-shift-stable-left-orthogonal).
Each summand O(-i), 0 <= i <= n, is orthogonal by its inclusion and projection;
finite sums of orthogonal objects remain orthogonal. For m >= n+1, apply the exact
coordinate Koszul sequence at a = -m (lem-sfb-projective-coordinate-koszul-sequence).
Deleting its first term gives a bounded complex representing O(-m), with terms
O(-m+j), 1 <= j <= n+1. Strong induction and bounded-complex triangulated devissage
(lem-weil-pbc-bounded-complex-triangulated-devissage) put O(-m) in the orthogonal.
The line-bundle dual is O(m), by its transition functions; finite locally free derived
Hom (lem-sc-finite-locally-free-derived-hom), unbounded perfect duality
(lem-sfb-ringed-site-perfect-duality), global derived Hom (lem-pur-rhom-global-sections)
and the shift identification (lem-sc-global-hom-shifted-hypercohomology) give
Hom(O(-m), K[q]) = H^q(X, K tensor O(m)). Thus all these groups vanish for m >= 0.
The coordinate sections of O(1) have the standard affine opens as nonvanishing loci,
so O(1) is ample (def-weil-pbc-ample-invertible-module). Ample-twist detection
(lem-sfb-ample-twist-hypercohomology-detection) forces K to be zero, as required
by def-pc-generators. This includes n = 0, the zero ring, and unbounded K. -/
theorem negativeTwistsGenerator_isWeakGenerator (A : Type u) [CommRing A] (n : ℕ)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))).toRingedSpace))]
    : schemeDerivedQCohProperty (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A)))
        (negativeTwistsGenerator A n) ∧
      ∀ K : schemeDerivedQCohCategory (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))),
        (∀ q : ℤ, Subsingleton (negativeTwistsGenerator A n ⟶ K.obj⟦q⟧)) →
          IsZero K.obj := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
