/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StalkComparisonSourceTransport

/-! # Naturality of the localized comparison into derived pullback

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-stalk-comparison-pullback-naturality).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- The comparison with the cohomology of the canonical derived pullback.
Its construction uses the invertible pullback counit on the representative, the
specified tensor-stalk isomorphism, and the localization comparison; no target
complex or morphism to a target is involved. -/
def comparisonIntoPullback (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (i : ℤ) :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  letI := hP
  (cohomologyModel f f' g g' sq z P).localizedComparison i ≫
    HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
    (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv ≫
    (comparisonStalkCohomology X' z i).map
      (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))

/-- The comparison into derived pullback is natural for derived isomorphisms of
K-flat sheaf representatives, using any tensor-algebra lift of the specified
underlying cohomology transport.

Proof: stalk K-flatness follows from the K-flat stalk criterion. Ordinary extension
from A to C therefore computes derived extension on each stalk representative.
The derived stalk of sheaf pullback identifies with this derived extension: on
complexes this is tensorStalkIso, and the two universal derived counits determine
the identification on the localized category. The transformation from base-derived
tensor to A-derived extension is induced by scalar extension and tensor
associativity. Its naturality holds on complexes and descends through localization;
thus it holds for the derived isomorphism a, without choosing a chain map for a.
Apply cohomology and use the counit-compatible comparison between the two base
derived tensor functors. The equations comparison_eq identify their cohomology
comparisons with these counits, and localized_eq transposes these comparisons
through extension/restriction adjunction. Naturality of tensorStalkIso and the
homology localization factors then gives the displayed equation. Faithfulness of
restriction to B identifies the given e with the tensor-algebra transport. Extend
e to C; functoriality of extension and the preceding adjunction equation yield
exactly the square below. No isomorphism assertion about localizedComparison is
used, and no flatness over R or Tor-independence of the square is required.
Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8; Cohomology,
Tag 06YB (K-flat stalks), and Tag 06Y6 (derived tensor functoriality).
(blueprint: lem-pc-stalk-comparison-pullback-naturality). -/
theorem comparisonIntoPullback_naturality (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlat) (hQ : Q.IsKFlat)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    ∀ e : (cohomologyModel f f' g g' sq z P).cohomology i ≅
        (cohomologyModel f f' g g' sq z Q).cohomology i,
      (ModuleCat.restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map e.hom =
        (comparisonSourceUnderlyingIso f f' g g' sq z P Q a i).hom →
      comparisonIntoPullback f f' g g' sq z P hcP i ≫
        (comparisonStalkCohomology X' z i).map ((derivedPullback g').map a.hom) =
      (ModuleCat.extendScalars.{u, u, u}
        (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z))).map e.hom ≫
        comparisonIntoPullback f f' g g' sq z Q hcQ i := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
