module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import WeilConjectures.RingTheory.RingPseudoCoherent

/-! # Perfect tensor tests detect pseudo-coherence

Source: Stacks Project, More on Morphisms, Tag 0GES,
`lemma-characterize-pseudo-coh-improved`, followed by Tag 09UU,
`lemma-check-relative-pseudo-coherence-on-charts`, with the identity immersion
(blueprint: lem-sfb-perfect-tests-detect-pseudocoherence).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wΓ wR

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- Perfect tensor tests with pseudo-coherent derived sections over the affine base detect
absolute pseudo-coherence for a separated, flat morphism of finite presentation.
The section functor is the existing affine derived section construction, written as its
composite to retain independent localization universes for X, its section ring and R.
Source: Stacks Project, More on Morphisms, Tags 0GES and 09UU
(blueprint: lem-sfb-perfect-tests-detect-pseudocoherence).

Proof:
1. Spec R is quasi-compact and quasi-separated. Finite presentation includes
quasi-compactness and quasi-separatedness of p; permanence under composition gives that X
is quasi-compact and quasi-separated (lem-weil-pbc-affine-scheme-qcqs and
lem-weil-pbc-qcqs-morphism-permanence).
2. Each pseudo-coherent perfect tensor test is represented by a bounded-above finite free
complex, hence has eventually vanishing cohomology. Apply
lem-sfb-perfect-tensor-tests-bounded-above to obtain a bound above for K; no uniform bound
on the perfect tests is needed.
3. Apply lem-sfb-perfect-to-pseudocoherent-tensor-tests to extend the test hypothesis to
all pseudo-coherent E. Then lem-sfb-pseudocoherent-tensor-relative-criterion gives relative
pseudo-coherence of K over Spec R.
4. Apply lem-sfb-flat-ambient-relative-pseudocoherence with ambient scheme X and the
identity closed immersion. The ambient map p is flat and locally of finite presentation,
so the identity derived direct image of K, namely K, is absolutely pseudo-coherent.
No Noetherian or properness hypothesis is used. -/
theorem isPseudoCoherent_of_perfect_tensor_tests
    (R : CommRingCat.{u}) (X : Scheme.{u}) (p : X ⟶ Spec R)
    [IsSeparated p] [Flat p] [LocallyOfFinitePresentation p] [QuasiCompact p]
    [QuasiSeparated p]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{wΓ}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (hTests : ∀ E : schemeDerivedCategory X, Scheme.IsPerfect X E →
      DerivedCategory.IsPseudoCoherent
        ((schemeDerivedGlobalSections X ⋙
          (affineGlobalSectionsRestriction p).mapDerivedCategory).obj (E ⊗ K))) :
    Scheme.IsPseudoCoherent X K := by
  sorry

end AlgebraicGeometry
