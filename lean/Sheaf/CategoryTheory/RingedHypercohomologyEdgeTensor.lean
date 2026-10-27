module

public import Sheaf.CategoryTheory.RingedSiteModuleCupProduct
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.KFlatMapFactorization
import Sheaf.Paper.ModuleCupShiftedUnitTensor

/-! # Tensor compatibility of the ringed hypercohomology edge

Source: Stacks Project, Cohomology on Sites, Tags 0BKV and 0FPK
(blueprint: lem-sfb-ringed-hypercohomology-edge-tensor).

## Main statements
- `hypercohomologyEdge_existsUnique`: the natural edge, normalized on every K-injective model.
- `hypercohomologyEdge_tensor`: the tensor-of-cocycles compatibility for arbitrary derived objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace SheafOfModules.RingedSiteCup

/-- The edge sends a global cocycle to its sheaf cohomology class, on every K-injective
representative. Here `z` is a cycle in the complex of global sections, and `s` is the
same compatible family as a section of the cycle sheaf. The equality involving
`iCycles` expresses precisely that they are the same cocycle. Global sections preserves
kernels, so each `z` has a unique such `s`.
Source: Stacks Project, Tag 0BKV, kernel/quotient description
(blueprint: lem-sfb-ringed-hypercohomology-edge-tensor). -/
def HypercohomologyEdgeSpec (X : RingedTensorCorner.{u, w}) (n : ℤ)
    (e : derivedGlobalSections X ⋙ scalarCohomology X n ⟶
      cohomology X n ⋙ globalSections X) : Prop :=
  ∀ (I : CochainComplex X.mateModules ℤ) (_hI : I.IsKInjective)
    (z : (((globalSections X).mapHomologicalComplex (.up ℤ)).obj I).cycles n)
    (s : (globalSections X).obj (I.cycles n)),
    (((globalSections X).mapHomologicalComplex (.up ℤ)).obj I).iCycles n z =
        (globalSections X).map (I.iCycles n) s →
      e.app (DerivedCategory.Q.obj I)
          ((scalarCohomology X n).map ((globalDerivedUnit X).app I)
            ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (scalars X)) n).inv.app
              (((globalSections X).mapHomologicalComplex (.up ℤ)).obj I)
                ((((globalSections X).mapHomologicalComplex (.up ℤ)).obj I).homologyπ n z))) =
        (globalSections X).map
          (I.homologyπ n ≫ (representativeCohomology X I n).hom) s

/-- There is a unique natural, representative-independent edge with the cocycle formula.
Source: Stacks Project, Tag 0BKV and Derived Categories, Tag 070I
(blueprint: lem-sfb-ringed-hypercohomology-edge-tensor).

Proof: for any complex M, send a global cycle to its image under cycles(M) to H(M).
The image of a global boundary is zero, hence the map descends to H(ΓM).
For a chain map v both routes send [z] to [v(z)], proving naturality; a homotopy
changes v(z) by d(h(z)), hence changes neither class. Choose K-injective models
using prop-pur-kinjective-resolutions-exist. They compute RΓ by
 def-pur-ringed-site-zeroth-hypercohomology in every degree. The bijection
lem-weil-pbc-kinjective-hom-derived represents every derived map by a chain map,
uniquely up to homotopy. Thus the maps descend to the asserted natural transformation,
independent of the model. On a K-injective model the derived unit is invertible,
and the homology projection from global cycles is surjective, so the displayed
normalization determines each component uniquely. Every derived object has such
a model, proving uniqueness of the natural transformation. -/
theorem hypercohomologyEdge_existsUnique (X : RingedTensorCorner.{u, w}) (n : ℤ) :
    ∃! e : derivedGlobalSections X ⋙ scalarCohomology X n ⟶
        cohomology X n ⋙ globalSections X,
      HypercohomologyEdgeSpec X n e := by
  sorry

/-- The edge e in every integer degree, selected by its unique cocycle normalization.
It is a natural transformation on the unbounded derived category, so its components
are natural for every derived morphism.
Source: Stacks Project, Tag 0BKV
(blueprint: lem-sfb-ringed-hypercohomology-edge-tensor). -/
def hypercohomologyEdge (X : RingedTensorCorner.{u, w}) (n : ℤ) :
    derivedGlobalSections X ⋙ scalarCohomology X n ⟶
      cohomology X n ⋙ globalSections X :=
  Classical.choose (hypercohomologyEdge_existsUnique X n)

/-- The edge takes the global derived cup of two classes to the sheaf tensor of their
edge classes, followed by κ. A global section is an O-linear map O to its module;
therefore the inverse left unitor followed by the tensor of those maps is exactly
the canonical tensor-of-global-sections map, without a final object of the site.
Source: Stacks Project, Tags 0BKV, 0G7D and 0FPK
(blueprint: lem-sfb-ringed-hypercohomology-edge-tensor).

Proof: choose K-injective models I,J of K,L and global cocycles z,w for x,y.
The shifted-unit map O[-a] to I defined by z has flat terms and is K-flat.
By lem-pur-kflat-map-factorization it factors up to homotopy through a flat-term
K-flat model P quasi-isomorphic to I. The lifted unit gives a global cycle in P
mapping to z modulo a global boundary. Repeat for w to obtain Q. By
lem-weil-pbc-site-derived-tensor-descent, Tot(P tensor Q) represents K tensor-derived L.
Apply lem-sfb-ringed-derived-naive-cup-comparison to Γ and P,Q. The derived cup
is the image under the derived unit of the (a,b) tensor summand of the two lifted
cycles. This remains true even if ΓP and ΓQ are not K-flat: apply
lem-sc-module-cup-shifted-unit-tensor to the two actual shifted free A-module maps;
its normalization gives the tensor summand with no sign. The edge normalization
on a K-injective resolution of Tot(P tensor Q), and naturality of the elementary
cycle-to-sheaf-class map, send this cup to that summand's sheaf class. On the
other route, def-sfb-ringed-site-module-cup-product defines κ on P,Q by the same
local tensor of cocycles. The two global sections therefore have equal values
at every site object. The Leibniz identity makes their tensor a cycle; changing
either lift by a boundary changes the tensor by a boundary, with sign (-1)^a
for a boundary in the second factor. This proves the equality without boundedness,
flatness of K or L, or quasi-coherence. -/
theorem hypercohomologyEdge_tensor (X : RingedTensorCorner.{u, w}) (b : RingedTensorModel X)
    (K L : X.mateDerived) (a d : ℕ)
    (x : (scalarCohomology X (a : ℤ)).obj ((derivedGlobalSections X).obj K))
    (y : (scalarCohomology X (d : ℤ)).obj ((derivedGlobalSections X).obj L)) :
    (hypercohomologyEdge X ((a : ℤ) + (d : ℤ))).app (X.tensor.obj (K, L))
        ((scalarCohomology X ((a : ℤ) + (d : ℤ))).map (global X b K L)
          ((scalarPairing X ((derivedGlobalSections X).obj K)
            ((derivedGlobalSections X).obj L) (a : ℤ) (d : ℤ))
              (TensorProduct.tmul (scalars X) x y))) =
      (λ_ (SheafOfModules.unit
        ((sheafCompose X.topology (forget₂ CommRingCat RingCat)).obj X.ring))).inv ≫
          (((hypercohomologyEdge X (a : ℤ)).app K x) ⊗ₘ
            ((hypercohomologyEdge X (d : ℤ)).app L y)) ≫
          cohomologyPairing X b K L (a : ℤ) (d : ℤ) := by
  sorry

end SheafOfModules.RingedSiteCup
