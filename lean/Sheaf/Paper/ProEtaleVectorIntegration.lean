module

public import Sheaf.Paper.ProEtaleFrameIntegration

/-! # Pro-etale vector integration with local normalization
Source: main-20261015, vector-bundle integration; Stacks 09AF and 099R
(blueprint: def-pur-proetale-vector-integration).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)
variable (S : Scheme.{u}) [IsNoetherian S]
variable (r : ℕ)
  (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
variable (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]

set_option linter.unusedVariables false in
/-- Boundedness of the actual vector coefficient follows from the locally free Tate line.
Source: finite Tate local freeness and exact inverse image
(blueprint: def-pur-proetale-vector-integration).
Proof: each shifted line has amplitude [-2,-2]. Its d-fold tensor has amplitude
[-2d,-2d], including the zero-fold constant. Exact inverse image along pi preserves
these bounds. In particular this complex is bounded below.
-/
theorem vectorCoefficient_plus (hS : IsUnit (l : Γ(S, ⊤))) :
    DerivedCategory.TStructure.t.plus
      (Etale.vectorIntegrationCoefficient (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA S d F) := by
  sorry

/-- The actual pro-etale compact-support source, at the canonical Nagata compactification.
Source: vector-bundle integration (blueprint: def-pur-proetale-vector-integration). -/
abbrev vectorSource :=
  (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (Etale.vectorBundlePurityCompactification S d F)).obj
      ((comparison (Scheme.finiteTateCoefficient l E n) _).obj
        (Etale.vectorIntegrationCoefficient _ (l ^ (r + 1)) hA S d F))

/-- Canonical compact-support comparison: proper counit mate after exact open extension.
Source: Stacks 09AF and 099R (blueprint: def-pur-proetale-vector-integration). -/
@[irreducible]
def vectorSite (hS : IsUnit (l : Γ(S, ⊤))) :
    vectorSource l E n S r hA d F ≅
      (comparison (Scheme.finiteTateCoefficient l E n) S).obj
        (Etale.vectorIntegrationSource _ (l ^ (r + 1)) hA S d F) :=
  (compactSupportSiteComparison (Scheme.finiteTateCoefficient l E n)
    (Etale.vectorBundlePurityCompactification S d F)).app
      ⟨_, vectorCoefficient_plus l E n S r hA d F hS⟩

/-- Every frame restriction equals the independently formed ordered pro-etale trace.
The canonical comparison only identifies the source of the chart exchange; it contains
no integration morphism. Source: blueprint vector-bundle integration, a_i
(blueprint: def-pur-proetale-vector-integration). -/
@[irreducible]
def VectorNormalization (hS : IsUnit (l : Γ(S, ⊤)))
    (t : vectorSource l E n S r hA d F ⟶ unit (Scheme.finiteTateCoefficient l E n) S) :
    Prop :=
  ∀ (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V),
    (upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) V.ι).leftDerivedFunctor.map
         t ≫
      (pullbackUnit (Scheme.finiteTateCoefficient l E n) V.ι).hom =
    (upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) V.ι).leftDerivedFunctor.map
         (vectorSite l E n S r hA d F hS).hom ≫
      (pullback (Scheme.finiteTateCoefficient l E n) V.ι).inv.app _ ≫
        localIntegration l E n S hS r hA d F V e

/-- The local maps agree on overlaps and glue uniquely as degree-zero sheaf maps.
Source: blueprint vector-bundle integration; Stacks 06XS and 03EM
(blueprint: def-pur-proetale-vector-integration).
Proof: compare each coordinate's open counit and proper trace under the canonical
mate. Induct on the ordered coordinates using the composite-counit formula. Under
site comparison these are the ordinary normalized affine traces; linear invariance
makes their restrictions agree on overlaps. The compact-support source has no
cohomology outside degree zero on a frame cover, so the same is true globally.
The target is also degree zero. The degree-zero embedding is fully faithful, so
sheaf-Hom gluing gives existence and uniqueness. Rank zero uses the identity trace;
for the empty base the unique sheaf morphism supplies the same conclusion.
-/
theorem existsUniqueVectorIntegration (hS : IsUnit (l : Γ(S, ⊤))) :
    ∃! t : vectorSource l E n S r hA d F ⟶ unit (Scheme.finiteTateCoefficient l E n) S,
      VectorNormalization l E n S r hA d F hS t := by
  sorry

/-- The unique glued morphism with the specified local integration formulas.
Source: blueprint vector-bundle integration
(blueprint: def-pur-proetale-vector-integration). -/
@[irreducible]
def vectorIntegration (hS : IsUnit (l : Γ(S, ⊤))) :
    vectorSource l E n S r hA d F ⟶ unit (Scheme.finiteTateCoefficient l E n) S :=
  (existsUniqueVectorIntegration l E n S r hA d F hS).exists.choose


end AlgebraicGeometry.ProEtale.VectorIntegrationSite
