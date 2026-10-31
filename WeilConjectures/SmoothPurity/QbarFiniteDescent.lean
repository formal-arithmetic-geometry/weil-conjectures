/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility
public import WeilConjectures.AlgebraicGeometry.FiniteCohomologicalDimensionHypothesis
public import Mathlib.CategoryTheory.PathCategory.Basic

import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import WeilConjectures.AlgebraicGeometry.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ScalarSixCompactSupport
import WeilConjectures.SixFunctors.ScalarSixPullback

/-!
# Finite coefficient descent of diagrams and scalar comparisons

Source: latest blueprint, sec-smooth-purity/sk-thm-sp-qbar/sk-thm-sp-qbar-descent.md,
clauses (1)--(3), and its proof (blueprint: det-sp-qbar-finite-descent).

The categories are the full bounded constructible subcategories of the ordinary
uncompleted module derived categories. Hom-colimit bijectivity is expressed by
surjectivity on representatives and eventual equality at a common finite stage.
The shifted target is T(L[q]), canonically (TL)[q] by exact scalar extension.
A finite graph diagram is a functor from its free path category; finitely many
specified parallel path pairs encode exactly the requested composite equalities.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The shifted Hom-colimit bijection, in representative and eventual-equality form.
Source: latest blueprint, sk-thm-sp-qbar-descent.md (1)
(blueprint: det-sp-qbar-finite-descent).

Proof: apply finiteCoefficientDescentTwoColimit (2) with C = K, D = L and r = q.
The bounded constructible categories are full, so their morphisms, identities and
composition agree with those of the ambient ordinary derived categories. Scalar
extension preserves bounded constructibility and shifts. Thus the ambient Hom
bijection is exactly the asserted full-subcategory Hom bijection, including shifts.
-/
theorem qbarFiniteDescentHom
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (T : Over (Spec (.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K L : BoundedConstructible (padicSubfieldRingObj T.left ℓ E)) (q : ℤ) :
    (∀ ψ : (derivedExtendScalarsToPadicAlgCl T.left ℓ E).obj K.obj ⟶
        (derivedExtendScalarsToPadicAlgCl T.left ℓ E).obj (L.obj⟦q⟧),
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
        (a : (derivedExtendScalarsSubfield T.left ℓ h).obj K.obj ⟶
          (derivedExtendScalarsSubfield T.left ℓ h).obj (L.obj⟦q⟧)),
        finiteDescentDerivedHomToAlgCl T.left ℓ h a = ψ) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (i : E ≤ G)
      (a : (derivedExtendScalarsSubfield T.left ℓ h).obj K.obj ⟶
        (derivedExtendScalarsSubfield T.left ℓ h).obj (L.obj⟦q⟧))
      (b : (derivedExtendScalarsSubfield T.left ℓ i).obj K.obj ⟶
        (derivedExtendScalarsSubfield T.left ℓ i).obj (L.obj⟦q⟧)),
      finiteDescentDerivedHomToAlgCl T.left ℓ h a =
        finiteDescentDerivedHomToAlgCl T.left ℓ i b →
      ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (j : F ≤ H) (s : G ≤ H),
        finiteDescentDerivedHomTransition T.left ℓ h j a =
          finiteDescentDerivedHomTransition T.left ℓ i s b) := by
  sorry

/-- A finite graph with finitely many specified composite relations descends,
with its object isomorphisms and all arrow compatibilities, above any prescribed E.
Source: latest blueprint, sk-thm-sp-qbar-descent.md (2)
(blueprint: det-sp-qbar-finite-descent).

Proof: descend each vertex by finiteCoefficientDescentTwoColimit (3), then take a
compositum of its finitely many fields and E. Scalar transitivity identifies the
extended vertex models with the original objects. Conjugate each generating arrow
by those vertex isomorphisms, and use the q = 0 Hom surjectivity to descend it.
Take another common finite upper bound for these finitely many fields. Each
specified relation is a pair of parallel finite paths, including empty paths.
Its two descended composites become equal over the closure, so Hom injectivity
makes them equal at some later finite stage. Take the compositum of these finitely
many stages. Scalar functors preserve composition, identities and equalities, so
all relations hold there. The vertex isomorphisms extend naturally to every path.
For empty vertex, arrow or relation sets the same construction starts with E.
-/
theorem qbarFiniteDiagramDescent
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (T : Over (Spec (.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (V : Type v) [Quiver.{w} V] [Finite V] [∀ a b : V, Finite (a ⟶ b)]
    (D : Paths V ⥤ BoundedConstructible (padicAlgClRingObj T.left ℓ))
    (R : Type z) [Finite R] (s t : R → Paths V)
    (lhs rhs : ∀ r : R, s r ⟶ t r)
    (hrel : ∀ r : R, D.map (lhs r) = D.map (rhs r)) :
    ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (_h : E ≤ F)
      (D_F : Paths V ⥤ BoundedConstructible (padicSubfieldRingObj T.left ℓ F)),
      (∀ r : R, D_F.map (lhs r) = D_F.map (rhs r)) ∧
        Nonempty (D_F ⋙ constructibleToPadicAlgCl T.left ℓ F ≅ D) := by
  sorry

/-- Natural scalar comparisons for compact support and pullback, with finite
ell-cohomological dimension assumed only in this third clause.
Source: latest blueprint, sk-thm-sp-qbar-descent.md (3), with the standing finite-CD
hypothesis of det-prop-scalar-six-compact-support (blueprint: det-sp-qbar-finite-descent).

Proof: rational Dctf equals Dbc, so every stated input has the required finite Tor
amplitude. The pullback comparison is scalar-six-pullback (1). For compact support
use the chosen compactification f = p j, with its middle scheme still in the
standing setting. Scalar-six-compact-support identifies extension of Rp_* j_! with
Rp_* of the extension of j_!, then with Rp_* j_! of the extended input, by the
proper coefficient comparison and exact extension by zero. This canonical composite
is an isomorphism independent of compactification. Its naturality, and the naturality
of the pullback comparison, give the two displayed natural isomorphisms.
-/
theorem qbarFiniteDescentOperations
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hcd : BaseFieldFiniteCD ℓ k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (F : PadicAlgCl.FiniteIntermediateField ℓ) :
    Nonempty (CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ F f ⋙
      CondensedRing.boundedConstructibleToPadicAlgCl Y.left ℓ F ≅
      CondensedRing.boundedConstructibleToPadicAlgCl X.left ℓ F ⋙
        CondensedRing.boundedConstructibleLowerShriek ℓ f) ∧
    Nonempty (CondensedRing.boundedConstructibleUpperStar
        (Profinite.continuousMapRingObj F) ℓ f ⋙
      CondensedRing.boundedConstructibleToPadicAlgCl X.left ℓ F ≅
      CondensedRing.boundedConstructibleToPadicAlgCl Y.left ℓ F ⋙
        CondensedRing.boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) := by
  sorry

end AlgebraicGeometry.ProEtale
