module

public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice

/-! # Finite Ext for coherent complexes on proper algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tag 0D0T, lemma-ext-finite
(blueprint: lem-sfb-proper-space-coherent-ext-finite).

The equivalent small affine étale model retains the original module universe.
Coherence is quasi-coherence and finite type: on this locally Noetherian space this
means association to a finite module on every Noetherian affine étale chart (Tag 07UB).
The action on derived Hom is restriction of the global-function action along the
structure morphism, without choosing an auxiliary module structure.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure-morphism action on Ext in every integer degree. This is the action
on derived morphisms of compatible global regular functions, restricted along the
actual pullback A → Γ(X,O_X).
Source: Stacks, Tag 0D0T and Modules on Sites, Section 04TT
(blueprint: lem-sfb-proper-space-coherent-ext-finite). -/
@[instance_reducible] def properSpaceExtModule (A : Type u) [CommRing A]
    (X : AlgebraicSpace (Spec (.of A)))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (.of A)))))
    [HasDerivedCategory.{w} X.SmallModules]
    (E F : X.DerivedModules) (n : ℤ) : Module A (E ⟶ F⟦n⟧) :=
  letI : Linear (RingCat.sectionsSubring X.smallStructureRings.obj) X.SmallModules :=
    SheafOfModules.homLinear X.smallStructureSheaf.obj X.smallStructureRings.property
  Module.compHom _ (affineGlobalScalar A (Over.mk (𝟙 (Spec (.of A)))) (Iso.refl _) X f)

/-- Global Ext between an upper-bounded coherent complex and a lower-bounded coherent
complex on a proper algebraic space over a Noetherian ring is finite in every degree.
The module in the conclusion has exactly the structure-morphism scalar action.

Source: Stacks Project, Derived Categories of Spaces, Tag 0D0T, lemma-ext-finite
(blueprint: lem-sfb-proper-space-coherent-ext-finite).

Proof:
1. Put Y = Spec A. It is Noetherian and quasi-compact. Finite type of X over Y
makes its affine étale chart rings finite-type A-algebras, hence Noetherian. Thus X
is locally Noetherian. On these charts quasi-coherence and finite type identify
cohomology with the étale sheaf associated to a finite module, with tensor-product
sections on every affine étale refinement.
2. Form G = RHom(E,F). Tag 0D0S (lem-sfb-space-coherent-derived-internal-hom)
shows that G has coherent cohomology and is bounded below, using the upper bound
on E and the lower bound on F. No perfectness is needed.
3. Tag 0D0R (lem-sfb-proper-space-coherent-derived-image), applied with auxiliary
base S = Y, shows that T = Rf_*G is bounded below with coherent cohomology.
4. Closed tensor-Hom adjunction and the derived internal-Hom sections model identify
Hom(E,F[n]) with H^n RΓ(X,G). The normalized K-injective composition comparison
identifies RΓ(X,G) with RΓ(Y,T), retaining the action of A.
5. The bounded-below hypercohomology spectral sequence has
E₂^{p,q} = H^p(Y,H^q(T)). Affine étale quasi-coherent acyclicity kills p > 0.
Each E₂^{0,q} is the finite A-module associated to the coherent sheaf H^q(T).
The module/additive evaluation comparison justifies this acyclicity for the
module-valued derived global-sections functor.
6. In each total degree only finitely many filtration terms occur. Descending from
the zero term shows F¹H^n = 0 and H^n = E₂^{0,n}; below the cohomological lower bound
both sides are zero. These comparisons are A-linear: naturality of the sections
model in a K-injective target identifies postcomposition by multiplication by a
with multiplication by a on the Hom complex. This is the global-function action
restricted by properSpaceExtModule. Transport a finite generating set across the
resulting A-linear isomorphism. -/
theorem properSpace_coherent_ext_finite (A : Type u) [CommRing A] [IsNoetherianRing A]
    (X : AlgebraicSpace (Spec (.of A)))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (.of A))))) (hf : MapIsProper f)
    [HasDerivedCategory.{w} X.SmallModules] (E F : X.DerivedModules)
    (hE : ∀ q : ℤ,
      ((DerivedCategory.homologyFunctor X.SmallModules q).obj E).IsQuasicoherent ∧
      ((DerivedCategory.homologyFunctor X.SmallModules q).obj E).IsFiniteType)
    (hF : ∀ q : ℤ,
      ((DerivedCategory.homologyFunctor X.SmallModules q).obj F).IsQuasicoherent ∧
      ((DerivedCategory.homologyFunctor X.SmallModules q).obj F).IsFiniteType)
    (hE_upper : ∃ a : ℤ, ∀ q : ℤ, a < q →
      IsZero ((DerivedCategory.homologyFunctor X.SmallModules q).obj E))
    (hF_lower : ∃ b : ℤ, ∀ q : ℤ, q < b →
      IsZero ((DerivedCategory.homologyFunctor X.SmallModules q).obj F))
    (n : ℤ) :
    @Module.Finite A (E ⟶ F⟦n⟧) _ _ (properSpaceExtModule A X f E F n) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
