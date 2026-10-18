/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtale.HypercoverExistence
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsDerived
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentationRing
import Sheaf.Algebra.Homology.BoundedBelowAugmentation
import Sheaf.Algebra.Homology.BoundedBelowTotalComparison
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Derived abelian sections from a weakly contractible hypercover

Source: blueprint main-20261015, sec-proetale-coefficients/sk-prop-pe-hypercover/
det-pe-hypercover-complex.md; Stacks Project, Tag 09A2
(blueprint: det-pe-hypercover-complex).

The helpers realize this node's alternating section total for arbitrary ring sheaves.
The existing `hypercoverTotal` has commutative coefficients and a module-valued target.
Here all values and derived categories use the common larger coefficient universe;
the pro-etale site's object and morphism universes stay different.
-/

@[expose] public section

set_option autoImplicit false

universe t u v wA wB

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

/-- Cosimplicial underlying abelian sections, with the actual sheaf restriction maps.
Source: Stacks Project, Tag 09A2, the construction of `s(E(K))`
(blueprint: det-pe-hypercover-complex). -/
noncomputable def hypercoverAbelianSections (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U)) :
    ringedSiteModules.{max u v (t + 1)} R ⥤
      CosimplicialObject AddCommGrpCat.{max u v (t + 1)} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
    (Functor.whiskeringLeft _ _ _).obj (W ⋙ Over.forget U).rightOp

/-- The alternating section rows, extended by zero in negative simplicial degrees.
The differential from degree r to r+1 is the sum of `(-1)^i` times the i-th
face restriction, for i in `Fin (r+2)`. No hypercover condition enters this data.
Source: Stacks Project, Tag 09A2
(blueprint: det-pe-hypercover-complex). -/
noncomputable def hypercoverAbelianRows (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U)) :
    ringedSiteModules.{max u v (t + 1)} R ⥤
      CochainComplex AddCommGrpCat.{max u v (t + 1)} ℤ :=
  hypercoverAbelianSections X R U W ⋙
    AlgebraicTopology.alternatingCofaceMapComplex _ ⋙
    ComplexShape.embeddingUpNat.extendFunctor _

/-- Additivity needed to apply the alternating section rows to a coefficient complex.
Source: Stacks Project, Tag 09A2, construction of the total complex; step 1 of the
node's proof (blueprint: det-pe-hypercover-complex).
Proof: a coefficient morphism acts by its section map in every degree. Addition of
module-sheaf morphisms, of abelian presheaf morphisms and of complex morphisms is
componentwise. Alternating cofaces do not change these components, and extension
by zero has zero components in the additional degrees. Thus each component of the
image of a sum is the sum of its images. -/
theorem hypercoverAbelianRows_additive (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U)) :
    (hypercoverAbelianRows.{t, u, v} X R U W).Additive := by
  sorry

attribute [instance] hypercoverAbelianRows_additive

/-- The actual coproduct total of the section bicomplex. Flip puts simplicial degree r
first; Mathlib's total differential is then `delta + (-1)^r d_K`. Its degree q is
the sum over r+b=q, r nonnegative, of K^b(W_r). For a strict lower bound a on K,
all summands outside `0 ≤ r ≤ q-a` are zero; for q<a the entire diagonal is zero.
Coefficient chain maps act componentwise. The definition uses no choice of a complex.
Source: Stacks Project, Tag 09A2; Homology, Tags 0132 and 0133
(blueprint: det-pe-hypercover-complex). -/
noncomputable def hypercoverAbelianTotal (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U)) :
    CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ ⥤
      CochainComplex AddCommGrpCat.{max u v (t + 1)} ℤ :=
  (hypercoverAbelianRows X R U W).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.totalFunctor _ _ _ (ComplexShape.up ℤ)

/-- The additive abelian section functor used for RΓ(U,-).
Source: Stacks Project, Tag 09A2
(blueprint: det-pe-hypercover-complex). -/
noncomputable abbrev hypercoverAbelianEvaluation (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt) :
    ringedSiteModules.{max u v (t + 1)} R ⥤ AddCommGrpCat.{max u v (t + 1)} :=
  SheafOfModules.evaluation R (op U) ⋙ forget₂ _ AddCommGrpCat

/-- Derived sections are naturally the alternating total sections of any weakly
contractible hypercover. `Plus` means that some integer a is a strict lower bound
on the terms, so it includes every complex and every bound in the node. The
natural isomorphism is on the full category of such complexes, hence includes maps
between complexes with different bounds. RΓ is exactly the recorded right derived
functor of abelian evaluation, using the existing K-injective resolution interface.
No affineness, quasi-compactness or quasi-separatedness assumption is imposed.

Source: blueprint main-20261015, det-pe-hypercover-complex.md; Stacks Project,
Tag 09A2 (blueprint: det-pe-hypercover-complex).

Proof (the seven steps of the node):
1. Simplicial identities pair the terms in delta squared with opposite signs.
   Naturality of d_K makes it commute with every restriction. The mixed terms
   `(-1)^(r+1) d_K delta` and `(-1)^r delta d_K` cancel. The construction above
   realizes this signed total functor. If b≥a and r+b=q, then 0≤r≤q-a, including
   the empty diagonal for q<a.
2. By def-weil-sheaf-of-modules-category, kernels are sectionwise. The forgetful
   functor to abelian sheaves preserves kernels and cokernels by
   lem-weil-pbc-module-sheaves-colimits-forgetful. The abelian- and set-sheaf
   locally-surjective-epi criteria and sk-def-pe-weak-contractible make evaluation
   at every W_r exact. The cycle-boundary short exact sequences then show that
   it preserves cohomology and every quasi-isomorphism.
3. On the common-universe small model of def-weil-pbc-proetale-site, choose a
   bounded-below termwise-injective K-injective resolution s:K→I by
   lem-sc-bounded-below-injective-resolution. If c bounds I, use N=min(a,c).
   The ring-sheaf Grothendieck theorem and lem-sfb-grothendieck-k-injective supply
   resolutions of all complexes, the hypothesis of def-sfb-right-derived-functor.
   Its resolution comparison identifies RΓ(U,K) with I(U).
4. det-pe-topos-functoriality-site gives the site axioms and subcanonicity.
   Pull the matching covers back along compatible lower-simplex tuples.
   Apply lem-sc-ringed-hypercover-injective-augmentation-ring to obtain each
   exact augmented row 0→I^b(U)→I^b(W_0)→I^b(W_1)→... . Injectivity here is
   injectivity as module sheaves, without forgetting the scalar action.
5. Restriction into column zero defines alpha_E:E(U)→T(E), naturally in E.
   The two faces agree after augmentation, so its outgoing horizontal component
   is zero. The vertical sign in column zero is one. The exact rows and common
   lower bound N let lem-weil-pbc-bounded-below-row-augmentation prove alpha_I
   a quasi-isomorphism.
6. Step 2 makes s a columnwise quasi-isomorphism. Apply
   lem-weil-pbc-bounded-below-total-column-comparison with P=0,Q=N to T(s).
   Compose the resolution comparison, alpha_I and the inverse of T(s) in D(Ab).
   The same argument with a common bound proves that T inverts every
   quasi-isomorphism between bounded-below complexes.
7. lem-weil-pbc-kinjective-hom-derived lifts derived comparison maps into
   K-injective resolutions to chain maps, uniquely up to homotopy, and makes
   the resolution squares commute up to homotopy. A coefficient homotopy h
   induces total homotopy `(-1)^r h(W_r)`; its horizontal terms cancel and its
   vertical terms give dh+hd. Restriction augmentation is strictly natural.
   These identities give the natural isomorphism below, independent of every
   resolution choice. Since T inverts quasi-isomorphisms, naturality also holds
   after passing to derived morphisms. -/
theorem hypercover_complex_natural_iso (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U))
    [HasDerivedCategory.{wA} (ringedSiteModules.{max u v (t + 1)} R)]
    [HasDerivedCategory.{wB} AddCommGrpCat.{max u v (t + 1)}]
    (hweak : ∀ r : ℕ,
      (topology X).IsWeaklyContractible.{max u v (t + 1)} (W _⦋r⦌).left)
    (hzero : Presieve.singleton (W _⦋0⦌).hom ∈ (precoverage X) U)
    (hmatching : ∀ r : ℕ,
      ∃ (c : Cone (SimplicialObject.properFaceDiagram W (r + 1)))
        (μ : W _⦋r + 1⦌ ⟶ c.pt),
        Nonempty (IsLimit c) ∧ Presieve.singleton μ.left ∈ (precoverage X) c.pt.left ∧
          ∀ a : SimplicialObject.ProperFaceCategory (r + 1),
            μ ≫ c.π.app (op a) = W.map a.obj.hom.op) :
    Nonempty
      (CochainComplex.Plus.ι (ringedSiteModules.{max u v (t + 1)} R) ⋙ DerivedCategory.Q ⋙
          (hypercoverAbelianEvaluation X R U).rightDerivedFunctorOfQuasiIsoResolutions
            (moduleQuasiIsoKInjectiveResolutions X R) ≅
        CochainComplex.Plus.ι (ringedSiteModules.{max u v (t + 1)} R) ⋙
          hypercoverAbelianTotal X R U W ⋙ DerivedCategory.Q) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
