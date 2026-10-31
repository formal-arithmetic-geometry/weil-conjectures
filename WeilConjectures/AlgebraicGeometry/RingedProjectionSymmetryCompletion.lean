/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedProjectionCoherenceData
public import WeilConjectures.Algebra.Homology.DerivedTensorAdditiveConstraints
public import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
/-! The symmetry half of the representative descent of tensor constraints.
Source: Stacks, sites-cohomology.tex, Tags 06YS, 06YU and 07A4
(blueprint: lem-sfb-ringed-projection-symmetry-completion).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace SheafOfModules.ProjectionCoherence
/-- The symmetry obtained by conjugating the normalized derived symmetry `σ` by the
comparison `e` between the fixed derived tensor and the recorded tensor is natural and
satisfies the Koszul representative equation of the recorded model.
Source: Stacks, sites-cohomology.tex, Tags 06YS, 06YU and 07A4.

Proof: by `hsym`, `sym E F = e⁻¹(E,F) ≫ σ(E,F) ≫ e(F,E)`, a composite of natural
isomorphisms, so naturality is naturality of `σ` and `e`. For the representative
equation, `cochainTensorRepresentativeArrow` is `KFlatFixedTensor.representativeIso`, so
`he` (transported along `hflat`) says `a.representative(P,Q) = rep(P,Q) ≫ e(P,Q)` on flat
K-flat complexes. The left side becomes `rep(P,Q) ≫ σ(QP,QQ) ≫ e(Q,P)`; the symmetry
conjunct of `hs` rewrites `rep(P,Q) ≫ σ` to `Q(braiding P Q) ≫ rep(Q,P)`, and the
Koszul braiding of cochain complexes is `totalSymmetry`. The result is
`Q(totalSymmetry P Q) ≫ a.representative(Q,P)`.
(blueprint: lem-sfb-ringed-projection-symmetry-completion) -/
theorem ringedProjectionSymmetryCompletion
    (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X)
    (e : SheafOfModules.DerivedTensorConstraints.tensor X.ring ≅ X.tensor)
    (hflat : (fun P : CochainComplex X.mateModules ℤ =>
      P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat) =
      (fun P : CochainComplex X.mateModules ℤ =>
        P.IsKFlatIndependentCoefficients ∧
          ∀ n : ℤ, (P.X n).IsFlatOnSite))
    (he : let arep := hflat ▸ a.representative
      ∀ z : (SheafOfModules.cochainTensorFlatRepresentatives X.topology X.ring).FullSubcategory ×
        (SheafOfModules.cochainTensorFlatRepresentatives X.topology X.ring).FullSubcategory,
      SheafOfModules.cochainTensorRepresentativeArrow X.topology X.ring z ≫
        e.hom.app (DerivedCategory.Q.obj z.1.obj, DerivedCategory.Q.obj z.2.obj) =
      arep.hom.app z)
    (t : ∀ i j : ℤ, SheafOfModules.DerivedTensorConstraints.shiftedSource X.ring i j ≅
      SheafOfModules.DerivedTensorConstraints.shiftedTarget X.ring i j)
    (α : SheafOfModules.DerivedTensorConstraints.leftAssociated X.ring ≅
      SheafOfModules.DerivedTensorConstraints.rightAssociated X.ring)
    (σ : SheafOfModules.DerivedTensorConstraints.tensor X.ring ≅
      SheafOfModules.DerivedTensorConstraints.swapped X.ring)
    (sym : ∀ E F : X.mateDerived,
      X.tensor.obj (E, F) ≅ X.tensor.obj (F, E))
    (hsym : ∀ E F, sym E F = asIso (e.inv.app (E, F)) ≪≫
      σ.app (E, F) ≪≫ asIso (e.hom.app (F, E)))
    (hs : SheafOfModules.DerivedTensorConstraints.IsNormalized X.ring t α σ) :
    (∀ {E E' F F' : X.mateDerived} (x : E ⟶ E') (y : F ⟶ F'),
      X.tensor.map (Prod.mkHom x y) ≫ (sym E' F').hom =
        (sym E F).hom ≫ X.tensor.map (Prod.mkHom y x)) ∧
      (∀ (P Q : CochainComplex X.mateModules ℤ) (hp : X.mateFlat P) (hq : X.mateFlat Q),
        a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
            (sym (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
          DerivedCategory.Q.map (totalSymmetry X P Q).hom ≫
            a.representative.hom.app (⟨Q, hq⟩, ⟨P, hp⟩)) := by
  sorry
end SheafOfModules.ProjectionCoherence
