/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N1 and H6
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EtaleSumPreservesFlat
import Sheaf.AlgebraicGeometry.EtaleSumPreservesKFlat

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Étale sum extension preserves flatness and K-flatness

Source: Stacks Project, More on Étale Cohomology, Tag 0GKF
(`lemma-f-shriek-projection`), with the unbounded total-tensor expansion recorded in
(blueprint: lem-pur-etale-sum-flat-kflat).

The three helper functors apply the published constant-scalar equivalence, its
canonical coefficient-ring transport, and the published sum extension degreewise.
They introduce no choice of a module action, extension functor, or tensor product.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Realize module-valued étale sheaves as modules over the constant commutative
ring sheaf, using the existing constant-scalar extension and canonical ring isomorphism.
Source: Stacks, Modules on Sites, Tags 093I and 03CV; the coefficient convention in
Tag 0GKF (blueprint: lem-pur-etale-sum-flat-kflat). -/
def etaleSumFlatModuleRealization (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      SheafOfModules.{u + 1} ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))) :=
  etaleConstantModuleFunctor T A ⋙
    SheafOfModules.pushforward (F := 𝟭 T.Etale)
      (constantModuleHomRingIso T.smallEtaleTopology A).inv

/-- Apply the canonical constant-coefficient realization degreewise, including to
unbounded complexes. Source: Stacks Tag 0GKF and the total-tensor expansion in
(blueprint: lem-pur-etale-sum-flat-kflat). -/
def etaleSumFlatComplexRealization (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (SheafOfModules.{u + 1} ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of A)))) ℤ :=
  letI := etaleConstantModuleFunctor_isEquivalence T A
  (etaleConstantModuleFunctor T A ⋙
    SheafOfModules.pushforward (F := 𝟭 T.Etale)
      (constantModuleHomRingIso T.smallEtaleTopology A).inv).mapHomologicalComplex
        (ComplexShape.up ℤ)

/-- Apply the existing sheafified sum extension degreewise. Its adjunction supplies
zero-morphism preservation, so all integer degrees are allowed. Source: Stacks Tag 0GKF
and its unbounded expansion (blueprint: lem-pur-etale-sum-flat-kflat). -/
def etaleSumFlatComplexExtension {U X : Scheme.{u}} (f : U ⟶ X) (hf : Etale f)
    (A : Type (u + 1)) [CommRing A] :
    CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  letI := (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f hf).isLeftAdjoint
  (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f hf).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Étale sum extension preserves flat terms.
Source: Tag 0GKF (blueprint: lem-pur-etale-sum-flat-terms-aux).

For each degree n, apply the flatness component to P.X n. The degree-n term of the
mapHomologicalComplex extension is definitionally the sum extension of that term,
so the resulting family of flatness proofs is exactly the required conclusion. -/
theorem etaleSum_preserves_flat_terms_aux {U X : Scheme.{u}} (f : U ⟶ X)
    [hf : Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (A : Type (u + 1)) [CommRing A] :
    ∀ P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := U.smallEtaleTopology) (R :=
        (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleSumFlatComplexRealization U A).obj P) →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := U.smallEtaleTopology) (R :=
        (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleSumFlatModuleRealization U A).obj (P.X n))) →
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := X.smallEtaleTopology) (R :=
        (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleSumFlatModuleRealization X A).obj
          (((etaleSumFlatComplexExtension f hf A).obj P).X n)) := by
  intro P _ hflat n
  exact etaleSum_preserves_flat_aux f A (P.X n) (hflat n)

/-- Étale sum extension preserves flat sheaves, arbitrary unbounded K-flat complexes,
and K-flat complexes with flat terms. Flatness uses exact sheaf tensor; K-flatness uses
acyclic tests and the direct-sum total tensor with Koszul signs.

Source: Stacks Tag 0GKF, `lemma-f-shriek-projection`, and its unbounded total-tensor
expansion (blueprint: lem-pur-etale-sum-flat-kflat).

Proof:
1. Given a short exact sequence on X, exact inverse image carries it to a short exact
sequence on U (prop-weil-pbc-inverse-image-modules-exact). Tensoring with a flat F and
then applying exact sum extension (lem-weil-pbc-etale-restriction-injectives) preserves
exactness. The canonical projection isomorphism (lem-pur-etale-sheaf-projection-map)
identifies this with tensor by the extension of F. Tensor symmetry reconciles the
order with def-pc-flat-sheaf-modules, which tests G tensor F. Thus the extension is flat.
2. For an acyclic complex B on X, exact inverse image makes its pullback acyclic.
The canonical direct-sum totalization isomorphism (lem-pur-etale-sum-tensor-totalization)
identifies Tot((f_! P) tensor B) with f_! Tot(P tensor f^* B). Signed symmetry, sending
x tensor y in bidegree (p,q) to (-1)^(pq) y tensor x, identifies this with the acyclic
complex provided by def-pc-kflat-complex. Indeed both differential composites send
x tensor y to (-1)^(pq)(dy tensor x + (-1)^q y tensor dx). Exact sum extension commutes
with cohomology and preserves acyclicity. Another signed symmetry puts the acyclic
test in the first factor, proving K-flatness of f_! P without a boundedness assumption.
3. The term in degree n of the degreewise extension is f_!(P.X n). Apply step 1 to
each flat term and combine with step 2 to obtain the final assertion. The canonical
constant-scalar equivalence and ring transport simply express these same sheaves
in the ringed-site definitions of flatness and K-flatness. -/
theorem etaleSum_preserves_flat_kflat {U X : Scheme.{u}} (f : U ⟶ X)
    [hf : Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (A : Type (u + 1)) [CommRing A] :
    (∀ F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
      SheafOfModules.IsFlatOnSite (J := U.smallEtaleTopology) (R :=
        (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleSumFlatModuleRealization U A).obj F) →
      SheafOfModules.IsFlatOnSite (J := X.smallEtaleTopology) (R :=
        (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleSumFlatModuleRealization X A).obj
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f hf).obj F))) ∧
    (∀ P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := U.smallEtaleTopology) (R :=
        (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleSumFlatComplexRealization U A).obj P) →
      CochainComplex.IsKFlatIndependentCoefficients (J := X.smallEtaleTopology) (R :=
        (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleSumFlatComplexRealization X A).obj
          ((etaleSumFlatComplexExtension f hf A).obj P))) ∧
    (∀ P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := U.smallEtaleTopology) (R :=
        (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleSumFlatComplexRealization U A).obj P) →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := U.smallEtaleTopology) (R :=
        (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleSumFlatModuleRealization U A).obj (P.X n))) →
      CochainComplex.IsKFlatIndependentCoefficients (J := X.smallEtaleTopology) (R :=
        (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleSumFlatComplexRealization X A).obj
          ((etaleSumFlatComplexExtension f hf A).obj P)) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := X.smallEtaleTopology) (R :=
        (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleSumFlatModuleRealization X A).obj
          (((etaleSumFlatComplexExtension f hf A).obj P).X n))) := by
  constructor
  · exact etaleSum_preserves_flat_aux f A
  constructor
  · exact etaleSum_preserves_kflat_aux f A
  · intro P hP hflat
    refine ⟨etaleSum_preserves_kflat_aux f A P hP, ?_⟩
    exact etaleSum_preserves_flat_terms_aux f A P hP hflat


end AlgebraicGeometry.Scheme
