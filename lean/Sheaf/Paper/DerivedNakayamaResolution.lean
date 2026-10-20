/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Topology.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# The two-term resolution of the finite coefficient sheaves

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-resolution.md`
(blueprint: det-pe-derived-nakayama-resolution).

All coefficients are continuous condensed rings pulled back from the point. A natural
cone is expressed using the standard cone functor on complexes, with its standard maps.
The comparison with a functor on the derived category also asserts its descent and naturality.

## Main definitions

* `quotientModule`: the continuous finite quotient with its restricted integer action.
* `reductionFunctor`: derived tensor with the pulled-back quotient in degree zero.
* `coneFunctor`: the standard localized mapping-cone model and its maps.

## Main statements

* `derived_nakayama_resolution`: exactness, the natural cone comparison, and the
  specified quotient-power triangles.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CategoryTheory.Triangulated CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.DerivedNakayama

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The continuous condensed integer ring with its spectral absolute-value topology.
Source: blueprint resolution, On the point, step 1
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev integerRingSheaf : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingSheaf (Padic.coefficientExtensionIntegers l E)

/-- The finite quotient with the quotient topology, not a constant replacement of the integers.
Source: blueprint resolution, On the point, step 1
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev quotientRingSheaf (n : ℕ) : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingSheaf (Padic.coefficientExtensionRing l E n)

/-- Continuous postcomposition with the actual quotient homomorphism.
Source: blueprint resolution, On the point, step 2
(blueprint: det-pe-derived-nakayama-resolution). -/
def reductionRingSheaf (n : ℕ) : integerRingSheaf l E ⟶ quotientRingSheaf l E n :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ⟨{
      app := fun _ ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)).compLeftContinuous _
            continuous_quot_mk).comp ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ rfl }⟩

/-- The internal ring underlying the continuous condensed integer ring.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev integerRing : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (integerRingSheaf l E)

/-- Pointwise commutativity of the integer ring object.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
instance integerRing_isCommMonObj : IsCommMonObj (integerRing l E) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.isCommMonObj_continuousCoefficientRingObj _

/-- The internal finite quotient ring.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev quotientRing (n : ℕ) : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (quotientRingSheaf l E n)

/-- Reduction as a morphism of internal rings.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev reductionRing (n : ℕ) : integerRing l E ⟶ quotientRing l E n :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (reductionRingSheaf l E n)

/-- The quotient with its canonical restricted scalar action from the integers.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev quotientModule (n : ℕ) :
    CategoryTheory.Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (integerRing l E) :=
  (Mod.comap (reductionRing l E n)).obj (Mod.regular (quotientRing l E n))

/-- The exact inverse image on the internal integer-module objects.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev pullback (X : Scheme.{u}) := (upperStarFromPoint X).mapMod (integerRing l E)

/-- The unbounded derived category with the pulled-back condensed integer coefficients.
Source: blueprint resolution, On X, step 5
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev Derived (X : Scheme.{u}) :=
  DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integerRing l E) X))

/-- The actual derived reduction functor, with the finite quotient in degree zero.
Source: blueprint resolution, On X, step 5
(blueprint: det-pe-derived-nakayama-resolution). -/
abbrev reductionFunctor (X : Scheme.{u}) (n : ℕ) : Derived l E X ⥤ Derived l E X :=
  (CondensedRing.derivedTensor (integerRing l E) X).flip.obj
    ((DerivedCategory.singleFunctor _ 0).obj ((pullback l E X).obj (quotientModule l E n)))

/-- Degree-zero realization of a coefficient morphism, followed by derived tensor with K.
Source: blueprint resolution, Triangles, step 7
(blueprint: det-pe-derived-nakayama-resolution). -/
def reductionMap (X : Scheme.{u}) {m n : ℕ}
    (f : quotientModule l E m ⟶ quotientModule l E n) :
    reductionFunctor l E X m ⟶ reductionFunctor l E X n :=
  (CondensedRing.derivedTensor (integerRing l E) X).flip.map
    ((DerivedCategory.singleFunctor _ 0).map ((pullback l E X).map f))

/-- Strong monoidal pullback takes the regular module to the regular module.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution).

Proof: both underlying objects are p_X^* R. The transported regular action is the
monoidal comparison followed by p_X^* of multiplication, exactly the multiplication
of the transported ring. Extensionality for module objects and proof irrelevance give
the equality. This is the scalar-action identification used in step 3 of the node. -/
theorem pullback_regular (X : Scheme.{u}) :
    (pullback l E X).obj (Mod.regular (integerRing l E)) =
      Mod.regular (condensedRingObj (integerRing l E) X) := by
  sorry

/-- The regular-module comparison, with underlying identity, obtained from its named equality.
Source: blueprint resolution, On X, step 3
(blueprint: det-pe-derived-nakayama-resolution). -/
def regularPullbackIso (X : Scheme.{u}) :
    (pullback l E X).obj (Mod.regular (integerRing l E)) ≅
      Mod.regular (condensedRingObj (integerRing l E) X) :=
  eqToIso (pullback_regular l E X)

/-- The scalar action induced by an endomorphism of the regular module, using unitors.
Source: blueprint resolution, On X, step 5
(blueprint: det-pe-derived-nakayama-resolution). -/
def scalarOnModules (X : Scheme.{u})
    (d : End (Mod.regular (integerRing l E))) :
    𝟭 (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integerRing l E) X)) ⟶ 𝟭 _ :=
  let dX : End (Mod.regular (condensedRingObj (integerRing l E) X)) :=
    (regularPullbackIso l E X).inv ≫ (pullback l E X).map d ≫
      (regularPullbackIso l E X).hom
  (leftUnitorNatIso (CategoryTheory.Mod
    (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integerRing l E) X))).inv ≫
      (tensoringLeft (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integerRing l E) X))).map dX ≫ (leftUnitorNatIso _).hom

/-- Scalar multiplication as an actual chain map, degree by degree.
Source: blueprint resolution, On X, step 5
(blueprint: det-pe-derived-nakayama-resolution). -/
def scalarOnComplex (X : Scheme.{u}) (d : End (Mod.regular (integerRing l E)))
    (C : CochainComplex (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integerRing l E) X)) ℤ) : C ⟶ C :=
  (NatTrans.mapHomologicalComplex (scalarOnModules l E X d) (.up ℤ)).app C

/-- The standard cone model, functorial on complexes and then localized.
Its map is the standard cone map of the square with the same chain map on both sides.
Source: blueprint resolution, On X, step 5
(blueprint: det-pe-derived-nakayama-resolution). -/
def coneFunctor (X : Scheme.{u}) (d : End (Mod.regular (integerRing l E))) :
    CochainComplex (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integerRing l E) X)) ℤ ⥤ Derived l E X where
  obj C := DerivedCategory.Q.obj (CochainComplex.mappingCone (scalarOnComplex l E X d C))
  map {C D} f := DerivedCategory.Q.map
    (CochainComplex.mappingCone.map (scalarOnComplex l E X d C) (scalarOnComplex l E X d D)
      f f ((NatTrans.mapHomologicalComplex
        (scalarOnModules l E X d) (.up ℤ)).naturality f).symm)
  map_id C := by
    rw [CochainComplex.mappingCone.map_id]
    exact DerivedCategory.Q.map_id _
  map_comp f g := by
    rw [CochainComplex.mappingCone.map_comp]
    exact DerivedCategory.Q.map_comp _ _

/-- The coefficient sequence, its natural cone interpretation, and the quotient-power triangles.
Source: blueprint main-20261015, resolution statement and its three proof paragraphs
(blueprint: det-pe-derived-nakayama-resolution).

Proof:
1. The DVR theorem gives a nonzero uniformizer, continuous division on its image and finite
   quotient rings. Its positive-power ideals are open, so their quotient topologies are discrete
   (`lem-weil-l-adic-extension-integers-dvr`, `lem-weil-pbc-standard-quotients-perfect`).
2. On each profinite S, division identifies the kernel and a lift chosen on each clopen fibre
   proves surjectivity of continuous reduction. Kernels are sectionwise and cokernels sheafify
   (`lem-weil-pbc-sheafification-exact`); all maps are linear for pointwise actions.
3. Exact monoidal inverse image from the point transports this sequence and its actions to X
   (`lem-weil-pbc-left-exact-site-inverse-image-tensor`, `lem-sfb-finite-upper-star-exact`).
   The internal/section-module equivalence preserves underlying sheaves
   (`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
   `lem-weil-pbc-sheaf-tensor-closed`, `def-weil-sheaf-of-modules-category`).
4. The complex [R -- pi^n --> R] in degrees -1,0 augments quasi-isomorphically to B_n[0].
   Its rank-one free terms are flat and it is bounded above, hence K-flat
   (`lem-weil-pbc-independent-bounded-flat-kflat`, `def-pc-flat-sheaf-modules`).
5. Choose a K-flat representative for arbitrary unbounded K (`lem-pc-kflat-resolution`).
   Tensor-model descent (`lem-weil-pbc-site-derived-tensor-descent`) and signed interchange
   compute its reduction by the cone differential (dx + pi^n y, -dy). This is functorial in
   chain maps. The displayed natural isomorphism identifies this standard cone model with
   the reduction functor after localization; hence it descends naturally to the derived category.
6. The maps [x] |-> [pi^n x] and [y] |-> [y] give the short exact quotient-power sequence:
   cancellation proves injectivity, representatives give the kernel and surjectivity. Finite
   discreteness gives continuous lifts on clopen fibres, and exact pullback gives the X sequence.
7. Its short-exact-sequence triangle (`lem-weil-pbc-complex-ses-triangle`) stays distinguished
   after derived tensor with K (`lem-sc-source-kflat-tensor-left-triangulated`). The two arrows
   are precisely the displayed derived images of the normalized quotient maps. Take m=1 for
   the final triangle. No boundedness of K or invertibility of l on X is used. -/
theorem derived_nakayama_resolution :
    ∃ (d : End (Mod.regular (integerRing l E))),
      (∀ (S : Profinite.{u}ᵒᵖ) (f : (integerRing l E).obj.obj S) (s : S.unop),
        ((d.hom.hom.app S) f).down s =
          Padic.coefficientExtensionUniformizer l E * f.down s) ∧
      ∃ (r : ∀ n : ℕ, Mod.regular (integerRing l E) ⟶ quotientModule l E n),
        (∀ n : ℕ, (r n).hom = reductionRing l E n) ∧
        ∃ (i : ∀ m n : ℕ, quotientModule l E m ⟶ quotientModule l E (n + m))
          (q : ∀ m n : ℕ, quotientModule l E (n + m) ⟶ quotientModule l E n),
          (∀ m n : ℕ, r m ≫ i m n = (d ^ n) ≫ r (n + m)) ∧
          (∀ m n : ℕ, r (n + m) ≫ q m n = r n) ∧
          ∀ (X : Scheme.{u}) (n : ℕ), 1 ≤ n →
            (∃ h : (pullback l E X).map (d ^ n) ≫ (pullback l E X).map (r n) = 0,
              (ShortComplex.mk _ _ h).ShortExact) ∧
            Nonempty (DerivedCategory.Q ⋙ reductionFunctor l E X n ≅
              coneFunctor l E X (d ^ n)) ∧
            (∀ (m : ℕ), 1 ≤ m → m ≤ n → ∀ K : Derived l E X,
              ∃ δ : (reductionFunctor l E X n).obj K ⟶
                  ((reductionFunctor l E X m).obj K)⟦(1 : ℤ)⟧,
                Triangle.mk ((reductionMap l E X (i m n)).app K)
                  ((reductionMap l E X (q m n)).app K) δ ∈ distTriang (Derived l E X)) := by
  sorry

end AlgebraicGeometry.ProEtale.DerivedNakayama
