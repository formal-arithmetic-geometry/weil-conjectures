/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import Sheaf.SixFunctors.OpenTensorNormalizationData
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The specified clopen unit on semilinear systems

Source: Stacks Project, sites-modules.tex, Tag 03DI (lemma-extension-by-zero),
and derived.tex, Tag 015F (lemma-right-derived-exact-functor), specialized to a
clopen decomposition on the ringed sequence site
(blueprint: lem-sf-semilinear-clopen-unit-projector).

All maps below act on the whole ordinary unbounded derived category of strict
semilinear systems. The projector is localized from the existing ordinary map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- The derived open unit is invertible, including for the empty clopen.
Source: Stacks 03DI; proof steps 1--5
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: restriction of ordinary extension is the identity, with precisely the ordinary
open unit. Localize the exact adjunction and its invertible unit; the normalized
right-derived/exact comparison identifies this with the specified jAdj unit. -/
theorem semilinearClopen_openUnit_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : IsIso (jAdj R φ s).unit := by
  sorry

/-- The specified transpose of the inverse open unit, with no choice of isomorphism.
Source: Stacks 03DI; proof step 5
(blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenToDirect {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : J R φ s ⟶ P R φ s :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (J R φ s) (adj R φ s).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (@inv _ _ _ _ (jAdj R φ s).unit (semilinearClopen_openUnit_isIso R φ s))
      (P R φ s) ≫ (Functor.leftUnitor _).hom

/-- The actual termwise localization of the ordinary identity/zero projector.
Source: Stacks 03DI; proof steps 3 and 5
(blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenPi {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Derived R φ X) ⟶ G R φ s ⋙ J R φ s :=
  (Functor.mapDerivedCategoryIdIso _).inv ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules R φ X) (.up ℤ)) _ _
      (𝟭 (Modules R φ X)).mapDerivedCategory
      (pull R φ s ⋙ extension R φ s).mapDerivedCategory
      (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (modulePi R φ s) (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom

/-- Clopen direct image is exact on actual ordinary systems.
Source: Stacks 03DI, 03DJ; proof steps 1--4
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: sheaf gluing on the two disjoint clopen pieces gives the product of section
modules, including zero sections on the empty object. Direct image is the first
factor with zero second factor, hence canonically isomorphic to exact extension by
zero via moduleOpenToP. Transfer finite-colimit preservation across this isomorphism. -/
theorem semilinearClopen_push_colimits {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : PreservesFiniteColimits (push R φ s) := by
  sorry

/-- The exactness witness used by the canonical exact/right-derived comparison.
Source: Stacks 015F (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
instance semilinearClopen_pushColimits {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : PreservesFiniteColimits (push R φ s) :=
  semilinearClopen_push_colimits R φ s

/-- The component projector is precisely the specified direct-image unit.
Source: Stacks 03DI and 015F; proof steps 1--5
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: on a test object H, split H into its pullbacks to U and C. The disjoint sheaf
cover gives M(H) = M(H_U) × M(H_C), with M(empty) = 0. All restrictions, scalars and
semilinear transitions preserve the factors. Direct image is the first factor.
The left-adjoint uniqueness comparison from extension by zero has transpose the
inverse open unit, so is exactly moduleOpenToP. Its inverse after the right unit is
modulePi, identity on U and zero on C. Thus its composite with moduleOpenToP is the
right unit, restriction to U is the open unit, and restriction to C is zero.
Exactness identifies total right-derived direct image with termwise direct image
(lem-weil-pbc-exact-functor-derived-functor). Localize the ordinary isomorphism
(lem-sfb-exact-derived-natural-iso) and both normalized adjunctions
(def-weil-exact-derived-adjunction). The transpose remains the inverse open unit,
identifying the localized map with clopenToDirect. Localizing the three ordinary
identities proves the displayed whole-system identities and the representative
normalization. No equality of derived morphisms is inferred from evaluation. -/
theorem semilinearClopen_unit_projector {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) :
    IsIso (clopenToDirect R φ s) ∧
    clopenPi R φ s ≫ Functor.whiskerLeft (G R φ s) (clopenToDirect R φ s) =
      (adj R φ s).unit ∧
    (∀ M : Derived R φ X,
      (G R φ s).map ((clopenPi R φ s).app M) =
        (jAdj R φ s).unit.app ((G R φ s).obj M)) ∧
    (∀ M : Derived R φ X, (G R φ c).map ((clopenPi R φ s).app M) = 0) ∧
    (∀ K : CochainComplex (Modules R φ U) ℤ,
      (clopenToDirect R φ s).app (DerivedCategory.Q.obj K) ≫
          (push R φ s).rightDerivedFunctorIsoMapDerivedCategory.hom.app
            (DerivedCategory.Q.obj K) ≫
          (push R φ s).mapDerivedCategoryFactors.hom.app K =
        (extension R φ s).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (moduleOpenToP R φ s) (.up ℤ)).app K)) := by
  sorry

section Coefficients

variable (D : ℕ → CommRingCat.{u + 1}) (ψ : ∀ n : ℕ, D (n + 1) ⟶ D n)
  (α : ∀ n : ℕ, R n ⟶ D n)
  (hα : ∀ n : ℕ, α (n + 1) ≫ ψ n = φ n ≫ α n)

/-- The actual map of constant coefficient sheaves.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientMap (X : Scheme.{u}) (n : ℕ) :
    coefficients R X n ⟶ coefficients D X n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2}
    (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (α n)

include hα in
/-- Compatibility of the actual coefficient sheaf maps.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: apply the constant-sheaf functor to hα and its functorial composition equation. -/
theorem clopenCoefficientMap_commute (X : Scheme.{u}) (n : ℕ) :
    clopenCoefficientMap R D α X (n + 1) ≫ coefficientTransition D ψ X n =
      coefficientTransition R φ X n ≫ clopenCoefficientMap R D α X n := by
  sorry

/-- Restriction along the actual map of ringed sequence sites.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
abbrev clopenCoefficientRestriction (X : Scheme.{u}) : Modules D ψ X ⥤ Modules R φ X :=
  SemilinearSections.res
    (SemilinearSections.systemMap (Scheme.ProEt.topology X)
      (coefficients R X) (coefficientTransition R φ X)
      (coefficients D X) (coefficientTransition D ψ X) (clopenCoefficientMap R D α X)
      (clopenCoefficientMap_commute R φ D ψ α hα X))

/-- Exact derived restriction on whole systems.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
abbrev clopenCoefficientRes (X : Scheme.{u}) : Derived D ψ X ⥤ Derived R φ X :=
  (clopenCoefficientRestriction R φ D ψ α hα X).mapDerivedCategory

/-- The dependency's K-flat scalar-extension model for the actual coefficient map.
Source: proof step 6; lem-coef-semilinear-derived-sections
(blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientScalar (X : Scheme.{u}) :=
  (SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X)).some.coefficientExtension
      (coefficients D X) (coefficientTransition D ψ X)
      (clopenCoefficientMap R D α X) (clopenCoefficientMap_commute R φ D ψ α hα X)

/-- The ordinary direct-image comparison is uniquely the identity on sections.
Source: Stacks 03DI, proof steps 1 and 6
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: both sides at (n,H) are the sections of M_n on H times_X U with the same
R_n action via α_n. Identity maps are linear and commute with restrictions and
semilinear transitions. Sectionwise extensionality proves uniqueness. -/
theorem clopenCoefficientPush_existsUnique {U X : Scheme.{u}} (s : U ⟶ X) :
    ∃! d : clopenCoefficientRestriction R φ D ψ α hα U ⋙ push R φ s ≅
        push D ψ s ⋙ clopenCoefficientRestriction R φ D ψ α hα X,
      ∀ (M : Modules D ψ U) (n : ℕ) (H : X.ProEt)
        (x : (((clopenCoefficientRestriction R φ D ψ α hα U ⋙ push R φ s).obj M).val.obj
          (op (n, H)))),
        HEq ((d.hom.app M).val.app (op (n, H)) x) x := by
  sorry

/-- The identity-on-sections ordinary pushforward comparison.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientPush {U X : Scheme.{u}} (s : U ⟶ X) :=
  (clopenCoefficientPush_existsUnique R φ D ψ α hα s).choose

/-- The ordinary inverse-image comparison is the mate of sectionwise restriction.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientPullInv {U X : Scheme.{u}} (s : U ⟶ X) :
    clopenCoefficientRestriction R φ D ψ α hα X ⋙ pull R φ s ⟶
      pull D ψ s ⋙ clopenCoefficientRestriction R φ D ψ α hα U :=
  (mateEquiv (moduleAdj D ψ s) (moduleAdj R φ s)).symm
    (clopenCoefficientPush R φ D ψ α hα s).inv

/-- Coefficient restriction commutes with clopen restriction.
Source: Stacks 03DI; proof steps 1 and 6
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: on the two-factor section decomposition pullback selects the first factor;
restriction of scalars leaves both factors unchanged. The identity comparison has
exactly the ordinary mate normalization, so the displayed mate is invertible. -/
theorem clopenCoefficientPullInv_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    IsIso (clopenCoefficientPullInv R φ D ψ α hα s) := by
  sorry

/-- Localize the actual ordinary coefficient/restriction comparison.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientG {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    clopenCoefficientRes R φ D ψ α hα X ⋙ G R φ s ≅
      G D ψ s ⋙ clopenCoefficientRes R φ D ψ α hα U :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (clopenCoefficientPullInv R φ D ψ α hα s)
        (clopenCoefficientPullInv_isIso R φ D ψ α hα s)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The open-extension coefficient comparison is fixed by the open adjunction mate.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientJInv {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    clopenCoefficientRes R φ D ψ α hα U ⋙ J R φ s ⟶
      J D ψ s ⋙ clopenCoefficientRes R φ D ψ α hα X :=
  (mateEquiv (jAdj D ψ s) (jAdj R φ s)).symm
    (clopenCoefficientG R φ D ψ α hα s).inv

/-- The direct-image coefficient comparison is fixed by the right adjunction mate.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientP {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    P D ψ s ⋙ clopenCoefficientRes R φ D ψ α hα X ⟶
      clopenCoefficientRes R φ D ψ α hα U ⋙ P R φ s :=
  mateEquiv (adj D ψ s) (adj R φ s) (clopenCoefficientG R φ D ψ α hα s).hom

/-- The coefficient/open mate is invertible on the whole system category.
Source: Stacks 03DI; proof step 6
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: the ordinary extension comparison is identity on the selected component
and zero on its complement, and commutes with coefficient restriction. Localize
this exact comparison and its inverse. Its transpose is clopenCoefficientG inverse,
so adjunction uniqueness identifies it with the specified mate. -/
theorem clopenCoefficientJInv_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    IsIso (clopenCoefficientJInv R φ D ψ α hα s) := by
  sorry

/-- Orient the canonical coefficient/open comparison toward restricted coefficients.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenCoefficientJ {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :=
  (@asIso _ _ _ _ (clopenCoefficientJInv R φ D ψ α hα s)
    (clopenCoefficientJInv_isIso R φ D ψ α hα s)).symm

/-- The coefficient/direct-image mate is invertible for clopen direct image.
Source: Stacks 03DI and 015F; proof step 6
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: localize the inverse of clopenCoefficientPush. Clopen direct image is exact,
so its canonical exact/right-derived comparison identifies the localization with
the displayed derived mate, with the same units and counits. -/
theorem clopenCoefficientP_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    IsIso (clopenCoefficientP R φ D ψ α hα s) := by
  sorry

/-- The three scalar-extension comparisons are the transposes of the actual
restriction comparisons under the normalized K-flat scalar adjunctions.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenScalarG {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    G R φ s ⋙ (clopenCoefficientScalar R φ D ψ α hα U).scalar.T ⟶
      (clopenCoefficientScalar R φ D ψ α hα X).scalar.T ⋙ G D ψ s :=
  (mateEquiv (clopenCoefficientScalar R φ D ψ α hα X).scalar.adjunction
    (clopenCoefficientScalar R φ D ψ α hα U).scalar.adjunction).symm
    (clopenCoefficientG R φ D ψ α hα s).hom

/-- Scalar extension of open extension, with its specified coefficient mate.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenScalarJ {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    J R φ s ⋙ (clopenCoefficientScalar R φ D ψ α hα X).scalar.T ⟶
      (clopenCoefficientScalar R φ D ψ α hα U).scalar.T ⋙ J D ψ s :=
  (mateEquiv (clopenCoefficientScalar R φ D ψ α hα U).scalar.adjunction
    (clopenCoefficientScalar R φ D ψ α hα X).scalar.adjunction).symm
    (clopenCoefficientJ R φ D ψ α hα s).inv

/-- Scalar extension of clopen direct image, with its specified coefficient mate.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def clopenScalarP {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    P R φ s ⋙ (clopenCoefficientScalar R φ D ψ α hα X).scalar.T ⟶
      (clopenCoefficientScalar R φ D ψ α hα U).scalar.T ⋙ P D ψ s :=
  (mateEquiv (clopenCoefficientScalar R φ D ψ α hα U).scalar.adjunction
    (clopenCoefficientScalar R φ D ψ α hα X).scalar.adjunction).symm
    (@inv _ _ _ _ (clopenCoefficientP R φ D ψ α hα s)
      (clopenCoefficientP_isIso R φ D ψ α hα s))

end Coefficients

/-- The four explicit coefficient-naturality squares for the clopen maps and units.
This predicate introduces no operations: its arguments are the actual coefficient
functors and the canonical comparison words constructed above.
Source: proof step 6 (blueprint: lem-sf-semilinear-clopen-unit-projector). -/
def ClopenCoefficientNaturality
    (D : ℕ → CommRingCat.{u + 1}) (ψ : ∀ n : ℕ, D (n + 1) ⟶ D n)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (EU : Derived R φ U ⥤ Derived D ψ U) (EX : Derived R φ X ⥤ Derived D ψ X)
    (g : G R φ s ⋙ EU ⟶ EX ⋙ G D ψ s)
    (j : J R φ s ⋙ EX ⟶ EU ⋙ J D ψ s)
    (p : P R φ s ⋙ EX ⟶ EU ⋙ P D ψ s) : Prop :=
  (∀ N : Derived R φ U,
    EX.map ((clopenToDirect R φ s).app N) ≫ p.app N =
      j.app N ≫ (clopenToDirect D ψ s).app (EU.obj N)) ∧
  (∀ M : Derived R φ X,
    EX.map ((clopenPi R φ s).app M) ≫ j.app ((G R φ s).obj M) ≫
        (J D ψ s).map (g.app M) = (clopenPi D ψ s).app (EX.obj M)) ∧
  (∀ N : Derived R φ U,
    EU.map ((jAdj R φ s).unit.app N) ≫ g.app ((J R φ s).obj N) ≫
        (G D ψ s).map (j.app N) = (jAdj D ψ s).unit.app (EU.obj N)) ∧
  (∀ M : Derived R φ X,
    EX.map ((adj R φ s).unit.app M) ≫ p.app ((G R φ s).obj M) ≫
        (P D ψ s).map (g.app M) = (adj D ψ s).unit.app (EX.obj M))

/-- All clopen comparisons are natural for every compatible coefficient-system map,
both for exact restriction and for unbounded K-flat derived extension of scalars.
Source: Stacks 03DI and proof step 6
(blueprint: lem-sf-semilinear-clopen-unit-projector).
Proof: restriction of scalars leaves the section pairs, inclusion (x,0) and
projection (x,y) to x unchanged. The identity-on-sections push comparison fixes
all three restriction comparisons by their adjunction transposes. Thus all four
squares commute already on ordinary systems and termwise complexes. Localize
them, using the exact/right-derived identification of clopen direct image.
For extension of scalars, the two clopen pieces identify systems with a product
of component categories. Balanced tensor maps, total tensor complexes, acyclicity
and K-flatness all split into the two components. Consequently the normalized
K-flat extension comparisons are invertible and are precisely the displayed
scalar-adjunction mates. Identity and zero commute with tensor on these actual
models. The four equations therefore descend from whole complexes of systems.
No flatness of α or of the transition maps, boundedness or cartesianness is used. -/
theorem semilinearClopen_coefficient_naturality
    (D : ℕ → CommRingCat.{u + 1}) (ψ : ∀ n : ℕ, D (n + 1) ⟶ D n)
    (α : ∀ n : ℕ, R n ⟶ D n)
    (hα : ∀ n : ℕ, α (n + 1) ≫ ψ n = φ n ≫ α n)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    ClopenCoefficientNaturality D ψ R φ s
      (clopenCoefficientRes R φ D ψ α hα U) (clopenCoefficientRes R φ D ψ α hα X)
      (clopenCoefficientG R φ D ψ α hα s).inv
      (clopenCoefficientJ R φ D ψ α hα s).hom
      (clopenCoefficientP R φ D ψ α hα s) ∧
    IsIso (clopenScalarG R φ D ψ α hα s) ∧
    IsIso (clopenScalarJ R φ D ψ α hα s) ∧
    IsIso (clopenScalarP R φ D ψ α hα s) ∧
    ClopenCoefficientNaturality R φ D ψ s
      (clopenCoefficientScalar R φ D ψ α hα U).scalar.T
      (clopenCoefficientScalar R φ D ψ α hα X).scalar.T
      (clopenScalarG R φ D ψ α hα s)
      (clopenScalarJ R φ D ψ α hα s)
      (clopenScalarP R φ D ψ α hα s) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
