/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.CategoryTheory.CondensedProductBarComparison
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Sheaf.CategoryTheory.CondensedProductActionInflation
import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
import Sheaf.CategoryTheory.InternalActionSitePresentation
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

/-! # Canonical derived inflation and scalar-restriction arrows

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
normalized derived-invariant arrow constructions
(blueprint: def-sfb-condensed-derived-inflation-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace Profinite.CondensedAction.PrimeToEll

section DerivedInflation
variable (R : CondensedRing.{u}) [IsCommMonObj R.X]
  (P Q : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]

/-- Use the standard localization size for ordinary internal modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
instance modulesDerived : HasDerivedCategory.{u + 2} (Modules R) :=
  HasDerivedCategory.standard _

/-- Use the same standard localization size for internal action modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
instance actionsDerived : HasDerivedCategory.{u + 2} (ActionModule R P) :=
  HasDerivedCategory.standard _

/-- Normalized invariants are additive by their recorded specification.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
instance invariantsAdditive (d : Invariants R P) : d.functor.Additive := d.additive

/-- Action restriction is exact since it leaves all underlying modules and maps unchanged.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows).

Proof: equivariance is preserved under addition. The kernel and sheafified cokernel
created by forgetting actions acquire the restricted action by precomposition with pi.
Their universal maps retain the same underlying maps, proving preservation of kernels
and cokernels and hence finite limits and finite colimits. -/
theorem inflation_exact (π : P →ₜ* Q) :
    (inflate (R := R) π).Additive ∧
    PreservesFiniteLimits (inflate (R := R) π) ∧
    PreservesFiniteColimits (inflate (R := R) π) := by
  sorry

/-- Additivity of the actual action restriction functor.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
instance inflateAdditive (π : P →ₜ* Q) : (inflate (R := R) π).Additive :=
  (inflation_exact R P Q π).1

/-- Left exactness of the actual action restriction functor.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
instance inflateLimits (π : P →ₜ* Q) : PreservesFiniteLimits (inflate (R := R) π) :=
  (inflation_exact R P Q π).2.1

/-- Right exactness of the actual action restriction functor.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
instance inflateColimits (π : P →ₜ* Q) : PreservesFiniteColimits (inflate (R := R) π) :=
  (inflation_exact R P Q π).2.2

/-- Trivial action followed by restriction is the same trivial action. The components
are identities on the original module, fixing the normalization of derived inflation.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
def trivialInflationIso (π : P →ₜ* Q) :
    trivial (R := R) (P := P) ≅
      trivial (R := R) (P := Q) ⋙ inflate (R := R) π :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The canonical inflation morphism: transpose the restricted counit followed by h.
This uses exactly the derived adjunctions of the normalized ordinary invariants.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
def derivedInflation (π : P →ₜ* Q) (dP : Invariants R P) (dQ : Invariants R Q)
    (X : DerivedCategory (ActionModule R Q)) (Y : DerivedCategory (ActionModule R P))
    (h : (inflate (R := R) π).mapDerivedCategory.obj X ⟶ Y) :
    dQ.functor.rightDerivedFunctor.obj X ⟶ dP.functor.rightDerivedFunctor.obj Y :=
  dP.adjunction.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
    ((Functor.mapDerivedCategoryNatIso (trivialInflationIso R P Q π) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app _ ≫
      (inflate (R := R) π).mapDerivedCategory.map
        (dQ.adjunction.mapDerivedCategoryRightDerivedAdjunction.counit.app X) ≫ h)

/-- Degree-zero input is inserted using the canonical exact-functor/single comparison.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
def inflationZero (π : P →ₜ* Q) (dP : Invariants R P) (dQ : Invariants R Q)
    {M : ActionModule R Q} {N : ActionModule R P}
    (i : (inflate (R := R) π).obj M ⟶ N) :
    dQ.functor.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      dP.functor.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj N) :=
  derivedInflation R P Q π dP dQ _ _
    (((inflate (R := R) π).mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor _ 0).map i)

/-- The ordinary inflation map on fixed submodules, with the same adjunction normalization.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
def invariantMap (π : P →ₜ* Q) (dP : Invariants R P) (dQ : Invariants R Q)
    {M : ActionModule R Q} {N : ActionModule R P}
    (i : (inflate (R := R) π).obj M ⟶ N) : dQ.functor.obj M ⟶ dP.functor.obj N :=
  dP.adjunction.homEquiv _ _
    ((trivialInflationIso R P Q π).hom.app _ ≫
      (inflate (R := R) π).map (dQ.adjunction.counit.app M) ≫ i)

/-- The ordinary map is inclusion on invariant sections.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows).
Proof: apply the forward-transpose formula for dP, the inverse-transpose formula for
dQ, and the identity components of trivialInflationIso. All maps retain their actual
section maps, so composing with the invariant inclusion gives i after inclusion. -/
theorem invariantMap_inclusion (π : P →ₜ* Q) (dP : Invariants R P) (dQ : Invariants R Q)
    {M : ActionModule R Q} {N : ActionModule R P}
    (i : (inflate (R := R) π).obj M ⟶ N) :
    invariantMap R P Q π dP dQ i ≫ dP.inclusion.app N =
      dQ.inclusion.app M ≫ i.val := by
  sorry

/-- The canonical map from ordinary fixed sections in degree zero to derived invariants.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
def unitZero (d : Invariants R P) (N : ActionModule R P) :
    (DerivedCategory.singleFunctor _ 0).obj (d.functor.obj N) ⟶
      d.functor.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj N) :=
  (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app (d.functor.obj N) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex d.functor (.up ℤ) 0).inv.app N) ≫
    d.functor.rightDerivedFunctorUnitQ ((CochainComplex.singleFunctor _ 0).obj N) ≫
    d.functor.rightDerivedFunctor.map
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app N)

/-- Degree zero of the canonical unit is an isomorphism because invariants are left exact.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows).
Proof: on an injective resolution, degree-zero cohomology is the kernel of the first
differential. A right adjoint preserves that kernel and identifies it with the ordinary
invariant object. The unit is this kernel identification, including on the zero object. -/
theorem unitZero_h0_isIso (d : Invariants R P) (N : ActionModule R P) :
    IsIso ((DerivedCategory.homologyFunctor (Modules R) 0).map (unitZero R P d N)) := by
  sorry

/-- The derived map agrees with ordinary inclusion on degree-zero invariants. Together
with unitZero_h0_isIso and invariantMap_inclusion this specifies the H^0 map exactly.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows).
Proof: the unit and counit equations for the normalized derived adjunctions agree on
complexes with the ordinary transpose equations followed by the right-derived units.
Substitute the defining transpose for inflationZero; naturality of the derived unit
and the two triangle identities give the displayed equality. -/
theorem inflationZero_unit (π : P →ₜ* Q) (dP : Invariants R P) (dQ : Invariants R Q)
    {M : ActionModule R Q} {N : ActionModule R P}
    (i : (inflate (R := R) π).obj M ⟶ N) :
    unitZero R Q dQ M ≫ inflationZero R P Q π dP dQ i =
      (DerivedCategory.singleFunctor _ 0).map (invariantMap R P Q π dP dQ i) ≫
        unitZero R P dP N := by
  sorry

/-- Naturality of the actual inflation arrow in every commutative equivariant square.
Continuous equivariant E-linear maps give exactly these squares by their section formulas.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows).
Proof: naturality of the derived counit and of the adjunction hom bijection moves f
through the defining transpose. The given inclusion square then replaces the final
composite by g. Transpose back to obtain the displayed equality. -/
theorem derivedInflation_natural (π : P →ₜ* Q) (dP : Invariants R P) (dQ : Invariants R Q)
    {X X' : DerivedCategory (ActionModule R Q)}
    {Y Y' : DerivedCategory (ActionModule R P)}
    (h : (inflate (R := R) π).mapDerivedCategory.obj X ⟶ Y)
    (h' : (inflate (R := R) π).mapDerivedCategory.obj X' ⟶ Y')
    (f : X ⟶ X') (g : Y ⟶ Y')
    (_hsq : (inflate (R := R) π).mapDerivedCategory.map f ≫ h' = h ≫ g) :
    dQ.functor.rightDerivedFunctor.map f ≫ derivedInflation R P Q π dP dQ X' Y' h' =
      derivedInflation R P Q π dP dQ X Y h ≫ dP.functor.rightDerivedFunctor.map g := by
  sorry

/-- Restricting along the identity has identity component maps.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
def inflateIdentityIso : inflate (R := R) (ContinuousMonoidHom.id P) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- After the evident trivial-factor identifications, inflation is the identity.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows).
Proof: restriction by the identity has identity components. The single and composition
comparisons descend those identities. The transpose defining derivedInflation is then
the derived counit; its transpose is the identity by the adjunction triangle identity.
For B trivial, projection B times L to L and the fixed-space inclusion become exactly
these identity maps under the canonical group and vector-space identifications. -/
theorem derivedInflation_identity (d : Invariants R P)
    (X : DerivedCategory (ActionModule R P)) :
    derivedInflation R P P (ContinuousMonoidHom.id P) d d X X
      ((Functor.mapDerivedCategoryNatIso (inflateIdentityIso R P) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app X) = 𝟙 _ := by
  sorry

end DerivedInflation

section CoefficientMaps
open CategoryTheory.CondensedBar
variable (A A' : CategoryTheory.CondensedBar.Ring.{u})
  (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

/-- The existing action abelian structure, in the interface used by the normalized bar
coefficient comparisons. Only proof fields are repackaged; the addition is unchanged.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
instance coefficientActionAbelian : CategoryTheory.CondensedBar.ActionAbelian A P where
  normalMono := (productBarActionAbelian A.toMon P).toIsNormalMonoCategory
  normalEpi := (productBarActionAbelian A.toMon P).toIsNormalEpiCategory
  products := (productBarActionAbelian A.toMon P).has_finite_products
  kernels := (productBarActionAbelian A.toMon P).has_kernels
  cokernels := (productBarActionAbelian A.toMon P).has_cokernels

variable {A A' P} (a : A ⟶ A') (M : Model A P) (M' : Model A' P)
  (s : ScalarModel a M M') (c : ScalarComputation a s)

/-- The canonical coefficient arrow, computed on any compatible injective resolutions.
The scalar comparison of invariant-resolution complexes is the recorded normalized
comparison, whose inverse is used after localization. All maps and inverses are fixed.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
def coefficientMap {N : ActionModule A.toMon P} {N' : ActionModule A'.toMon P}
    (f : N ⟶ s.restriction.functor.obj N')
    (I : InjectiveResolution (s.restriction.functor.obj N')) (J : InjectiveResolution N')
    (β : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶
      I.cocomplex) (hβ : s.restriction.functor.map (J.ι.f 0) ≫ β.f 0 = I.ι.f 0) :
    M.invariants.functor.rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N) ⟶
      (Mod.comap a.hom.hom).mapDerivedCategory.obj
        (M'.invariants.functor.rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj N')) :=
  M.invariants.functor.rightDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map f) ≫
    (resolutionComparison M.invariants I).hom ≫
    (localizedIso (scalarInvariantChain a s J.cocomplex I.cocomplex β)
      (c.invariantQI N' I J β hβ)).inv ≫
    DerivedCategory.Q.map
      (HomologicalComplex.mapExtendIso
        ((M'.invariants.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
        ComplexShape.embeddingUpNat (Mod.comap a.hom.hom)).inv ≫
    (Mod.comap a.hom.hom : CategoryTheory.CondensedBar.Modules A' ⥤
      CategoryTheory.CondensedBar.Modules A).mapDerivedCategoryFactors.inv.app
        (extend ((M'.invariants.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex)) ≫
    (Mod.comap a.hom.hom).mapDerivedCategory.map
      (resolutionComparison M'.invariants J).inv

/-- Scalar restriction commutes with action restriction by the unique comparison whose
underlying module maps are the identity. This is a characterization, not extra data.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows).
Proof: compose the two underlying scalar-action identifications with each other, one
inverted. They retain the original module and its generalized action. The action law
of ScalarAction makes the resulting map equivariant. Naturality and invertibility
follow from those identifications. Their normalization makes every underlying map
fixed, and faithfulness of forgetting actions proves uniqueness. -/
theorem scalarInflation_comparison {Q : Type u} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (π : P →ₜ* Q) (t : ScalarAction a Q) :
    ∃! e : t.functor ⋙ inflate (R := A.toMon) π ≅
        inflate (R := A'.toMon) π ⋙ s.restriction.functor,
      ∀ N : ActionModule A'.toMon Q,
        (e.hom.app N).val ≫
          s.restriction.underlying.hom.app ((inflate (R := A'.toMon) π).obj N) =
        t.underlying.hom.app N := by
  sorry

/-- The unique normalized scalar/action restriction comparison.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows). -/
def scalarInflationIso {Q : Type u} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (π : P →ₜ* Q) (t : ScalarAction a Q) :
    t.functor ⋙ inflate (R := A.toMon) π ≅
      inflate (R := A'.toMon) π ⋙ s.restriction.functor :=
  Classical.choose (scalarInflation_comparison a M M' s π t).exists

variable {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
  (π : P →ₜ* Q) (M_Q : Model A Q) (M'_Q : Model A' Q)
  (sQ : ScalarModel a M_Q M'_Q) (cQ : ScalarComputation a sQ)

/-- Inflation commutes with canonical derived coefficient maps. This is the node's
coefficient square, in a presentation independent of resolutions and scalar-action models.
The equation on the underlying comparison says its sections are the identity, fixing
its normalization; the final inclusion square is induced by v mapping to 1 tensor v.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-inflation-arrows).

Proof: choose the four indicated injective resolutions and the normalized lifts beta.
The scalar comparison is the inverse of the localized invariant-chain comparison.
The ordinary invariant identifications commute with the invariant inclusions, by
ScalarModel.inclusion. Both group inflation transposes therefore have the same map
on the two invariant-resolution complexes after the given inclusion square. The
normalized action comparison carries generalized group elements identically.
The comparison equation in lem-sfb-derived-invariants-normal-subgroup-comparison,
or equivalently the normalized bar augmentation square, identifies their localizations
with the two defining derived adjunction transposes. Invert the scalar comparison
quasi-isomorphisms. Independence of all lifts follows because two lifts are homotopic,
and localization kills their difference. This proves the exact displayed square. -/
theorem inflationZero_coefficients
    (e : sQ.restriction.functor ⋙ inflate (R := A.toMon) π ≅
      inflate (R := A'.toMon) π ⋙ s.restriction.functor)
    (_he : ∀ N : ActionModule A'.toMon Q,
      (e.hom.app N).val ≫
        s.restriction.underlying.hom.app ((inflate (R := A'.toMon) π).obj N) =
      sQ.restriction.underlying.hom.app N)
    {NQ : ActionModule A.toMon Q} {NP : ActionModule A.toMon P}
    {N'Q : ActionModule A'.toMon Q} {N'P : ActionModule A'.toMon P}
    (i : (inflate (R := A.toMon) π).obj NQ ⟶ NP)
    (i' : (inflate (R := A'.toMon) π).obj N'Q ⟶ N'P)
    (fQ : NQ ⟶ sQ.restriction.functor.obj N'Q)
    (fP : NP ⟶ s.restriction.functor.obj N'P)
    (_hsq : (inflate (R := A.toMon) π).map fQ ≫ e.hom.app N'Q ≫
        s.restriction.functor.map i' = i ≫ fP)
    (IP : InjectiveResolution (s.restriction.functor.obj N'P))
    (JP : InjectiveResolution N'P)
    (βP : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj JP.cocomplex ⟶
      IP.cocomplex) (hβP : s.restriction.functor.map (JP.ι.f 0) ≫ βP.f 0 = IP.ι.f 0)
    (IQ : InjectiveResolution (sQ.restriction.functor.obj N'Q))
    (JQ : InjectiveResolution N'Q)
    (βQ : (sQ.restriction.functor.mapHomologicalComplex (.up ℕ)).obj JQ.cocomplex ⟶
      IQ.cocomplex) (hβQ : sQ.restriction.functor.map (JQ.ι.f 0) ≫ βQ.f 0 = IQ.ι.f 0) :
    inflationZero A.toMon P Q π M.invariants M_Q.invariants i ≫
        coefficientMap a M M' s c fP IP JP βP hβP =
      coefficientMap a M_Q M'_Q sQ cQ fQ IQ JQ βQ hβQ ≫
        (Mod.comap a.hom.hom).mapDerivedCategory.map
          (inflationZero A'.toMon P Q π M'.invariants M'_Q.invariants i') := by
  sorry

end CoefficientMaps

end Profinite.CondensedAction.PrimeToEll
