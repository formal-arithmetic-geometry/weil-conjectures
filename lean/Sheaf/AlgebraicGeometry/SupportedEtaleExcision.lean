/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.ElementaryEtaleShriekExact
public import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
public import Sheaf.CategoryTheory.ExactDerivedAdjunction
import Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Supported étale excision for unbounded structure-sheaf modules

Source: Stacks Project, Derived Categories of Spaces, Tag 08GG(2), and
Modules on Sites, Tags 03DI--03DJ
(blueprint: lem-sfb-space-supported-etale-excision).

Extension by zero is transported through the existing affine-basis equivalences.
The comparison is specified by its adjoint transpose and is natural on the entire
full subcategory of complexes vanishing on the overlap.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X V : AlgebraicSpace S}

/-- The existing module extension by zero in the equivalent small affine models.
Source: Stacks 03DI and 039Z (blueprint: lem-sfb-space-supported-etale-excision). -/
def smallEtaleModuleShriek (p : V ⟶ X) (hp : IsEtale p.hom.hom) :
    V.SmallModules ⥤ X.SmallModules :=
  V.smallModuleEquivalence.inverse ⋙ etaleModuleShriek p hp ⋙ X.smallModuleRestriction

/-- Transport the actual shriek adjunction and the multiplication-normalized
identification of tensor pullback with literal étale restriction.
Source: Stacks 03DI, 03LV, 03LW and 039Z
(blueprint: lem-sfb-space-supported-etale-excision). -/
def smallEtaleModuleShriekAdjunction (p : V ⟶ X) (hp : IsEtale p.hom.hom) :
    smallEtaleModuleShriek p hp ⊣ smallModuleTensorPullback p :=
  Adjunction.ofNatIsoRight
    ((V.smallModuleEquivalence.symm.toAdjunction.comp
      (etaleModuleShriekAdjunction p hp)).comp X.smallModuleEquivalence.toAdjunction)
    (isoWhiskerLeft X.smallModuleEquivalence.inverse
      (isoWhiskerRight (Classical.choose
        (moduleTensorPullback_etale_restriction p hp)).symm V.smallModuleRestriction))

/-- Exactness and additivity of the transported extension by zero, without size or
finiteness conditions on the étale morphism beyond the fixed universe convention.
Source: Stacks 03DI--03DJ and 08GG(2)
(blueprint: lem-sfb-space-supported-etale-excision).
Proof: etaleModuleShriek is the sheafification of direct sums over lifts, as in
lem-sfb-space-elementary-shriek-exact and lem-pur-site-restriction-module-adjunction-exact.
Direct sums and module sheafification are exact and additive. The affine-basis
equivalences preserve all finite limits, colimits, and biproducts. Their composite
therefore has these same properties, including for the empty space and infinite fibres. -/
theorem smallEtaleModuleShriek_exact (p : V ⟶ X) (hp : IsEtale p.hom.hom) :
    (smallEtaleModuleShriek p hp).Additive ∧
      PreservesFiniteLimits (smallEtaleModuleShriek p hp) ∧
      PreservesFiniteColimits (smallEtaleModuleShriek p hp) := by
  sorry

/-- Additivity inherited from the exact module extension.
Source: Stacks 03DI (blueprint: lem-sfb-space-supported-etale-excision). -/
instance smallEtaleModuleShriek_additive (p : V ⟶ X) (hp : IsEtale p.hom.hom) :
    (smallEtaleModuleShriek p hp).Additive := (smallEtaleModuleShriek_exact p hp).1

/-- Finite-limit preservation inherited from the exact module extension.
Source: Stacks 03DJ (blueprint: lem-sfb-space-supported-etale-excision). -/
instance smallEtaleModuleShriek_limits (p : V ⟶ X) (hp : IsEtale p.hom.hom) :
    PreservesFiniteLimits (smallEtaleModuleShriek p hp) :=
  (smallEtaleModuleShriek_exact p hp).2.1

/-- Finite-colimit preservation inherited from the exact module extension.
Source: Stacks 03DI (blueprint: lem-sfb-space-supported-etale-excision). -/
instance smallEtaleModuleShriek_colimits (p : V ⟶ X) (hp : IsEtale p.hom.hom) :
    PreservesFiniteColimits (smallEtaleModuleShriek p hp) :=
  (smallEtaleModuleShriek_exact p hp).2.2

variable [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} V.SmallModules]

/-- Termwise extension by zero on the unbounded derived category.
Source: Stacks 015F and 08GG (blueprint: lem-sfb-space-supported-etale-excision). -/
def spaceEtaleDerivedShriek (p : V ⟶ X) (hp : IsEtale p.hom.hom) :
    V.DerivedModules ⥤ X.DerivedModules :=
  (smallEtaleModuleShriek p hp).mapDerivedCategory

/-- The localized actual shriek adjunction, transported along the canonical exact
restriction comparison fixed on complex representatives.
Source: Stacks 015F, 08FJ and 08GG
(blueprint: lem-sfb-space-supported-etale-excision). -/
def spaceEtaleShriekAdjunction (p : V ⟶ X) (hp : IsEtale p.hom.hom) :
    spaceEtaleDerivedShriek p hp ⊣ spaceDerivedPullback p :=
  letI := (spaceEtaleTensorPullback_exact p hp).1
  letI := (spaceEtaleTensorPullback_exact p hp).2
  (smallEtaleModuleShriekAdjunction p hp).mapExactDerivedCategory.ofNatIsoRight
    (Classical.choose (spaceEtaleDerivedRestriction_existsUnique p hp)).symm

/-- The canonical shift comparison of exact étale restriction, transported to the
already fixed derived tensor pullback using its representative-normalized comparison.
Source: Stacks 015F and 08GG (blueprint: lem-sfb-space-supported-etale-excision). -/
def spaceEtalePullbackShift (p : V ⟶ X) (hp : IsEtale p.hom.hom) (n : ℤ) :
    shiftFunctor X.DerivedModules n ⋙ spaceDerivedPullback p ≅
      spaceDerivedPullback p ⋙ shiftFunctor V.DerivedModules n :=
  letI := (spaceEtaleTensorPullback_exact p hp).1
  letI := (spaceEtaleTensorPullback_exact p hp).2
  isoWhiskerLeft (shiftFunctor X.DerivedModules n)
      (Classical.choose (spaceEtaleDerivedRestriction_existsUnique p hp)) ≪≫
    (smallModuleTensorPullback p).mapDerivedCategory.commShiftIso n ≪≫
    isoWhiskerRight (Classical.choose
      (spaceEtaleDerivedRestriction_existsUnique p hp)).symm (shiftFunctor V.DerivedModules n)

/-- On supported complexes, the canonical comparison from extension by zero to
derived direct image is a natural isomorphism. Its transpose is inverse to the
shriek unit; the direct-image counit is invertible, restriction to U vanishes, and
precomposition followed by shriek adjunction gives the natural shifted Hom bijection.

Source: Stacks Project, spaces-perfect.tex, Tag 08GG(2), with Tags 08GE and 08H9;
sites-cohomology.tex, Tag 08FJ
(blueprint: lem-sfb-space-supported-etale-excision).

Proof:
1. Localize the exact additive adjunction of lem-sfb-space-elementary-shriek-exact
using def-weil-exact-derived-adjunction and the termwise factorizations of
lem-weil-pbc-exact-functor-derived-factorization. The other adjunction is the canonical
one of lem-sfb-space-derived-etale-chart-calculus. Write L=p_!, P=p*, R=Rp_*.
2. The forgetful functor is exact by lem-weil-pbc-module-sheaves-colimits-forgetful.
Geometric module stalks preserve cohomology and detect isomorphisms by
lem-sfb-space-etale-conservative-geometric-points. Exact L and P commute with cohomology.
3. The sum-stalk formula of lem-sfb-space-etale-sum-stalks shows LF vanishes on U:
every lift lies in T and F vanishes there. Outside U a geometric point factors through
the reduced closed complement, by lem-sfb-space-reduced-closed-support: the closed
subscheme of a field spectrum has proper, hence zero, ideal. The assumed isomorphism
over that complement makes its lift to V unique. No reducedness after base change is used.
4. The localized shriek unit on stalks is inclusion into the given lift's summand,
by def-weil-extension-by-zero-presheaf and the actual adjunction construction in
lem-pur-site-restriction-module-adjunction-exact. Outside U it is the singleton identity;
over U its source and all summands vanish. Thus alpha:F -> PLF is invertible.
5. Etale base change from lem-sfb-space-derived-etale-chart-calculus gives
i*RF = Rq_*t*F = 0. The same stalk calculation gives i*LF=0.
6. For every B vanishing on U, lem-sfb-space-derived-hom-mayer-vietoris makes
Hom(A,B) -> Hom(PA,PB) bijective: its U and overlap terms and their adjacent shifts vanish.
Under P adjoint R this is postcomposition with eta_B:B -> RPB, by the triangle identity.
Taking A=RPB produces a right inverse, and injectivity for A=B makes it a left inverse.
Hence eta_B is invertible; apply this to B=LF.
7. Set c_F = eta_LF followed by R(alpha_F inverse). Naturality and the triangle
identity show its transpose is alpha_F inverse. Both factors are invertible. The same
identity implies the canonical counit PRF -> F is invertible. These constructions are
natural on the full subcategory t*F=0, giving the stated natural isomorphism c.
8. Precompose h:RF -> M[n] with c_F and apply L adjoint P, then the canonical
exact-functor shift comparison P(M[n]) -> (PM)[n]. Each step is a bijection and natural
in F and M; all integers n and all unbounded module complexes are allowed. -/
theorem supported_etale_excision {U T : AlgebraicSpace S}
    [HasDerivedCategory.{w} U.SmallModules] [HasDerivedCategory.{w} T.SmallModules]
    (i : U ⟶ X) (p : V ⟶ X)
    (hi : IsRepresentableWith (fun _ _ f ↦ IsOpenImmersion f.left) i.hom.hom)
    (hp : IsEtale p.hom.hom) (Z : ClosedSubspace X)
    (hZ : IsReduced (Z.val : AlgebraicSpace S))
    (hSupport : pointImage Z.val.arrow.hom.hom = (pointImage i.hom.hom)ᶜ)
    (hIso : IsIso (Limits.pullback.snd p.hom Z.val.arrow.hom))
    (q : T ⟶ U) (t : T ⟶ V) (sq : IsPullback q t i p) :
    ∃ c : (ObjectProperty.ι (fun F : V.DerivedModules ↦
          IsZero ((spaceDerivedPullback t).obj F))) ⋙ spaceEtaleDerivedShriek p hp ≅
        (ObjectProperty.ι (fun F : V.DerivedModules ↦
          IsZero ((spaceDerivedPullback t).obj F))) ⋙ derivedDirectImage p,
      ∀ F : ObjectProperty.FullSubcategory
          (fun F : V.DerivedModules ↦ IsZero ((spaceDerivedPullback t).obj F)),
        IsIso ((spaceEtaleShriekAdjunction p hp).unit.app F.obj) ∧
        (spaceEtaleShriekAdjunction p hp).unit.app F.obj ≫
            ((spaceDerivedAdjunction p).homEquiv _ _).symm (c.hom.app F) = 𝟙 F.obj ∧
        IsIso ((spaceDerivedAdjunction p).counit.app F.obj) ∧
        IsZero ((spaceDerivedPullback i).obj ((derivedDirectImage p).obj F.obj)) ∧
        ∀ (M : X.DerivedModules) (n : ℤ),
          Function.Bijective (fun h : (derivedDirectImage p).obj F.obj ⟶ M⟦n⟧ ↦
            (spaceEtaleShriekAdjunction p hp).homEquiv F.obj (M⟦n⟧)
                (c.hom.app F ≫ h) ≫
              (spaceEtalePullbackShift p hp n).hom.app M) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
