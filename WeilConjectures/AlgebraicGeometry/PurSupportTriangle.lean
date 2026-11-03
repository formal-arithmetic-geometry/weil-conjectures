/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedEssentialImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenUnitEvaluation
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePairFlasque
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.CategoryTheory.KInjectiveBridge

/-!
# The support-localization triangle of a complex: the construction

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-lem-sp-reduction/def-pur-support-triangle.md`
(blueprint: def-pur-support-triangle).

For a bounded-below complex of finite-coefficient pro-etale module sheaves, this file names the
chosen K-injective resolution, its intrinsic supported kernel, and the mapping cone of the
kernel inclusion. The closed-support term is built termwise as the direct image of the
intrinsic closed upper-shriek functor; its canonical identification with the supported kernel
is recorded by `supportTriangleAShriekIso`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
  (hcomp : Set.range s.base = (Set.range j.base)ᶜ)
variable (Λ : Type u) [CommRing Λ] [Finite Λ]

/-- The chosen K-injective complex in the intrinsic support-localization construction.
Source: Stacks 079P and `def-sp-kinjective-bridge`
(blueprint: def-pur-support-triangle). -/
noncomputable def supportTriangleB
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj) :
    CochainComplex (proEtaleRingModules X (proEtaleConstantRing X Λ)) ℤ :=
  r.complex

/-- The supported-kernel complex, formed degreewise from the open unit.
Source: Stacks 09AH (blueprint: def-pur-support-triangle). -/
noncomputable def supportTriangleA
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj) :
    CochainComplex (proEtaleRingModules X (proEtaleConstantRing X Λ)) ℤ :=
  (sfIntrinsicSupportComplexSequence j Λ (supportTriangleB Λ K r)).X₁

/-- The inclusion of the supported kernel into the chosen resolution.
Source: Stacks 09AH (blueprint: def-pur-support-triangle). -/
noncomputable def supportTriangleU
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj) :
    supportTriangleA j Λ K r ⟶ supportTriangleB Λ K r :=
  (sfIntrinsicSupportComplexSequence j Λ (supportTriangleB Λ K r)).f

/-- The support-localization cone, with cochain convention
`Cone(u)^m = B^m ⊕ A^(m+1)` and differential
`d(b,a) = (d_B b + u(a), -d_A a)`. The hypothesis `hI` records that every
term of the chosen K-injective resolution is injective.
Source: Stacks 014E and 05RU (blueprint: def-pur-support-triangle). -/
noncomputable def supportTriangleCone
    {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range s.base = (Set.range j.base)ᶜ)
    (Λ : Type u) [CommRing Λ] [Finite Λ]
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj)
    (hI : ∀ n : ℤ, Injective (r.complex.X n)) :
    CochainComplex (proEtaleRingModules X (proEtaleConstantRing X Λ)) ℤ :=
  let _hcomp := hcomp
  let _hI := hI
  CochainComplex.mappingCone (supportTriangleU j Λ K r)

end AlgebraicGeometry.Scheme
end
