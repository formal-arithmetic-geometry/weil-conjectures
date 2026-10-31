/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInjectiveSupportExact
public import WeilConjectures.AlgebraicGeometry.IntrinsicFlasqueSupport
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

/-- The open direct-image complex in the support-localization construction.
Source: Stacks 09BN (blueprint: def-pur-support-triangle). -/
noncomputable def supportTriangleC
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj) :
    CochainComplex (proEtaleRingModules X (proEtaleConstantRing X Λ)) ℤ :=
  (sfIntrinsicSupportComplexSequence j Λ (supportTriangleB Λ K r)).X₃

/-- The termwise unit from the chosen resolution to its open direct image.
Source: Stacks 079P and 09BN (blueprint: def-pur-support-triangle). -/
noncomputable def supportTriangleUnit
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj) :
    supportTriangleB Λ K r ⟶ supportTriangleC j Λ K r :=
  (sfIntrinsicSupportComplexSequence j Λ (supportTriangleB Λ K r)).g

/-- The supported-kernel complex, formed degreewise from the open unit.
Source: Stacks 09AH (blueprint: def-pur-support-triangle). -/
noncomputable def supportTriangleA
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj) :
    CochainComplex (proEtaleRingModules X (proEtaleConstantRing X Λ)) ℤ :=
  (sfIntrinsicSupportComplexSequence j Λ (supportTriangleB Λ K r)).X₁

/-- The closed-support term, built as `s_* s^! I(K)` termwise.
Source: Stacks 09AH and the intrinsic closed-support construction
(blueprint: def-pur-support-triangle). -/
noncomputable def supportTriangleAShriek
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj) :
    CochainComplex (proEtaleRingModules X (proEtaleConstantRing X Λ)) ℤ :=
  ((sfIntrinsicClosedUpperShriek s j Λ ⋙ sfConstantModuleDirectImage s Λ).mapHomologicalComplex
    (.up ℤ)).obj (supportTriangleB Λ K r)

/-- The canonical identification of the supported kernel with the closed-support term.
The quasi-compact hypothesis supplies the invertibility of the natural comparison.
Source: Stacks 09AH (blueprint: def-pur-support-triangle). -/
noncomputable def supportTriangleAShriekIso
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj) :
    supportTriangleA j Λ K r ≅ supportTriangleAShriek (s := s) (j := j) Λ K r := by
  let hPair : IsCompl (Set.range s) (Set.range j) := by
    rw [hcomp]
    exact isCompl_compl.symm
  letI : IsIso (sfIntrinsicSupportedComparison s j Λ) :=
    (sfIntrinsicFlasqueSupport Λ s j hPair).2.2.2.2.1
  let e : sfIntrinsicSectionsWithSupport j Λ ≅
      sfIntrinsicClosedUpperShriek s j Λ ⋙ sfConstantModuleDirectImage s Λ :=
    NatIso.ofComponents (fun M ↦ asIso ((sfIntrinsicSupportedComparison s j Λ).app M)) (by
      intro M N f
      exact (sfIntrinsicSupportedComparison s j Λ).naturality f)
  exact (NatIso.mapHomologicalComplex e (.up ℤ)).app (supportTriangleB Λ K r)

/-- The inclusion of the supported kernel into the chosen resolution.
Source: Stacks 09AH (blueprint: def-pur-support-triangle). -/
noncomputable def supportTriangleU
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj) :
    supportTriangleA j Λ K r ⟶ supportTriangleB Λ K r :=
  (sfIntrinsicSupportComplexSequence j Λ (supportTriangleB Λ K r)).f

/-- The closed-support inclusion, transported along the canonical kernel comparison.
Source: Stacks 09AH (blueprint: def-pur-support-triangle). -/
noncomputable def supportTriangleUShriek
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X Λ)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj) :
    supportTriangleAShriek s j Λ K r ⟶ supportTriangleB Λ K r :=
  (supportTriangleAShriekIso s j hcomp Λ K r).inv ≫ supportTriangleU j Λ K r

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
