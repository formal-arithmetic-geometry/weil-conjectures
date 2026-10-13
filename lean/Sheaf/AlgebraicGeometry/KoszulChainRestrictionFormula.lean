/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction
import Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology
import Sheaf.Paper.AffinePerfectKoszulPrincipalUnitIso

/-! # The restriction formula for a Koszul chain representative

Source: Stacks Project, Tags 06Z0, 08DC and 08DD.
(blueprint: lem-sc-koszul-chain-restriction-formula).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The canonical comparison on an actual chain representative is restriction followed
by inverse augmentation and evaluation at one.
Source: Stacks Project, Equation 36.9.4.1, Tag 08DC; Tags 08D1 and 08DD.
(blueprint: lem-sc-koszul-chain-restriction-formula)

Proof: On the principal intersection indexed by J, apply the canonical affine counit
s to the module chain map g. The Koszul-to-Cech cocone evaluates g on the ordered wedge
and divides by the product of the f_j to exponent e+1. Contracting the localized full
Koszul complex with a generator whose f_j is invertible shows that the same fraction
represents restriction composed with the inverse augmentation. The totalization sign
in the cocone is precisely the sign converting the negative tail differential into
the alternating Cech differential. Pass this equality to degree-zero homology; hz
identifies the cycle represented by g. The Cech-to-derived-sections map carries it to
the corresponding derived section. Evaluation at one identifies sections with Hom
from the restricted structure object, additively, and postcomposition by eF transports
the target. This supplies b and the equality for every psi satisfying the displayed
augmentation equation; invertibility is given by
affine_perfect_koszul_principal_unit_iso at exponent e+1. Empty cover and zero ring yield
zero groups; no exactness of
filtered colimits, regularity, boundedness of F or injectivity is used. -/
theorem koszulChain_restriction_formula
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (eF : DerivedCategory.Q.obj F ≅ E.obj)
    (s : ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj
      (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F) ≅ F)
    (hs : ∀ n : ℤ, s.hom.f n = Scheme.Modules.fromTildeΓ (R := .of A) (F.X n)) :
    let R := ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{u}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
    let D := koszulCechHomDiagram A r f M
    let C := koszulCechHomColimit A r f M
    let β := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app C).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (koszulCechDerivedComparison A r f F ≫
          (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map eF.hom)
    ∃ b : (R.obj (koszulOpenStructure A) ⟶ R.obj E.obj) ≃+
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.obj E.obj),
      ∀ (e : ℕ)
        (g : (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat ⟶ M)
        (z : (CochainComplex.moduleHomComplex
          ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M).cycles 0),
        (CochainComplex.moduleHomComplex
          ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M).iCycles 0 z =
            CochainComplex.HomComplex.Cochain.ofHom g →
        ∀ ψ : R.obj (koszulOpenStructure A) ⟶ R.obj E.obj,
          R.map (koszulOpenUnit A r f e) ≫ ψ =
            R.map (DerivedCategory.Q.map
              (((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map g) ≫
                DerivedCategory.Q.map s.hom ≫ eF.hom) →
          b ψ = β (HomologicalComplex.homologyMap (colimit.ι D e) 0
            (HomologicalComplex.homologyMap (koszulCechHomObjIso A r f M e).inv 0
              ((CochainComplex.moduleHomComplex
                ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M).homologyπ
                  0 z))) := by
  sorry

end AlgebraicGeometry
