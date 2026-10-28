/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower
public import Sheaf.SixFunctors.IntegralDualizingResolvedGlobalHom
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv

/-! # Strict global Hom cochains before taking any inverse limit

Source: Stacks Project, Tags 0A95, 0A96, 08JA and 0941.
(blueprint: lem-coef-integral-dualizing-resolved-mapping-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Transpose the strict tower of signed global Hom complexes, keeping its maps.
Source: Stacks 08JA, 0941
(blueprint: lem-coef-integral-dualizing-resolved-mapping-tower). -/
def integralDualizingResolvedMappingCochains
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :
    (CochainComplex (scalarReductionSource l E X) ℤ)ᵒᵖ ⥤
      CochainComplex (coefPairingModules l E) ℤ :=
  integralDualizingResolvedHom l E X ⋙
    (Functor.whiskeringLeft _ _ _).obj I.asFunctor ⋙
      HomologicalComplex.functorEquivalence.inverse _ (.up ℤ) ℕᵒᵖ

/-- The sequence-site derived mapping tower is represented by strict signed global
Hom cochains, naturally in every source complex, before applying any inverse limit.

Source: Stacks Project, sites-cohomology.tex, Tags 0A95, 0A96 and 08JA; Tag 0941,
proof of lemma-derived-limit-is-ok, sequence-site internal-Hom calculation.
(blueprint: lem-coef-integral-dualizing-resolved-mapping-tower).

Proof: carry I through the additive exact constant-ring sequence equivalence.
It stays K-injective. The exact constant-source functor commutes with localization.
The replacement-normalized internal-Hom comparison identifies derived internal Hom
with the sheaf Hom complex into this K-injective. For a flat-term K-flat source,
that Hom complex is K-injective and ordinary sequence sections compute its derived
sections. Restricting a slice morphism to its terminal sequence index gives the
signed Hom complex into I_n, with postcomposition transitions. Reconstruction from
that component is inverse, and both operations commute with precomposition.
For an arbitrary source P take a K-flat resolution P' to P. K-injectivity of I and
of each evaluation I_n makes both the sheaf Hom and global Hom precomposition maps
quasi-isomorphisms. Naturality of the derived-sections unit then proves its
invertibility for P too. The scalar action on compatible sections is the specified
integralDualizingScalarSections action, so this identification is in strict towers
of integral modules. These canonical maps give a natural isomorphism without
choosing a functorial K-flat resolution. Zero sources and zero targets are included.
No injectivity of the terms of I and no assertion about limits is used. -/
theorem integralDualizing_resolved_mappingTower
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ)
    [I.IsKInjective] :
    Nonempty (DerivedCategory.Q.op ⋙
      (coefHomDerivedConstant l E X).op ⋙
      (Functor.curry.obj (coefHomConstantInternalHom l E X)).flip.obj
        ((coefHomEquivalence l E X).inverse.mapDerivedCategory.obj
          (DerivedCategory.Q.obj I)) ⋙ coefHomConstantDerivedSections l E X ≅
      integralDualizingResolvedMappingCochains l E X I ⋙ DerivedCategory.Q) := by sorry

end WeilConjectures
