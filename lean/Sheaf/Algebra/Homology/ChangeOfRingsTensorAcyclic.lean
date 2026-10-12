/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.KFlat

/-!
# Detecting acyclicity of change of rings by total tensor

Source: Stacks Project, Tag 06YY.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- Universal tensor acyclicity implies acyclicity after extension of scalars.
Source: Stacks Project, Tag 06YY, and the degree-zero total tensor comparison.

Proof: Regard O' as an O-module S by restriction of scalars, and take its single
complex in degree zero. Apply hT to this single complex. The degree-n total is
S ⊗ K^n, since all other S-degrees are zero, and its differential is id_S ⊗ d_K.
Sheafification of the sectionwise tensor identifies this with restriction of the
termwise change of rings, naturally in K^n and d_K. This remains valid for the zero
ring and zero modules. Restriction of scalars is exact and faithful: its underlying
abelian sheaf is unchanged, so it preserves and reflects kernels, cokernels and
vanishing of homology. It therefore reflects acyclicity of the extended complex.
Finally the components eqToIso (h M) form a natural isomorphism, since hm is precisely
its naturality square after cancelling equality transports. Map this isomorphism
termwise to identify the prescribed E-complex with that extension of scalars complex.
No K-flatness, acyclicity of K, or flatness of O' is assumed in this comparison lemma.
(blueprint: lem-pur-change-of-rings-tensor-acyclic) -/
theorem changeOfRings_acyclic_of_tensor_acyclic
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (E : SheafOfModules.{u} (𝓡 O) ⥤ SheafOfModules.{u} (𝓡 O'))
    (h : ∀ M : SheafOfModules.{u} (𝓡 O), E.obj M = changeOfRings.{u, u, u} φ M)
    (hm : ∀ {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N),
      E.map a = eqToHom (h M) ≫ changeOfRingsHom.{u, u, u} φ M a ≫ eqToHom (h N).symm)
    [E.Additive]
    (K : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ)
    (hT : ∀ F : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ,
      letI := monoidalCategory O
      (CochainComplex.mapBifunctor F K (curriedTensor _)).Acyclic) :
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by sorry

end SheafOfModules
