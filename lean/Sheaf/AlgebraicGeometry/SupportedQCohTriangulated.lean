/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Triangulated closure of supported quasi-coherent complexes

Source: Stacks Project, Tag 0A9A, preceding definition of D_QCoh,T.
(blueprint: lem-pc-supported-qcoh-triangulated).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

abbrev supportedProperty (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) : ObjectProperty (schemeDerivedCategory X) := fun K ↦
  schemeDerivedQCohProperty X K ∧ ∀ (n : ℤ) (x : X), x ∉ T →
    Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x))

/-- The supported quasi-coherent property contains a zero object.
Source: Stacks Project, Derived Categories of Schemes, definition preceding Tag 0A9A.
(blueprint: lem-pc-supported-qcoh-contains-zero).

Proof: Choose the zero object of the derived category. Each homology functor is additive,
so its image is a zero sheaf of modules. A zero module sheaf is quasi-coherent: on every
affine open it is the sheaf associated to the zero module, or equivalently it has the
presentation with no generators and no relations. Its underlying additive sheaf has
zero sections on every open, and hence zero stalk at every point. Thus all homology
sheaves are quasi-coherent and all stalks outside T are subsingleton, independently of T. -/
theorem supported_qcoh_containsZero (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) : (supportedProperty X T).ContainsZero := by
  sorry

/-- The supported quasi-coherent property is stable under every integer shift.
Source: Stacks Project, Derived Categories of Schemes, definition preceding Tag 0A9A.
(blueprint: lem-pc-supported-qcoh-stable-shift).

Proof: For integers a and n, the shift sequence gives H^n(K[a]) ≅ H^(a+n)(K).
Transport quasi-coherence along its inverse. Applying the underlying additive
presheaf functor and the stalk functor at x gives an isomorphism of additive groups.
Its forward map is injective, so a subsingleton stalk of H^(a+n)(K) implies a
subsingleton stalk of H^n(K[a]). This works for all shifts and every subset T. -/
theorem supported_qcoh_stableShift (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) : (supportedProperty X T).IsStableUnderShift ℤ := by
  refine ⟨fun a ↦ ⟨fun K hK ↦ ?_⟩⟩
  constructor
  · intro n
    exact (SheafOfModules.isQuasicoherent.{u} (moduleRings X.toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).shiftIso
        a n (a + n) rfl).app K).symm (hK.1 (a + n))
  · intro n x hx
    let e := (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).shiftIso
      a n (a + n) rfl).app K)
    let F := SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.toPresheaf.{u} (moduleRings X.toRingedSpace).obj ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    let h : Subsingleton (↑(F.obj ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (a + n)).obj K))) :=
      hK.2 (a + n) x hx
    refine ⟨fun b c ↦ (ConcreteCategory.bijective_of_isIso (F.mapIso e).hom).1 ?_⟩
    exact h.elim _ _

/-- The supported quasi-coherent property is closed under middle terms of triangles.
Source: Stacks Project, Derived Categories of Schemes, definition preceding Tag 0A9A.
(blueprint: lem-pc-supported-qcoh-closed-middle).

Proof: For a distinguished triangle K → L → M → K[1] with K and M in the property,
the long exact homology sequence gives a short exact sequence from the cokernel of
H^(n-1)(M) → H^n(K) to H^n(L) to the kernel of H^n(M) → H^(n+1)(K).
Kernels, cokernels, and extensions of quasi-coherent module sheaves on a scheme are
quasi-coherent. For kernels and cokernels this follows on affine opens from exactness
of the module-to-sheaf correspondence. For extensions, on an affine open the outer
quasi-coherent sheaves have vanishing H^1, so sections form an exact extension of
modules; sheafifying this extension identifies its middle term with the given sheaf.
At a point x outside T, the stalk functor is exact and both outer stalks in the long
exact sequence are zero. Exactness forces the middle stalk to be zero as well.
Thus L itself has the property, and in particular lies in its isomorphism closure,
as required by IsTriangulatedClosed₂. The argument also covers empty T and T = X. -/
theorem supported_qcoh_closedMiddle (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) : (supportedProperty X T).IsTriangulatedClosed₂ := by
  sorry

/-- Quasi-coherent cohomology with zero stalks off T is stable under triangles.
No compactness or closedness assumption on T is needed for this closure assertion.
Source: Stacks Project, Derived Categories of Schemes, definition preceding Tag 0A9A.
(blueprint: lem-pc-supported-qcoh-triangulated).

Proof:
1. The zero complex has zero cohomology sheaves; these are quasi-coherent and their
   stalks are zero. This verifies ContainsZero.
2. Cohomology of K shifted by m is canonically cohomology of K in degree n+m.
   Quasi-coherence and zero stalks are invariant under these isomorphisms. This verifies
   IsStableUnderShift for every integer shift, including negative shifts.
3. Apply cohomology to a distinguished triangle with its first and third objects in
   the property. Its middle cohomology sheaf is an extension of a cokernel between
   quasi-coherent cohomology sheaves and a kernel between such sheaves. Kernels,
   cokernels and extensions of quasi-coherent modules on a scheme are quasi-coherent,
   as can be checked on affine opens by the exact module-to-sheaf equivalence.
4. At a point outside T, stalks preserve exact sequences. The long exact cohomology
   sequence has zero terms on both sides of each middle term, so that term is zero.
   Consequently the middle object has the property itself, hence also its isoClosure.
   These three assertions give ObjectProperty.IsTriangulated. The empty subset and
   the whole space require exactly the same argument. -/
theorem supported_qcoh_isTriangulated (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) :
    ObjectProperty.IsTriangulated (fun K : schemeDerivedCategory X ↦
      schemeDerivedQCohProperty X K ∧
        ∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x))) := by
  let : (supportedProperty X T).ContainsZero := supported_qcoh_containsZero X T
  let : (supportedProperty X T).IsStableUnderShift ℤ := supported_qcoh_stableShift X T
  let : (supportedProperty X T).IsTriangulatedClosed₂ := supported_qcoh_closedMiddle X T
  exact ObjectProperty.IsTriangulated.mk


end AlgebraicGeometry
