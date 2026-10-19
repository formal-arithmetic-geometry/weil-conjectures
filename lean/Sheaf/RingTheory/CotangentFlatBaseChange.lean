/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Sheaf.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.RingTheory.Kaehler.Polynomial
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.KFlatScalarExtensionCounit

/-!
# Derived base change for ring cotangent complexes

Source: Stacks Project, Cotangent Complex, Tags 08QQ and 08QL
(blueprint: lem-trf-cotangent-flat-base-change).

The scalar extension below is the existing universal K-flat left derived functor.
The adjunction is derived from the ordinary tensor/restriction adjunction and
identified with exact restriction by its unit-compatible comparison. Both the
multiplication hypothesis and the cotangent base-change map are its actual adjuncts.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace Algebra.CotangentResolution

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The existing universal K-flat scalar extension, at the localization universe of
`Coherence`. This merely supplies its proved instance arguments; it does not choose
an arbitrary left adjoint. Source: Stacks, Tags 06Y0 and 08QQ
(blueprint: lem-trf-cotangent-flat-base-change). -/
def baseChangeExtension {A B : CommRingCat.{u}} (f : A ⟶ B) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B) := by
  letI : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  letI (M : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).flip.obj M) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight M))
  letI : (ModuleCat.extendScalars f.hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj f.hom).left_adjoint_additive
  letI := ModuleCat.extendScalars_preservesKFlatQuasiIso f.hom
  exact (ModuleCat.extendScalars f.hom).leftDerivedFunctor

/-- The normalized derived tensor/restriction adjunction, using the ordinary
`extendRestrictScalarsAdj` and the unit-compatible exact-restriction comparison.
Source: Stacks, Tags 07A6, 0FND and 09T5
(blueprint: lem-trf-cotangent-flat-base-change). -/
def baseChangeAdjunction {A B : CommRingCat.{u}} (f : A ⟶ B) :
    baseChangeExtension f ⊣ (ModuleCat.restrictScalars f.hom).mapDerivedCategory := by
  letI : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  letI (M : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).flip.obj M) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight M))
  letI : (ModuleCat.extendScalars f.hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj f.hom).left_adjoint_additive
  letI := ModuleCat.extendScalars_preservesKFlatQuasiIso f.hom
  exact (ModuleCat.extendRestrictScalarsAdj f.hom).derivedAdjunction.ofNatIsoRight
    (ModuleCat.restrictScalars f.hom).rightDerivedFunctorIsoMapDerivedCategory

/-- The `A`-linear map `C → C'` induced by a commutative ring square. Both
modules retain their specified scalar actions. Source: Stacks, Tag 08QL
(blueprint: lem-trf-cotangent-flat-base-change). -/
def squareModuleMap {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    (ModuleCat.restrictScalars f.hom.hom).obj (ModuleCat.of f.right f.right) ⟶
      (ModuleCat.restrictScalars q.left.hom).obj
        ((ModuleCat.restrictScalars g.hom.hom).obj (ModuleCat.of g.right g.right)) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars f.hom.hom).obj (ModuleCat.of f.right f.right))
    (Y := (ModuleCat.restrictScalars q.left.hom).obj
      ((ModuleCat.restrictScalars g.hom.hom).obj (ModuleCat.of g.right g.right)))
    { toFun := q.right
      map_add' := q.right.hom.map_add
      map_smul' := fun (a : f.left) (x : f.right) ↦ by
        change q.right (f.hom a * (x : f.right)) = g.hom (q.left a) * q.right x
        rw [map_mul]
        have h := congrArg (fun h : f.left ⟶ g.right ↦ h a) q.w
        change g.hom (q.left a) = q.right (f.hom a) at h
        rw [h] }

/-- The canonical multiplication `C ⊗ᴸ_A A' → C'[0]` in `D(A')`.
It is the adjunct of the square's actual map `C[0] → Res(C'[0])`;
on flat representatives it sends `p ⊗ a'` to `f(ε(p)) a'`.
Source: Stacks, Tag 08QQ (blueprint: lem-trf-cotangent-flat-base-change). -/
def derivedSquareMultiplication {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    (baseChangeExtension q.left).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} f.left) 0).obj
          ((ModuleCat.restrictScalars f.hom.hom).obj (ModuleCat.of f.right f.right))) ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} g.left) 0).obj
        ((ModuleCat.restrictScalars g.hom.hom).obj (ModuleCat.of g.right g.right)) :=
  ((baseChangeAdjunction q.left).homEquiv _ _).symm
    ((DerivedCategory.singleFunctor (ModuleCat.{u} f.left) 0).map (squareModuleMap q) ≫
      ((ModuleCat.restrictScalars q.left.hom).mapDerivedCategorySingleFunctor 0).inv.app
        ((ModuleCat.restrictScalars g.hom.hom).obj (ModuleCat.of g.right g.right)))

/-- The canonical `C'`-linear base-change morphism, defined as the normalized
scalar-extension adjunct of the recorded standard cotangent functoriality map.
Source: Stacks, Tags 08QL and 08QQ
(blueprint: lem-trf-cotangent-flat-base-change). -/
def cotangentBaseChange (C : Coherence.{u}) {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    (baseChangeExtension q.right).obj (cotangentComplex C f) ⟶ cotangentComplex C g :=
  ((baseChangeAdjunction q.right).homEquiv _ _).symm (cotangentMap C q)

/-- The canonical cotangent base-change map is invertible whenever the square
induces a derived-tensor quasi-isomorphism. No ring map is assumed flat.
Source: Stacks, Tag 08QQ (blueprint: lem-trf-cotangent-flat-base-change).

Proof:
1. Take the standard polynomial resolution P of C/A. Its terms are free A-modules
on monomials (def-weil-pbc-mv-polynomial-ring), hence flat, including empty and
infinite variable sets. Its alternating complex S is bounded above, so is K-flat
by lem-pc-module-bounded-flat-kflat and resolves C[0].
2. Compute the canonical multiplication on S: its augmentation is p tensor a'
to f(epsilon(p)) a'. The normalized adjunct formula gives precisely this map.
The hypothesis makes it a quasi-isomorphism. Its zeroth cohomology identifies
the canonical ring map alpha: C tensor_A A' to C' as an isomorphism, since tensor
preserves the presentation of C as the cokernel of the degree -1 differential.
No flatness of either ring map follows or is needed.
3. The canonical derived-to-ordinary tensor map is alpha inverse followed by mu.
Apply lem-trf-tor-independent-cotangent-base-change to see that P tensor_A A'
is a polynomial resolution; compose its augmentation with alpha to resolve C'.
4. The standard differential complex K has free C-module terms with basis dx_i,
by lem-weil-pbc-polynomial-ring-kahler-basis-any-variables. It is bounded above,
hence K-flat by lem-pc-module-bounded-flat-kflat.
5. Define theta degreewise by (dp tensor c) tensor b' to d(p tensor 1) tensor f(c)b'.
The universal derivation and tensor balancing make it well defined. Polynomial
base change identifies both modules as free C'-modules on the same variable set;
theta carries each basis vector to its counterpart and is an isomorphism.
6. For every face and degeneracy, both composites send a generator to the
same differential of the image polynomial. Thus theta commutes with all
simplicial operators and alternating differentials, giving a chain isomorphism.
7. Map P tensor_A A' to the standard resolution R of C'/A' by p tensor a' to t(p)a',
where t is the square-induced standard map. Comparison coherence identifies its
differential map followed by the standard comparison with the comparison for P'.
On generators, this composite with theta and x to x tensor 1 is cotangentMap C q.
8. The K-flat scalar-extension counit (lem-pc-kflat-scalar-extension-counit) computes
L_{C/A} tensor_C^L C' as Q(K tensor_C C'). The normalized derived adjunction shows
that cotangentBaseChange C q is exactly this computation isomorphism followed by
Q(theta), the differential comparison map and the standard comparison. Each factor
is invertible. The ordinary-module normalization agrees with the one-point sheaf
transport of lem-trf-one-point-derived-ring-identification and with
lem-pur-sheaf-ring-derived-coefficient-adjunction. Therefore beta is invertible. -/
theorem isIso_cotangentBaseChange (C : Coherence.{u})
    {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (hmu : IsIso (derivedSquareMultiplication q)) : IsIso (cotangentBaseChange C q) := by
  sorry

end Algebra.CotangentResolution
