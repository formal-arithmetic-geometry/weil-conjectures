/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated
import WeilConjectures.AlgebraicGeometry.DualizingComplexCtf
import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
import WeilConjectures.AlgebraicGeometry.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.DerivedCategory.NativeInternalHomExact

/-! # The Verdier dual restricts to an exact functor on Dctf

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-verdier-biduality/sk-lem-pd-preservation/
det-pd-verdier-dual-ctf.md and its proof
(blueprint: det-pd-verdier-dual-ctf).

The coefficient category is the ordinary, uncompleted derived category of internal
modules. The exceptional inverse image is presented by its adjunction to the actual
compactification lower shriek on the localizing closures. The restricted functor is
specified on objects and morphisms by equality after the full inclusion. Its shifts
and triangles are inherited from the ambient category, with the standard reversed
shift on the opposite category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated.Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- For every admissible coefficient, RHom into the dualizing complex preserves Dctf
and restricts to an exact contravariant functor.

The parameters `c`, `h`, `G`, `adj` present the exceptional inverse image by the
compactification adjunction, exactly as in `dualizingComplex_mem_ctf_and_composition`.
They impose no preservation condition on the right adjoint. The degree-zero regular
module is the coefficient unit on Spec k. Its localizing membership is concluded,
not assumed. The predicate in the conclusion is the existing finite-constant-model
bounded constructibility intersected with relative finite Tor amplitude.

The existential triangulated-closure witness installs the inherited triangulation
on the full subcategory, rather than postulating an unrelated structure. The functor
equality fixes both objects and morphisms. `CommShift ℤ` includes the unit and addition
coherences; `IsTriangulated` uses that very shift structure and the standard opposite
triangulation, whose shift by n is the opposite of shift by -n.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-verdier-biduality/sk-lem-pd-preservation/
det-pd-verdier-dual-ctf.md, both sentences, and
`det-pd-verdier-dual-ctf.proof.md`, both paragraphs
(blueprint: det-pd-verdier-dual-ctf).

Proof:
1. The global field is algebraically closed, hence has ell-cohomological dimension
   zero by sk-lem-base-field-cd. The first assertion of
   det-pd-dualizing-complex-ctf supplies the coefficient-unit membership h0 and
   omega = G(Lambda_s) in Dctf. It applies to every displayed adjoint presentation,
   by uniqueness of right adjoints to the compactification lower shriek.
2. For K in Dctf, apply det-thm-sf-ctf-stability-internal-hom to K and omega.
   The separated finite-type, admissibility, characteristic and finite-cd hypotheses
   hold by the standing datum and step 1. Its membership clause gives RHom(K,omega)
   in Dctf, the first conjunct.
3. By lem-sfb-admissible-bounded-constructible-triangulated, bounded constructibility
   is triangulated. By det-def-sfb-constructible-tor-amplitude, finite Tor amplitude
   is thick, and bounded constructibility is replete. Their intersection is therefore
   triangulated. The full-subcategory construction supplies the inherited shifts and
   precisely those triangles whose ambient image is distinguished.
4. By det-prop-sfb-module-category, the relative module category is closed symmetric
   monoidal Grothendieck abelian with functorial flat resolutions. Tensor is additive
   because it preserves colimits in each variable. Apply
   lem-weil-native-internal-hom-contravariant-exact with W = omega. By
   sk-def-sfb-derived-tensor-hom, its native internal Hom is the relative derivedHom
   here. This gives coherent shifts and exactness on the ambient opposite category.
5. Restrict the functor by step 2 using fullness, keeping its ambient morphism map.
   The equality after inclusion holds definitionally for ObjectProperty.lift.
   By step 3, the ambient shift isomorphisms restrict, and step 4 carries each
   distinguished triangle to a distinguished triangle. Fullness and faithfulness
   retain all shift coherence identities, yielding CommShift and IsTriangulated.
-/
theorem verdierDual_ctf_exact
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (_hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom)
    (h : ∀ K, localizingClosureProEtale Λ X.left K →
      localizingClosureProEtale Λ (Spec (.of D.k))
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K))
    (G : (localizingClosureProEtale Λ (Spec (.of D.k))).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.left).FullSubcategory)
    (_adj : localizingLowerShriek Λ c h ⊣ G) :
    ∃ h0 : localizingClosureProEtale Λ (Spec (.of D.k))
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj Λ (Spec (.of D.k))))),
      (∀ K, (constantModelBoundedConstructible Λ X.left ⊓
          DerivedCategory.finiteTorAmplitude _) K →
        (constantModelBoundedConstructible Λ X.left ⊓
          DerivedCategory.finiteTorAmplitude _)
          (((derivedHom Λ X.left).obj (Opposite.op K)).obj
            (G.obj ⟨(DerivedCategory.singleFunctor _ 0).obj
              (Mod.regular (condensedRingObj Λ (Spec (.of D.k)))), h0⟩).obj)) ∧
      ∃ (_ : (constantModelBoundedConstructible Λ X.left ⊓
          DerivedCategory.finiteTorAmplitude _).IsTriangulated),
        ∃ F : (ConstantModelConstructibleFiniteTor Λ X.left)ᵒᵖ ⥤
            ConstantModelConstructibleFiniteTor Λ X.left,
          F ⋙ (constantModelBoundedConstructible Λ X.left ⊓
              DerivedCategory.finiteTorAmplitude _).ι =
            (constantModelBoundedConstructible Λ X.left ⊓
                DerivedCategory.finiteTorAmplitude _).ι.op ⋙
              (derivedHom Λ X.left).flip.obj
                (G.obj ⟨(DerivedCategory.singleFunctor _ 0).obj
                  (Mod.regular (condensedRingObj Λ (Spec (.of D.k)))), h0⟩).obj ∧
          ∃ (_ : F.CommShift ℤ), F.IsTriangulated := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
