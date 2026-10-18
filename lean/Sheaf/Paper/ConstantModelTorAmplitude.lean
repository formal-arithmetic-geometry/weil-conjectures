/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SheafTensorClosed
import Sheaf.CategoryTheory.SheafTensorStructure
import Sheaf.Paper.ProjectionMateExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-!
# Tor amplitude and `Dᵇ_ctf(X,Λ)` with finite constant scalar models

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sfb-constructible,
node det-def-sfb-constructible-tor-amplitude, statement and its well-definedness paragraph
(blueprint: det-def-sfb-constructible-tor-amplitude).

The four notions of the node are the landed declarations of
`Sheaf.Paper.CondensedConstantConstructibility` and the generic Tor amplitude of
`WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`, which are not redefined here:

1. `Cons(X,Λ)` is `AlgebraicGeometry.ProEtale.ConstantModelConstructible`, the full
   subcategory of `IsConstantModelConstructible` (finite constant local models
   `HasFiniteConstantLocalModel` on the strata of a finite constructible stratification for
   qcqs `X`, imposed on affine opens otherwise).
2. `Dᵇ_c(X,Λ)` is `ConstantModelBoundedConstructible`, the full subcategory of
   `constantModelBoundedConstructible`: bounded for the canonical t-structure (`H^q = 0` for
   all but finitely many `q`) with every `H^q` in `Cons(X,Λ)`.
3. Tor amplitude in `[a,b]` is `DerivedCategory.torAmplitudeIn _ a b`: for every
   `Λ_X`-module `N`, `K ⊗ᴸ N[0]` has cohomology concentrated in `[a,b]`. Its tensor is,
   definitionally, the relative derived tensor `CondensedRing.derivedTensor Λ X` over
   `Λ_X`. Finite Tor amplitude is `DerivedCategory.finiteTorAmplitude _`.
4. `Dᵇ_ctf(X,Λ)` is `ConstantModelConstructibleFiniteTor`, the full subcategory of the
   intersection of `constantModelBoundedConstructible` with `finiteTorAmplitude`.

This module states the well-definedness assertions of the node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- **Well-definedness of `Cons`, `Dᵇ_c`, Tor amplitude and `Dᵇ_ctf`.** Let `Λ` be a
commutative condensed ring and `X` a scheme. Constructibility, bounded constructibility,
Tor amplitude in `[a,b]` and finite Tor amplitude are invariant under isomorphism, so the
four full subcategories are replete. If `K` has Tor amplitude in `[a,b]` then `K[1]` has
Tor amplitude in `[a-1,b-1]`. If `K' → K → K'' → K'[1]` is distinguished and `K'`, `K''`
have Tor amplitude in `[a,b]`, so does `K`. A direct summand (retract) of a complex of Tor
amplitude in `[a,b]` has Tor amplitude in `[a,b]`. Hence the complexes of finite Tor
amplitude form a thick subcategory (a triangulated subcategory closed under retracts) of
`D(X_proét,Λ)`; `Dᵇ_ctf(X,Λ)` is by definition its intersection with `Dᵇ_c(X,Λ)`.

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sfb-constructible,
node det-def-sfb-constructible-tor-amplitude, well-definedness paragraph
(blueprint: det-def-sfb-constructible-tor-amplitude).

Proof plan:
1. Isomorphism invariance. If `M ≅ M'`, restrict the isomorphism to every stratum and every
member of the pro-étale cover; composing with the local-model isomorphisms gives the same
finitely presented scalar modules and the same stratification for `M'`
(det-def-sfb-constructible-local-model), also in the affine-local convention. Cohomology
functors carry `K ≅ L` to `H^q(K) ≅ H^q(L)` (def-weil-abstract-derived-category), and for
each `N[0]` the relative derived tensor (sk-def-sfb-derived-tensor-hom) carries `K ≅ L` to an
isomorphism of tensors, so each Tor interval and its existence are unchanged.
2. Internal-module comparison. The pro-étale site is small relative to the universe of the
module sheaves (def-weil-sheaf-of-modules-category) and sheafification is strong monoidal
(det-def-sfb-sheaf-tensor-structure), so local equivalences are monoidal and
def-weil-pbc-internal-abelian-sheaf-module-equivalence gives an exact equivalence `E` of
internal `Λ_X`-modules with sectionwise modules. By det-def-sfb-sheaf-tensor-closed the
hypotheses of def-sfb-modobj-relative-tensor hold, and by
lem-pc-sites-sheaf-tensor-bilinear-universal both relative tensor products represent the
`Λ_X`-bilinear maps, hence agree naturally, with the same unit.
3. Derived comparison. `E` preserves cohomology, quasi-isomorphisms, shifts and cones, so it
induces exact equivalences of derived categories, preserving K-flatness and total tensor
complexes; thus a K-flat resolution `P → K` computes the Layer B derived tensor on both sides.
4. Shifts. By the exactness clause of lem-weil-pbc-ringed-projection-mate-exact for the
identity ringed topos `(X_proét, Λ_X)`, `T_N(K) = K ⊗ᴸ N` is exact, so
`T_N(K[1]) ≅ T_N(K)[1]` (def-weil-triangulated-category) and `H^q(L[1]) ≅ H^{q+1}(L)`; the
interval `[a,b]` becomes `[a-1,b-1]`.
5. Extensions. `T_N` sends the triangle to a distinguished triangle; by
lem-sf-derived-homology-long-exact the segment `H^q(T_N K') → H^q(T_N K) → H^q(T_N K'')` is
exact, with zero outer terms for `q ∉ [a,b]`, so the middle term vanishes, for every `N`.
6. Retracts. From `r ∘ i = 1_E`, `H^q(T_N r) ∘ H^q(T_N i)` is the identity of `H^q(T_N E)`
and factors through `H^q(T_N K) = 0` for `q ∉ [a,b]`; a direct summand is such a retract.
7. Thickness. Zero has amplitude `[0,0]`; intervals can be enlarged to a common one; steps 4
and 5 and rotation of triangles give closure under shifts and cones, and the cone of a zero
map gives finite biproducts, so TR1–TR4 restrict and the full replete subcategory is
triangulated; step 6 makes it thick. Its intersection with `Dᵇ_c(X,Λ)` is `Dᵇ_ctf(X,Λ)` by
clause 4 of the definition. -/
theorem constantModelConstructibleFiniteTor_wellDefined (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) ∧
    (constantModelBoundedConstructible Λ X).IsClosedUnderIsomorphisms ∧
    (∀ a b : ℤ, a ≤ b → (DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) a b
      ).IsClosedUnderIsomorphisms) ∧
    (DerivedCategory.finiteTorAmplitude
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      ).IsClosedUnderIsomorphisms ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      (a b : ℤ), a ≤ b → DerivedCategory.torAmplitudeIn _ a b K →
        DerivedCategory.torAmplitudeIn _ (a - 1) (b - 1) (K⟦(1 : ℤ)⟧)) ∧
    (∀ (T : Triangle (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
      (a b : ℤ), a ≤ b → T ∈ distTriang _ →
        DerivedCategory.torAmplitudeIn _ a b T.obj₁ →
        DerivedCategory.torAmplitudeIn _ a b T.obj₃ →
        DerivedCategory.torAmplitudeIn _ a b T.obj₂) ∧
    (∀ a b : ℤ, a ≤ b → (DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) a b
      ).IsStableUnderRetracts) ∧
    (DerivedCategory.finiteTorAmplitude
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      ).IsTriangulated ∧
    (DerivedCategory.finiteTorAmplitude
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      ).IsStableUnderRetracts := by
  sorry

end AlgebraicGeometry.ProEtale
