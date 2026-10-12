/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Finite selection of module-valued geometric stalk tests

Source: Stacks Project, Tag 09Z6, the partition alternative in the first proof paragraph.
(blueprint: lem-weil-pbc-constructible-module-finite-selection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- A family of module-sheaf maps that contains an injective test at every geometric stalk
of a constructible source has a finite subfamily whose biproduct lift is monomorphic.

Source: Stacks Project, Tag 09Z6, partition alternative, transferred to (3), and the
abelian-sheaf finite-selection statement
`lem-weil-pbc-constructible-noetherian-finite-selection`.
(blueprint: lem-weil-pbc-constructible-module-finite-selection).

Proof: Forget module structure to abelian sheaves. The constructible stratification of F
and its finite module trivializations give a constructible underlying sheaf of sets:
forgetting commutes with restriction, inverse image and constant sheaves. It also commutes
with geometric stalks, because the underlying abelian group functor preserves filtered
colimits. Thus the given stalk injections give injections on abelian stalks. Apply the
abelian finite-selection lemma: refine the strata into finitely many irreducible lisse
strata, select finitely many tests at their geometric generic points, and propagate
injectivity across each stratum by the generic-kernel lemma. Stalks detect monomorphisms,
so the joint map of the selected tests is mono. Forgetting modules preserves finite
biproducts, and the comparison identifies the underlying map of the module biproduct lift
with this abelian biproduct lift. The forgetful functor is faithful and therefore reflects
monomorphisms. Enumerate the finite selected set by Fin n and reindex its biproduct by this
equivalence. For the empty source scheme or zero sheaf the empty family is permitted;
no finiteness or constructibility hypothesis on any target G l is used. -/
theorem exists_mono_biproduct_of_constructible_module_stalk_injective
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F)
    (L : Type w) (G : L → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (φ : ∀ l : L, F ⟶ G l)
    (hφ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ l : L, Function.Injective
        (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map (φ l))) :
    ∃ (n : ℕ) (l : Fin n → L), Mono (biproduct.lift (fun i : Fin n ↦ φ (l i))) := by sorry

end AlgebraicGeometry.Scheme
