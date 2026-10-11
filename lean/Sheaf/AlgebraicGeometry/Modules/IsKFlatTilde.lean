/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Sheaf.Algebra.Homology.KFlat

/-!
# Associated sheaves of K-flat complexes on affine schemes

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.3.6 (Tag 08DV)
(blueprint: lem-pc-affine-tilde-kflat).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- (blueprint: lem-pc-affine-tilde-kflat) The termwise associated sheaf of a K-flat
complex of modules over a commutative ring `A` is K-flat on `Spec A`.
Source: Stacks Project, Lemma 36.3.6 (Tag 08DV).

Proof: At a prime `p`, the stalks of the terms of the associated sheaf identify naturally
with the localizations of the terms of `K`, compatibly with differentials, by Tag 01HV
(`lem-weil-pbc-spec-tilde-stalk-localization`). Thus the stalk complex is `K ⊗_A A_p`.
Base change preserves K-flatness (Tag 06Y1): an acyclic complex `L` over `A_p` remains
acyclic over `A`, and `Tot(L ⊗_{A_p} (K ⊗_A A_p))` identifies with `Tot(L ⊗_A K)`,
which is acyclic by the hypothesis. Every stalk complex is therefore K-flat, so the
reverse direction of the stalk criterion, Tag 06YB (`lem-pc-kflat-stalk-criterion`),
implies that the associated sheaf complex is K-flat. -/
theorem isKFlat_tilde (A : Type u) [CommRing A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ F : CochainComplex (ModuleCat.{u} A) ℤ,
      F.Acyclic → (CochainComplex.mapBifunctor F K (curriedTensor (ModuleCat A))).Acyclic) :
    CochainComplex.IsKFlat (R := (Spec (.of A)).sheaf)
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A) (Spec (.of A)).Modules
        _ _ _ _ (tilde.functor (.of A)) ⟨fun _ _ => tilde.map_zero⟩
        (ComplexShape.up ℤ)).obj K) :=
  sorry

end AlgebraicGeometry
