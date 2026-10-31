/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.AffineSquareMonomorphismAbsoluteSeparated
import WeilConjectures.AlgebraicGeometry.MonomorphismFiniteTypeComposite
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-!
# Separated locally quasi-finite morphisms of an affine étale relation

Source: Stacks Project, Spaces, Tag 0265, the opening two proof paragraphs and the
first representability step (blueprint: lem-trf-affine-etale-relation-separated-lqf).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- The relation axioms are not needed for these geometric properties.
set_option linter.unusedVariables false in
/-- For an étale equivalence relation on an affine `S`-scheme, both projections and
its monomorphism into the relative square are separated and locally quasi-finite.
Here local quasi-finiteness includes the finite-type requirement of Stacks Tag 01TD.
The schemes and morphisms over `S` are bundled in `Over S`; `hrel` states the
relation condition on every `S`-scheme's points. The relation map is the canonical
`pullback.lift` into `U.left ×[S] U.left`. No separatedness of `S` or quasi-compactness
of `R.left` is assumed.

Source: Stacks Project, Spaces, Tag 0265, opening two proof paragraphs and the first
representability step (blueprint: lem-trf-affine-etale-relation-separated-lqf).

Proof:
1. Apply `affine_square_monomorphism_absolute_separated` to the relation map,
   using the canonical affine presentation of `U.left`. This makes `R.left`
   absolutely separated. Separated cancellation makes `s.left` and `t.left`
   separated.
2. The étale projections are locally of finite type with open diagonals.
   Apply `Scheme.Hom.isLocallyQuasiFinite_of_unramified` to each.
3. The composite of the relation map with the first projection is `s.left`,
   hence locally of finite type. Apply
   `Scheme.Hom.monomorphism_properties_of_locallyOfFiniteType_comp` to obtain
   separatedness and local quasi-finiteness of the relation map. -/
theorem affine_etale_relation_separated_locally_quasi_finite
    {S : Scheme.{u}} (R U : Over S) [IsAffine U.left] (s t : R ⟶ U)
    [Mono (pullback.lift s.left t.left (s.w.trans t.w.symm))]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Etale s.left] [Etale t.left] :
    (IsSeparated s.left ∧ Scheme.Hom.IsLocallyQuasiFinite s.left) ∧
    (IsSeparated t.left ∧ Scheme.Hom.IsLocallyQuasiFinite t.left) ∧
    (IsSeparated (pullback.lift s.left t.left (s.w.trans t.w.symm)) ∧
      Scheme.Hom.IsLocallyQuasiFinite (pullback.lift s.left t.left (s.w.trans t.w.symm))) := by
  let j := pullback.lift s.left t.left (s.w.trans t.w.symm)
  have hsep := affine_square_monomorphism_absolute_separated S U.left R.left
    U.hom R.hom Γ(U.left, ⊤) U.left.isoSpec j (by simp [j, s.w])
  have : R.left.IsSeparated := ⟨hsep.2.2.2.2⟩
  have hjft : LocallyOfFiniteType (j ≫ pullback.fst U.hom U.hom) := by
    simpa only [j, pullback.lift_fst] using
      (inferInstance : LocallyOfFiniteType s.left)
  have hj := Scheme.Hom.monomorphism_properties_of_locallyOfFiniteType_comp
    j (pullback.fst U.hom U.hom)
  exact ⟨⟨inferInstance, Scheme.Hom.isLocallyQuasiFinite_of_unramified s.left
      ⟨inferInstance, inferInstance⟩⟩,
    ⟨inferInstance, Scheme.Hom.isLocallyQuasiFinite_of_unramified t.left
      ⟨inferInstance, inferInstance⟩⟩,
    hj.2.2.2.2.1, hj.2.2.2.2.2.2.2⟩

end AlgebraicGeometry
