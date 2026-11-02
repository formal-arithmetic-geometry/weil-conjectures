/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LineSubbundleProjectiveDivisorData
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleMorphism
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleSymmetricAlgebraIso
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleProper
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

/-!
Intermediate finiteness conclusion for the line-subbundle divisor theorem.
Source: Stacks Project, Tags 01OE and 01T3.
(blueprint: lem-pur-line-subbundle-projective-divisor-finite-type).

The projective bundle projections are projective-bundle morphisms via the canonical symmetric
algebra comparison. Properness then supplies the separated, locally finite type, and
quasi-compact properties after composition with a field-valued structure morphism.

Proof:
1. The normalized symmetric algebra of each realization is canonically isomorphic to the
   canonical symmetric algebra of its module (def-pur-projective-bundle-symmetric-algebra-iso).
   The induced relative Proj isomorphism identifies each realization projection with a
   projective-bundle morphism (def-trf-projective-bundle-morphism).
2. Projective-bundle morphisms are proper (lem-trf-projective-bundle-proper), hence separated,
   locally of finite type, and quasi-compact by the structure of `IsProper`.
3. Mathlib composition instances for separated, locally finite type, and quasi-compact
   morphisms give the six required properties after composition with `a`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry

private theorem isProjectiveBundle_realization
    {S : Scheme.{u}} {F : S.Modules}
    {r : ℕ} [F.IsFiniteLocallyFreeOfRank r]
    (D : ProjectiveBundleRealization S F) :
    IsProjectiveBundle D.A.data.relProjHom := by
  have : F.IsLocallyFree := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree F r
  let : F.IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r
  let hF : F.IsQuasicoherent := inferInstance
  let e : @SymmetricAlgebraSheaf.gradedAlgebraData S F hF ≅ D.A.data :=
    projectiveBundleSymmetricAlgebraIso D.A
  let i := Scheme.GradedAlgebraData.relProjIsoOfIso e
  refine ⟨F, hF, ?_, i.hom, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · exact Scheme.GradedAlgebraData.relProjIsoOfIso_hom_relProjHom e

/-- Step 6 of the line-subbundle divisor theorem: over a separated base of finite type over a
field, both projective bundles are separated, locally of finite type and quasi-compact.
Source: Stacks Project, Tags 01OE and 01T3. The proof in words is in the module docstring.
(blueprint: lem-pur-line-subbundle-projective-divisor-finite-type). -/
theorem lineSubbundle_projective_divisor_finite_type
    (S : Scheme.{u}) (r : ℕ) (hr : 2 ≤ r)
    (L F G : S.Modules) [L.IsInvertible]
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank (r - 1)]
    (P : ProjectiveBundleRealization S F) (Q : ProjectiveBundleRealization S G) :
    ∀ (k : Type u) [Field k] (a : S ⟶ Spec (.of k)),
      IsSeparated a → LocallyOfFiniteType a → QuasiCompact a →
      IsSeparated (P.A.data.relProjHom ≫ a) ∧
        LocallyOfFiniteType (P.A.data.relProjHom ≫ a) ∧
        QuasiCompact (P.A.data.relProjHom ≫ a) ∧
        IsSeparated (Q.A.data.relProjHom ≫ a) ∧
        LocallyOfFiniteType (Q.A.data.relProjHom ≫ a) ∧
        QuasiCompact (Q.A.data.relProjHom ≫ a) := by
  intro k _instK a ha hlt hqc
  have _hr : 2 ≤ r := hr
  let hP : IsProper P.A.data.relProjHom :=
    projectiveBundle_proper _ (isProjectiveBundle_realization (r := r) P)
  let hQ : IsProper Q.A.data.relProjHom :=
    projectiveBundle_proper _ (isProjectiveBundle_realization (r := r - 1) Q)
  let : IsProper P.A.data.relProjHom := hP
  let : IsProper Q.A.data.relProjHom := hQ
  let : IsSeparated a := ha
  let : LocallyOfFiniteType a := hlt
  let : QuasiCompact a := hqc
  exact ⟨inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
