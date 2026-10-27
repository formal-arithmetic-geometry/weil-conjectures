/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.AlgebraicGeometry.InertEigenparameterRigidificationData

/-! # Strict inert affine covers with eigenparameter rigidifications

Source: ILO, Travaux de Gabber, VIII Lemmas 5.3.5 and 5.3.7, pp.124--125;
Lemma 5.3.2, p.123 (blueprint: lem-per-abelian-inert-rigidification-cover).

The input is an ordinary scheme with its scheme action. The canonical divisorial
log structures are supplied in the conclusion, rather than assumed as extra data.
The auxiliary predicates retain the eigenfunctions, induction presentation and
strict inert pullback comparison. No construction is chosen from a theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
namespace GabberModification

/-- Strict inert affine rigidification cover, including eigenparameters, finite
induction and its local pullback assertion. The input is the ordinary scheme pair;
its divisorial fs log presentation is part of the conclusion.

Source: ILO VIII Lemmas 5.3.5 and 5.3.7, printed pp.124--125, and Lemma 5.3.2,
p.123 (blueprint: lem-per-abelian-inert-rigidification-cover).

Proof plan:
1. At a geometric point with inertia H remove the fixed loci of elements outside H.
Separatedness makes these closed. Invert |H| and intersect finitely many translates
of an affine neighbourhood to obtain an H-invariant affine neighbourhood.
2. Use lem-per-cyclotomic-finite-etale-cover to adjoin the |H|-th roots of unity,
with H trivial on the cyclotomic factor. Inertia is unchanged. The labelled coordinate
locus of lem-per-ind-etale-regular-coordinate-locus gives the old boundary parameters.
3. Apply lem-per-semilinear-character-projector-lifting to the maximal ideal modulo
its square. Preserve the old component ideals and complete their cotangent lines to
an eigenbasis. Nakayama (lem-weil-pbc-nakayama-local-generators) gives a regular
parameter system, with the exact character equations.
4. Spread the parameters, character equations and component-ideal equalities to an
invariant affine neighbourhood. Shrink to the regular-coordinate locus, remove the
other components, and take the union of the parameter divisors. It contains the old
boundary. lem-per-regular-boundary-divisorial-chart gives its fs log regular structure.
At the chosen point the stratum is a field and the characteristic action is trivial;
lem-per-very-tame-locus-open permits shrinking to a very tame neighbourhood.
5. Induce each H-neighbourhood to G by the disjoint union over G/H, using coset
representatives r_c and the action r_(gc)^(-1) g r_c. Inertia is conjugated to the
original inertia. Étaleness, strictness and very tameness hold componentwise.
lem-weil-pbc-finite-affine-coproduct-spectrum makes each induced source affine.
Étale maps are open by finite presentation and flatness; Noetherian compactness
selects finitely many. Their disjoint union is the desired affine surjective cover.
For the empty scheme take the empty union, Spec of the zero ring.
6. Pull back along any strict inert equivariant étale morphism. The stabilizer of a
geometric pair is the intersection of the two stabilizers, both equal to that of the
common image, so both projections are inert. Strictness and étaleness pull back.
The very-tame-locus and coordinate-locus lemmas preserve the log and boundary
conditions. Repeat the character-projector argument at each point to obtain the
local eigenparameters for both pulled-back boundaries. No affineness is asserted
for the entire pulled-back source. -/
theorem exists_abelian_inert_rigidification_cover
    {G : Type v} [Group G] [Finite G] (X : Scheme.{u})
    (a : G →* Aut X) (B : X.IdealSheafData)
    (hnoeth : IsNoetherian X) (hqe : QuasiExcellent X)
    (hreg : IsRegularScheme X) (hsep : X.IsSeparated)
    (hsnc : IsStrictNormalCrossingsBoundary B) (hstrict : GStrict a B)
    (hinvariant : ∀ g : G, B.comap (a g).hom = B)
    (htame : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
      IsUnit (Nat.card {g : G // t ≫ (a g).hom = t} : Ω))
    (hfree : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X) (g : G),
      t default ∉ B.support → t ≫ (a g).hom = t → g = 1)
    (habelian : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X) (g h : G),
      t ≫ (a g).hom = t → t ≫ (a h).hom = t → g * h = h * g) :
    ∃ (L : FineSaturatedLogScheme.{u}) (e : L.scheme ≅ X)
      (aL : FSLogGroupAction G L),
      DivisorialBoundary L (B.comap e.hom) ∧
      (∀ g : G, (aL.baseAction g).hom ≫ e.hom = e.hom ≫ (a g).hom) ∧
      ∃ (U : FineSaturatedLogScheme.{u}) (b : FSLogGroupAction G U)
        (f : EtaleLogHom U L),
        IsAffine U.scheme ∧ Etale f.base ∧ Surjective f.base ∧
        f.IsStrict ∧ Inert b aL (MonoidHom.id G) f ∧
        DivisorialBoundary U (B.comap (f.base ≫ e.hom)) ∧
        HasFiniteInertiaInduction b ∧
        ∃ R : Rigidification b,
          R.HasEigenparameters (B.comap (f.base ≫ e.hom)) ∧
          R.PullsBack (a := aL) f (B.comap (f.base ≫ e.hom)) := by
  sorry

end GabberModification
end AlgebraicGeometry
