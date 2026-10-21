/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
public import Sheaf.Paper.StrictHenselizationFunctoriality
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import WeilConjectures.RingTheory.FiniteRingMapQuasiFinite
import Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.RingTheory.QuasiFiniteFourRings
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.FiniteLocalHenselian
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing
import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.IndPrincipalZariski
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Etale.Basic
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Sheaf.RingTheory.IndEtaleUniverseTransport

/-!
# Strict henselization under a quasi-finite ring map

Source: Stacks Project, Algebra, Tag 05WR, `lemma-quasi-finite-strict-henselization`
(blueprint: lem-trf-strict-henselization-quasi-finite-ring).

The canonical map is finite and local, its residue extension is finite purely inseparable,
and the tensor-product localization identifies the target ring via both structural maps.
-/

@[expose] public section

universe u
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The structural `A`-algebra on the strict henselization ring at a point of `Spec A`.
Source: Stacks Project, Algebra, Tag 05WR
(blueprint: lem-trf-strict-henselization-quasi-finite-ring). -/
@[instance_reducible] noncomputable def strictHenselizationAlgebra
    {A : Type u} [CommRing A] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (pbar : Spec (.of Ω) ⟶ Spec (.of A)) : Algebra A (strictHenselizationRing pbar) :=
  RingHom.toAlgebra
    ((ΓSpecIso (strictHenselizationRing pbar)).hom.hom.comp
      ((strictHenselizationStructuralMap pbar).appTop.hom.comp
        (ΓSpecIso (.of A)).inv.hom))

/-- Strict henselization comparison for a quasi-finite ring map.

Source: Stacks Project, Algebra, Tag 05WR, `lemma-quasi-finite-strict-henselization`;
(blueprint: lem-trf-strict-henselization-quasi-finite-ring).

The hypotheses give a finite-type ring map, a quasi-finite target prime, and compatible
geometric points.  The conclusion gives the canonical strict-henselization map, its
finite-local property, the finite purely inseparable residue extension, and an explicit
localization of the pushout (the tensor product) at the kernel of its evaluation map.
Proof, following the seven steps of the node:
1. Functoriality supplies the local strict henselizations R and H, the canonical local
   map φ, and their residue embeddings into Ω. Set C = R ⊗[A] B, let ε multiply the two
   evaluations, and put n = ker ε and D = C_n. The contractions of n are m_R and q
   (`lem-weil-pbc-strict-henselization-functoriality`).
2. The four-rings lemma applied to A, B, R, C, with the tensor symmetry as its surjection,
   makes R → C finite type and quasi-finite at n (`lem-weil-pbc-quasi-finite-four-rings`).
3. Henselian finite-type product decomposition isolates the finite local factor selected
   by n; the residual non-quasi-finite factor is excluded by the four-rings lemma.
   The selected prime is maximal because its quotient is a finite-dimensional domain
   over κ(R), hence a field. Thus D is finite local over R and henselian
   (`lem-weil-pbc-henselian-finite-type-product-decomposition`,
   `lem-weil-pbc-finite-local-henselian`).
4. Its residue E is finite over κ(R). The finite-extension lemma makes E separably closed;
   the separable-first lemma makes E/κ(R) purely inseparable, since κ(R) is separably
   closed. Hence D is strictly henselian
   (`lem-weil-pbc-sepclosed-finite-extension-unique-embedding`,
   `lem-weil-pbc-separable-first-purely-inseparable`).
5. The affine-chart theorem makes A → R and B → H ind-etale. Base change makes B → C
   ind-etale, and D is the filtered colimit of the principal localizations C_f for f ∉ n.
   Each such localization is etale of finite presentation. Composition makes B → D
   ind-etale (`lem-weil-pbc-strict-henselization-affine-chart-ind-etale`,
   `lem-weil-pbc-ind-etale-stability`,
   `lem-weil-pbc-etale-algebra-finite-presentation-localization`).
6. The tensor map C → H, r ⊗ b ↦ φ(r)b, contracts m_H to n, so extends uniquely to a
   local B-map D → H. Relative ind-etale stability makes this map weakly etale;
   Olivier's strictly-local theorem makes it an isomorphism. Its R-composite is φ
   (`lem-weil-pbc-ind-etale-stability`, `thm-weil-pbc-weak-etale-strict-local`).
7. Elements of A outside p are already units in R, and elements of B outside q are
   inverted in D. Thus C_n is canonically the stated localization of R ⊗[A_p] B_q.
   The isomorphism of step 6 respects both R and B structural maps, transporting module
   finiteness, locality, and the residue assertions to φ. Finite ring maps satisfy the
   finite-type and quasi-finite hypotheses (`lem-weil-pbc-finite-ring-map-quasi-finite`). -/
theorem strictHenselization_quasiFinite_ring
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B]
    (q : PrimeSpectrum B)
    (hq : Algebra.IsQuasiFiniteAtPrime A B q)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (pbar : Spec (.of Ω) ⟶ Spec (.of A))
    (qbar : Spec (.of Ω) ⟶ Spec (.of B))
    (qbar_point : qbar (IsLocalRing.closedPoint Ω) = q)
    (compat : qbar ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = pbar) :
    letI := strictHenselizationAlgebra pbar
    ∃ (_ : IsLocalRing (strictHenselizationRing pbar)),
      ∃ (_ : IsLocalRing (strictHenselizationRing qbar)),
      ∃ (φ : strictHenselizationRing pbar →+* strictHenselizationRing qbar),
        Spec.map (CommRingCat.ofHom φ) =
            strictHenselizationMap (Spec.map (CommRingCat.ofHom (algebraMap A B))) qbar ≫
              eqToHom (congrArg strictHenselizationScheme compat) ∧
        ∃ (_ : IsLocalHom φ),
          (@Module.Finite (strictHenselizationRing pbar) (strictHenselizationRing qbar)
            _ _ φ.toAlgebra.toModule) ∧
          (@Module.Finite (IsLocalRing.ResidueField (strictHenselizationRing pbar))
            (IsLocalRing.ResidueField (strictHenselizationRing qbar)) _ _
            (IsLocalRing.ResidueField.map φ).toAlgebra.toModule) ∧
          @IsPurelyInseparable
            (IsLocalRing.ResidueField (strictHenselizationRing pbar))
            (IsLocalRing.ResidueField (strictHenselizationRing qbar)) _ _
            (IsLocalRing.ResidueField.map φ).toAlgebra ∧
          ∃ (ε : TensorProduct A (strictHenselizationRing pbar) B →+* Ω),
            (∀ (r : strictHenselizationRing pbar) (b : B),
              ε (TensorProduct.tmul A r b) =
                strictHenselizationPointEvaluation pbar r *
                  ((ΓSpecIso (.of Ω)).hom.hom
                    (qbar.appTop.hom ((ΓSpecIso (.of B)).inv.hom b)))) ∧
            ∃ (hε : (RingHom.ker ε).IsPrime),
              ∃ (e : strictHenselizationRing qbar ≃+*
                Localization.AtPrime (RingHom.ker ε)),
                (∀ r : strictHenselizationRing pbar,
                  e (φ r) =
                    algebraMap (TensorProduct A (strictHenselizationRing pbar) B)
                      (Localization.AtPrime (RingHom.ker ε)) (TensorProduct.tmul A r 1)) ∧
                (∀ b : B,
                  e ((ΓSpecIso (strictHenselizationRing qbar)).hom.hom
                      ((strictHenselizationStructuralMap qbar).appTop.hom
                        ((ΓSpecIso (.of B)).inv.hom b))) =
                    algebraMap (TensorProduct A (strictHenselizationRing pbar) B)
                      (Localization.AtPrime (RingHom.ker ε)) (TensorProduct.tmul A 1 b)) := by
  sorry

end AlgebraicGeometry.Scheme
