/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.RingTheory.FiniteLocalHenselian
import WeilConjectures.RingTheory.FilteredColimitHenselianPair
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Local structure of the finite-lift colimit

Source: Stacks Project, Algebra, Tags 0BSL, 04GH, 04GI; More on Algebra, Tag 0FWT
(blueprint: lem-wf-finite-local-lift-colimit-structure).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace HenselianLocalRing

/-- The finite local etale lifts of all finite separable residue subextensions have
strictly henselian local ind-etale colimit. The residue field `k` is written canonically
as `ResidueField H`. The ring equivalences `r` are `k`-linear by `hr_base`, using the
canonical residue-field maps; `hr_transition` expresses the inclusions into `K`.

Source: Stacks Project, Algebra, Tags 0BSL, 04GH (2), 04GI; More on Algebra, Tag 0FWT
(blueprint: lem-wf-finite-local-lift-colimit-structure).

Proof plan:
1. The finite separable intermediate fields form a nonempty directed small poset.
   Apply lem-weil-pbc-commutative-algebras-colimits-exist. For any colimit cocone,
   lem-weil-pbc-filtered-colimit-algebras-elementwise gives the underlying ring colimit
   and representatives for every element.
2. The compatible reduction maps followed by `r` and inclusion into `K` induce `q` by
   def-weil-pbc-category-colimit. Every element of `K` lies in a finite separable
   subfield by def-pd-separable-closure, so `q` is surjective. A representative maps
   to zero exactly when it lies in its stage maximal ideal, giving the kernel union.
3. Apply lem-sfb-local-colimit-residue-field: the kernel union is the unique maximal
   ideal and each coprojection is local. A representative outside it is a unit by
   lem-weil-pbc-local-ring-unit-criterion. Compose a local structure map at any stage
   with its local coprojection to obtain locality of the structure map from `H`.
4. The surjection `q` descends to a bijection from the residue field to `K`; its
   compatibility with each `r` makes this identification linear over `ResidueField H`.
5. By lem-weil-pbc-finite-local-henselian every finite local stage is henselian.
6. Apply lem-weil-pbc-filtered-colimit-henselian-pair to their maximal-ideal pairs.
   The resulting ideal is the kernel union, hence the colimit is henselian local.
   Its residue field is the separably closed field `K`, so it is strictly henselian
   by def-weil-pbc-henselian-terminology.
7. The same diagram consists of etale, hence finitely presented, algebras, so it
   exhibits ind-etaleness by def-weil-pbc-ind-etale-algebra. No Noetherianity or
   completeness is used. -/
theorem finite_local_lift_colimit_structure
    (H K : Type u) [CommRing H] [HenselianLocalRing H] [Field K]
    [Algebra (ResidueField H) K] [IsSepClosure (ResidueField H) K]
    (B : {e : IntermediateField (ResidueField H) K //
      FiniteDimensional (ResidueField H) e ∧ Algebra.IsSeparable (ResidueField H) e} ⥤
        CommAlgCat.{u} H)
    [∀ e, IsLocalRing (B.obj e)]
    [∀ e, Module.Finite H (B.obj e)]
    [∀ e, Algebra.Etale H (B.obj e)]
    [∀ e, IsLocalHom (algebraMap H (B.obj e))]
    [∀ (e f) (a : e ⟶ f), IsLocalHom (B.map a).hom.toRingHom]
    (hn : ∀ e, maximalIdeal (B.obj e) =
      Ideal.map (algebraMap H (B.obj e)) (maximalIdeal H))
    (r : ∀ e, ResidueField (B.obj e) ≃+* e.1)
    (hr_base : ∀ e, (r e).toRingHom.comp
      (ResidueField.map (algebraMap H (B.obj e))) = algebraMap (ResidueField H) e.1)
    (hr_transition : ∀ (e f) (a : e ⟶ f) (b : B.obj e),
      ((r f) (residue (B.obj f) ((B.map a).hom b)) : K) =
        ((r e) (residue (B.obj e) b) : K)) :
    Nonempty (ColimitCocone B) ∧
      ∀ (c : Cocone B), IsColimit c →
        Nonempty (IsColimit ((forget₂ (CommAlgCat H) CommRingCat).mapCocone c)) ∧
        ∃ q : c.pt →+* K,
          (∀ e, ∀ b : B.obj e, q ((c.ι.app e).hom b) =
            ((r e) (residue (B.obj e) b) : K)) ∧
          Function.Surjective q ∧
          (RingHom.ker q : Set c.pt) =
            (⋃ e, (c.ι.app e).hom '' (maximalIdeal (B.obj e) : Set (B.obj e))) ∧
          (∀ x : c.pt, ∃ e, ∃ b : B.obj e, (c.ι.app e).hom b = x) ∧
          (∀ x : c.pt, x ∉ RingHom.ker q → IsUnit x) ∧
          ∃ (_ : IsLocalRing c.pt) (_ : IsLocalHom (algebraMap H c.pt)),
            maximalIdeal c.pt = RingHom.ker q ∧
            (∀ e, IsLocalHom (c.ι.app e).hom.toRingHom) ∧
            (∃ rC : ResidueField c.pt ≃+* K,
              (∀ x : c.pt, rC (residue c.pt x) = q x) ∧
              rC.toRingHom.comp (ResidueField.map (algebraMap H c.pt)) =
                algebraMap (ResidueField H) K) ∧
            (∀ e, HenselianLocalRing (B.obj e)) ∧
            HenselianRing c.pt (maximalIdeal c.pt) ∧
            IsStrictlyHenselianLocalRing c.pt ∧
            RingHom.IndEtaleAcrossUniverses (algebraMap H c.pt) := by
  sorry

end HenselianLocalRing
