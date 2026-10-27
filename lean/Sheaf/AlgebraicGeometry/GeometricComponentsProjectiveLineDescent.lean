/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Mathlib.RingTheory.Adjoin.FG
import WeilConjectures.AlgebraicGeometry.SubsetGeometricIrreducibility
import Sheaf.AlgebraicGeometry.ProductIrreducibleComponentsBijection
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest
import WeilConjectures.FieldTheory.FieldTensorUniqueMinimalPrime
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Geometric components and descent of the projective line

Source: Stacks Project, Tags 038F, 01ZM (2)--(3), 00FV and 01J3
(blueprint: lem-trf-geometric-components-projective-line-descent).

The first statement uses the canonical reduced induced closed subscheme. The other two
allow any reduced closed immersion whose image is a component: Tag 01J3 uniquely identifies
it with that canonical scheme. All isomorphisms are in the category over the indicated field
or algebra. The equations for `r` and `s` uniquely characterize the canonical transition
and specialization maps by the two pullback projections.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Reduced component schemes correspond under an extension of algebraically closed fields.
Source: Stacks Project, Tags 038F, 038H, 035X, 020I and 01J3.
(blueprint: lem-trf-geometric-components-projective-line-descent)

Proof (node steps 1--5 and 11):
1. Tag 01J3 supplies the reduced closed component, finite type by its affine radical
   quotient charts (lem-weil-pbc-reduced-induced-closed-subscheme).
2. Apply lem-trf-geometric-reducedness-algebraic-closure-test with the identity closure
   of `k`. Apply lem-sbc-subset-geometric-irreducibility with the identity extension to
   obtain reducedness and nonempty irreducibility after extension to `L`.
3. The projection is surjective on affine charts by
   lem-weil-pbc-field-extension-base-change-faithfully-flat and
   lem-weil-pbc-faithfully-flat-surjective-spectrum, using
   lem-weil-pbc-fibre-product-affine-spectra.
4. The field-tensor theorem makes `Spec L` geometrically irreducible. Apply
   lem-sc-product-irreducible-components-bijection. Maximality identifies the corresponding
   component with the full inverse image of the original component.
5. Closed-immersion base change and uniqueness in Tag 01J3 identify its ideal with the
   vanishing ideal of this inverse image. The empty scheme gives the empty bijection. -/
theorem geometric_components_baseChange
    (k L : Type u) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    Set.BijOn (Set.preimage (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
      (irreducibleComponents C)
      (irreducibleComponents ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ∧
    ∀ T : TopologicalSpace.Closeds C, (T : Set C) ∈ irreducibleComponents C →
      IsReduced (pullback (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ∧
      IrreducibleSpace ↥(pullback (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ∧
      Surjective (pullback.fst (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ∧
      ∀ D : TopologicalSpace.Closeds ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
        (D : Set _) =
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹' (T : Set C) →
        (pullback.snd (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))))).ker =
            Scheme.IdealSheafData.vanishingIdeal D := by
  sorry

/-- A reduced component becomes a projective line exactly when it already is one.
Source: Stacks Project, Tags 01ZM (2)--(3), 00FV and 01J3.
(blueprint: lem-trf-geometric-components-projective-line-descent)

Proof (node steps 1 and 6--11): the component and the projective line are of finite
presentation over the Noetherian field, without a separatedness assumption. Write `L` as
the filtered union of its finitely generated `k`-subalgebras (lem-kun-algebra-union), and
apply thm-pd-spreading-out twice to the isomorphism and inverse and then to their inverse
identities. Specialize at a maximal ideal, whose residue field is `k` by
lem-weil-pbc-closed-point-residue-field-base and Tag 00FV. This gives the forward implication;
base-changing a `k`-isomorphism gives the converse. ProjectiveSpace.isPullback_map supplies
the canonical projective-line base-change identifications (node step 6). -/
theorem reduced_component_projectiveLine_iff
    (k L : Type u) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (R : Scheme.{u}) (i : R ⟶ C) [IsClosedImmersion i] [IsReduced R]
    (hi : Set.range i ∈ irreducibleComponents C) :
    Nonempty (Over.mk (pullback.snd (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ≅
      Over.mk (ProjectiveLine (Spec (.of L)) ↘ Spec (.of L))) ↔
    Nonempty (Over.mk (i ≫ f) ≅ Over.mk (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))) := by
  sorry

/-- The prescribed isomorphism and its inverse descend together, and specialize to a
`k`-isomorphism. The specialized isomorphism need not recover the prescribed one over `L`.
Source: Stacks Project, Tags 01ZM (2)--(3), 00FV and 01J3.
(blueprint: lem-trf-geometric-components-projective-line-descent)

Proof (node steps 1 and 6--11):
1. The finite-type reduced component is quasi-compact and locally Noetherian, hence
   quasi-separated and of finite presentation. The two standard affine charts prove the
   same for the projective line; their gluing identifies the standard and base-change models.
2. Use lem-kun-algebra-union and lem-weil-pbc-spec-colimit-limit for the directed system
   of finitely generated subalgebras, all affine and qcqs.
3. Apply thm-pd-spreading-out, Tag 01ZM (2), to the given isomorphism and to its inverse,
   and choose one stage containing both stages of definition.
4. Apply Tag 01ZM (3) to both inverse identities and enlarge the stage once more. The
   resulting isomorphism `a` still pulls back to the prescribed maps, as the two equations
   involving `r` express. Its inverse identities are encoded by the `Iso` structure.
5. A maximal ideal exists since this subalgebra of `L` is nonzero. Nullstellensatz and
   lem-weil-pbc-closed-point-residue-field-base give its residue algebra isomorphism `q`.
6. Pull back `a` and its inverse along this quotient point. The canonical map `s` is
   characterized by its two projections. The two final equations say that `b` and its
   inverse are precisely the specialized maps. No assertion identifies `b_L` with `e`. -/
theorem reduced_component_projectiveLine_iso_descends
    (k L : Type u) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (R : Scheme.{u}) (i : R ⟶ C) [IsClosedImmersion i] [IsReduced R]
    (hi : Set.range i ∈ irreducibleComponents C)
    (e : Over.mk (pullback.snd (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ≅
      Over.mk (ProjectiveLine (Spec (.of L)) ↘ Spec (.of L))) :
    ∃ A : Subalgebra k L, A.FG ∧
      ∃ a : Over.mk (pullback.snd (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k A)))) ≅
          Over.mk (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)),
        ∃ r : pullback (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶
            pullback (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k A))),
          r ≫ pullback.fst (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
            pullback.fst (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧
          r ≫ pullback.snd (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
            pullback.snd (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫
              Spec.map (CommRingCat.ofHom A.val.toRingHom) ∧
          e.hom.left ≫ ProjectiveSpace.map (ULift.{u} (Fin 2))
              (Spec.map (CommRingCat.ofHom A.val.toRingHom)) = r ≫ a.hom.left ∧
          e.inv.left ≫ r =
            ProjectiveSpace.map (ULift.{u} (Fin 2))
              (Spec.map (CommRingCat.ofHom A.val.toRingHom)) ≫ a.inv.left ∧
          ∃ m : Ideal A, m.IsMaximal ∧ ∃ q : (A ⧸ m) ≃ₐ[k] k,
            ∃ b : Over.mk (i ≫ f) ≅ Over.mk (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)),
              ∃ s : R ⟶ pullback (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k A))),
                s ≫ pullback.fst (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k A))) = 𝟙 R ∧
                s ≫ pullback.snd (i ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
                  (i ≫ f) ≫ Spec.map (CommRingCat.ofHom
                    (q.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk m))) ∧
                b.hom.left ≫ ProjectiveSpace.map (ULift.{u} (Fin 2))
                    (Spec.map (CommRingCat.ofHom
                      (q.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk m)))) = s ≫ a.hom.left ∧
                b.inv.left ≫ s =
                  ProjectiveSpace.map (ULift.{u} (Fin 2))
                    (Spec.map (CommRingCat.ofHom
                      (q.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk m)))) ≫ a.inv.left := by
  sorry

end AlgebraicGeometry
