/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

import Sheaf.AlgebraicGeometry.BertiniUniversalBaseChange
import Sheaf.AlgebraicGeometry.BertiniUniversalGenericFibre
import WeilConjectures.AlgebraicGeometry.GenericGeometricIrreducibilityShrink
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Geometric irreducibility of a general member of a linear system

Source: Stacks Project, More on Morphisms, Tag 0G4F, lemma-bertini-irreducible,
in Varieties Situation 0G47 (blueprint: lem-zl-bertini-irreducible-member).

The helper constructs the member over an extension field using the canonical tensor-pullback
unit, then uses the recorded zero-scheme construction. Codimension is `Order.coheight` on
irreducible closed subsets, ordered by inclusion. Components of a closed subset are its maximal
irreducible closed subsets. Generality is written out using all extension-field points of a
nonempty open in affine coordinate space.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry


attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

/-- The ideal of the member with coordinates `a` over `K`: pull back the sections `s i`
along `Y_K → Y`, multiply by the functions from `a i`, and take the zero scheme of their sum.
The adjunction chosen here has the prescribed sectionwise unit `m ↦ 1 ⊗ m`.
Source: Stacks Project, Varieties Situation 0G47, formula for `H_v`
(blueprint: lem-zl-bertini-irreducible-member). -/
noncomputable def linearSystemMemberIdeal
    {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    (L : Y.Modules) {r : ℕ} (s : Fin r → Γ(L, ⊤))
    (K : Type u) [Field K] [Algebra k K] (a : Fin r → K) :
    (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IdealSheafData :=
  (Scheme.Modules.homOfGlobalSection _
    (∑ i : Fin r,
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
          ((Scheme.ΓSpecIso (.of K)).inv (a i)) •
        (@id Γ((Scheme.Modules.tensorPullback
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj L, ⊤)
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))).unit.app L).val.app
            (op ⊤) (s i))))).zeroLocus

attribute [local irreducible] linearSystemMemberIdeal bertiniUniversalIdeal


private theorem coefficientPoint_comp {k K : Type u} [Field k] [Field K] [Algebra k K]
    {I : Type u} (a : I → K) :
    (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact MvPolynomial.aeval_C _ c

private noncomputable def memberToUniversalAmbient {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) {I : Type u} (a : I → K) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
      pullback (Spec.map
        (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f :=
  pullback.lift
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
      (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a).toRingHom)))
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (by rw [Category.assoc, coefficientPoint_comp, pullback.condition])

private theorem memberToUniversalAmbient_isPullback
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) {I : Type u} (a : I → K) :
    IsPullback (memberToUniversalAmbient f a)
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.fst (Spec.map
        (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f)
      ((Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a).toRingHom))) := by
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback _ _).flip)
  · simpa only [memberToUniversalAmbient, pullback.lift_snd, coefficientPoint_comp] using
      (IsPullback.of_hasPullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  · exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    Scheme.Modules.tensorSectionsUnit f M =
      (show Γ(M, ⊤) ⟶ Γ((Scheme.Modules.tensorPullback f).obj M, ⊤) from
        Scheme.Modules.Hom.app
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app M)
          ⊤) := by
  unfold Scheme.Modules.tensorSectionsUnit
  have hi : (homOfLE f.preimage_top.ge).op = 𝟙 (op (⊤ : X.Opens)) := rfl
  erw [hi, ((Scheme.Modules.tensorPullback f).obj M).presheaf.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem universalIdeal_comap_member
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k))
    (L : Y.Modules) [L.IsInvertible] {r : ℕ}
    (s : Fin r → Γ(L, ⊤)) (a : Fin r → K) :
    (bertiniUniversalIdeal f L (fun i : ULift.{u} (Fin r) ↦ s i.down)).comap
      (memberToUniversalAmbient f (fun i : ULift.{u} (Fin r) ↦ a i.down)) =
      linearSystemMemberIdeal f L s K a := by
  let m := memberToUniversalAmbient f (fun i : ULift.{u} (Fin r) ↦ a i.down)
  have hm₁ : m ≫ pullback.fst
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin r)) k))) f =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.aeval (R := k) (fun i : ULift.{u} (Fin r) ↦ a i.down)).toRingHom) :=
    pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin r)) k))) f =
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    pullback.lift_snd _ _ _
  rw [bertiniUniversalIdeal_comap f L _ m, hm₁, hm₂]
  unfold linearSystemMemberIdeal
  apply congrArg (fun t : Γ((Scheme.Modules.tensorPullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj L, ⊤) ↦
    (Scheme.Modules.homOfGlobalSection _ t).zeroLocus)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hcoord (i : ULift.{u} (Fin r)) :
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (R := k) (fun j : ULift.{u} (Fin r) ↦ a j.down)).toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} (Fin r)) k))).inv
          (MvPolynomial.X i)) = (Scheme.ΓSpecIso (.of K)).inv (a i.down) := by
    rw [Scheme.specMap_appTop_ΓSpecIso_inv]
    change (Scheme.ΓSpecIso (.of K)).inv
      (MvPolynomial.aeval (R := k) (fun j : ULift.{u} (Fin r) ↦ a j.down)
        (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
  simp only [hcoord]
  refine (Equiv.ulift.sum_comp (fun i : Fin r ↦
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
      ((Scheme.ΓSpecIso (.of K)).inv (a i)) •
      Scheme.Modules.tensorSectionsUnit
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L (s i))).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun t ↦
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
      ((Scheme.ΓSpecIso (.of K)).inv (a i)) • t)
  rw [tensorUnit_eq]
  rfl

private noncomputable def coefficientLift {k : Type u} [Field k] (r : ℕ) :
    Spec (.of (MvPolynomial (Fin r) k)) ≅
      Spec (.of (MvPolynomial (ULift.{u} (Fin r)) k)) :=
  Scheme.Spec.mapIso
    (MvPolynomial.renameEquiv k Equiv.ulift).toRingEquiv.toCommRingCatIso.op

private theorem coefficientLift_point {k K : Type u} [Field k] [Field K] [Algebra k K]
    {r : ℕ} (a : Fin r → K) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a).toRingHom) ≫
      (coefficientLift (k := k) r).hom =
    Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := k) (fun i : ULift.{u} (Fin r) ↦ a i.down)).toRingHom) := by
  unfold coefficientLift
  rw [Scheme.Spec.mapIso_hom]
  change Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.rename Equiv.ulift).toRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    simp

private theorem geometric_baseChange_of_geometric_fibre
    {H T : Scheme.{u}} (q : H ⟶ T) {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ T)
    (h : GeometricallyIrreducible
      (q.fiberToSpecResidueField (a (IsLocalRing.closedPoint K)))) :
    GeometricallyIrreducible (pullback.snd q a) := by
  let t := a (IsLocalRing.closedPoint K)
  let e := Spec.map (T.descResidueField (Scheme.stalkClosedPointTo a))
  have he : e ≫ T.fromSpecResidueField t = a :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K T a
  let d : pullback q a ⟶ q.fiber t := pullback.lift
    (pullback.fst q a) (pullback.snd q a ≫ e)
    (by rw [Category.assoc, he, pullback.condition])
  have hd : IsPullback d (pullback.snd q a) (q.fiberToSpecResidueField t) e := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback q (T.fromSpecResidueField t))
    · simpa only [d, pullback.lift_fst, he] using IsPullback.of_hasPullback q a
    · exact pullback.lift_snd _ _ _
  exact MorphismProperty.of_isPullback hd h

/-- Under the codimension-two hypotheses, a general member is geometrically irreducible.
The `k`-structure on global sections is restriction of scalars along the structure morphism;
`b` supplies the coordinates in the definition of "general". Maximality is taken among
irreducible closed subsets contained in the indicated intersection or base locus.

Source: Stacks Project, Tag 0G4F, in Varieties Situation 0G47
(blueprint: lem-zl-bertini-irreducible-member).

Proof:
1. Finite type over a field gives a Noetherian scheme (pqf-lem-locnoeth-lft and
   pqf-lem-affine-open-locnoeth). Its nilradical has a positive power zero
   (lem-sc-reduction-nilradical-nilpotent). Reduction and all its field base changes,
   including the section zero schemes and intersections, have identical underlying spaces.
   Thus reduce to an integral scheme (def-pc-integral-scheme).
2. The three vectors in the first hypothesis are independent. At the generic point of W,
   any relation has zero first coefficient. Dependence of the other two would make W a
   component of a single equation, of height at most one by
   lem-weil-pbc-noetherian-height-quotient-bound. Extend them to a basis.
3. Construct the universal zero scheme of sum x_i psi(b_i) over affine parameter space.
   On a trivializing affine Spec A it is Spec A[x_i]/(sum x_i f_i), hence its projection
   is finite type and its field-point fibres are the members defined above
   (def-pc-zero-scheme and def-weil-pbc-mv-polynomial-ring).
4. The first section is nonzero on every nonempty trivializing affine, by integrality.
   The base-locus hypothesis makes every minimal prime of (f_i) have height at least two.
   Apply lem-zl-linear-incidence-irreducible. The irreducible affine incidence charts
   overlap over the complement of the first zero scheme, so their union is irreducible.
5. Choose a trivializing affine meeting W in that complement. Dividing by the first
   section gives functions g_2,...,g_r. The common maximal chain length in a finite-type
   domain (lem-weil-pbc-finite-type-domain-dimension-local-ring) shows W has dimension d-2.
   Apply lem-zl-bertini-independent-functions to obtain constants c_i such that the
   variables, sum g_i x_i, and sum c_i g_i are algebraically independent.
6. The function field K of Y is geometrically irreducible over k by
   lem-zl-generic-point-geometric-irreducibility and is finitely generated as a field.
   Apply lem-zl-bertini-field-extension. Eliminating x_1 identifies the incidence function
   field with K(x_2,...,x_r), geometrically irreducible over the parameter function field;
   independence also gives dominance of the incidence projection.
7. The generic fibre is irreducible, with this function field: localization preserves the
   generic point on its nonempty affine charts. Apply
   lem-zl-generic-point-geometric-irreducibility to make the generic fibre geometrically
   irreducible over the parameter function field.
8. Apply lem-sbc-generic-geometric-irreducibility-shrink to obtain a nonempty parameter
   open with geometrically irreducible residue-field fibres. Every extension-field point
   gives a base change of such a fibre, hence is geometrically irreducible. Transfer back
   through the nilpotent thickenings of step 1. This is precisely generality in 0G47. -/
theorem exists_open_geometricallyIrreducible_linearSystemMember
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [GeometricallyIrreducible (Y ↘ Spec (.of k))]
    (L : Y.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    letI : Module k Γ(L, ⊤) :=
      Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
    ∀ ψ : V →ₗ[k] Γ(L, ⊤),
      (∃ (v₁ v₂ v₃ : V) (W : TopologicalSpace.IrreducibleCloseds Y),
        Maximal (fun Z : TopologicalSpace.IrreducibleCloseds Y ↦
          (Z : Set Y) ⊆ (Scheme.Modules.homOfGlobalSection L (ψ v₂)).zeroLocus.support ∩
            (Scheme.Modules.homOfGlobalSection L (ψ v₃)).zeroLocus.support) W ∧
        ¬ (W : Set Y) ⊆ (Scheme.Modules.homOfGlobalSection L (ψ v₁)).zeroLocus.support ∧
        Order.coheight W = 2) →
      (∀ B : TopologicalSpace.IrreducibleCloseds Y,
        Maximal (fun Z : TopologicalSpace.IrreducibleCloseds Y ↦
          (Z : Set Y) ⊆ ⋂ w : V,
            ((Scheme.Modules.homOfGlobalSection L (ψ w)).zeroLocus.support : Set Y)) B →
        2 ≤ Order.coheight B) →
      ∀ (r : ℕ) (b : Module.Basis (Fin r) k V),
        ∃ U : (Spec (.of (MvPolynomial (Fin r) k))).Opens,
          (U : Set (Spec (.of (MvPolynomial (Fin r) k)))).Nonempty ∧
          ∀ (K : Type u) [Field K] [Algebra k K] (a : Fin r → K),
            Set.range (Spec.map
              (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a).toRingHom)) ⊆ (U : Set _) →
            GeometricallyIrreducible
              ((linearSystemMemberIdeal (Y ↘ Spec (.of k)) L (fun i ↦ ψ (b i)) K a).subschemeι ≫
                pullback.snd (Y ↘ Spec (.of k))
                  (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  classical
  intro ψ hcomp hbase r b
  let f := Y ↘ Spec (.of k)
  let s : Fin r → Γ(L, ⊤) := fun i ↦ ψ (b i)
  let q := bertiniUniversalProjection f L (fun i : ULift.{u} (Fin r) ↦ s i.down)
  let η := genericPoint (Spec (.of (MvPolynomial (ULift.{u} (Fin r)) k)))
  have hη : IsGenericPoint η Set.univ := genericPoint_spec _
  have hgeom : GeometricallyIrreducible (q.fiberToSpecResidueField η) :=
    geometricallyIrreducible_bertiniUniversal_genericFiber k Y L V ψ hcomp hbase r b
  have : LocallyOfFiniteType q := by
    dsimp [q, bertiniUniversalProjection]
    infer_instance
  have : QuasiCompact q := by
    dsimp [q, bertiniUniversalProjection]
    infer_instance
  obtain ⟨U, hηU, hU⟩ := exists_open_generic_geometric_irreducibility_shrink q η hη hgeom
  let R := coefficientLift (k := k) r
  refine ⟨R.hom ⁻¹ᵁ U, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := R.hom.homeomorph.surjective η
    exact ⟨x, by change R.hom x ∈ U; rwa [show R.hom x = η from hx]⟩
  intro K _ _ a ha
  let a' : ULift.{u} (Fin r) → K := fun i ↦ a i.down
  have ha' : Set.range
      (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a').toRingHom)) ⊆ U := by
    rintro _ ⟨z, rfl⟩
    rw [← coefficientLift_point a]
    exact ha (Set.mem_range_self z)
  have hpoint := hU _ (ha' (Set.mem_range_self (IsLocalRing.closedPoint K)))
  have hgeom := geometric_baseChange_of_geometric_fibre q
    (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a').toRingHom)) hpoint
  have hJ := universalIdeal_comap_member f L s a
  have hp := ((bertiniUniversalIdeal f L
    (fun i : ULift.{u} (Fin r) ↦ s i.down)).isPullback_comap
      (memberToUniversalAmbient f a')).flip.paste_vert
        (memberToUniversalAmbient_isPullback f a')
  change IsPullback _ (_ ≫ _) q _ at hp
  rw [← hJ]
  let e := hp.isoPullback
  have he : e.hom ≫ pullback.snd q
      (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a').toRingHom)) = _ :=
    hp.isoPullback_hom_snd
  rw [← he]
  infer_instance

end AlgebraicGeometry
