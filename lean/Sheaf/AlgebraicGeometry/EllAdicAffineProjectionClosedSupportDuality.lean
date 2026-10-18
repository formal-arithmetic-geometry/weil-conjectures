/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.AffineSpace
import Sheaf.AlgebraicGeometry.EllAdicAffineProjectionRepresentable
import all Sheaf.AlgebraicGeometry.EllAdicCompactSupportComposition

/-! # Affine projection duality with closed supports -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

private theorem transport_representability
    {C A D E : Type*} [Category C] [Category A] [Category D] [Category E]
    {F : C ⥤ D} {I : C ⥤ A} {J : A ⥤ D} {H : A ⥤ E} {Q : C ⥤ E}
    (β : F ≅ I ⋙ J) (ζ : I ⋙ H ≅ Q) (K : D) (P : E)
    (e : ∀ M : A, (J.obj M ⟶ K) ≃ (H.obj M ⟶ P))
    (he : ∀ (M N : A) (a : M ⟶ N) (b : J.obj N ⟶ K),
      e M (J.map a ≫ b) = H.map a ≫ e N b) :
    ∃ e' : ∀ M : C, (F.obj M ⟶ K) ≃ (Q.obj M ⟶ P),
      ∀ (M N : C) (a : M ⟶ N) (b : F.obj N ⟶ K),
        e' M (F.map a ≫ b) = Q.map a ≫ e' N b := by
  let e' (M : C) : (F.obj M ⟶ K) ≃ (Q.obj M ⟶ P) :=
    { toFun := fun b ↦ (ζ.app M).inv ≫ e (I.obj M) ((β.app M).inv ≫ b)
      invFun := fun b ↦ (β.app M).hom ≫ (e (I.obj M)).symm ((ζ.app M).hom ≫ b)
      left_inv := fun b ↦ by simp
      right_inv := fun b ↦ by simp }
  refine ⟨e', fun M N a b ↦ ?_⟩
  have hβ := β.inv.naturality a
  have hζ := ζ.inv.naturality a
  change J.map (I.map a) ≫ (β.app N).inv = (β.app M).inv ≫ F.map a at hβ
  change Q.map a ≫ (ζ.app N).inv = (ζ.app M).inv ≫ H.map (I.map a) at hζ
  change (ζ.app M).inv ≫ e (I.obj M) ((β.app M).inv ≫ (F.map a ≫ b)) =
    Q.map a ≫ ((ζ.app N).inv ≫ e (I.obj N) ((β.app N).inv ≫ b))
  calc
    _ = (ζ.app M).inv ≫ e (I.obj M)
        (J.map (I.map a) ≫ ((β.app N).inv ≫ b)) := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ (ζ.app M).inv ≫ e (I.obj M) (z ≫ b)) hβ.symm
    _ = (ζ.app M).inv ≫
        (H.map (I.map a) ≫ e (I.obj N) ((β.app N).inv ≫ b)) :=
      congrArg (fun z ↦ (ζ.app M).inv ≫ z)
        (he (I.obj M) (I.obj N) (I.map a) ((β.app N).inv ≫ b))
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ e (I.obj N) ((β.app N).inv ≫ b)) hζ.symm

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ hΛ in
/-- Affine projection duality, evaluated on closed supports, before applying the closed
exceptional adjoint. The representing object lives on affine space and is independent of
both the closed immersion and the compactification.

Source: blueprint `sk-thm-existence/sk-thm-existence.proof.md`, geometric restriction
paragraph; `sk-thm-restriction/sk-thm-restriction-local.proof.md`, factorization and
constructibility; `sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md`.
Proof: write `d` for the cardinality of `n`. The diagonal class and trace on the projective
line give inverse adjunction Hom maps for the affine-line compact-support functor and
pullback twisted by one and shifted by two. The trace/diagonal triangle identities show
that these maps are inverse and natural in the source. Iterate along the `d` coordinate
projections and transport along a finite reindexing of affine space. For a bounded
constructible `K`, take `P = p* K(d)[2d]`. Exact pullback preserves constructibility; the Tate
line is locally free of rank one, and a finite shift preserves boundedness and
constructibility. For integral coefficients the trace and diagonal are the compatible
integral ones and the same calculation allows torsion. Rational coefficients follow by
scalar extension from an integral model, and the algebraic-closure case by the filtered
finite-subextension realization; none of these steps replaces the ordinary category by a
completed derived category. Compactification independence and composition identify compact
support of `i ≫ p` with closed pushforward followed by compact support of `p`, since a closed
immersion is proper and its pushforward is exact. Apply the projection adjunction to
`i_* M` and use that comparison to obtain `e M`. Naturality of the comparison and the
adjunction gives the displayed identity for every source morphism. For dimension zero the
projection is the identity and the construction is the identity Hom equivalence; for an
empty support or a zero complex the same maps give the zero Hom equivalences.
(blueprint: lem-sfb-adic-affine-projection-closed-support-duality) -/
theorem affine_projection_closedSupport_duality (n : Type u) [Finite n]
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    let A : Over (Spec (.of k)) := Over.mk ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom)
    let p : A ⟶ Y := Over.homMk (𝔸(n; Y.left) ↘ Y.left) rfl
    ∃ P : (boundedConstructible (condensedRingObj Λ A.left)).FullSubcategory,
      ∀ {U : Over (Spec (.of k))}
        [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
        (i : U ⟶ A) [IsClosedImmersion i.left]
        [PreservesFiniteColimits ((i.left)_*⟦Λ⟧)]
        (c : Compactification (i ≫ p).left),
        ∃ e : ∀ M : (boundedConstructible (condensedRingObj Λ U.left)).FullSubcategory,
          ((rightDerivedLowerShriekOfCompactification Λ c).obj M.obj ⟶ K.obj) ≃
            (D((i.left)_*⟦Λ⟧).obj M.obj ⟶ P.obj),
          ∀ (M N : (boundedConstructible (condensedRingObj Λ U.left)).FullSubcategory)
            (a : M.obj ⟶ N.obj)
            (b : (rightDerivedLowerShriekOfCompactification Λ c).obj N.obj ⟶ K.obj),
            e M ((rightDerivedLowerShriekOfCompactification Λ c).map a ≫ b) =
              D((i.left)_*⟦Λ⟧).map a ≫ e N b := by
  classical
  let A : Over (Spec (.of k)) := Over.mk ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom)
  let p : A ⟶ Y := Over.homMk (𝔸(n; Y.left) ↘ Y.left) rfl
  have : LocallyOfFiniteType A.hom :=
    inferInstanceAs (LocallyOfFiniteType ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom))
  have : QuasiCompact A.hom :=
    inferInstanceAs (QuasiCompact ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom))
  have : IsSeparated A.hom :=
    inferInstanceAs (IsSeparated ((𝔸(n; Y.left) ↘ Y.left) ≫ Y.hom))
  have : IsFinitenessCoefficient ℓ Λ := by cases hΛ <;> infer_instance
  obtain ⟨P, e, he⟩ := affine_projection_representable Λ ℓ hΛ n K
  refine ⟨P, ?_⟩
  intro U _ _ _ i _ _ c
  let αcomp := Classical.choice (ellAdic_compactSupport_comp Λ ℓ hΛ i p)
  let αc := Classical.choice (all_adic_compactificationIso Λ ℓ hΛ (f := i ≫ p) c
    (compactificationOverField (i ≫ p)))
  let αi := Classical.choice (properLowerShriekIso Λ ℓ hΛ i)
  let I := boundedConstructibleLowerStar Λ ℓ i
  let α : boundedConstructibleLowerShriekOfCompactification Λ ℓ (f := i ≫ p) c ≅
      I ⋙ boundedConstructibleLowerShriek Λ ℓ p :=
    αc ≪≫ αcomp ≪≫ Functor.isoWhiskerRight αi _
  let β : (boundedConstructible _).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c ≅
      I ⋙ (boundedConstructible _).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ (compactificationOverField p) :=
    (boundedConstructibleLowerShriekOfCompactificationCompatibility Λ ℓ (f := i ≫ p) c).symm ≪≫
      Functor.isoWhiskerRight α (boundedConstructible _).ι ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft I
        (boundedConstructibleLowerShriekOfCompactificationCompatibility Λ ℓ (f := p)
          (compactificationOverField p))
  let ζ : I ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ D((i.left)_*⟦Λ⟧) :=
    boundedConstructibleLowerStarCompatibility Λ ℓ i ≪≫
      Functor.isoWhiskerLeft (boundedConstructible _).ι
        ((i.left)_*⟦Λ⟧).rightDerivedFunctorIsoMapDerivedCategory
  obtain ⟨e', he'⟩ := transport_representability β ζ K.obj P.obj e
    (fun M N a b ↦ he M N a.hom b)
  exact ⟨e', fun M N a b ↦ he' M N (ObjectProperty.homMk a) b⟩

end AlgebraicGeometry.ProEtale.CondensedRing
