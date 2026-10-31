/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Created abelian structure on fixed pairs

Source: `WeilConjectures/Mathlib/CategoryTheory/Preadditive/EndoFunctor.lean`,
`IsoAlgebra.abelian` and the forgetful functor; the limit and colimit constructions in
`WeilConjectures/Mathlib/CategoryTheory/Endofunctor/Algebra.lean`.
(blueprint: lem-sf-fixed-pair-created-abelian-structure)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

private noncomputable def liftLimit
    {A : Type u} [Category.{v} A] (T : A ⥤ A) [T.IsEquivalence]
    {J : Type w} [Category.{w} J] (D : J ⥤ IsoAlgebra T)
    (c : Cone (D ⋙ forget T)) (t : IsLimit c) :
    LiftsToLimit D (forget T) c t := by
  let α := IsLimit.conePointsIsoOfNatIso (isLimitOfPreserves T t) t
    (Functor.isoWhiskerLeft D (strNatIso T))
  have hα (j : J) : α.hom ≫ c.π.app j = T.map (c.π.app j) ≫ (D.obj j).str.hom :=
    IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ j
  let π : (Functor.const J).obj (mk c.pt α) ⟶ D :=
    { app j := ObjectProperty.homMk { f := c.π.app j, h := (hα j).symm }
      naturality i j f := (forget T).map_injective (by
        change 𝟙 c.pt ≫ c.π.app j = c.π.app i ≫ (D.map f).hom.f
        simpa using (c.w f).symm) }
  refine { liftedCone := Cone.mk (mk c.pt α) π
           validLift := Cone.ext (Iso.refl _) (fun _ ↦ (Category.id_comp _).symm)
           makesLimit := ?_ }
  refine
    { lift := fun s ↦ ObjectProperty.homMk
        { f := t.lift ((forget T).mapCone s)
          h := ?_ }
      fac := fun s j ↦ (forget T).map_injective (t.fac _ j)
      uniq := fun s m hm ↦ (forget T).map_injective
        (t.uniq ((forget T).mapCone s) m.hom.f
          (fun j ↦ congrArg (fun f ↦ (forget T).map f) (hm j))) }
  apply t.hom_ext
  intro j
  change (T.map (t.lift ((forget T).mapCone s)) ≫ α.hom) ≫ c.π.app j =
    (s.pt.str.hom ≫ t.lift ((forget T).mapCone s)) ≫ c.π.app j
  rw [Category.assoc, hα, ← T.map_comp_assoc, t.fac, Category.assoc, t.fac]
  exact (s.π.app j).hom.h

private noncomputable def liftColimit
    {A : Type u} [Category.{v} A] (T : A ⥤ A) [T.IsEquivalence]
    {J : Type w} [Category.{w} J] (D : J ⥤ IsoAlgebra T)
    (c : Cocone (D ⋙ forget T)) (t : IsColimit c) :
    LiftsToColimit D (forget T) c t := by
  let α := IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves T t) t
    (Functor.isoWhiskerLeft D (strNatIso T))
  have hα (j : J) : T.map (c.ι.app j) ≫ α.hom = (D.obj j).str.hom ≫ c.ι.app j :=
    IsColimit.comp_coconePointsIsoOfNatIso_hom (isColimitOfPreserves T t) t
      (Functor.isoWhiskerLeft D (strNatIso T)) j
  let ι : D ⟶ (Functor.const J).obj (mk c.pt α) :=
    { app j := ObjectProperty.homMk { f := c.ι.app j, h := hα j }
      naturality i j f := (forget T).map_injective (by
        change (D.map f).hom.f ≫ c.ι.app j = c.ι.app i ≫ 𝟙 c.pt
        simpa using c.w f) }
  refine { liftedCocone := Cocone.mk (mk c.pt α) ι
           validLift := Cocone.ext (Iso.refl _) (fun _ ↦ Category.comp_id _)
           makesColimit := ?_ }
  refine
    { desc := fun s ↦ ObjectProperty.homMk
        { f := t.desc ((forget T).mapCocone s)
          h := ?_ }
      fac := fun s j ↦ (forget T).map_injective (t.fac _ j)
      uniq := fun s m hm ↦ (forget T).map_injective
        (t.uniq ((forget T).mapCocone s) m.hom.f
          (fun j ↦ congrArg (fun f ↦ (forget T).map f) (hm j))) }
  apply (isColimitOfPreserves T t).hom_ext
  intro j
  change T.map (c.ι.app j) ≫ T.map (t.desc ((forget T).mapCocone s)) ≫ s.pt.str.hom =
    T.map (c.ι.app j) ≫ α.hom ≫ t.desc ((forget T).mapCocone s)
  rw [← T.map_comp_assoc, t.fac, ← Category.assoc, hα, Category.assoc, t.fac]
  exact (s.ι.app j).hom.h

/-- Fixed pairs of an additive autoequivalence inherit the abelian operations and all small
limits and colimits from their carriers. The two explicit lifting clauses specify the
structure isomorphism and the underlying projections or coprojections for every ambient
universal cone or cocone, including the empty ones.

Source: `Preadditive/EndoFunctor.lean`, `IsoAlgebra.abelian` and forgetful exactness;
`Endofunctor/Algebra.lean`, `ForgetCreatesLimits` and `ForgetCreatesColimits`.
(blueprint: lem-sf-fixed-pair-created-abelian-structure)

Proof plan (the eleven steps of the node):
1. The intertwining equation is closed under zero, addition and negation because `T` is
additive. Ambient bilinearity gives the inherited preadditive structure and faithfulness.
2. Multiplying the intertwining equation by the underlying inverse on both sides proves
that the inverse also intertwines; this proves conservativity before using abelianness.
3. By `lem-galois-equivalence-preserves-limits`, `T` takes an ambient limiting cone to a
limiting cone. Factor the cone with legs `T(p_i)` followed by the structure maps to obtain
alpha, and factor the inverse-structure cone to obtain beta. Uniqueness of factorizations
gives both inverse identities. This is the displayed comparison isomorphism.
4. Any ambient map into this limit intertwines: test its square against each projection.
Uniqueness gives the lifted universal property and uniqueness of structure; step 2 then
reflects limiting cones, so the forgetful functor creates limits.
5. Dually factor the cocones with legs the structure maps followed by the coprojections,
and their inverse-structure counterparts, through the ambient colimits preserved by `T`.
Uniqueness gives inverse maps and the displayed colimit comparison.
6. Test an ambient descent against `T` of each coprojection to prove that it intertwines.
This proves the lifted universal property, uniqueness of structure and creation of colimits.
7. Apply these constructions to empty, finite discrete and parallel-pair diagrams. The
ambient biproduct injections intertwine by testing against the projections; faithfulness
transfers their identities. Kernels and cokernels are the resulting (co)equalizers.
8. Faithfulness reflects monos and epis. Conversely a monic fixed-pair map has zero kernel,
and its created ambient kernel is zero, so its carrier is monic. Use cokernels dually.
9. A monic fixed-pair map is the kernel of its created cokernel: this holds on carriers by
`def-sp-abelian`, and cancellation by the ambient mono makes every factorization intertwine.
10. Dually an epic map is the cokernel of its created kernel. The final cancellation uses
that `T(f)` is epic, since it is conjugate to `f` by the structure isomorphisms. Together
with steps 1 and 7 these are the abelian axioms in `def-sp-abelian`.
11. Exactness means that the canonical inclusion of the image into the kernel is invertible.
Created kernels and cokernels identify its carrier with the ambient comparison. Step 2
reflects its invertibility, and additivity and faithfulness reflect the zero composite.
Apply this at each position of a sequence, including sequences with zero end terms. -/
theorem fixedPairCreatedAbelianStructure
    {A : Type u} [Category.{v} A] [Abelian A] [LocallySmall.{w} A]
    [HasLimitsOfSize.{w, w} A] [HasColimitsOfSize.{w, w} A]
    (T : A ⥤ A) [T.Additive] [T.IsEquivalence] :
    Nonempty (Abelian (IsoAlgebra T)) ∧
    (∀ (X Y : IsoAlgebra T) (f g : X ⟶ Y),
      (f + g).hom.f = f.hom.f + g.hom.f) ∧
    Nonempty (CreatesLimitsOfSize.{w, w} (forget T)) ∧
    Nonempty (CreatesColimitsOfSize.{w, w} (forget T)) ∧
    (∀ (J : Type w) [Category.{w} J] (D : J ⥤ IsoAlgebra T)
      (c : Cone (D ⋙ forget T)) (t : IsLimit c),
      ∃ (α : T.obj c.pt ≅ c.pt)
        (π : (Functor.const J).obj (mk c.pt α) ⟶ D),
        α = IsLimit.conePointsIsoOfNatIso (isLimitOfPreserves T t) t
          (Functor.isoWhiskerLeft D (strNatIso T)) ∧
        (∀ j : J, (π.app j).hom.f = c.π.app j) ∧
        Nonempty (IsLimit (Cone.mk (mk c.pt α) π))) ∧
    (∀ (J : Type w) [Category.{w} J] (D : J ⥤ IsoAlgebra T)
      (c : Cocone (D ⋙ forget T)) (t : IsColimit c),
      ∃ (α : T.obj c.pt ≅ c.pt)
        (ι : D ⟶ (Functor.const J).obj (mk c.pt α)),
        α = IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves T t) t
          (Functor.isoWhiskerLeft D (strNatIso T)) ∧
        (∀ j : J, (ι.app j).hom.f = c.ι.app j) ∧
        Nonempty (IsColimit (Cocone.mk (mk c.pt α) ι))) ∧
    PreservesFiniteLimits (forget T) ∧
    PreservesFiniteColimits (forget T) ∧
    PreservesFiniteBiproducts (forget T) ∧
    (∀ (X Y : IsoAlgebra T) (f : X ⟶ Y),
      (Mono f ↔ Mono ((forget T).map f)) ∧
      (Epi f ↔ Epi ((forget T).map f)) ∧
      (IsIso f ↔ IsIso ((forget T).map f))) ∧
    (∀ (X Y : IsoAlgebra T) (f : X ⟶ Y) [IsIso ((forget T).map f)],
      T.map (inv ((forget T).map f)) ≫ X.str.hom =
        Y.str.hom ≫ inv ((forget T).map f)) ∧
    (forget T).Additive ∧ (forget T).Faithful ∧ (forget T).ReflectsIsomorphisms ∧
    (∀ S : ShortComplex (IsoAlgebra T), (S.map (forget T)).Exact ↔ S.Exact) := by
  refine ⟨⟨inferInstance⟩, ?_, ?_, ?_, ?_, ?_, inferInstance, inferInstance,
    inferInstance, ?_, ?_, inferInstance, inferInstance, inferInstance, ?_⟩
  · intro X Y f g
    exact (forget T).map_add
  · exact ⟨{ CreatesLimitsOfShape := fun {J} _ ↦
      { CreatesLimit := fun {D} ↦ createsLimitOfReflectsIso (liftLimit T D) } }⟩
  · exact ⟨{ CreatesColimitsOfShape := fun {J} _ ↦
      { CreatesColimit := fun {D} ↦ createsColimitOfReflectsIso (liftColimit T D) } }⟩
  · intro J _ D c t
    exact ⟨_, (liftLimit T D c t).liftedCone.π, rfl, fun _ ↦ rfl,
      ⟨(liftLimit T D c t).makesLimit⟩⟩
  · intro J _ D c t
    exact ⟨_, (liftColimit T D c t).liftedCocone.ι, rfl, fun _ ↦ rfl,
      ⟨(liftColimit T D c t).makesColimit⟩⟩
  · intro X Y f
    exact ⟨⟨fun _ ↦ inferInstance, fun h ↦ (forget T).mono_of_mono_map h⟩,
      ⟨fun _ ↦ inferInstance, fun h ↦ (forget T).epi_of_epi_map h⟩,
      (isIso_iff_of_reflects_iso f (forget T)).symm⟩
  · intro X Y f _
    have : IsIso f.hom.f := ‹IsIso ((forget T).map f)›
    apply (cancel_mono ((forget T).map f)).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    change T.map (inv f.hom.f) ≫ X.obj.str ≫ f.hom.f = Y.obj.str
    rw [← f.hom.h, ← T.map_comp_assoc, IsIso.inv_hom_id, T.map_id, Category.id_comp]
  · intro S
    exact S.exact_map_iff_of_faithful (forget T)

end CategoryTheory.Endofunctor.IsoAlgebra
