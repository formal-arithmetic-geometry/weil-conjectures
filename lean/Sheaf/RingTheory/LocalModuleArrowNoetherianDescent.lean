/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Noetherian.Defs

import Sheaf.RingTheory.LocalTowerCollapseNoetherian
import Sheaf.RingTheory.FixedArrowScalarExtensionDiagram
import Mathlib.Order.Antisymmetrization
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Sheaf.Paper.LimitTowerEssentiallyFinitePresentation
import WeilConjectures.Algebra.FinitePresentationColimit
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final

/-!
# Simultaneous Noetherian local approximation of a module arrow

Source: Stacks Project, Algebra, Tag 046Y (first proof paragraph), with Tags 00QX,
00QV, 00R7 and 01ZR (blueprint: lem-trf-local-module-arrow-noetherian-descent).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

set_option autoImplicit false

namespace RingHom

private theorem finitePresentation_restrict_equiv
    {A C : Type u} [CommRing A] [CommRing C] (e : A ≃+* C)
    (P : ModuleCat.{u} C) [Module.FinitePresentation C P] :
    Module.FinitePresentation A ((ModuleCat.restrictScalars e.toRingHom).obj P) := by
  let : Algebra A C := e.toRingHom.toAlgebra
  let P' := (ModuleCat.restrictScalars e.toRingHom).obj P
  let : Module C P' := P.isModule
  have : Module.FinitePresentation C P' := inferInstanceAs (Module.FinitePresentation C P)
  have : IsScalarTower A C P' := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e' : A ≃ₗ[A] C :=
    { e with map_smul' := fun a b ↦ by change e (a * b) = e a * e b; exact e.map_mul a b }
  have : Module.FinitePresentation A C := Module.FinitePresentation.of_equiv e'
  exact Module.FinitePresentation.trans A P' C

private theorem exists_cocone_model
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (A : CommRingCat.{u})
    (κ : F ⟶ (Functor.const I).obj A) (hκ : IsColimit (Cocone.mk A κ))
    (P : ModuleCat.{u} A) [Module.FinitePresentation A P] :
    ∃ (i : I) (Q : ModuleCat.{u} (F.obj i)),
      Module.FinitePresentation (F.obj i) Q ∧
      Nonempty ((ModuleCat.extendScalars (κ.app i).hom).obj Q ≅ P) := by
  classical
  let e : colimit F ≅ A := (colimit.isColimit F).coconePointUniqueUpToIso hκ
  let P' := (ModuleCat.restrictScalars e.hom.hom).obj P
  have : Module.FinitePresentation (colimit F : CommRingCat) P' :=
    finitePresentation_restrict_equiv (e.commRingCatIsoToRingEquiv) P
  obtain ⟨i, Q, hQ, ⟨q⟩⟩ :=
    (ModuleCat.finitePresentation_descent_directedColimit.{u, u, u, u} F).1 P'
      inferInstance
  have he : e.hom.hom.comp (colimit.ι F i).hom = (κ.app i).hom := by
    apply congrArg CommRingCat.Hom.hom
    exact (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hκ i
  have : (ModuleCat.restrictScalars e.hom.hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e.commRingCatIsoToRingEquiv
  let ε := (ModuleCat.extendRestrictScalarsAdj e.hom.hom).counit.app P
  have : IsIso ε := inferInstance
  refine ⟨i, Q, hQ, ⟨?_⟩⟩
  exact (eqToIso (by rw [← he])).trans
    (((ModuleCat.extendScalarsComp (colimit.ι F i).hom e.hom.hom).app Q).trans
      (((ModuleCat.extendScalars e.hom.hom).mapIso q).trans (asIso ε)))

private noncomputable def coconeComparison
    {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u}) (A : CommRingCat.{u})
    (κ : F ⟶ (Functor.const I).obj A) (i j : I) (h : i ≤ j)
    (P : ModuleCat.{u} (F.obj i)) :
    (ModuleCat.extendScalars (κ.app i).hom).obj P ≅
      (ModuleCat.extendScalars (κ.app j).hom).obj
        ((ModuleCat.extendScalars (F.map (homOfLE h)).hom).obj P) := by
  have hc : (κ.app j).hom.comp (F.map (homOfLE h)).hom = (κ.app i).hom :=
    congrArg CommRingCat.Hom.hom (κ.naturality (homOfLE h))
  exact (eqToIso (by rw [← hc])).trans
    ((ModuleCat.extendScalarsComp (F.map (homOfLE h)).hom (κ.app j).hom).app P)

private noncomputable def changeLimit
    {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u}) (A : CommRingCat.{u})
    (κ : F ⟶ (Functor.const I).obj A) (hκ : IsColimit (Cocone.mk A κ)) (i : I) :
    ModuleCat.extendScalars (κ.app i).hom ≅
      ModuleCat.extendScalars (colimit.ι F i).hom ⋙
        ModuleCat.extendScalars ((colimit.isColimit F).coconePointUniqueUpToIso hκ).hom.hom := by
  have he := congrArg CommRingCat.Hom.hom
    ((colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hκ i)
  exact (eqToIso (by rw [← he]; rfl)).trans
    (ModuleCat.extendScalarsComp (colimit.ι F i).hom
      ((colimit.isColimit F).coconePointUniqueUpToIso hκ).hom.hom)

private theorem exists_cocone_map
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (A : CommRingCat.{u})
    (κ : F ⟶ (Functor.const I).obj A) (hκ : IsColimit (Cocone.mk A κ))
    (i : I) (P Q : ModuleCat.{u} (F.obj i))
    [Module.FinitePresentation (F.obj i) P] [Module.FinitePresentation (F.obj i) Q]
    (f : (ModuleCat.extendScalars (κ.app i).hom).obj P ⟶
      (ModuleCat.extendScalars (κ.app i).hom).obj Q) :
    ∃ (j : I) (hij : i ≤ j)
      (g : (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).obj P ⟶
        (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).obj Q)
      (eP : (ModuleCat.extendScalars (κ.app i).hom).obj P ≅
        (ModuleCat.extendScalars (κ.app j).hom).obj
          ((ModuleCat.extendScalars (F.map (homOfLE hij)).hom).obj P))
      (eQ : (ModuleCat.extendScalars (κ.app i).hom).obj Q ≅
        (ModuleCat.extendScalars (κ.app j).hom).obj
          ((ModuleCat.extendScalars (F.map (homOfLE hij)).hom).obj Q)),
      f ≫ eQ.hom = eP.hom ≫ (ModuleCat.extendScalars (κ.app j).hom).map g := by
  classical
  let e := (colimit.isColimit F).coconePointUniqueUpToIso hκ
  let H := ModuleCat.extendScalars e.hom.hom
  have : (ModuleCat.restrictScalars e.hom.hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e.commRingCatIsoToRingEquiv
  have : H.IsEquivalence :=
    (ModuleCat.extendRestrictScalarsAdj e.hom.hom).isEquivalence_left_of_isEquivalence_right
  let a := changeLimit F A κ hκ i
  let f₀ := H.preimage ((a.app P).inv ≫ f ≫ (a.app Q).hom)
  have hf₀ : f ≫ (a.app Q).hom = (a.app P).hom ≫ H.map f₀ := by
    simp [f₀]
  obtain ⟨j, hij, g, eP₀, eQ₀, _, _, hg⟩ :=
    (ModuleCat.finitePresentation_descent_directedColimit.{u, u, u, u} F).2.1
      i P Q inferInstance inferInstance f₀
  let b := changeLimit F A κ hκ j
  let Pj := (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).obj P
  let Qj := (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).obj Q
  refine ⟨j, hij, g, (a.app P).trans ((H.mapIso eP₀).trans (b.app Pj).symm),
    (a.app Q).trans ((H.mapIso eQ₀).trans (b.app Qj).symm), ?_⟩
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  calc
    f ≫ (a.app Q).hom ≫ H.map eQ₀.hom ≫ (b.app Qj).inv =
        (a.app P).hom ≫ H.map (f₀ ≫ eQ₀.hom) ≫ (b.app Qj).inv := by
      rw [← Category.assoc f, hf₀]
      simp only [Functor.map_comp, Category.assoc]
    _ = (a.app P).hom ≫ H.map (eP₀.hom ≫
        (ModuleCat.extendScalars (colimit.ι F j).hom).map g) ≫ (b.app Qj).inv := by rw [hg]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [show H.map ((ModuleCat.extendScalars (colimit.ι F j).hom).map g) ≫
        (b.app Qj).inv = (b.app Pj).inv ≫
          (ModuleCat.extendScalars (κ.app j).hom).map g from b.inv.naturality g]

private theorem finitePresentation_extend
    {A C : Type u} [CommRing A] [CommRing C] (r : A →+* C)
    (P : ModuleCat.{u} A) [Module.FinitePresentation A P] :
    Module.FinitePresentation C ((ModuleCat.extendScalars r).obj P) := by
  let := r.toAlgebra
  change Module.FinitePresentation C (C ⊗[A] P)
  infer_instance

private theorem exists_cocone_arrow
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (A : CommRingCat.{u})
    (κ : F ⟶ (Functor.const I).obj A) (hκ : IsColimit (Cocone.mk A κ))
    (M N : ModuleCat.{u} A)
    [Module.FinitePresentation A M] [Module.FinitePresentation A N] (f : M ⟶ N) :
    ∃ (c : I) (P Q : ModuleCat.{u} (F.obj c))
      (_ : Module.FinitePresentation (F.obj c) P)
      (_ : Module.FinitePresentation (F.obj c) Q) (g : P ⟶ Q)
      (eM : (ModuleCat.extendScalars (κ.app c).hom).obj P ≅ M)
      (eN : (ModuleCat.extendScalars (κ.app c).hom).obj Q ≅ N),
      (ModuleCat.extendScalars (κ.app c).hom).map g ≫ eN.hom = eM.hom ≫ f := by
  classical
  obtain ⟨i, P, hP, ⟨eP⟩⟩ := exists_cocone_model F A κ hκ M
  obtain ⟨j, Q, hQ, ⟨eQ⟩⟩ := exists_cocone_model F A κ hκ N
  let := hP
  let := hQ
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let Pk := (ModuleCat.extendScalars (F.map (homOfLE hik)).hom).obj P
  let Qk := (ModuleCat.extendScalars (F.map (homOfLE hjk)).hom).obj Q
  have : Module.FinitePresentation (F.obj k) Pk := finitePresentation_extend _ P
  have : Module.FinitePresentation (F.obj k) Qk := finitePresentation_extend _ Q
  let eM := (coconeComparison F A κ i k hik P).symm.trans eP
  let eN := (coconeComparison F A κ j k hjk Q).symm.trans eQ
  obtain ⟨c, hkc, g, eP', eQ', hg⟩ :=
    exists_cocone_map F A κ hκ k Pk Qk (eM.hom ≫ f ≫ eN.inv)
  let Pc := (ModuleCat.extendScalars (F.map (homOfLE hkc)).hom).obj Pk
  let Qc := (ModuleCat.extendScalars (F.map (homOfLE hkc)).hom).obj Qk
  refine ⟨c, Pc, Qc, finitePresentation_extend _ Pk, finitePresentation_extend _ Qk, g,
    eP'.symm.trans eM, eQ'.symm.trans eN, ?_⟩
  have hg' := congrArg (fun t ↦ eP'.inv ≫ t ≫ eQ'.inv ≫ eN.hom) hg
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hg'.symm

-- This criterion accepts a colimit of underlying types, for any filtered category.
-- In particular it does not require the index universe to fit in the group universe.
private noncomputable def additive_isColimit_of_types
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (D : J ⥤ AddCommGrpCat.{v}) (c : Cocone D)
    (hc : IsColimit ((forget AddCommGrpCat).mapCocone c)) : IsColimit c := by
  classical
  have rep (x : c.pt) : ∃ (i : J) (y : D.obj i), (c.ι.app i).hom y = x :=
    Types.jointly_surjective_of_isColimit hc x
  let value (s : Cocone D) := hc.desc ((forget AddCommGrpCat).mapCocone s)
  have value_rep (s : Cocone D) (i : J) (x : D.obj i) :
      value s ((c.ι.app i).hom x) = (s.ι.app i).hom x :=
    ConcreteCategory.congr_hom (hc.fac ((forget AddCommGrpCat).mapCocone s) i) x
  have compat (i j : J) (f : i ⟶ j) (x : D.obj i) :
      (c.ι.app j).hom ((D.map f).hom x) = (c.ι.app i).hom x :=
    ConcreteCategory.congr_hom (c.w f) x
  apply IsColimit.ofFaithful (forget AddCommGrpCat) hc
    (fun s ↦ AddCommGrpCat.ofHom
      { toFun := value s
        map_zero' := by
          obtain ⟨i⟩ := IsFiltered.nonempty (C := J)
          simpa only [map_zero] using value_rep s i 0
        map_add' := by
          intro x y
          obtain ⟨i, a, rfl⟩ := rep x
          obtain ⟨j, b, rfl⟩ := rep y
          obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
          rw [← compat i k f a, ← compat j k g b, ← map_add (c.ι.app k).hom, value_rep,
            map_add (s.ι.app k).hom, ← value_rep s k ((D.map f).hom a),
            ← value_rep s k ((D.map g).hom b)] })
  intro s
  rfl

set_option linter.unusedVariables false in
/--
Simultaneous Noetherian local approximation of a morphism of finitely presented modules.

Source: Stacks Project, Algebra, Tag 046Y (lemma-mod-injective-general), first proof
paragraph, using Tags 00QX, 00QV, 00R7, 00FN and Limits Tag 01ZR
(blueprint: lem-trf-local-module-arrow-noetherian-descent).

Proof:
1. Apply `lem-weil-pbc-limit-tower-essentially-finite-presentation` to `R → S → S`
   and `M`, using the identity as the second map. Write its stages `Rᵢ → Aᵢ → Sᵢ`.
   `lem-weil-pbc-essentially-finite-type-composition` makes `Sᵢ` essentially of finite
   type over `Rᵢ`. Starting with the Noetherian ring of integers, apply
   `lem-weil-pbc-finite-type-algebra-noetherian` and `lem-weil-pbc-localization-noetherian`
   to obtain Noetherianity of all stages. The chosen finite-type algebras are finitely
   presented by `lem-weil-pbc-finite-type-noetherian-finite-presentation`.
2. Apply `lem-weil-pbc-tensor-localization-tower-transition` to the two adjacent tower
   comparisons. This gives the displayed `Sᵢ ⊗ Rⱼ → Sⱼ` localization, and its application
   at the limit gives `Sᵢ ⊗ R → S`, with exactly the displayed pure-tensor formulas.
3. Apply the object clause of `lem-pc-fp-module-map-descent-affine` to descend `N` over
   the ring colimit. Move to a common stage with the model of `M`, tensor both finite
   cokernel presentations there, and apply the morphism clause to descend `u`. Thus
   at a stage `c` there are finitely presented modules `P,Q` and a map `v : P → Q`
   whose scalar extensions identify with `M,N,u`.
4. Restrict to the nonempty directed tail above `c`. Its inclusion is final, so
   `lem-weil-pbc-colimit-initial-full-subcategory` preserves both ring colimits. Set
   `Mⱼ = P ⊗ Sⱼ`, `Nⱼ = Q ⊗ Sⱼ`, and `uⱼ = v ⊗ 1`. The transitions send `x ⊗ a` to
   `x ⊗ sⱼₖ(a)` and the cocones send it to `a` times the fixed limit image of `x`.
   The tensor universal property (`def-weil-pbc-module-tensor-product`) gives these
   additive maps. Their formulas verify semilinearity, identity, composition,
   cocone compatibility, and both arrow squares.
5. Associativity identifies `(P ⊗ Sᵢ) ⊗ Sⱼ` with `P ⊗ Sⱼ` by the displayed canonical
   map, with inverse `x ⊗ b ↦ (x ⊗ 1) ⊗ b`; balancing proves both composites are
   identities. The same formulas apply to `Q` and at the limit. Applying them to
   `v(x)` proves compatibility with the arrow. Tensoring the finite cokernel
   presentations of `P,Q` gives finite presentation at every stage. We place the
   scalar ring first in the Lean tensor products, using `TensorProduct.comm`.
6. For compatible additive maps out of `P ⊗ Sⱼ`, define a map out of `P ⊗ S` by
   choosing a stage representative for each scalar. Eventual equality makes this
   well-defined; common upper bounds prove additivity and balancing. The tensor
   universal property gives existence and uniqueness, so these are the required
   additive-group colimits (`def-weil-pbc-category-colimit`). The usual quotient of
   stage elements by common-stage equality constructs directed ring and group
   colimits; hence all four colimits have the stated representation and equality
   criteria. Empty finite presentations and zero `v` include zero modules/maps.
   Universes may be enlarged in the construction. To retain an independently small
   module universe, replace each stage module by its small copy: each stage ring is
   countable (essential finite type over the integers), and each finite stage module
   is countable. Transport structures and maps along these equivalences.
-/
theorem exists_local_module_arrow_noetherian_descent
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    [IsLocalRing R] [IsLocalRing S]
    (α : R →+* S) [IsLocalHom α]
    [Algebra R B] [Algebra.FinitePresentation R B]
    (W : Submonoid B) (f : B →+* S)
    (hf : f.comp (algebraMap R B) = α)
    (hS : letI := f.toAlgebra; IsLocalization W S)
    {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N]
    (u : M →ₗ[S] N) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (Rdiag Sdiag : I ⥤ CommRingCat.{u})
      (ρ : Rdiag ⟶ Sdiag)
      (π : Rdiag ⟶ (Functor.const I).obj (CommRingCat.of R))
      (κ : Sdiag ⟶ (Functor.const I).obj (CommRingCat.of S))
      (Mdiag Ndiag : I ⥤ AddCommGrpCat.{v})
      (μ : Mdiag ⟶ (Functor.const I).obj (AddCommGrpCat.of M))
      (ν : Ndiag ⟶ (Functor.const I).obj (AddCommGrpCat.of N))
      (hModM : ∀ i : I, Module (Sdiag.obj i) (Mdiag.obj i))
      (hModN : ∀ i : I, Module (Sdiag.obj i) (Ndiag.obj i))
      (ui : ∀ i : I, Mdiag.obj i →ₗ[Sdiag.obj i] Ndiag.obj i),
      -- local rings, local homomorphisms, and commuting ring squares
      (∀ i, IsLocalRing (Rdiag.obj i)) ∧
      (∀ i, IsLocalRing (Sdiag.obj i)) ∧
      (∀ i, IsLocalHom (ρ.app i).hom) ∧
      (∀ (i j : I) (h : i ≤ j), IsLocalHom (Rdiag.map (homOfLE h)).hom) ∧
      (∀ (i j : I) (h : i ≤ j), IsLocalHom (Sdiag.map (homOfLE h)).hom) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i))) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i))) ∧
      (∀ i, ρ.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom α) ∧
      -- semilinear transition and cocone maps, including their arrow squares
      (∀ (i j : I) (h : i ≤ j) (s : Sdiag.obj i) (x : Mdiag.obj i),
        (Mdiag.map (homOfLE h)).hom (s • x) =
          (Sdiag.map (homOfLE h)).hom s • (Mdiag.map (homOfLE h)).hom x) ∧
      (∀ (i j : I) (h : i ≤ j) (s : Sdiag.obj i) (x : Ndiag.obj i),
        (Ndiag.map (homOfLE h)).hom (s • x) =
          (Sdiag.map (homOfLE h)).hom s • (Ndiag.map (homOfLE h)).hom x) ∧
      (∀ i (s : Sdiag.obj i) (x : Mdiag.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) (s • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) s •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) x) ∧
      (∀ i (s : Sdiag.obj i) (x : Ndiag.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) (s • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) s •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) x) ∧
      (∀ (i j : I) (h : i ≤ j) (x : Mdiag.obj i),
        (Ndiag.map (homOfLE h)).hom (ui i x) =
          ui j ((Mdiag.map (homOfLE h)).hom x)) ∧
      (∀ i (x : Mdiag.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) (ui i x) =
          u ((@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) x)) ∧
      -- (1) Noetherianity and essential finite type
      (∀ i, IsNoetherianRing (Rdiag.obj i)) ∧
      (∀ i, IsNoetherianRing (Sdiag.obj i)) ∧
      (∀ i, (algebraMap ℤ (Rdiag.obj i)).EssFiniteType) ∧
      (∀ i, (ρ.app i).hom.EssFiniteType) ∧
      (∀ i, Module.FinitePresentation (Sdiag.obj i) (Mdiag.obj i)) ∧
      (∀ i, Module.FinitePresentation (Sdiag.obj i) (Ndiag.obj i)) ∧
      -- (2) ring and additive-group filtered colimits
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) μ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of N) ν)) ∧
      (∀ x : R, ∃ i r, (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)) r = x) ∧
      (∀ x : S, ∃ i s, (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) s = x) ∧
      (∀ i j (x : Rdiag.obj i) (y : Rdiag.obj j),
        (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)) x =
            (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app j)) y ↔
          ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
            (Rdiag.map (homOfLE hik)).hom x = (Rdiag.map (homOfLE hjk)).hom y) ∧
      (∀ i j (x : Sdiag.obj i) (y : Sdiag.obj j),
        (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) x =
            (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app j)) y ↔
          ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
            (Sdiag.map (homOfLE hik)).hom x = (Sdiag.map (homOfLE hjk)).hom y) ∧
      (∀ x : M, ∃ i m, (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) m = x) ∧
      (∀ x : N, ∃ i n, (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) n = x) ∧
      (∀ i j (x : Mdiag.obj i) (y : Mdiag.obj j),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) x =
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app j)) y ↔
          ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
            (Mdiag.map (homOfLE hik)).hom x = (Mdiag.map (homOfLE hjk)).hom y) ∧
      (∀ i j (x : Ndiag.obj i) (y : Ndiag.obj j),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) x =
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app j)) y ↔
          ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
            (Ndiag.map (homOfLE hik)).hom x = (Ndiag.map (homOfLE hjk)).hom y) ∧
      -- (3) transition localizations and module base changes
      (∀ (i j : I) (h : i ≤ j),
        letI := (ρ.app i).hom.toAlgebra
        letI := (Rdiag.map (homOfLE h)).hom.toAlgebra
        ∃ φ : Sdiag.obj i ⊗[Rdiag.obj i] Rdiag.obj j →+* Sdiag.obj j,
          (∀ (s : Sdiag.obj i) (r : Rdiag.obj j),
            φ (s ⊗ₜ[Rdiag.obj i] r) =
              (Sdiag.map (homOfLE h)).hom s * (ρ.app j).hom r) ∧
          (letI := φ.toAlgebra
           ∃ V : Submonoid (Sdiag.obj i ⊗[Rdiag.obj i] Rdiag.obj j),
             IsLocalization V (Sdiag.obj j))) ∧
      (∀ (i j : I) (h : i ≤ j),
        letI := (Sdiag.map (homOfLE h)).hom.toAlgebra
        ∃ (eM : Sdiag.obj j ⊗[Sdiag.obj i] Mdiag.obj i ≃ₗ[Sdiag.obj j] Mdiag.obj j)
          (eN : Sdiag.obj j ⊗[Sdiag.obj i] Ndiag.obj i ≃ₗ[Sdiag.obj j] Ndiag.obj j),
          (∀ (s : Sdiag.obj j) (x : Mdiag.obj i),
            eM (s ⊗ₜ[Sdiag.obj i] x) = s • (Mdiag.map (homOfLE h)).hom x) ∧
          (∀ (s : Sdiag.obj j) (y : Ndiag.obj i),
            eN (s ⊗ₜ[Sdiag.obj i] y) = s • (Ndiag.map (homOfLE h)).hom y) ∧
          (∀ (s : Sdiag.obj j) (x : Mdiag.obj i),
            eN (s ⊗ₜ[Sdiag.obj i] ui i x) = ui j (eM (s ⊗ₜ[Sdiag.obj i] x)))) ∧
      -- (4) localizations and module base changes at the limit
      (∀ i,
        letI := (ρ.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)).toAlgebra
        ∃ φ : Sdiag.obj i ⊗[Rdiag.obj i] R →+* S,
          (∀ (s : Sdiag.obj i) (r : R),
            φ (s ⊗ₜ[Rdiag.obj i] r) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) s * α r) ∧
          (letI := φ.toAlgebra
           ∃ V : Submonoid (Sdiag.obj i ⊗[Rdiag.obj i] R), IsLocalization V S)) ∧
      (∀ i,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)).toAlgebra
        ∃ (eM : S ⊗[Sdiag.obj i] Mdiag.obj i ≃ₗ[S] M)
          (eN : S ⊗[Sdiag.obj i] Ndiag.obj i ≃ₗ[S] N),
          (∀ (s : S) (x : Mdiag.obj i),
            eM (s ⊗ₜ[Sdiag.obj i] x) =
              s • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) x) ∧
          (∀ (s : S) (y : Ndiag.obj i),
            eN (s ⊗ₜ[Sdiag.obj i] y) =
              s • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) y) ∧
          (∀ (s : S) (x : Mdiag.obj i),
            eN (s ⊗ₜ[Sdiag.obj i] ui i x) = u (eM (s ⊗ₜ[Sdiag.obj i] x)))) := by
  classical
  obtain ⟨t, s, p, H, hp, hHp⟩ := Module.FinitePresentation.exists_fin' S M
  have hM : Nonempty (((Fin t → S) ⧸ LinearMap.range H) ≃ₗ[S] M) :=
    ⟨(Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hHp).symm).trans
      (LinearMap.quotKerEquivOfSurjective p hp)⟩
  obtain ⟨I, po, ne, di, A, Bs, C, ρ, σ, π, κ, κ', D, δ, hMod, htower⟩ :=
    WeilConjectures.limit_tower_essentially_finite_presentation α (RingHom.id S)
      B W f hf hS B W f hf hS M s t H hM
  let := po
  let := ne
  let := di
  let := hMod
  rcases htower with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, h25, h26, h27, h28, h29, h30⟩
  let := h1
  let := h2
  let := h3
  have hABtr : ∀ i j h, IsTensorLocalizationSquare (ρ.app i).hom
      (A.map (homOfLE h)).hom (Bs.map (homOfLE h)).hom (ρ.app j).hom := by
    intro i j h
    obtain ⟨φ, hφ, V, hV⟩ := h25 i j h
    exact ⟨φ, hφ, V, (letI := φ.toAlgebra; (isLocalization_iff_isLocalizationMap V _).mp hV)⟩
  have hBCtr : ∀ i j h, IsTensorLocalizationSquare (σ.app i).hom
      (Bs.map (homOfLE h)).hom (C.map (homOfLE h)).hom (σ.app j).hom := by
    intro i j h
    obtain ⟨φ, hφ, V, hV⟩ := h26 i j h
    exact ⟨φ, hφ, V, (letI := φ.toAlgebra; (isLocalization_iff_isLocalizationMap V _).mp hV)⟩
  have hABlim : ∀ i, IsTensorLocalizationSquare (ρ.app i).hom
      (π.app i).hom (κ.app i).hom α := by
    intro i
    obtain ⟨φ, hφ, V, hV⟩ := h28 i
    exact ⟨φ, hφ, V, (letI := φ.toAlgebra; (isLocalization_iff_isLocalizationMap V _).mp hV)⟩
  have hBClim : ∀ i, IsTensorLocalizationSquare (σ.app i).hom
      (κ.app i).hom (κ'.app i).hom (RingHom.id S) := by
    intro i
    obtain ⟨φ, hφ, V, hV⟩ := h29 i
    exact ⟨φ, hφ, V, (letI := φ.toAlgebra; (isLocalization_iff_isLocalizationMap V _).mp hV)⟩
  obtain ⟨hnoeth, hft, _, htr, hlim, _, _, _, _⟩ :=
    Module.local_tower_collapse_noetherian I A Bs C ρ σ
      (Cocone.mk (CommRingCat.of R) π) (Cocone.mk (CommRingCat.of S) κ)
      (Cocone.mk (CommRingCat.of S) κ') (CommRingCat.ofHom α) (𝟙 _)
      h4 h5 inferInstance (by change IsLocalHom (RingHom.id S); infer_instance)
      h6 h7 h8 h9 h10 h11 h12 h13
      h16.some h17.some h18.some (fun i ↦ RingHom.essFiniteType_algebraMap.mp (h20 i))
      h21 h22 hABtr hBCtr hABlim hBClim
  let K := Antisymmetrization I (· ≤ ·)
  let qI : I → K := toAntisymmetrization (· ≤ ·)
  let E : K ⥤ I := (OrderEmbedding.ofAntisymmetrization (α := I)).monotone.functor
  have hrep (i : I) : i ≤ E.obj (qI i) := by
    apply toAntisymmetrization_le_toAntisymmetrization_iff.mp
    change toAntisymmetrization (· ≤ ·) i ≤
      toAntisymmetrization (· ≤ ·) (ofAntisymmetrization (· ≤ ·) (qI i))
    rw [toAntisymmetrization_ofAntisymmetrization]
  have : Nonempty K := ⟨qI (Classical.arbitrary I)⟩
  have : IsDirected K (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, hak, hbk⟩ := exists_ge_ge (E.obj a) (E.obj b)
    refine ⟨qI k, ?_, ?_⟩
    · change ofAntisymmetrization (· ≤ ·) a ≤ k at hak
      simpa only [toAntisymmetrization_ofAntisymmetrization] using
        toAntisymmetrization_mono hak
    · change ofAntisymmetrization (· ≤ ·) b ≤ k at hbk
      simpa only [toAntisymmetrization_ofAntisymmetrization] using
        toAntisymmetrization_mono hbk⟩
  have : E.Final := (OrderEmbedding.ofAntisymmetrization (α := I)).monotone.final_functor_iff.mpr
    (fun i ↦ ⟨qI i, hrep i⟩)
  let C' := E ⋙ C
  let κC : C' ⟶ (Functor.const K).obj (CommRingCat.of S) :=
    (Cocone.mk (CommRingCat.of S) κ').whisker E |>.ι
  have hκC : IsColimit (Cocone.mk (CommRingCat.of S) κC) :=
    (Functor.Final.isColimitWhiskerEquiv E _).symm h18.some
  let M' := ModuleCat.of S (Module.Finite.repr S M)
  let N' := ModuleCat.of S (Module.Finite.repr S N)
  let eM' : M' ≃ₗ[S] M := Module.Finite.reprEquiv S M
  let eN' : N' ≃ₗ[S] N := Module.Finite.reprEquiv S N
  have : Module.FinitePresentation S M' := Module.FinitePresentation.of_equiv eM'.symm
  have : Module.FinitePresentation S N' := Module.FinitePresentation.of_equiv eN'.symm
  let u' : M' ⟶ N' := ModuleCat.ofHom
    (eN'.symm.toLinearMap.comp (u.comp eM'.toLinearMap))
  obtain ⟨c, P, Q, hP, hQ, g, eP, eQ, hg⟩ :=
    exists_cocone_arrow C' (CommRingCat.of S) κC hκC M' N' u'
  let := hP
  let := hQ
  let eM : Module.fixedArrowLimit C' (CommRingCat.of S) κC c P ≃ₗ[S] M :=
    { eP.toLinearEquiv.toAddEquiv.trans eM'.toAddEquiv with
      map_smul' := fun s x ↦ by
        change eM' (eP.hom (s • x)) = s • eM' (eP.hom x)
        rw [map_smul, eM'.map_smul] }
  let eN : Module.fixedArrowLimit C' (CommRingCat.of S) κC c Q ≃ₗ[S] N :=
    { eQ.toLinearEquiv.toAddEquiv.trans eN'.toAddEquiv with
      map_smul' := fun s x ↦ by
        change eN' (eQ.hom (s • x)) = s • eN' (eQ.hom x)
        rw [map_smul, eN'.map_smul] }
  have hge (x : Module.fixedArrowLimit C' (CommRingCat.of S) κC c P) :
      eN (Module.fixedArrowLimitArrow C' (CommRingCat.of S) κC c g x) = u (eM x) := by
    have hx := ConcreteCategory.congr_hom hg x
    exact (congrArg eN' hx).trans (by simp [u', eM, eM', eN'])
  obtain ⟨pm, pn, μ₀, ν₀, _, _, pmid, pmcomp, μcomp, pmfp, _, _, pnid,
    pncomp, νcomp, pnfp, gsquare, glimit, hbase, hlimit, _, hmrep, hmeq,
    _, hnrep, hneq, hJne, hJdir⟩ :=
    Module.fixedArrow_scalarExtension_diagram C' (CommRingCat.of S) κC ⟨hκC⟩ c P Q g
  let J := Set.Ici c
  let := hJne
  let := hJdir
  let L : J ⥤ I :=
    (show Monotone (fun j : J ↦ j.1) from fun _ _ h ↦ h).functor ⋙ E
  let (j : J) : Small.{v} (C'.obj j.1) := by
    let : Algebra (A.obj (L.obj j)) (C'.obj j.1) :=
      ((σ.app (L.obj j)).hom.comp (ρ.app (L.obj j)).hom).toAlgebra
    have : Algebra.EssFiniteType (A.obj (L.obj j)) (C'.obj j.1) := hft (L.obj j)
    have : Algebra.EssFiniteType ℤ (A.obj (L.obj j)) :=
      RingHom.essFiniteType_algebraMap.mp (h20 (L.obj j))
    have : Algebra.EssFiniteType ℤ (C'.obj j.1) :=
      Algebra.EssFiniteType.comp ℤ (A.obj (L.obj j)) (C'.obj j.1)
    let S₀ := Algebra.EssFiniteType.subalgebra ℤ (C'.obj j.1)
    let W := Algebra.EssFiniteType.submonoid ℤ (C'.obj j.1)
    have : Small.{v} S₀ := Algebra.FiniteType.small.{v} (R := ℤ)
    exact small_of_surjective (IsLocalization.mk'_surjective W (S := C'.obj j.1))
  let (j : J) : Module.FinitePresentation (C'.obj j.1)
      (Module.fixedArrowStage C' c P j) := pmfp j
  let (j : J) : Module.FinitePresentation (C'.obj j.1)
      (Module.fixedArrowStage C' c Q j) := pnfp j
  let (j : J) : Small.{v} (Module.fixedArrowStage C' c P j) :=
    Module.Finite.small (C'.obj j.1) (Module.fixedArrowStage C' c P j)
  let (j : J) : Small.{v} (Module.fixedArrowStage C' c Q j) :=
    Module.Finite.small (C'.obj j.1) (Module.fixedArrowStage C' c Q j)
  let em (j : J) := Shrink.linearEquiv.{v} (C'.obj j.1) (Module.fixedArrowStage C' c P j)
  let en (j : J) := Shrink.linearEquiv.{v} (C'.obj j.1) (Module.fixedArrowStage C' c Q j)
  let MD : J ⥤ AddCommGrpCat.{v} :=
    { obj := fun j ↦ AddCommGrpCat.of (Shrink.{v} (Module.fixedArrowStage C' c P j))
      map := fun {i j} h ↦ AddCommGrpCat.ofHom
        ((em j).symm.toAddMonoidHom.comp
          ((pm i j (leOfHom h)).toAddMonoidHom.comp (em i).toAddMonoidHom))
      map_id := by intro i; ext x; simp [pmid]
      map_comp := by intro i j k h l; ext x; simp [pmcomp] }
  let ND : J ⥤ AddCommGrpCat.{v} :=
    { obj := fun j ↦ AddCommGrpCat.of (Shrink.{v} (Module.fixedArrowStage C' c Q j))
      map := fun {i j} h ↦ AddCommGrpCat.ofHom
        ((en j).symm.toAddMonoidHom.comp
          ((pn i j (leOfHom h)).toAddMonoidHom.comp (en i).toAddMonoidHom))
      map_id := by intro i; ext x; simp [pnid]
      map_comp := by intro i j k h l; ext x; simp [pncomp] }
  let μ : MD ⟶ (Functor.const J).obj (AddCommGrpCat.of M) :=
    { app := fun j ↦ AddCommGrpCat.ofHom
        (eM.toAddMonoidHom.comp ((μ₀ j).toAddMonoidHom.comp (em j).toAddMonoidHom))
      naturality := by intro i j h; ext x; simp [MD, μcomp] }
  let ν : ND ⟶ (Functor.const J).obj (AddCommGrpCat.of N) :=
    { app := fun j ↦ AddCommGrpCat.ofHom
        (eN.toAddMonoidHom.comp ((ν₀ j).toAddMonoidHom.comp (en j).toAddMonoidHom))
      naturality := by intro i j h; ext x; simp [ND, νcomp] }
  let ui (j : J) : MD.obj j →ₗ[C'.obj j.1] ND.obj j :=
    (en j).symm.toLinearMap.comp ((Module.fixedArrowStageArrow C' c g j).hom.comp
      (em j).toLinearMap)
  have : L.Final := by
    have htail : (show Monotone (fun j : J ↦ j.1) from fun _ _ h ↦ h).functor.Final := by
      apply Functor.final_of_exists_of_isFiltered
      · intro i
        obtain ⟨j, hij, hcj⟩ := exists_ge_ge i c
        exact ⟨⟨j, hcj⟩, ⟨homOfLE hij⟩⟩
      · intro i j a b
        exact ⟨j, 𝟙 j, Subsingleton.elim _ _⟩
    exact inferInstanceAs
      (((show Monotone (fun j : J ↦ j.1) from fun _ _ h ↦ h).functor ⋙ E).Final)
  let RA := L ⋙ A
  let SC := L ⋙ C
  let ρ' : RA ⟶ SC := Functor.whiskerLeft L (ρ ≫ σ)
  let π' : RA ⟶ (Functor.const J).obj (CommRingCat.of R) :=
    (Cocone.mk (CommRingCat.of R) π).whisker L |>.ι
  let κ'' : SC ⟶ (Functor.const J).obj (CommRingCat.of S) :=
    (Cocone.mk (CommRingCat.of S) κ').whisker L |>.ι
  have hRcol : Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π')) :=
    ⟨(Functor.Final.isColimitWhiskerEquiv L _).symm h16.some⟩
  have hScol : Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ'')) :=
    ⟨(Functor.Final.isColimitWhiskerEquiv L _).symm h18.some⟩
  have hMrep : ∀ x : M, ∃ i y, (μ.app i).hom y = x := by
    intro x
    obtain ⟨j, z, hz⟩ := hmrep (eM.symm x)
    exact ⟨j, (em j).symm z, by
      change eM (μ₀ j (em j ((em j).symm z))) = x
      rw [LinearEquiv.apply_symm_apply, hz, LinearEquiv.apply_symm_apply]⟩
  have hNrep : ∀ x : N, ∃ i y, (ν.app i).hom y = x := by
    intro x
    obtain ⟨j, z, hz⟩ := hnrep (eN.symm x)
    exact ⟨j, (en j).symm z, by
      change eN (ν₀ j (en j ((en j).symm z))) = x
      rw [LinearEquiv.apply_symm_apply, hz, LinearEquiv.apply_symm_apply]⟩
  have hMeq : ∀ i j (x : MD.obj i) (y : MD.obj j),
      (μ.app i).hom x = (μ.app j).hom y ↔
        ∃ (k : J) (hik : i ≤ k) (hjk : j ≤ k),
          (MD.map (homOfLE hik)).hom x = (MD.map (homOfLE hjk)).hom y := by
    intro i j x y
    change eM (μ₀ i (em i x)) = eM (μ₀ j (em j y)) ↔ _
    constructor
    · intro hx
      obtain ⟨k, hik, hjk, hk⟩ := (hmeq i j (em i x) (em j y)).mp (eM.injective hx)
      exact ⟨k, hik, hjk, congrArg (em k).symm hk⟩
    · rintro ⟨k, hik, hjk, hk⟩
      apply eM.injective.eq_iff.mpr
      apply (hmeq i j (em i x) (em j y)).mpr
      exact ⟨k, hik, hjk, by simpa [MD] using congrArg (em k) hk⟩
  have hNeq : ∀ i j (x : ND.obj i) (y : ND.obj j),
      (ν.app i).hom x = (ν.app j).hom y ↔
        ∃ (k : J) (hik : i ≤ k) (hjk : j ≤ k),
          (ND.map (homOfLE hik)).hom x = (ND.map (homOfLE hjk)).hom y := by
    intro i j x y
    change eN (ν₀ i (en i x)) = eN (ν₀ j (en j y)) ↔ _
    constructor
    · intro hx
      obtain ⟨k, hik, hjk, hk⟩ := (hneq i j (en i x) (en j y)).mp (eN.injective hx)
      exact ⟨k, hik, hjk, congrArg (en k).symm hk⟩
    · rintro ⟨k, hik, hjk, hk⟩
      apply eN.injective.eq_iff.mpr
      apply (hneq i j (en i x) (en j y)).mpr
      exact ⟨k, hik, hjk, by simpa [ND] using congrArg (en k) hk⟩
  have hMcol : Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) μ)) := by
    refine ⟨additive_isColimit_of_types MD _
      (Types.FilteredColimit.isColimitOf _ _ ?_ ?_)⟩
    · intro x
      obtain ⟨i, y, hy⟩ := hMrep x
      exact ⟨i, y, hy.symm⟩
    · intro i j x y hxy
      obtain ⟨k, hik, hjk, hk⟩ := (hMeq i j x y).mp hxy
      exact ⟨k, homOfLE hik, homOfLE hjk, hk⟩
  have hNcol : Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of N) ν)) := by
    refine ⟨additive_isColimit_of_types ND _
      (Types.FilteredColimit.isColimitOf _ _ ?_ ?_)⟩
    · intro x
      obtain ⟨i, y, hy⟩ := hNrep x
      exact ⟨i, y, hy.symm⟩
    · intro i j x y hxy
      obtain ⟨k, hik, hjk, hk⟩ := (hNeq i j x y).mp hxy
      exact ⟨k, homOfLE hik, homOfLE hjk, hk⟩
  refine ⟨J, inferInstance, inferInstance, inferInstance, RA, SC, ρ', π', κ'', MD, ND,
    μ, ν, (fun j ↦ inferInstance), (fun j ↦ inferInstance), ui,
    (fun j ↦ h1 (L.obj j)), (fun j ↦ h3 (L.obj j)), ?_,
    (fun i j h ↦ h6 _ _ (leOfHom (L.map (homOfLE h)))),
    (fun i j h ↦ h8 _ _ (leOfHom (L.map (homOfLE h)))),
    (fun j ↦ h9 (L.obj j)), (fun j ↦ h11 (L.obj j)), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (fun j ↦ (hnoeth (L.obj j)).1), (fun j ↦ (hnoeth (L.obj j)).2.2),
    (fun j ↦ h20 (L.obj j)), (fun j ↦ hft (L.obj j)), ?_, ?_,
    hRcol, hScol, hMcol, hNcol, ?_, ?_, ?_, ?_, hMrep, hNrep, hMeq, hNeq,
    ?_, ?_, ?_, ?_⟩
  · intro j
    let := h4 (L.obj j)
    let := h5 (L.obj j)
    exact RingHom.isLocalHom_comp _ _
  · intro j
    change ρ.app (L.obj j) ≫ σ.app (L.obj j) ≫ κ'.app (L.obj j) = _
    rw [h13]
    simpa [π'] using h12 (L.obj j)
  · intro i j h a x
    change (em j).symm (pm i j h (em i (a • x))) = _
    rw [(em i).map_smul, (pm i j h).map_smulₛₗ, (em j).symm.map_smul]
    rfl
  · intro i j h a x
    change (en j).symm (pn i j h (en i (a • x))) = _
    rw [(en i).map_smul, (pn i j h).map_smulₛₗ, (en j).symm.map_smul]
    rfl
  · intro j a x
    change eM (μ₀ j (em j (a • x))) = _
    rw [(em j).map_smul, (μ₀ j).map_smulₛₗ, eM.map_smul]
    rfl
  · intro j a x
    change eN (ν₀ j (en j (a • x))) = _
    rw [(en j).map_smul, (ν₀ j).map_smulₛₗ, eN.map_smul]
    rfl
  · intro i j h x
    apply (en j).injective
    simpa [ND, MD, ui] using gsquare i j h (em i x)
  · intro j x
    change eN (ν₀ j (en j ((en j).symm
      ((Module.fixedArrowStageArrow C' c g j).hom (em j x))))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg eN (glimit j (em j x))).trans (hge _)
  · intro j
    let : Module.FinitePresentation (C'.obj j.1)
        (Module.fixedArrowStage C' c P j) := pmfp j
    change Module.FinitePresentation (C'.obj j.1)
      (Shrink.{v} (Module.fixedArrowStage C' c P j))
    exact Module.FinitePresentation.of_equiv (em j).symm
  · intro j
    let : Module.FinitePresentation (C'.obj j.1)
        (Module.fixedArrowStage C' c Q j) := pnfp j
    change Module.FinitePresentation (C'.obj j.1)
      (Shrink.{v} (Module.fixedArrowStage C' c Q j))
    exact Module.FinitePresentation.of_equiv (en j).symm
  · intro x
    exact Concrete.isColimit_exists_rep RA hRcol.some x
  · intro x
    exact Concrete.isColimit_exists_rep SC hScol.some x
  · intro i j x y
    change ((Cocone.mk (CommRingCat.of R) π').ι.app i) x =
      ((Cocone.mk (CommRingCat.of R) π').ι.app j) y ↔ _
    rw [Concrete.isColimit_rep_eq_iff_exists RA hRcol.some x y]
    exact ⟨fun ⟨k, f, g, h⟩ ↦ ⟨k, leOfHom f, leOfHom g, h⟩,
      fun ⟨k, hf, hg, h⟩ ↦ ⟨k, homOfLE hf, homOfLE hg, h⟩⟩
  · intro i j x y
    change ((Cocone.mk (CommRingCat.of S) κ'').ι.app i) x =
      ((Cocone.mk (CommRingCat.of S) κ'').ι.app j) y ↔ _
    rw [Concrete.isColimit_rep_eq_iff_exists SC hScol.some x y]
    exact ⟨fun ⟨k, f, g, h⟩ ↦ ⟨k, leOfHom f, leOfHom g, h⟩,
      fun ⟨k, hf, hg, h⟩ ↦ ⟨k, homOfLE hf, homOfLE hg, h⟩⟩
  · intro i j h
    obtain ⟨φ, hφ, V, hV⟩ := htr (L.obj i) (L.obj j) (leOfHom (L.map (homOfLE h)))
    refine ⟨φ, hφ, ?_⟩
    let := (ρ.app (L.obj i)).hom.toAlgebra
    let := (A.map (homOfLE (leOfHom (L.map (homOfLE h))))).hom.toAlgebra
    let := φ.toAlgebra
    exact ⟨V, (isLocalization_iff_isLocalizationMap V (C.obj (L.obj j))).mpr hV⟩
  · intro i j h
    let : Algebra (C'.obj i.1) (C'.obj j.1) :=
      (C'.map (homOfLE h)).hom.toAlgebra
    obtain ⟨a, b, ha, hb, hab⟩ := hbase i j h
    let a' := ((em i).baseChange (C'.obj i.1) (C'.obj j.1)).trans
      (a.toLinearEquiv.trans (em j).symm)
    let b' := ((en i).baseChange (C'.obj i.1) (C'.obj j.1)).trans
      (b.toLinearEquiv.trans (en j).symm)
    refine ⟨a', b', ?_, ?_, ?_⟩
    · intro s x
      change (em j).symm (a.hom
        ((show C'.obj j.1 from s) ⊗ₜ[C'.obj i.1] (em i x))) = _
      rw [ha, (em j).symm.map_smul]
      rfl
    · intro s x
      change (en j).symm (b.hom
        ((show C'.obj j.1 from s) ⊗ₜ[C'.obj i.1] (en i x))) = _
      rw [hb, (en j).symm.map_smul]
      rfl
    · intro s x
      change (en j).symm (b.hom
        ((show C'.obj j.1 from s) ⊗ₜ[C'.obj i.1] (en i (ui i x)))) = _
      rw [hb, (en j).symm.map_smul]
      change s • (en j).symm (pn i j h ((en i) (ui i x))) =
        ui j (a' (s ⊗ₜ[C'.obj i.1] x))
      change s • (en j).symm (pn i j h
        ((en i) ((en i).symm ((Module.fixedArrowStageArrow C' c g i).hom (em i x))))) = _
      rw [LinearEquiv.apply_symm_apply, gsquare]
      change s • (en j).symm ((Module.fixedArrowStageArrow C' c g j).hom
        (pm i j h (em i x))) = _
      change s • (en j).symm ((Module.fixedArrowStageArrow C' c g j).hom
        (pm i j h (em i x))) =
        ui j ((em j).symm (a.hom
          ((show C'.obj j.1 from s) ⊗ₜ[C'.obj i.1] (em i x))))
      rw [ha, (em j).symm.map_smul, (ui j).map_smul]
      change s • (en j).symm ((Module.fixedArrowStageArrow C' c g j).hom
        (pm i j h (em i x))) =
        s • (en j).symm ((Module.fixedArrowStageArrow C' c g j).hom
          (em j ((em j).symm (pm i j h (em i x)))))
      rw [LinearEquiv.apply_symm_apply]
  · intro i
    obtain ⟨φ, hφ, V, hV⟩ := hlim (L.obj i)
    refine ⟨φ, hφ, ?_⟩
    let := ((σ.app (L.obj i)).hom.comp (ρ.app (L.obj i)).hom).toAlgebra
    let := (π.app (L.obj i)).hom.toAlgebra
    let := φ.toAlgebra
    exact ⟨V, (isLocalization_iff_isLocalizationMap V
      (((Functor.const I).obj (CommRingCat.of S)).obj (L.obj i))).mpr hV⟩
  · intro i
    let : Algebra (C'.obj i.1) S := (κC.app i.1).hom.toAlgebra
    obtain ⟨a, b, ha, hb, hab⟩ := hlimit i
    dsimp only [Functor.const_obj_obj] at a b ha hb hab
    let a' := ((em i).baseChange (C'.obj i.1) S).trans
      (a.toLinearEquiv.trans eM)
    let b' := ((en i).baseChange (C'.obj i.1) S).trans
      (b.toLinearEquiv.trans eN)
    refine ⟨a', b', ?_, ?_, ?_⟩
    · intro s x
      change eM (a.hom (s ⊗ₜ[C'.obj i.1] (em i x))) = _
      rw [ha, eM.map_smul]
      rfl
    · intro s x
      change eN (b.hom (s ⊗ₜ[C'.obj i.1] (en i x))) = _
      rw [hb, eN.map_smul]
      rfl
    · intro s x
      change eN (b.hom (s ⊗ₜ[C'.obj i.1] (en i (ui i x)))) = _
      rw [hb, eN.map_smul]
      change s • eN (ν₀ i ((en i) ((en i).symm
        ((Module.fixedArrowStageArrow C' c g i).hom (em i x))))) = _
      rw [LinearEquiv.apply_symm_apply, glimit, hge]
      change s • u (eM (μ₀ i (em i x))) =
        u (eM (a.hom (s ⊗ₜ[C'.obj i.1] (em i x))))
      rw [ha, eM.map_smul, u.map_smul]

end RingHom
