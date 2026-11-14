/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Limits

import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Finite disjoint unions in the pro-etale site

Source: Stacks Project, Tags 0F4P and 0DB1
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Finite qcqs families admit a qcqs disjoint union in the pro-etale site, affine if
all summands are affine. Its representable sheaf is the coproduct of the representable
summands, and restriction gives a bijection on sections natural in the sheaf.
Here `uliftYoneda` places representables in the same universe as the sheaves of sets.
The colimit witness asserts existence in sheaves; `hc.desc` is the canonical comparison
from any chosen coproduct. Empty families give the empty scheme and singleton sections.

Source: Stacks Project, Tag 0F4P, proof of `lemma-weakly-contractible-cover`, and
Tag 0DB1, `remark-take-unions-hypercovering-X`, hypotheses (a)-(c)
(auxiliary; not a blueprint node).

Proof:
1. Construct the scheme coproduct and its clopen coprojections using
   lem-weil-pbc-scheme-coproduct-family. Apply lem-weil-pbc-finite-coproduct-lfp-qcqs
   for qcqs and lem-weil-pbc-finite-affine-coproduct-spectrum for affineness.
   The empty coproduct is the spectrum of the zero ring, hence empty.
2. The structural morphism is weakly etale: flatness and flatness of its diagonal
   are checked on each open summand using definition-ind-etale-pro-etale-weakly--3 and
   def-weil-flat-morphism. Finite unions respect prose-01-10.
3. The summand inclusions cover in definition-small-pro-etale-site--1. For an affine open
   of the union, its intersections with summands are clopen and quasi-compact;
   finite affine covers of these intersections verify the covering criterion.
   The empty family covers the empty scheme, so its sections form a singleton.
   Apply the sheaf equalizer axiom of def-weil-pbc-sites-and-cohomology: distinct
   summands have empty overlaps, and self-overlaps give identity restrictions.
   Every tuple therefore glues uniquely. Naturality of a sheaf morphism on each
   coprojection proves naturality of this bijection.
4. By lem-weil-pbc-proetale-subcanonical the representables are sheaves.
   Use lem-galois-yoneda-hom-bijection to identify maps out of each representable
   with sections. Step 3 gives exactly the coproduct universal property of
   def-weil-pbc-category-colimit. The universal maps in both directions between
   two such coproducts are inverse since they agree on all coprojections. -/
theorem finite_coproduct_evaluation (X : Scheme.{u}) (I : Type v) [Finite I]
    (V : I → X.ProEt) (hqc : ∀ i, CompactSpace (V i).left)
    (hqs : ∀ i, QuasiSeparatedSpace (V i).left) :
    ∃ (W : X.ProEt) (ι : ∀ i, V i ⟶ W)
      (e : (∐ fun i ↦ (V i).left) ≅ W.left),
      (∀ i, Sigma.ι (fun i ↦ (V i).left) i ≫ e.hom = (ι i).left) ∧
      CompactSpace W.left ∧ QuasiSeparatedSpace W.left ∧
      ((∀ i, IsAffine (V i).left) → IsAffine W.left) ∧
      Nonempty (IsColimit (Cofan.mk ((topology X).uliftYoneda.{max (u + 1) w}.obj W)
        (fun i ↦ (topology X).uliftYoneda.{max (u + 1) w}.map (ι i)))) ∧
      (∀ (c : Cofan (fun i ↦ (topology X).uliftYoneda.{max (u + 1) w}.obj (V i)))
        (hc : IsColimit c),
        IsIso (hc.desc (Cofan.mk ((topology X).uliftYoneda.{max (u + 1) w}.obj W)
          (fun i ↦ (topology X).uliftYoneda.{max (u + 1) w}.map (ι i))))) ∧
      (∀ F : Sheaf (topology X) (Type (max (u + 1) w)),
        Function.Bijective (fun s : F.obj.obj (op W) ↦
          fun i ↦ F.obj.map (ι i).op s)) ∧
      (∀ (F G : Sheaf (topology X) (Type (max (u + 1) w))) (η : F ⟶ G)
        (s : F.obj.obj (op W)) (i : I),
        G.obj.map (ι i).op (η.hom.app (op W) s) =
          η.hom.app (op (V i)) (F.obj.map (ι i).op s)) ∧
      (IsEmpty I → IsEmpty W.left ∧
        ∀ F : Sheaf (topology X) (Type (max (u + 1) w)),
          Nonempty (Unique (F.obj.obj (op W)))) := by
  classical
  let f : (∐ fun i ↦ (V i).left) ⟶ X := Sigma.desc (fun i ↦ (V i).hom)
  have hf : WeaklyEtale f :=
    IsZariskiLocalAtSource.sigmaDesc (fun i ↦ (V i).prop)
  let W : X.ProEt := ProEt.mk f
  let ι : ∀ i, V i ⟶ W := fun i ↦
    MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (V i).left) i)
      (by dsimp [W]; simp [f])
  let e : (∐ fun i ↦ (V i).left) ≅ W.left := Iso.refl _
  have hgeom := finite_coproduct_lfp_qcqs (fun i ↦ (V i).left) X
    (fun i ↦ (V i).hom)
  have haff : (∀ i, IsAffine (V i).left) →
      IsAffine (∐ fun i ↦ (V i).left) := by
    intro h
    infer_instance
  have hι (i : I) : Sigma.ι (fun i ↦ (V i).left) i ≫ e.hom = (ι i).left := by
    change Sigma.ι (fun i ↦ (V i).left) i = (ι i).left
    rfl
  have hcore := finite_coproduct_sheaf_core X I V W ι e hqc hqs hι
  obtain ⟨hsec, hempty⟩ := hcore
  let cW := Cofan.mk ((topology X).uliftYoneda.{max (u + 1) w}.obj W)
    (fun i ↦ (topology X).uliftYoneda.{max (u + 1) w}.map (ι i))
  let desc : ∀ t : Cofan (fun i ↦
      (topology X).uliftYoneda.{max (u + 1) w}.obj (V i)),
      cW.pt ⟶ t.pt := fun t ↦
    let x : ∀ i, t.pt.obj.obj (op (V i)) := fun i ↦
      (topology X).uliftYonedaEquiv (t.inj i)
    let s := Classical.choose ((hsec t.pt).2 x)
    (topology X).uliftYonedaEquiv.symm s
  have desc_spec (t : Cofan (fun i ↦
      (topology X).uliftYoneda.{max (u + 1) w}.obj (V i))) :
      (fun i ↦ t.pt.obj.map (ι i).op
        ((topology X).uliftYonedaEquiv (desc t))) =
        (fun i ↦ (topology X).uliftYonedaEquiv (t.inj i)) := by
    let x : ∀ i, t.pt.obj.obj (op (V i)) := fun i ↦
      (topology X).uliftYonedaEquiv (t.inj i)
    have hs := Classical.choose_spec ((hsec t.pt).2 x)
    funext i
    rw [CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_naturality]
    exact congr_fun hs i
  have hcolim : IsColimit cW := by
    refine Cofan.IsColimit.mk cW desc ?_ ?_
    · intro t i
      apply (topology X).uliftYonedaEquiv.injective
      change (desc t).hom.app (op (V i))
        ((topology X).uliftYonedaEquiv
          ((topology X).uliftYoneda.map (ι i))) = _
      calc
        _ = (topology X).uliftYonedaEquiv
            ((topology X).uliftYoneda.map (ι i) ≫ desc t) :=
          ((topology X).uliftYonedaEquiv_comp
            ((topology X).uliftYoneda.map (ι i)) (desc t)).symm
        _ = _ := by
          rw [← (topology X).uliftYonedaEquiv_naturality (desc t) (ι i)]
          exact congr_fun (desc_spec t) i
    · intro t m hm
      apply (topology X).uliftYonedaEquiv.injective
      apply (hsec t.pt).1
      funext i
      have hn := (topology X).uliftYonedaEquiv_naturality m (ι i)
      have hm_i := congrArg (fun q ↦ (topology X).uliftYonedaEquiv q) (hm i)
      calc
        (fun s i ↦ t.pt.obj.map (ι i).op s) ((topology X).uliftYonedaEquiv m) i =
            (topology X).uliftYonedaEquiv
              ((topology X).uliftYoneda.map (ι i) ≫ m) := by
                simpa only [Function.comp_apply] using hn
        _ = (topology X).uliftYonedaEquiv (t.inj i) := by
          simpa [cW] using hm_i
        _ = (fun j ↦ t.pt.obj.map (ι j).op
            ((topology X).uliftYonedaEquiv (desc t))) i :=
          (congr_fun (desc_spec t) i).symm
  refine ⟨W, ι, e, hι, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [W]
    exact hgeom.1 hqc
  · dsimp [W]
    exact hgeom.2.1 hqs
  · intro h
    dsimp [W]
    exact haff h
  · exact ⟨hcolim⟩
  · intro c hc
    exact (hc.nonempty_isColimit_iff_isIso_desc).mp ⟨hcolim⟩
  · exact hsec
  · intro F G η s i
    have hn := ConcreteCategory.congr_hom (η.hom.naturality (ι i).op) s
    exact hn.symm
  · exact hempty

end AlgebraicGeometry.Scheme.ProEt
