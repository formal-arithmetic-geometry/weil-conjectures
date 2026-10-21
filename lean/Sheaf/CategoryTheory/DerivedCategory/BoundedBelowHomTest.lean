/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q22, U1
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Bounded-below objects detect derived isomorphisms

Source: Weil conjectures blueprint, main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, final composition/open-locality paragraph
(blueprint: lem-sf-bounded-below-hom-test).

The derived category is ordinary and unbounded. Boundedness below of a test object
is expressed directly by eventual vanishing of its cohomology objects.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Brutal lower truncations detect zero objects: the inclusion of the truncation
starting in degree `q - 1` induces an isomorphism on degree-`q` cohomology.
Source: Stacks Project, Homology, Tag 0118 (cochain version), and the cohomology
criterion for derived isomorphisms (blueprint: lem-sf-bounded-below-hom-test). -/
private theorem isZero_of_boundedBelow_hom_zero
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : DerivedCategory A)
    (hX : ∀ H : DerivedCategory A,
      (∃ a : ℤ, ∀ q : ℤ, q < a → IsZero ((homologyFunctor A q).obj H)) →
      ∀ f : H ⟶ X, f = 0) : IsZero X := by
  have hhom (q : ℤ) : IsZero ((homologyFunctor A q).obj X) := by
    let K := Q.objPreimage X
    let e : Q.obj K ≅ X := Q.objObjPreimageIso X
    let L := K.stupidTrunc (ComplexShape.embeddingUpIntGE (q - 1))
    let i : L ⟶ K := K.ιStupidTrunc (ComplexShape.embeddingUpIntGE (q - 1))
    have hL : ∃ a : ℤ, ∀ n : ℤ, n < a →
        IsZero ((homologyFunctor A n).obj (Q.obj L)) := by
      refine ⟨q - 1, fun n hn ↦ ?_⟩
      exact isZero_of_isGE (Q.obj L) (q - 1) n hn
    have hi (n : ℤ) (hn : q - 1 ≤ n) : IsIso (i.f n) :=
      K.isIso_ιStupidTrunc_f _ (i := (n - (q - 1)).toNat) (by
        simp only [ComplexShape.embeddingUpIntGE_f]
        omega)
    have hprev : IsIso (i.f ((ComplexShape.up ℤ).prev q)) := hi _ (by simp)
    have hmid : IsIso (i.f q) := hi q (by omega)
    have hnext : IsIso (i.f ((ComplexShape.up ℤ).next q)) := hi _ (by simp; omega)
    have hqi : QuasiIsoAt i q := by
      rw [quasiIsoAt_iff]
      have : IsIso ((HomologicalComplex.shortComplexFunctor A (.up ℤ) q).map i).τ₁ :=
        hprev
      have : IsIso ((HomologicalComplex.shortComplexFunctor A (.up ℤ) q).map i).τ₂ :=
        hmid
      have : IsIso ((HomologicalComplex.shortComplexFunctor A (.up ℤ) q).map i).τ₃ :=
        hnext
      have : IsIso ((HomologicalComplex.shortComplexFunctor A (.up ℤ) q).map i) :=
        ShortComplex.isIso_of_isIso _
      infer_instance
    have hmap : IsIso ((homologyFunctor A q).map (Q.map i)) := by
      exact (NatIso.isIso_map_iff (homologyFunctorFactors A q) i).2
        (show IsIso (HomologicalComplex.homologyMap i q) from inferInstance)
    have hz := hX (Q.obj L) hL (Q.map i ≫ e.hom)
    have : IsIso ((homologyFunctor A q).map (Q.map i ≫ e.hom)) := by
      rw [Functor.map_comp]
      infer_instance
    exact IsZero.of_epi_eq_zero ((homologyFunctor A q).map (Q.map i ≫ e.hom))
      (by rw [hz, Functor.map_zero])
  have : IsIso (0 : X ⟶ X) := (isIso_iff A _).2 fun q ↦ by
    rw [Functor.map_zero]
    exact ⟨⟨0, (hhom q).eq_of_src _ _, (hhom q).eq_of_src _ _⟩⟩
  exact IsZero.of_mono_eq_zero (0 : X ⟶ X) rfl

/-- Postcomposition tested on every shift of every bounded-below object detects
isomorphisms in the ordinary unbounded derived category of module sheaves.

Source: Weil conjectures blueprint, main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, final composition/open-locality paragraph
(blueprint: lem-sf-bounded-below-hom-test).

Proof:
1. Complete alpha to a distinguished triangle B -> G -> Z -> B[1]. For every
   bounded-below H, the hypothesis at shift -1, transported by the shift
   adjunction, makes Hom(H,B[1]) -> Hom(H,G[1]) injective. Thus every f : H -> Z
   has zero composite to B[1]. Exactness factors f through G; the hypothesis at
   shift 0 lifts that factor through alpha. Consecutive triangle arrows compose
   to zero, hence f = 0.
2. Represent Z by a complex K. For every q, its brutal truncation starting at
   q - 1 is bounded below. Its inclusion into K, followed by QK = Z, is zero
   by step 1, but induces an isomorphism on degree-q cohomology: all three
   terms in the defining short complex are retained. Hence H^q(Z) = 0.
3. The cohomology criterion makes the zero endomorphism of Z invertible, so Z
   is zero. The distinguished triangle then makes alpha invertible.
No coproduct, telescope, or boundedness of B and G is required. -/
theorem isIso_of_boundedBelow_hom_bijective
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    {B G : DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))}
    (α : B ⟶ G)
    (hα : ∀ H : DerivedCategory
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)),
      (∃ a : ℤ, ∀ q : ℤ, q < a → IsZero ((homologyFunctor _ q).obj H)) →
      ∀ n : ℤ, Function.Bijective (fun f : H⟦n⟧ ⟶ B ↦ f ≫ α)) :
    IsIso α := by
  classical
  let A := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  obtain ⟨Z, g, d, hT⟩ := Pretriangulated.distinguished_cocone_triangle α
  let T := Pretriangulated.Triangle.mk α g d
  have hZ : IsZero Z := by
    apply isZero_of_boundedBelow_hom_zero Z
    intro H hH f
    have hshift : Function.Injective (fun k : H ⟶ B⟦(1 : ℤ)⟧ ↦ k ≫ α⟦1⟧') := by
      let adj : shiftFunctor (DerivedCategory A) (-1 : ℤ) ⊣
          shiftFunctor (DerivedCategory A) (1 : ℤ) :=
        (shiftEquiv' (DerivedCategory A) (-1 : ℤ) 1 (by decide)).toAdjunction
      intro k l hkl
      apply (adj.homEquiv H B).symm.injective
      apply (hα H hH (-1)).1
      exact (adj.homEquiv_naturality_right_symm k α).symm.trans
        ((congrArg (adj.homEquiv H G).symm hkl).trans
          (adj.homEquiv_naturality_right_symm l α))
    have hfd : f ≫ d = 0 := hshift (by
      change (f ≫ d) ≫ α⟦1⟧' = 0 ≫ α⟦1⟧'
      have hd : d ≫ α⟦1⟧' = 0 := Pretriangulated.comp_distTriang_mor_zero₃₁ T hT
      rw [Category.assoc, hd, comp_zero, zero_comp])
    obtain ⟨k, hk⟩ := Pretriangulated.Triangle.coyoneda_exact₃ T hT f hfd
    have hzero : Function.Surjective (fun k : H ⟶ B ↦ k ≫ α) := by
      intro k
      obtain ⟨l, hl⟩ := (hα H hH 0).2 ((shiftFunctorZero _ ℤ).hom.app H ≫ k)
      refine ⟨(shiftFunctorZero _ ℤ).inv.app H ≫ l, ?_⟩
      change ((shiftFunctorZero _ ℤ).inv.app H ≫ l) ≫ α = k
      change l ≫ α = _ at hl
      rw [Category.assoc, hl]
      simp
    obtain ⟨l, hl⟩ := hzero k
    change f = k ≫ g at hk
    change l ≫ α = k at hl
    have hg : α ≫ g = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ T hT
    rw [hk, ← hl, Category.assoc, hg, comp_zero]
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ T hT).1 hZ

end DerivedCategory
