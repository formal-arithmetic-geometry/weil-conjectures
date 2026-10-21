/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.CompactificationCoherenceCocycle
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Paper.NonrationalCompositionSeed
import Sheaf.Paper.CompactificationRefinementIdentity

/-!
# Composition of finite and integral lower shriek on localizing constructible categories

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-comp-composition,
clause (1), finite and integral cases, and its proof, paragraphs "The composition isomorphism" and
"Canonicity and associativity"
(blueprint: lem-sfb-nonrational-localizing-lower-shriek-composition).

The coefficients are exactly finite torsion rings, ℤ_ℓ, and valuation rings of finite
subextensions of ℚ_ℓ, with the condensed topologies specified in the statement.
The functors are the existing restrictions of `Rp_* D(j_!)`.
Compatibility is expressed using the canonical refinement components of the recorded
compactification cocycle. Every triple of compactifications is allowed, including
nondense ones. Common dense refinements and the cocycle law identify the final equation
with compatibility with all compactification comparison isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem transportComposition
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {I J L : Type*} (F : I → C ⥤ D) (G : J → D ⥤ E) (H : L → C ⥤ E)
    (pf : ∀ c d, F c ≅ F d) (pg : ∀ c d, G c ≅ G d) (ph : ∀ c d, H c ≅ H d)
    (cpf : ∀ c d e X, (pf c d).hom.app X ≫ (pf d e).hom.app X = (pf c e).hom.app X)
    (cpg : ∀ c d e X, (pg c d).hom.app X ≫ (pg d e).hom.app X = (pg c e).hom.app X)
    (cph : ∀ c d e X, (ph c d).hom.app X ≫ (ph d e).hom.app X = (ph c e).hom.app X)
    (i₀ : I) (j₀ : J) (l₀ : L) (β : F i₀ ⋙ G j₀ ≅ H l₀) :
    ∃ α : ∀ i j l, F i ⋙ G j ≅ H l,
      ∀ i j l i' j' l' X,
        (G j).map ((pf i i').hom.app X) ≫
            (pg j j').hom.app ((F i').obj X) ≫ (α i' j' l').hom.app X =
          (α i j l).hom.app X ≫ (ph l l').hom.app X := by
  let α := fun i j l ↦
    Functor.isoWhiskerRight (pf i i₀) (G j) ≪≫
      Functor.isoWhiskerLeft (F i₀) (pg j j₀) ≪≫ β ≪≫ ph l₀ l
  refine ⟨α, ?_⟩
  intro i j l i' j' l' X
  dsimp only [α, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight, Functor.whiskerLeft]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc, ← Functor.map_comp_assoc, cpf]
  rw [← Category.assoc ((pg j j').hom.app _), cpg]
  rw [cph]

set_option backward.isDefEq.respectTransparency false in
/-- There is a natural composition isomorphism on the ordinary localizing closures for
finite and integral condensed coefficients, compatible with change of
compactification. The witnesses
`hf`, `hg`, `hgf` only certify preservation by the actual ambient compactification functors;
`localizingLowerShriek` uses those same objects and maps. The equation is an equality in the
ambient derived category, hence also in its full localizing subcategory. Its refinement
maps are exactly those used to normalize the comparisons in
`compactification_coherence_cocycle`, rather than arbitrary isomorphisms of their endpoints.

Source: blueprint sk-thm-sf-comp-composition, clause (1), finite and integral cases, and its proof
(blueprint: lem-sfb-nonrational-localizing-lower-shriek-composition).

Proof:
1. Embed the coefficient alternatives into IsLocalizingAdmissibleCoefficient. Apply
   exists_localizingExceptionalAdjoint to every compactification of f, g, and gf,
   retaining the preservation witnesses that type localizingLowerShriek.
2. Obtain a composition isomorphism for one triple from
   exists_nonrationalLocalizingLowerShriekCompositionSeed. Obtain the comparison
   isomorphisms for each of f, g, and gf from compactification_coherence_cocycle and
   lift them through the full inclusions of the localizing closures.
3. Define the isomorphism for any triple by comparing its f and g compactifications
   with the seed, applying the seed isomorphism, and comparing the seed composite
   with the requested composite. The private transportComposition calculation uses
   naturality and the three cocycle equations to prove compatibility with comparison
   isomorphisms in all three variables.
4. At a dense compactification d, the normalization equation for the common refinement
   d with its identity projection identifies the comparison c to d with the actual
   refinement component. Here compactificationRefinementComponent_id removes the
   identity-projection factor. Taking underlying ambient morphisms in the transport
   equation gives exactly the displayed simultaneous refinement square. -/
theorem exists_nonrationalLocalizingLowerShriekComposition
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (_hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    ∃ (hf : ∀ (c : Compactification.BoundaryCompactification f)
          (K : DerivedCategory (CategoryTheory.Mod
            (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
          localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hg : ∀ (c : Compactification.BoundaryCompactification g)
          (K : DerivedCategory (CategoryTheory.Mod
            (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))),
          localizingClosureProEtale Λ Y K → localizingClosureProEtale Λ Z
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hgf : ∀ (c : Compactification.BoundaryCompactification (f ≫ g))
          (K : DerivedCategory (CategoryTheory.Mod
            (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
          localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Z
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)),
      ∃ α : ∀ (cf : Compactification.BoundaryCompactification f)
          (cg : Compactification.BoundaryCompactification g)
          (cgf : Compactification.BoundaryCompactification (f ≫ g)),
          localizingLowerShriek Λ cf.obj.obj (hf cf) ⋙
              localizingLowerShriek Λ cg.obj.obj (hg cg) ≅
            localizingLowerShriek Λ cgf.obj.obj (hgf cgf),
        ∀ (cf : Compactification.BoundaryCompactification f)
          (cg : Compactification.BoundaryCompactification g)
          (cgf : Compactification.BoundaryCompactification (f ≫ g))
          (df : Compactification.DenseBoundaryCompactification f)
          (dg : Compactification.DenseBoundaryCompactification g)
          (dgf : Compactification.DenseBoundaryCompactification (f ≫ g))
          (rf : df.obj ⟶ cf) (rg : dg.obj ⟶ cg) (rgf : dgf.obj ⟶ cgf)
          (K : (localizingClosureProEtale Λ X).FullSubcategory),
          (rightDerivedLowerShriekOfCompactification Λ cg.obj.obj).map
              (compactificationRefinementComponent Λ rf K.obj) ≫
            compactificationRefinementComponent Λ rg
              ((rightDerivedLowerShriekOfCompactification Λ df.obj.obj.obj).obj K.obj) ≫
            ((α df.obj dg.obj dgf.obj).hom.app K).hom =
          ((α cf cg cgf).hom.app K).hom ≫
            compactificationRefinementComponent Λ rgf K.obj := by
  classical
  have hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases _hΛ with h | h | ⟨E, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩))))
  have hf := fun c ↦ (exists_localizingExceptionalAdjoint Λ ℓ k f c hΛ).choose
  have hg := fun c ↦ (exists_localizingExceptionalAdjoint Λ ℓ k g c hΛ).choose
  have hgf := fun c ↦ (exists_localizingExceptionalAdjoint Λ ℓ k (f ≫ g) c hΛ).choose
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated
    (Y ↘ Spec (.of k))
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (.of k))
  let : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated
    (Z ↘ Spec (.of k))
  obtain ⟨φf, hif, hnf, hrf, hcf⟩ := compactification_coherence_cocycle Λ ℓ hΛ f
  obtain ⟨φg, hig, hng, hrg, hcg⟩ := compactification_coherence_cocycle Λ ℓ hΛ g
  obtain ⟨φh, hih, hnh, hrh, hch⟩ := compactification_coherence_cocycle Λ ℓ hΛ (f ≫ g)
  let F := fun c : Compactification.BoundaryCompactification f ↦
    localizingLowerShriek Λ c.obj.obj (hf c)
  let G := fun c : Compactification.BoundaryCompactification g ↦
    localizingLowerShriek Λ c.obj.obj (hg c)
  let H := fun c : Compactification.BoundaryCompactification (f ≫ g) ↦
    localizingLowerShriek Λ c.obj.obj (hgf c)
  let pf : ∀ c d, F c ≅ F d := fun c d ↦
    NatIso.ofComponents (fun K ↦ (localizingClosureProEtale Λ Y).isoMk ((φf c d).app K))
      (fun a ↦ (localizingClosureProEtale Λ Y).ι.map_injective ((φf c d).hom.naturality a))
  let pg : ∀ c d, G c ≅ G d := fun c d ↦
    NatIso.ofComponents (fun K ↦ (localizingClosureProEtale Λ Z).isoMk ((φg c d).app K))
      (fun a ↦ (localizingClosureProEtale Λ Z).ι.map_injective ((φg c d).hom.naturality a))
  let ph : ∀ c d, H c ≅ H d := fun c d ↦
    NatIso.ofComponents (fun K ↦ (localizingClosureProEtale Λ Z).isoMk ((φh c d).app K))
      (fun a ↦ (localizingClosureProEtale Λ Z).ι.map_injective ((φh c d).hom.naturality a))
  have seed : ∃ cf cg ch, Nonempty (F cf ⋙ G cg ≅ H ch) :=
    exists_nonrationalLocalizingLowerShriekCompositionSeed Λ ℓ _hΛ k f g hf hg hgf
  obtain ⟨cf₀, cg₀, ch₀, ⟨β⟩⟩ := seed
  have cpf (c d e) (L : (localizingClosureProEtale Λ X).FullSubcategory) :
      (pf c d).hom.app L ≫ (pf d e).hom.app L = (pf c e).hom.app L := by
    apply (localizingClosureProEtale Λ Y).ι.map_injective
    change (φf c d).hom.app L ≫ (φf d e).hom.app L = (φf c e).hom.app L
    exact congrArg (fun e ↦ e.hom.app L) (hcf c d e)
  have cpg (c d e) (L : (localizingClosureProEtale Λ Y).FullSubcategory) :
      (pg c d).hom.app L ≫ (pg d e).hom.app L = (pg c e).hom.app L := by
    apply (localizingClosureProEtale Λ Z).ι.map_injective
    change (φg c d).hom.app L ≫ (φg d e).hom.app L = (φg c e).hom.app L
    exact congrArg (fun e ↦ e.hom.app L) (hcg c d e)
  have cph (c d e) (L : (localizingClosureProEtale Λ X).FullSubcategory) :
      (ph c d).hom.app L ≫ (ph d e).hom.app L = (ph c e).hom.app L := by
    apply (localizingClosureProEtale Λ Z).ι.map_injective
    change (φh c d).hom.app L ≫ (φh d e).hom.app L = (φh c e).hom.app L
    exact congrArg (fun e ↦ e.hom.app L) (hch c d e)
  obtain ⟨α, hα⟩ := transportComposition F G H pf pg ph cpf cpg cph cf₀ cg₀ ch₀ β
  refine ⟨hf, hg, hgf, α, ?_⟩
  intro cf cg ch df dg dh rf rg rh K
  have idf := compactificationRefinementComponent_id Λ ℓ k hΛ f df K.obj
  have idg : ∀ L : (localizingClosureProEtale Λ Y).FullSubcategory,
      compactificationRefinementComponent Λ (𝟙 dg.obj) L.obj = 𝟙 _ :=
    fun L ↦ compactificationRefinementComponent_id Λ ℓ k hΛ g dg L.obj
  have idh := compactificationRefinementComponent_id Λ ℓ k hΛ (f ≫ g) dh K.obj
  have ef : ((pf cf df.obj).hom.app K).hom =
      compactificationRefinementComponent Λ rf K.obj := by
    change (φf cf df.obj).hom.app K = _
    have hn := hnf cf df.obj df rf (𝟙 df.obj) K
    rw [idf] at hn
    exact (Category.comp_id _).symm.trans hn
  have eg : ∀ L : (localizingClosureProEtale Λ Y).FullSubcategory,
      ((pg cg dg.obj).hom.app L).hom =
        compactificationRefinementComponent Λ rg L.obj := by
    intro L
    change (φg cg dg.obj).hom.app L = _
    have hn := hng cg dg.obj dg rg (𝟙 dg.obj) L
    rw [idg L] at hn
    exact (Category.comp_id _).symm.trans hn
  have eh : ((ph ch dh.obj).hom.app K).hom =
      compactificationRefinementComponent Λ rh K.obj := by
    change (φh ch dh.obj).hom.app K = _
    have hn := hnh ch dh.obj dh rh (𝟙 dh.obj) K
    rw [idh] at hn
    exact (Category.comp_id _).symm.trans hn
  have e := congrArg (fun q ↦ q.hom) (hα cf cg ch df.obj dg.obj dh.obj K)
  change (rightDerivedLowerShriekOfCompactification Λ cg.obj.obj).map
      ((pf cf df.obj).hom.app K).hom ≫
        ((pg cg dg.obj).hom.app ((F df.obj).obj K)).hom ≫
          ((α df.obj dg.obj dh.obj).hom.app K).hom =
      ((α cf cg ch).hom.app K).hom ≫ ((ph ch dh.obj).hom.app K).hom at e
  rw [ef, eg, eh] at e
  exact e

end AlgebraicGeometry.ProEtale.CondensedRing
