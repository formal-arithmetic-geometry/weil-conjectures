/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData

import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarCompositionModel
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarIdentityModel
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients

/-! # Normalized clopen scalar comparison

Source: Stacks Project, Tags 06YY and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] ClopenLocalization.sheafify ClopenLocalization.locallyBijective

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  computation

private theorem model_ext {Z : Scheme.{t}} (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)})
    {E : Type*} [Category E] {F G : DerivedCategory (Mods.{t, u} R) ⥤ E}
    (α β : F ⟶ G)
    (h : ∀ (P : CochainComplex (Mods.{t, u} R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      (∀ k : ℤ, IsFlatOnSite (J := topology Z) (R := R) (P.X k)) →
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Mods.{t, u} R) (.up ℤ))
  intro K
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  have := hf
  have h' := h P hP (fun k ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso R (P.X k)).symm (hflat k))
  apply (cancel_epi (F.map (DerivedCategory.Q.map f))).1
  rw [α.naturality, β.naturality, h']

private theorem tensor_ext {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    (M : Mods.{t, u} R) (N : Mods.{t, u} S)
    (f g : (ext (p a)).obj M ⟶ N)
    (h : ∀ (W : Z.ProEtᵒᵖ) (x : M.val.obj W),
      f.val.app W (sectionTensor (p a) M W 1 x) =
        g.val.app W (sectionTensor (p a) M W 1 x)) : f = g := by
  apply ((n.ordinaryAdjunction a).homEquiv M N).injective
  ext W x
  change f.val.app W (((n.ordinaryAdjunction a).unit.app M).val.app W x) =
    g.val.app W (((n.ordinaryAdjunction a).unit.app M).val.app W x)
  rw [n.ordinary_unit]
  exact h W x

private theorem tensor_map_one {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    {M N : Mods.{t, u} R} (f : M ⟶ N) (W : Z.ProEtᵒᵖ) (x : M.val.obj W) :
    ((ext (p a)).map f).val.app W (sectionTensor (p a) M W 1 x) =
      sectionTensor (p a) N W 1 (f.val.app W x) := by
  have h := congrArg (fun g ↦ g.val.app W x)
    ((n.ordinaryAdjunction a).unit.naturality f).symm
  change ((ext (p a)).map f).val.app W
      (((n.ordinaryAdjunction a).unit.app M).val.app W x) =
    (((n.ordinaryAdjunction a).unit.app N).val.app W (f.val.app W x)) at h
  simpa only [n.ordinary_unit] using h

private theorem tensor_transport {Z : Scheme.{t}} (p : Presentations.{t, u} Z)
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}}
    (a b : R ⟶ S) (h : a = b) (M : Mods.{t, u} R) (W : Z.ProEtᵒᵖ)
    (s : S.obj.obj W) (x : M.val.obj W) :
    (eqToHom (congrArg (fun f ↦ (ext (p f)).obj M) h)).val.app W
      (sectionTensor (p a) M W s x) = sectionTensor (p b) M W s x := by
  cases h
  rfl

private theorem restricted_tensor_ext {X Y : Scheme.{t}} {j : Y ⟶ X}
    [IsOpenImmersion j] {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (m : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Y.ProEt) (J := topology Y) (hD := derived.{t, u} Y) @q)
    (d : Comparison.{t, u} j @p @q) (hd : d.sections)
    {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    (M : Mods.{t, u} R) (N : Mods.{t, u} ((rings j).obj S))
    (f g : (res j S).obj ((ext (p a)).obj M) ⟶ N)
    (h : ∀ (W : Y.ProEtᵒᵖ) (x : ((res j R).obj M).val.obj W),
      f.val.app W (sectionTensor (p a) M
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.obj W) 1 x) =
      g.val.app W (sectionTensor (p a) M
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.obj W) 1 x)) :
    f = g := by
  apply (cancel_epi ((d.ordinary a).inv.app M)).1
  apply tensor_ext m ((rings j).map a)
  intro W x
  have hi := congrArg (fun f ↦ f.val.app W
    (sectionTensor (p a) M
      ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.obj W) 1 x))
    ((d.ordinary a).hom_inv_id_app M)
  change ((d.ordinary a).inv.app M).val.app W
    (((d.ordinary a).hom.app M).val.app W _) = _ at hi
  rw [hd] at hi
  change f.val.app W (((d.ordinary a).inv.app M).val.app W _) =
    g.val.app W (((d.ordinary a).inv.app M).val.app W _)
  rw [hi]
  exact h W x

private theorem ordinary_comp
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := X.ProEt) (J := topology X) (hD := derived.{t, u} X) @p)
    (m : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Y.ProEt) (J := topology Y) (hD := derived.{t, u} Y) @q)
    (d : Comparison.{t, u} j @p @q) (hs : d.sections) :
    ∀ {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (a : R ⟶ S) (b : S ⟶ T) (M : Mods.{t, u} R),
    (res.{t, u} j T).map ((n.ordinary a b).hom.app M) ≫
        (d.ordinary (a ≫ b)).hom.app M =
      (d.ordinary b).hom.app ((ext.{t, u} (Z := X) (p a)).obj M) ≫
        (ext.{t, u} (Z := Y) (q ((rings.{t, u} j).map b))).map ((d.ordinary a).hom.app M) ≫
        (m.ordinary ((rings.{t, u} j).map a) ((rings.{t, u} j).map b)).hom.app ((res.{t, u} j R).obj
          M) ≫
        eqToHom (congrArg (fun f ↦ (ext.{t, u} (Z := Y) (q f)).obj ((res.{t, u} j R).obj M))
          ((rings.{t, u} j).map_comp a b).symm) := by
  intro R S T a b M
  let e := (res j T).mapIso ((n.ordinary a b).app M)
  apply (cancel_epi e.inv).1
  apply restricted_tensor_ext m d hs (a ≫ b)
  intro W x
  let W' := (MorphismProperty.Over.map ⊤
    (inferInstance : WeaklyEtale j)).op.obj W
  let f₁ := (d.ordinary b).hom.app ((ext (p a)).obj M)
  let f₂ := (ext (q ((rings j).map b))).map ((d.ordinary a).hom.app M)
  let f₃ := (m.ordinary ((rings j).map a) ((rings j).map b)).hom.app
    ((res j R).obj M)
  let f₄ := eqToHom (congrArg (fun f ↦ (ext (q f)).obj ((res j R).obj M))
    ((rings j).map_comp a b).symm)
  have hi := n.ordinary_inv a b M W' x 1
  have hn := n.ordinary_hom a b M W' x 1 1
  simp only [map_one, one_mul] at hn
  have h₁ := hs b ((ext (p a)).obj M) W 1
    (sectionTensor (p a) M W' 1 x)
  have h₂ := tensor_map_one m ((rings j).map b) ((d.ordinary a).hom.app M) W
    (sectionTensor (p a) M W' 1 x)
  rw [hs] at h₂
  have h₃ := m.ordinary_hom ((rings j).map a) ((rings j).map b)
    ((res j R).obj M) W x 1 1
  simp only [map_one, one_mul] at h₃
  have h₄ := tensor_transport q _ _ ((rings j).map_comp a b).symm
    ((res j R).obj M) W 1 x
  change ((d.ordinary (a ≫ b)).hom.app M).val.app W
      (((n.ordinary a b).hom.app M).val.app W'
        (((n.ordinary a b).inv.app M).val.app W' _)) =
    f₄.val.app W (f₃.val.app W (f₂.val.app W (f₁.val.app W
      (((n.ordinary a b).inv.app M).val.app W' _))))
  rw [hi, hn, hs]
  change _ = f₄.val.app W (f₃.val.app W (f₂.val.app W (f₁.val.app W _)))
  rw [h₁]
  erw [h₂]
  erw [h₃]
  exact h₄.symm

private theorem ordinary_id
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (m : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Y.ProEt) (J := topology Y) (hD := derived.{t, u} Y) @q)
    (U : Units.{t, u} @p) (V : Units.{t, u} @q)
    (d : Comparison.{t, u} j @p @q) (hs : d.sections) :
    ∀ (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) (M : Mods.{t, u} R),
    (d.ordinary (𝟙 R)).hom.app M ≫
        eqToHom (congrArg (fun f ↦ (ext.{t, u} (Z := Y) (q f)).obj ((res.{t, u} j R).obj M))
          ((rings.{t, u} j).map_id R)) ≫
        (V.ordinary ((rings.{t, u} j).obj R)).hom.app ((res.{t, u} j R).obj M) =
      (res.{t, u} j R).map ((U.ordinary R).hom.app M) := by
  intro R M
  apply restricted_tensor_ext m d hs (𝟙 R)
  intro W x
  let f := eqToHom (congrArg (fun a ↦ (ext (q a)).obj ((res j R).obj M))
    ((rings j).map_id R))
  let v := (V.ordinary ((rings j).obj R)).hom.app ((res j R).obj M)
  change v.val.app W (f.val.app W
    (((d.ordinary (𝟙 R)).hom.app M).val.app W _)) =
      ((U.ordinary R).hom.app M).val.app _ _
  dsimp only [f, v]
  rw [hs, tensor_transport, V.sections, U.sections]
  rfl

/-- A normalized scalar restriction square commutes with the scalar compositor
and multiplication units.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6D, composition and identity
cases, and the pure-tensor calculation in steps 4 and 5 of the parent node.
(blueprint: lem-pur-clopen-scalar-comparison-coherence).

Proof: first check ordinary composition on z tensor (s tensor x). The ambient
normalization sends this to (b(s) z) tensor x; restriction leaves the sections and
ring operations unchanged. The other path applies the two restriction
comparisons, whose sections formulas leave the same tensors, and then the
component normalization, giving precisely the same tensor. Local sheafified pure
tensors generate, so these module maps agree. This also proves the asserted
composite-sections equation. For identity coefficients, multiplication sends
s tensor x to sx on both paths, proving the ordinary identity equation.
For derived composition choose a flat-term K-flat input model. Its first scalar
extension is again K-flat with flat terms over the new ring by the extended
hypothesis. Apply the representative equations for both squares and the
normalization representative equations for both scalar compositors. Cancel the
computation isomorphisms supplied by computed. The equation reduces to the
ordinary composition equation on the same model, degree by degree. Localization
of the flat-term K-flat subcategory is equivalent to the derived category;
faithfulness extends the equation to every derived object. For the derived
identity equation use the Units representative equations in the same argument,
reducing it to the ordinary multiplication identity. Equality transports along
map_comp and map_id merely identify the same actual composite or identity ring
map and introduce no further choice. Empty components and zero rings are covered
by the same generating and localization arguments. -/
theorem clopen_scalar_comparison_coherence
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (p : Presentations.{t, u} X)
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := X.ProEt) (J := topology X) (hD := derived.{t, u} X) @p)
    (q : ∀ i, Presentations.{t, u} (Y i))
    (m : ∀ i, Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := (Y i).ProEt) (J := topology (Y i)) (hD := derived.{t, u} (Y i))
      (fun {R S} a ↦ q i (R := R) (S := S) a))
    (U : Units.{t, u} @p)
    (V : ∀ i, Units.{t, u} (fun {R S} a ↦ q i (R := R) (S := S) a))
    (d : ∀ i, Comparison.{t, u} (j i) @p
      (fun {R S} a ↦ q i (R := R) (S := S) a))
    (hnorm : ∀ i, (d i).sections ∧ (d i).degree ∧ (d i).representative ∧
      (d i).computed ∧ (d i).extended ∧ (d i).unique) :
    ∀ i, Coherence.{t, u} (j i) n (m i) U (V i) (d i) := by
  intro i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro R S T a b K
    let α : extD (p a) ⋙ extD (p b) ⋙ resD (j i) T ⟶
        resD (j i) R ⋙ extD (q i ((rings (j i)).map (a ≫ b))) :=
      whiskerRight (n.derived a b).hom (resD (j i) T) ≫
        ((d i).derived (a ≫ b)).hom
    let β : extD (p a) ⋙ extD (p b) ⋙ resD (j i) T ⟶
        resD (j i) R ⋙ extD (q i ((rings (j i)).map (a ≫ b))) :=
      whiskerLeft (extD (p a)) ((d i).derived b).hom ≫
        whiskerRight ((d i).derived a).hom (extD (q i ((rings (j i)).map b))) ≫
        whiskerLeft (resD (j i) R)
          ((m i).derived ((rings (j i)).map a) ((rings (j i)).map b)).hom ≫
        whiskerLeft (resD (j i) R)
          (eqToHom (congrArg (fun f ↦ extD (q i f))
            ((rings (j i)).map_comp a b).symm))
    have h : α = β := by
      apply model_ext R
      intro P hP hf
      have hR := clopen_total_tensor_kflat_detection X I Y j hd hc R
      have hiP := (hR.2.1 P).mp hP i
      have hif := fun k ↦ (hR.1 (P.X k)).mp (hf k) i
      simpa only [α, β, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
        eqToHom_app] using
        clopen_scalar_composition_model (j i) n (m i) (d i)
          (hnorm i).2.1 (hnorm i).2.2.1 (hnorm i).2.2.2.1
          (hnorm i).2.2.2.2.1 (ordinary_comp (j i) n (m i) (d i) (hnorm i).1)
          a b P hP hf hiP hif
    have hK := NatTrans.congr_app h K
    simpa only [α, β, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      eqToHom_app] using hK
  · exact ordinary_comp (j i) n (m i) (d i) (hnorm i).1
  · intro R S T a b M W x s z
    change (((d i).ordinary (a ≫ b)).hom.app M).val.app W
      (((n.ordinary a b).hom.app M).val.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).op.obj W)
        (sectionTensor (p b) ((ext (p a)).obj M)
          ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).op.obj W) z
          (sectionTensor (p a) M
            ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).op.obj W)
            s x))) = _
    rw [n.ordinary_hom]
    exact (hnorm i).1 (a ≫ b) M W _ x
  · intro R K
    let α : extD (p (𝟙 R)) ⋙ resD (j i) R ⟶ resD (j i) R :=
      ((d i).derived (𝟙 R)).hom ≫
        whiskerLeft (resD (j i) R)
          (eqToHom (congrArg (fun f ↦ extD (q i f)) ((rings (j i)).map_id R))) ≫
        whiskerLeft (resD (j i) R) ((V i).derived ((rings (j i)).obj R)).hom
    let β : extD (p (𝟙 R)) ⋙ resD (j i) R ⟶ resD (j i) R :=
      whiskerRight (U.derived R).hom (resD (j i) R)
    have h : α = β := by
      apply model_ext R
      intro P hP hf
      have hR := clopen_total_tensor_kflat_detection X I Y j hd hc R
      have hiP := (hR.2.1 P).mp hP i
      have hif := fun k ↦ (hR.1 (P.X k)).mp (hf k) i
      simpa only [α, β, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
        eqToHom_app] using
        clopen_scalar_identity_model (j i) U (V i) (d i)
          (hnorm i).2.1 (hnorm i).2.2.1
          (ordinary_id (j i) (m i) U (V i) (d i) (hnorm i).1) R P hP hf hiP hif
    have hK := NatTrans.congr_app h K
    simpa only [α, β, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      eqToHom_app] using hK
  · exact ordinary_id (j i) (m i) U (V i) (d i) (hnorm i).1

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
