/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenOrdinaryScalarComparison
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
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] ClopenLocalization.sheafify ClopenLocalization.locallyBijective

universe a₁ b₁ a₂ b₂ d₁

private noncomputable def cochainRepresentativeWhiskering
    {A : Type a₁} [Category.{b₁} A] [Abelian A] [HasDerivedCategory.{d₁} A]
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), good L ∧ QuasiIso p)
    (E : Type a₂) [Category.{b₂} E] :
    ((Functor.whiskeringLeft _ _ E).obj
      (ObjectProperty.ι good ⋙ DerivedCategory.Q)).FullyFaithful := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let P : ObjectProperty (CochainComplex A ℤ) := good
  let S : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ good X.as
  let f := S.lift (P.ι ⋙ q) (fun X ↦ X.property)
  have : f.Full := ⟨by
    intro X Y g
    obtain ⟨a, ha⟩ := q.map_surjective g.hom
    refine ⟨ObjectProperty.homMk a, ?_⟩
    exact ObjectProperty.hom_ext _ ha⟩
  have : f.EssSurj := ⟨by
    intro X
    obtain ⟨Y, hy⟩ := HomotopyCategory.quotient_obj_surjective X.obj
    refine ⟨⟨Y, ?_⟩, ⟨ObjectProperty.isoMk S (eqToIso hy)⟩⟩
    change S (q.obj Y)
    rw [hy]
    exact X.property⟩
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : S.FullSubcategory) (s : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨L, p, hL, hp⟩ := res X.as
    exact ⟨⟨q.obj L, hL⟩, q.map p,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩
  have : (S.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage S.ι) :=
    CategoryTheory.restriction_localization _ _ S hres
  let ff := (Localization.fullyFaithfulWhiskeringLeft (S.ι ⋙ DerivedCategory.Qh)
    ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage S.ι) E).comp
      (CategoryTheory.fullyFaithfulWhiskeringOfFullEssSurj f E)
  exact ff.ofIso ((Functor.whiskeringLeft _ _ E).mapIso
    (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A)))

private def computationNat {Z : Scheme.{t}}
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} {a : R ⟶ S}
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation.{t + 1, t,
      max u (t + 1), max (u + 1) (t + 2)} a) :
    DerivedCategory.Q ⋙ p.derived ⟶
      p.ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Mods.{t, u} R)).inv p.derived ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ _) p.counit ≫
    Functor.whiskerRight (p.ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (p.ordinary.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso (Mods.{t, u} S)).hom

private theorem computationNat_app {Z : Scheme.{t}}
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} {a : R ⟶ S}
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation.{t + 1, t,
      max u (t + 1), max (u + 1) (t + 2)} a)
    (P : CochainComplex (Mods.{t, u} R) ℤ) :
    (computationNat p).app P = computation p P := by
  rfl

private theorem computation_isIso {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    (P : CochainComplex (Mods.{t, u} R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ k : ℤ, IsFlatOnSite (J := topology Z) (R := R) (P.X k)) :
    IsIso ((computationNat (p a)).app P) := by
  have := n.computed a P hP hf
  dsimp only [computationNat, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

private theorem models_resolve {Z : Scheme.{t}}
    (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)})
    (K : CochainComplex (Mods.{t, u} R) ℤ) :
    ∃ (P : CochainComplex (Mods.{t, u} R) ℤ) (f : P ⟶ K),
      (CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
        ∀ k : ℤ, IsFlatOnSite (J := topology Z) (R := R) (P.X k)) ∧ QuasiIso f := by
  obtain ⟨P, f, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  refine ⟨P, f, ⟨hP, fun k ↦ ?_⟩, hq⟩
  exact (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso R (P.X k)).symm (hf k)

attribute [local irreducible] computation computationNat
  SheafOfModules.monoidalCategory HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

private theorem descendComparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{d₁} A] [HasDerivedCategory.{d₁} B]
    [HasDerivedCategory.{d₁} C] [HasDerivedCategory.{d₁} D]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (N : C ⥤ D) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (E : A ⥤ C) [E.Additive] (F : B ⥤ D) [F.Additive]
    (T : DerivedCategory A ⥤ DerivedCategory C)
    (U : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ : DerivedCategory.Q ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (P : CochainComplex A ℤ) (f : P ⟶ K), good P ∧ QuasiIso f)
    (hε : ∀ P, good P → IsIso (ε.app P))
    (hδ : ∀ P, good P → IsIso (δ.app ((L.mapHomologicalComplex (.up ℤ)).obj P)))
    (c : E ⋙ N ≅ L ⋙ F) :
    ∃ e : T ⋙ N.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ U,
      (∀ P, good P → e.hom.app (DerivedCategory.Q.obj P) ≫
        U.map (L.mapDerivedCategoryFactors.hom.app P) ≫
          δ.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
        N.mapDerivedCategory.map (ε.app P) ≫
          N.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P)) ∧
      ∀ e' : T ⋙ N.mapDerivedCategory ⟶ L.mapDerivedCategory ⋙ U,
        (∀ P, good P → e'.app (DerivedCategory.Q.obj P) ≫
          U.map (L.mapDerivedCategoryFactors.hom.app P) ≫
            δ.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
          N.mapDerivedCategory.map (ε.app P) ≫
            N.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P)) →
        e' = e.hom := by
  let P : ObjectProperty (CochainComplex A ℤ) := good
  let l := P.ι ⋙ DerivedCategory.Q
  let EC := E.mapHomologicalComplex (.up ℤ)
  let LC := L.mapHomologicalComplex (.up ℤ)
  let FC := F.mapHomologicalComplex (.up ℤ)
  let H := LC ⋙ FC ⋙ (DerivedCategory.Q : CochainComplex D ℤ ⥤ _)
  let a : DerivedCategory.Q ⋙ (T ⋙ N.mapDerivedCategory) ⟶ H :=
    Functor.whiskerRight ε N.mapDerivedCategory ≫
      Functor.whiskerLeft EC N.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (NatIso.mapHomologicalComplex c (.up ℤ)).hom DerivedCategory.Q
  let b : DerivedCategory.Q ⋙ (L.mapDerivedCategory ⋙ U) ⟶ H :=
    Functor.whiskerRight L.mapDerivedCategoryFactors.hom U ≫ Functor.whiskerLeft LC δ
  let a' : l ⋙ (T ⋙ N.mapDerivedCategory) ⟶ P.ι ⋙ H := Functor.whiskerLeft P.ι a
  let b' : l ⋙ (L.mapDerivedCategory ⋙ U) ⟶ P.ι ⋙ H := Functor.whiskerLeft P.ι b
  have (K : P.FullSubcategory) : IsIso (a'.app K) := by
    have hK : IsIso (ε.app (P.ι.obj K)) := hε K.obj K.property
    dsimp only [a', a, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance
  have (K : P.FullSubcategory) : IsIso (b'.app K) := by
    have hK : IsIso (δ.app (LC.obj (P.ι.obj K))) := hδ K.obj K.property
    dsimp only [b', b, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance
  have : IsIso a' := NatIso.isIso_of_isIso_app a'
  have : IsIso b' := NatIso.isIso_of_isIso_app b'
  let ff := cochainRepresentativeWhiskering good res (DerivedCategory D)
  let e := ff.preimageIso
    (show ((Functor.whiskeringLeft _ _ _).obj l).obj (T ⋙ N.mapDerivedCategory) ≅
      ((Functor.whiskeringLeft _ _ _).obj l).obj (L.mapDerivedCategory ⋙ U) from
      asIso a' ≪≫ (asIso b').symm)
  have he : Functor.whiskerLeft l e.hom ≫ b' = a' := by
    rw [show Functor.whiskerLeft l e.hom =
      (asIso a' ≪≫ (asIso b').symm).hom from ff.map_preimage _]
    simp
  refine ⟨e, fun K hK ↦ NatTrans.congr_app he ⟨K, hK⟩, ?_⟩
  intro e' he'
  apply ff.map_injective
  apply (cancel_mono b').1
  ext K
  exact (he' K.obj K.property).trans (NatTrans.congr_app he K).symm

/-- The ordinary scalar restriction square and its unique normalized derived lift.
Source: Stacks Project, sites-cohomology.tex, Tag 06YY, and sites-modules.tex,
Tag 03EK; the construction in steps 1 and 3 of the parent node.
(blueprint: lem-pur-clopen-scalar-comparison-descent).

Proof: the ordinary extension is the sheafification of sectionwise scalar tensor.
Restrict its sheafification unit to the component site. The composition functor
from the component pro-etale site is cocontinuous, so this unit remains locally
bijective. The component extension has the same presheaf of tensors, up to the
identity sectionwise identification. The universal property of sheafification
therefore gives a natural isomorphism sending s tensor x to s tensor x. It is
linear over the component target ring. Apply it degreewise to obtain the chain
isomorphism; naturality with differentials and homotopies follows from ordinary
naturality. On the full homotopy subcategory of flat-term K-flat input complexes,
restrict the universal computation counits. These are isomorphisms, both globally
and on the component, by scalar computation and clopen K-flat detection. Together
with the exact restriction localization factors, they conjugate the chain
comparison into an isomorphism of the two derived functors on that subcategory.
The localized resolving subcategory is equivalent to the entire derived category.
Full faithfulness of restriction of natural transformations along this
localization extends the isomorphism and its inverse uniquely. Cancellation of
the same computation isomorphisms gives exactly the representative equation;
faithfulness gives the stated uniqueness. This argument applies to zero modules
and empty components, and uses no flatness of the coefficient maps. -/
theorem clopen_scalar_comparison_descent
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
    : ∃ d : ∀ i, Comparison.{t, u} (j i) @p
        (fun {R S} a ↦ q i (R := R) (S := S) a),
      ∀ i, (d i).sections ∧ (d i).degree ∧ (d i).representative ∧ (d i).unique := by
  classical
  have ho (i : I) := clopen_ordinary_scalar_comparison (j i) @p
    (fun {R S} a ↦ q i (R := R) (S := S) a)
  choose c hs using ho
  have hderived (i : I) {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
      (a : R ⟶ S) := by
    let good (P : CochainComplex (Mods.{t, u} R) ℤ) :=
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
        ∀ k : ℤ, IsFlatOnSite (J := topology X) (R := R) (P.X k)
    have hδ (P : CochainComplex (Mods.{t, u} R) ℤ) (hP : good P) := by
      have hR := clopen_total_tensor_kflat_detection X I Y j hd hc R
      exact computation_isIso (m i) ((rings (j i)).map a) _
        ((hR.2.1 P).mp hP.1 i) (fun k ↦ (hR.1 (P.X k)).mp (hP.2 k) i)
    exact descendComparison (res (j i) R) (res (j i) S)
      (ext (p a)) (ext (q i ((rings (j i)).map a)))
      (extD (p a)) (extD (q i ((rings (j i)).map a)))
      (computationNat (p a)) (computationNat (q i ((rings (j i)).map a)))
      good (models_resolve R) (fun P hP ↦ computation_isIso n a P hP.1 hP.2)
      hδ (c i a)
  choose e he hu using hderived
  let d (i : I) : Comparison.{t, u} (j i) @p
      (fun {R S} a ↦ q i (R := R) (S := S) a) :=
    { ordinary := c i
      chain := fun a ↦ NatIso.mapHomologicalComplex (c i a) (.up ℤ)
      derived := e i }
  refine ⟨d, fun i ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · exact hs i
  · intro R S a P k
    rfl
  · intro R S a P hP hf
    simpa only [computationNat_app] using he i a P ⟨hP, hf⟩
  · intro R S a e' he'
    exact hu i a e' (fun P hP ↦ by
      simpa only [computationNat_app] using he' P hP.1 hP.2)

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
