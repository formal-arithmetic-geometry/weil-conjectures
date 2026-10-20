# AlgebraicGeometry.tensorHomUncurry_chain_natural

## Reason

The upstream sync quarantined the Sheaf chain-naturality module because its
IsAcyclicTensorKFlat predicate no longer elaborates against the imported canonical
model. Its sole direct consumer, descent naturality, was quarantined with it.
Both complete proofs already exist in the adopted upstream library, using the
current IsKFlatTensor predicate. Its definition has the same acyclic-total-tensor
condition as the old predicate. Restore the two compatibility import paths by
re-exporting the canonical proofs; attach both nodes to the actual declarations.
This removes duplicate declarations and the incompatible old KFlat dependency.
No adopted-source file or target statement is changed.

Reconciled after returned head d2c797c18: at current sheaf-dag dba334d2528 both
compatibility paths are still quarantined, and the approved re-exports have not
landed. The current canonical proof bodies agree with the archived bodies after
the import-root and K-flat predicate renames. The retry retains those archives,
restores the compatibility files, and compiles both against the current server
build. The delivery tool generates the commit on a fresh sheaf-dag base.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KInjectiveHomComplex

/-! # Naturality on localized chain maps

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-chain-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem hom_model_natural (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L L' M M' : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (b : L' ⟶ L) (c : M ⟶ M') :
    DerivedCategory.Q.map
      ((Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
        (X := (op L, (schemeHomKInjectiveResolution X).obj M))
        (Y := (op L', (schemeHomKInjectiveResolution X).obj M'))
        (b.op, (schemeHomKInjectiveResolution X).map c)) ≫
      (schemeDerivedInternalHomResolutionIso X L' M').inv =
    (schemeDerivedInternalHomResolutionIso X L M).inv ≫
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).map ((DerivedCategory.Q.map b).op, DerivedCategory.Q.map c) := by
  have : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  let e := Localization.fac
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := X.sheaf)) ⋙ DerivedCategory.Q)
    (derivedInternalHom_inverts (Opens.grothendieckTopology X) X.sheaf
      (CochainComplex.kInjectiveResolutionFunctor.{u}
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      (CochainComplex.toKInjectiveResolution.{u} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)
  exact e.inv.naturality (X := (op L, M)) (Y := (op L', M')) (b.op, c)

private theorem chain_lift
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P I : CochainComplex C ℤ) [I.IsKInjective]
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) :
    ∃ φ : P ⟶ I, DerivedCategory.Q.map φ = f := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj P) I).surjective
      ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ f ≫
        (DerivedCategory.quotientCompQhIso C).inv.app I)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨φ, ?_⟩
  have h := congrArg (fun k ↦ (DerivedCategory.quotientCompQhIso C).inv.app P ≫ k ≫
    (DerivedCategory.quotientCompQhIso C).hom.app I) hg
  simpa [DerivedCategory.quotientCompQhIso_hom_naturality, Category.assoc] using h

private theorem kflat_arrow_rep (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : DerivedCategory.Q.obj P' ⟶ DerivedCategory.Q.obj P) :
    ∃ (F F' : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (g : F' ⟶ F) (e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj P)
      (e' : DerivedCategory.Q.obj F' ≅ DerivedCategory.Q.obj P'),
      F.IsAcyclicTensorKFlat ∧ F'.IsAcyclicTensorKFlat ∧ e'.hom ≫ a = DerivedCategory.Q.map g ≫ e.hom := by
  obtain ⟨F, s, hF, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := X.sheaf) P
  have := hs
  have : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  obtain ⟨R, r, hr, g, hg⟩ := DerivedCategory.right_fac (a ≫ inv (DerivedCategory.Q.map s))
  have := hr
  obtain ⟨F', q, hF', _, hq, _⟩ := CochainComplex.exists_isKFlatResolution (R := X.sheaf) R
  have := hq
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  refine ⟨F, F', q ≫ g, asIso (DerivedCategory.Q.map s),
    asIso (DerivedCategory.Q.map q ≫ DerivedCategory.Q.map r), hF, hF', ?_⟩
  have h := congrArg (fun k ↦ DerivedCategory.Q.map q ≫ DerivedCategory.Q.map r ≫ k ≫
    DerivedCategory.Q.map s) hg
  simpa [Category.assoc] using h

private theorem naturality_transport
    {D : Type*} [Category D] [MonoidalCategory D]
    (H : Dᵒᵖ × D ⥤ D)
    (t : ∀ K L M : D, (K ⟶ H.obj (op L, M)) → (K ⊗ L ⟶ M))
    {K K' L L' M M' P P' N N' I I' : D}
    (eK : P ≅ K) (eK' : P' ≅ K') (eL : N ≅ L) (eL' : N' ≅ L')
    (eM : I ≅ M) (eM' : I' ≅ M')
    (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
    (a₀ : P' ⟶ P) (b₀ : N' ⟶ N) (c₀ : I ⟶ I')
    (ha : eK'.hom ≫ a = a₀ ≫ eK.hom)
    (hb : eL'.hom ≫ b = b₀ ≫ eL.hom)
    (hc : eM.hom ≫ c = c₀ ≫ eM'.hom)
    (hn : ∀ f : P ⟶ H.obj (op N, I),
      t P' N' I' (a₀ ≫ f ≫ H.map (X := (op N, I)) (Y := (op N', I')) (b₀.op, c₀)) =
        (a₀ ⊗ₘ b₀) ≫ t P N I f ≫ c₀)
    (f : K ⟶ H.obj (op L, M))
    (hs : t P N I (eK.hom ≫ f ≫
      H.map (X := (op L, M)) (Y := (op N, I)) (eL.hom.op, eM.inv)) =
      (eK.hom ⊗ₘ eL.hom) ≫ t K L M f ≫ eM.inv)
    (ht : t P' N' I' (eK'.hom ≫ (a ≫ f ≫ H.map (b.op, c)) ≫
      H.map (X := (op L', M')) (Y := (op N', I')) (eL'.hom.op, eM'.inv)) =
      (eK'.hom ⊗ₘ eL'.hom) ≫ t K' L' M' (a ≫ f ≫ H.map (b.op, c)) ≫ eM'.inv) :
    t K' L' M' (a ≫ f ≫ H.map (b.op, c)) =
      (a ⊗ₘ b) ≫ t K L M f ≫ c := by
  have hc' : c ≫ eM'.inv = eM.inv ≫ c₀ := by
    have h := congrArg (fun g ↦ eM.inv ≫ g ≫ eM'.inv) hc
    simpa [Category.assoc] using h
  have hm :
      H.map (X := (op L, M)) (Y := (op L', M')) (b.op, c) ≫
        H.map (X := (op L', M')) (Y := (op N', I')) (eL'.hom.op, eM'.inv) =
      H.map (X := (op L, M)) (Y := (op N, I)) (eL.hom.op, eM.inv) ≫
        H.map (X := (op N, I)) (Y := (op N', I')) (b₀.op, c₀) := by
    rw [← H.map_comp, ← H.map_comp]
    congr 1
    ext
    · exact congrArg Quiver.Hom.op hb
    · exact hc'
  have hinput : eK'.hom ≫ (a ≫ f ≫ H.map (X := (op L, M)) (Y := (op L', M')) (b.op, c)) ≫
      H.map (X := (op L', M')) (Y := (op N', I')) (eL'.hom.op, eM'.inv) =
      a₀ ≫ (eK.hom ≫ f ≫
        H.map (X := (op L, M)) (Y := (op N, I)) (eL.hom.op, eM.inv)) ≫
          H.map (X := (op N, I)) (Y := (op N', I')) (b₀.op, c₀) := by
    simp only [Category.assoc]
    rw [← Category.assoc eK'.hom a, ha]
    simp only [Category.assoc]
    rw [hm]
  have h := hn (eK.hom ≫ f ≫
    H.map (X := (op L, M)) (Y := (op N, I)) (eL.hom.op, eM.inv))
  simp only [Category.assoc] at hinput h ht hs
  rw [← hinput, ht, hs] at h
  have hab : (a₀ ⊗ₘ b₀) ≫ (eK.hom ⊗ₘ eL.hom) =
      (eK'.hom ⊗ₘ eL'.hom) ≫ (a ⊗ₘ b) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ha, hb]
  simp only [Category.assoc] at h
  rw [← Category.assoc (a₀ ⊗ₘ b₀), hab] at h
  apply (cancel_epi (eK'.hom ⊗ₘ eL'.hom)).mp
  apply (cancel_mono eM'.inv).mp
  simpa only [Category.assoc, hc'] using h


set_option maxHeartbeats 800000 in
-- The resolution and localization instances need extra elaboration heartbeats.
/-- Componentwise uncurrying is natural on the images of actual chain maps.
The input `f` is an arbitrary derived morphism; the three variable maps are chain maps.
Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-chain-naturality).

Proof: Represent the derived images of a and b by chain maps between K-flat
complexes, using right fractions followed by K-flat resolutions of their
sources. The localized quasi-isomorphisms give commuting squares with the
original maps. On these models the Hom complex from the K-flat L-model into
I(M) is K-injective. The bijectivity of Qh on homotopy classes and fullness of
the homotopy quotient lift the transported f to a chain map φ. Naturality of
the fixed internal-Hom factorization identifies the transported input with
the localization of a₀;φ;Hom(b₀,I(c)). Apply ht to this input and to φ, then
use schemeTensorHomUncurry_localized_evaluation for the two explicit evaluation
composites. Finally use hi to transport the equality along the replacement
isomorphisms. Tensor functoriality identifies the source factors, and
cancellation of the tensor of the replacement isomorphisms gives the result.
Only the componentwise localized evaluation remains a separate theorem; the
lifting, replacement squares, factorization naturality and cancellation are
proved here. Identities, zero maps and unbounded complexes require no extra
hypotheses. -/
theorem tensorHomUncurry_chain_natural (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M))
    (ht : ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsAcyclicTensorKFlat →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M)
    (hi : letI := schemeDerivedTensorMonoidal X
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      t K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ t K L M f ≫ c.hom) :
    letI := schemeDerivedTensorMonoidal X
    ∀ (P P' L L' M M' : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (a : P' ⟶ P) (b : L' ⟶ L) (c : M ⟶ M')
      (f : DerivedCategory.Q.obj P ⟶
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M)),
      t (DerivedCategory.Q.obj P') (DerivedCategory.Q.obj L') (DerivedCategory.Q.obj M')
          (DerivedCategory.Q.map a ≫ f ≫
            (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).map ((DerivedCategory.Q.map b).op,
                DerivedCategory.Q.map c)) =
        (DerivedCategory.Q.map a ⊗ₘ DerivedCategory.Q.map b) ≫
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) f ≫
            DerivedCategory.Q.map c := by
  let := schemeDerivedTensorMonoidal X
  intro P P' L L' M M' a b c f
  obtain ⟨F, F', a₀, eP, eP', hF, hF', ha⟩ :=
    kflat_arrow_rep X P P' (DerivedCategory.Q.map a)
  obtain ⟨N, N', b₀, eL, eL', hN, hN', hb⟩ :=
    kflat_arrow_rep X L L' (DerivedCategory.Q.map b)
  have hn (f₀ : DerivedCategory.Q.obj F ⟶
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op (DerivedCategory.Q.obj N), DerivedCategory.Q.obj M)) :
      t (DerivedCategory.Q.obj F') (DerivedCategory.Q.obj N') (DerivedCategory.Q.obj M')
        (DerivedCategory.Q.map a₀ ≫ f₀ ≫
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).map ((DerivedCategory.Q.map b₀).op,
              DerivedCategory.Q.map c)) =
      (DerivedCategory.Q.map a₀ ⊗ₘ DerivedCategory.Q.map b₀) ≫
        t (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj N) (DerivedCategory.Q.obj M) f₀ ≫
          DerivedCategory.Q.map c := by
    have : IsGrothendieckAbelian.{u}
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
      SheafOfModules.isGrothendieckAbelian _
    have : ((schemeHomKInjectiveResolution X).obj M).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M
    have : (homComplex (R := X.sheaf) N
        ((schemeHomKInjectiveResolution X).obj M)).IsKInjective :=
      CochainComplex.isKInjective_homComplex_of_isKFlat N _ hN
    obtain ⟨φ, hφ⟩ := chain_lift F
      (homComplex (R := X.sheaf) N ((schemeHomKInjectiveResolution X).obj M))
      (f₀ ≫ (schemeDerivedInternalHomResolutionIso X N M).hom)
    have hf : DerivedCategory.Q.map φ ≫
        (schemeDerivedInternalHomResolutionIso X N M).inv = f₀ := by
      rw [hφ]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    let ψ : F' ⟶ homComplex (R := X.sheaf) N'
        ((schemeHomKInjectiveResolution X).obj M') :=
      a₀ ≫ φ ≫ (Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
        (X := (op N, (schemeHomKInjectiveResolution X).obj M))
        (Y := (op N', (schemeHomKInjectiveResolution X).obj M'))
        (b₀.op, (schemeHomKInjectiveResolution X).map c)
    have hψ : DerivedCategory.Q.map ψ ≫
        (schemeDerivedInternalHomResolutionIso X N' M').inv =
        DerivedCategory.Q.map a₀ ≫ f₀ ≫
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).map ((DerivedCategory.Q.map b₀).op,
              DerivedCategory.Q.map c) := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      rw [hom_model_natural, ← Category.assoc (DerivedCategory.Q.map φ), hf]
    rw [← hψ, ht F' N' M' hF' ψ, ← hf, ht F N M hF φ]
    exact schemeTensorHomUncurry_localized_evaluation X F F' N N' M M' a₀ b₀ c φ
  exact naturality_transport
    (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf) t eP eP' eL eL'
    (Iso.refl (DerivedCategory.Q.obj M)) (Iso.refl (DerivedCategory.Q.obj M'))
    (DerivedCategory.Q.map a) (DerivedCategory.Q.map b) (DerivedCategory.Q.map c)
    (DerivedCategory.Q.map a₀) (DerivedCategory.Q.map b₀) (DerivedCategory.Q.map c)
    ha hb (by simp) hn f
    (hi _ _ _ _ _ _ eP eL (Iso.refl _) f)
    (hi _ _ _ _ _ _ eP' eL' (Iso.refl _)
      (DerivedCategory.Q.map a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map ((DerivedCategory.Q.map b).op, DerivedCategory.Q.map c)))

end AlgebraicGeometry
```

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Naturality forced by componentwise uncurrying

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-descent-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem derived_arrow_rep
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {A B : DerivedCategory C} (a : A ⟶ B) :
    ∃ (P Q : CochainComplex C ℤ) (g : P ⟶ Q)
      (eP : DerivedCategory.Q.obj P ≅ A) (eQ : DerivedCategory.Q.obj Q ≅ B),
      eP.hom ≫ a = DerivedCategory.Q.map g ≫ eQ.hom := by
  let P := (DerivedCategory.Q (C := C)).objPreimage A
  let Q := (DerivedCategory.Q (C := C)).objPreimage B
  let eP := (DerivedCategory.Q (C := C)).objObjPreimageIso A
  let eQ := (DerivedCategory.Q (C := C)).objObjPreimageIso B
  obtain ⟨R, s, hs, g, hg⟩ := DerivedCategory.right_fac (eP.hom ≫ a ≫ eQ.inv)
  let := hs
  refine ⟨R, Q, g, asIso (DerivedCategory.Q.map s) ≪≫ eP, eQ, ?_⟩
  have h := congrArg (fun f ↦ DerivedCategory.Q.map s ≫ f ≫ eQ.hom) hg
  simpa [Category.assoc] using h

private theorem naturality_transport
    {D : Type*} [Category D] [MonoidalCategory D]
    (H : Dᵒᵖ × D ⥤ D)
    (t : ∀ K L M : D, (K ⟶ H.obj (op L, M)) → (K ⊗ L ⟶ M))
    (hi : ∀ (K K' L L' M M' : D) (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ H.obj (op L, M)),
      t K' L' M' (a.hom ≫ f ≫ H.map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ t K L M f ≫ c.hom)
    {K K' L L' M M' P P' N N' I I' : D}
    (eK : P ≅ K) (eK' : P' ≅ K') (eL : N ≅ L) (eL' : N' ≅ L')
    (eM : I ≅ M) (eM' : I' ≅ M')
    (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
    (a₀ : P' ⟶ P) (b₀ : N' ⟶ N) (c₀ : I ⟶ I')
    (ha : eK'.hom ≫ a = a₀ ≫ eK.hom)
    (hb : eL'.hom ≫ b = b₀ ≫ eL.hom)
    (hc : eM.hom ≫ c = c₀ ≫ eM'.hom)
    (hn : ∀ f : P ⟶ H.obj (op N, I),
      t P' N' I' (a₀ ≫ f ≫ H.map (X := (op N, I)) (Y := (op N', I')) (b₀.op, c₀)) =
        (a₀ ⊗ₘ b₀) ≫ t P N I f ≫ c₀)
    (f : K ⟶ H.obj (op L, M)) :
    t K' L' M' (a ≫ f ≫ H.map (b.op, c)) =
      (a ⊗ₘ b) ≫ t K L M f ≫ c := by
  have hc' : c ≫ eM'.inv = eM.inv ≫ c₀ := by
    have h := congrArg (fun g ↦ eM.inv ≫ g ≫ eM'.inv) hc
    simpa [Category.assoc] using h
  have hm :
      H.map (X := (op L, M)) (Y := (op L', M')) (b.op, c) ≫
        H.map (X := (op L', M')) (Y := (op N', I')) (eL'.hom.op, eM'.inv) =
      H.map (X := (op L, M)) (Y := (op N, I)) (eL.hom.op, eM.inv) ≫
        H.map (X := (op N, I)) (Y := (op N', I')) (b₀.op, c₀) := by
    rw [← H.map_comp, ← H.map_comp]
    congr 1
    ext
    · exact congrArg Quiver.Hom.op hb
    · exact hc'
  have hinput : eK'.hom ≫ (a ≫ f ≫ H.map (X := (op L, M)) (Y := (op L', M')) (b.op, c)) ≫
      H.map (X := (op L', M')) (Y := (op N', I')) (eL'.hom.op, eM'.inv) =
      a₀ ≫ (eK.hom ≫ f ≫
        H.map (X := (op L, M)) (Y := (op N, I)) (eL.hom.op, eM.inv)) ≫
          H.map (X := (op N, I)) (Y := (op N', I')) (b₀.op, c₀) := by
    simp only [Category.assoc]
    rw [← Category.assoc eK'.hom a, ha]
    simp only [Category.assoc]
    rw [hm]
  have h := hn (eK.hom ≫ f ≫
    H.map (X := (op L, M)) (Y := (op N, I)) (eL.hom.op, eM.inv))
  have ht := hi K' P' L' N' M' I' eK' eL' eM'.symm (a ≫ f ≫ H.map (b.op, c))
  have hs := hi K P L N M I eK eL eM.symm f
  dsimp only [Iso.symm_hom] at ht hs
  simp only [Category.assoc] at hinput h ht hs
  rw [← hinput, ht, hs] at h
  have hab : (a₀ ⊗ₘ b₀) ≫ (eK.hom ⊗ₘ eL.hom) =
      (eK'.hom ⊗ₘ eL'.hom) ≫ (a ⊗ₘ b) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ha, hb]
  simp only [Category.assoc] at h
  rw [← Category.assoc (a₀ ⊗ₘ b₀), hab] at h
  apply (cancel_epi (eK'.hom ⊗ₘ eL'.hom)).mp
  apply (cancel_mono eM'.inv).mp
  simpa only [Category.assoc, hc'] using h

/-- The representative localization equation forces three-variable naturality.
Assume also transport along isomorphisms; this is essential when the chosen
derived category has objects which are not literally images of complexes.
No existence of a family, or existence of chain representatives, is asserted here.
Source: Stacks Project, cohomology.tex, Tag 08DJ, naturality of evaluation;
sites-cohomology.tex, Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-descent-naturality).

Proof: Choose K-flat representatives for the four source objects K,K',L,L',
and the functorial K-injective models for M and M'. Represent maps between them
by roofs, using common K-flat resolutions for source denominators. Maps to a
K-injective complex are actual chain maps modulo homotopy. On these models,
restrict the two uncurried chain maps to every total tensor summand. Naturality
of the sheaf tensor-Hom adjunction and of the Hom product projections identifies
both sides with evaluation after precomposition in P and L and postcomposition
in I(M). The coproduct universal property proves equality of the chain maps.
Apply Q and the assumed representative equation to these chain maps. Naturality
of Q's lax tensor map, of the derived Hom localization factorization, and of the
functorial resolution map gives the claimed equality on representatives.
Use the assumed isomorphism transport to cancel the localized quasi-isomorphisms
in the roofs and the representative isomorphisms to obtain the equation for
arbitrary derived maps a,b,c. Homotopy invariance ensures that none of the roof
choices affects the calculation. The identity and zero-map cases obey the same
component equation, without boundedness assumptions. -/
theorem tensorHomUncurry_descent_natural (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M))
    (ht : ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsAcyclicTensorKFlat →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M)
    (hi : letI := schemeDerivedTensorMonoidal X
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      t K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ t K L M f ≫ c.hom) :
    letI := schemeDerivedTensorMonoidal X
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      t K' L' M' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (a ⊗ₘ b) ≫ t K L M f ≫ c := by
  let := schemeDerivedTensorMonoidal X
  have hn := tensorHomUncurry_chain_natural X t ht hi
  intro K K' L L' M M' a b c f
  obtain ⟨P', P, a₀, eK', eK, ha⟩ := derived_arrow_rep a
  obtain ⟨N', N, b₀, eL', eL, hb⟩ := derived_arrow_rep b
  obtain ⟨I, I', c₀, eM, eM', hc⟩ := derived_arrow_rep c
  exact naturality_transport
    (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf) t hi eK eK' eL eL' eM eM'
    a b c (DerivedCategory.Q.map a₀) (DerivedCategory.Q.map b₀) (DerivedCategory.Q.map c₀)
    ha hb hc (hn P P' N N' I I' a₀ b₀ c₀) f

end AlgebraicGeometry
```

## New

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality

/-! Compatibility re-export of the canonical upstream proof.

The upstream theorem uses `CochainComplex.IsKFlatTensor`, the current name for
the acyclic-tensor K-flatness predicate. No duplicate declarations are introduced.
(blueprint: lem-pc-tensor-hom-uncurry-chain-naturality).
-/

@[expose] public section
```

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentNaturality

/-! Compatibility re-export of the canonical upstream proof.

The upstream theorem uses `CochainComplex.IsKFlatTensor`, the current name for
the acyclic-tensor K-flatness predicate. No duplicate declarations are introduced.
(blueprint: lem-pc-tensor-hom-uncurry-descent-naturality).
-/

@[expose] public section
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality | H7 | Restored from quarantine as canonical proof re-export. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentNaturality | unclaimed | Sole quarantined direct consumer; restored as the corresponding upstream re-export. |

No live Lean module imports either quarantined path. The rework cluster contains
exactly these two modules. The upstream descent proof imports upstream chain
naturality, preserving the existing proof route.

## Status

landed 20261020T154619-L-3137164 2026-10-20 (merge of deliver/H7/Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality)
