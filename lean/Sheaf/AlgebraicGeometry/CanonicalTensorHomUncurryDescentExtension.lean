/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem extendNormalizedValues
    {D : Type*} [Category D] [MonoidalCategory D] (H : Dᵒᵖ × D ⥤ D)
    {I : Type*} (A B C : I → D)
    (n : ∀ i, A i ⟶ H.obj (op (B i), C i))
    (v : ∀ i, A i ⊗ B i ⟶ C i)
    (cover : ∀ (K L M : D) (f : K ⟶ H.obj (op L, M)),
      ∃ (i : I) (a : A i ≅ K) (b : B i ≅ L) (c : C i ≅ M),
        n i = a.hom ≫ f ≫ H.map (b.hom.op, c.inv))
    (coherent : ∀ (i j : I) (a : A i ≅ A j) (b : B i ≅ B j) (c : C i ≅ C j),
      n i = a.hom ≫ n j ≫ H.map (b.hom.op, c.inv) →
        v i = (a.hom ⊗ₘ b.hom) ≫ v j ≫ c.inv) :
    ∃ s : ∀ K L M : D, (K ⟶ H.obj (op L, M)) → (K ⊗ L ⟶ M),
      (∀ i, s (A i) (B i) (C i) (n i) = v i) ∧
      ∀ (K K' L L' M M' : D) (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
        (f : K ⟶ H.obj (op L, M)),
        s K' L' M' (a.hom ≫ f ≫ H.map (b.hom.op, c.hom)) =
          (a.hom ⊗ₘ b.hom) ≫ s K L M f ≫ c.hom := by
  classical
  let R (K L M : D) (f : K ⟶ H.obj (op L, M)) (g : K ⊗ L ⟶ M) : Prop :=
    ∃ (i : I) (a : A i ≅ K) (b : B i ≅ L) (c : C i ≅ M),
      n i = a.hom ≫ f ≫ H.map (b.hom.op, c.inv) ∧
        v i = (a.hom ⊗ₘ b.hom) ≫ g ≫ c.inv
  have hcover (K L M : D) (f : K ⟶ H.obj (op L, M)) : ∃ g, R K L M f g := by
    obtain ⟨i, a, b, c, hi⟩ := cover K L M f
    refine ⟨(a.inv ⊗ₘ b.inv) ≫ v i ≫ c.hom, i, a, b, c, hi, ?_⟩
    simp [← Category.assoc]
    simp [Category.assoc]
  have huniq (K L M : D) (f : K ⟶ H.obj (op L, M))
      (g g' : K ⊗ L ⟶ M) (hg : R K L M f g) (hg' : R K L M f g') : g = g' := by
    obtain ⟨i, a, b, c, hi, hv⟩ := hg
    obtain ⟨j, a', b', c', hj, hv'⟩ := hg'
    have hn : n i = (a ≪≫ a'.symm).hom ≫ n j ≫
        H.map ((b ≪≫ b'.symm).hom.op, (c ≪≫ c'.symm).inv) := by
      rw [hj, hi]
      simp [Category.assoc, ← H.map_comp, ← op_comp]
    have he := coherent i j (a ≪≫ a'.symm) (b ≪≫ b'.symm) (c ≪≫ c'.symm) hn
    rw [hv, hv'] at he
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv] at he
    have he' : (a.hom ⊗ₘ b.hom) ≫ g ≫ c.inv =
        (a.hom ⊗ₘ b.hom) ≫ g' ≫ c.inv := by
      simpa [Category.assoc, ← tensorHom_comp_tensorHom] using he
    exact (cancel_epi (a.hom ⊗ₘ b.hom)).1 ((cancel_mono c.inv).1
      (by simpa only [← Category.assoc] using he'))
  let s (K L M : D) (f : K ⟶ H.obj (op L, M)) := (hcover K L M f).choose
  have hs (K L M : D) (f : K ⟶ H.obj (op L, M)) : R K L M f (s K L M f) :=
    (hcover K L M f).choose_spec
  refine ⟨s, ?_, ?_⟩
  · intro i
    apply huniq _ _ _ _ _ _ (hs _ _ _ _)
    refine ⟨i, Iso.refl _, Iso.refl _, Iso.refl _, ?_, ?_⟩
    · change n i = 𝟙 _ ≫ n i ≫ H.map (𝟙 (op (B i), C i))
      simp
    · simp
  · intro K K' L L' M M' a b c f
    apply huniq _ _ _ _ _ _ (hs _ _ _ _)
    obtain ⟨i, d, e, k, hn, hv⟩ := hs K L M f
    refine ⟨i, d ≪≫ a.symm, e ≪≫ b.symm, k ≪≫ c, ?_, ?_⟩
    · rw [hn]
      simp [Category.assoc, ← H.map_comp, ← op_comp]
    · rw [hv]
      simp [Category.assoc, ← tensorHom_comp_tensorHom]

set_option maxHeartbeats 1000000 in
-- Elaborating the two sheaf K-flat resolutions requires a larger heartbeat budget.
private theorem normalizedInput_exists (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K L M : schemeDerivedCategory X)
    (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X)
      X.sheaf).obj (op L, M)) :
    ∃ (P Lc Mc : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (_ : P.IsKFlat) (a : DerivedCategory.Q.obj P ≅ K)
      (b : DerivedCategory.Q.obj Lc ≅ L) (c : DerivedCategory.Q.obj Mc ≅ M)
      (φ : P ⟶ homComplex (R := X.sheaf) Lc
        ((schemeHomKInjectiveResolution X).obj Mc)),
      DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X Lc Mc).inv =
        a.hom ≫ f ≫ (derivedInternalHom (Opens.grothendieckTopology X)
          X.sheaf).map (b.hom.op, c.inv) := by
  classical
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let Q := DerivedCategory.Q.{w} (C := C)
  let H := derivedInternalHom (Opens.grothendieckTopology X) X.sheaf
  have : IsGrothendieckAbelian.{u} C := SheafOfModules.isGrothendieckAbelian _
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (Q.objPreimage K)
  obtain ⟨Lc, l, hL, _, hl, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (Q.objPreimage L)
  have : IsIso (Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have : IsIso (Q.map l) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ l).2 hl
  let a : Q.obj P ≅ K := asIso (Q.map p) ≪≫ Q.objObjPreimageIso K
  let b : Q.obj Lc ≅ L := asIso (Q.map l) ≪≫ Q.objObjPreimageIso L
  let Mc := Q.objPreimage M
  let c : Q.obj Mc ≅ M := Q.objObjPreimageIso M
  let I := (schemeHomKInjectiveResolution X).obj Mc
  have : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} C Mc
  have : (homComplex (R := X.sheaf) Lc I).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlat (R := X.sheaf) Lc I hL
  let j := schemeDerivedInternalHomResolutionIso X Lc Mc
  let g : Q.obj P ⟶ H.obj (op (Q.obj Lc), Q.obj Mc) :=
    a.hom ≫ f ≫ H.map (b.hom.op, c.inv)
  let q := HomotopyCategory.quotient C (.up ℤ)
  let d := DerivedCategory.quotientCompQhIso.{w} C
  obtain ⟨v, hv⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    (q.obj P) (homComplex (R := X.sheaf) Lc I)).surjective
      ((d.app P).hom ≫ g ≫ j.hom ≫ (d.app _).inv)
  obtain ⟨φ, hφ⟩ := q.map_surjective v
  have hφQ : Q.map φ = g ≫ j.hom := by
    have hn := DerivedCategory.quotientCompQhIso_hom_naturality φ
    rw [hφ, hv] at hn
    change ((d.app P).hom ≫ g ≫ j.hom ≫ (d.app _).inv) ≫
      (d.app _).hom = (d.app P).hom ≫ Q.map φ at hn
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hn
    exact ((cancel_epi (d.app P).hom).1 hn).symm
  refine ⟨P, Lc, Mc, hP, a, b, c, φ, ?_⟩
  change Q.map φ ≫ j.inv = g
  rw [hφQ]
  simp

private structure NormalizedInput (X : Scheme.{u}) where
  P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ
  L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ
  M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ
  hP : P.IsKFlat
  φ : P ⟶ homComplex (R := X.sheaf) L ((schemeHomKInjectiveResolution X).obj M)

/-- Extend representative-normalized values to an isomorphism-compatible family.
The new family agrees with the given one only on the specified chain inputs;
the given family need not be compatible on arbitrary derived objects.
Source: Stacks Project, cohomology.tex, Tag 08DJ (functoriality on representatives),
and sites-cohomology.tex, Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-descent-extension).

Proof: Choose complex representatives of the three derived objects and K-flat
resolutions of the first two. Maps into Hom(Lc,I(M)) lift to chain maps modulo
homotopy because that Hom complex is K-injective. Evaluate t on these chain
inputs and transport the answer along the chosen representative isomorphisms.
The normalization hypothesis expresses every value used here as localized
componentwise evaluation, so it supplies homotopy invariance and compatibility
under changes of the chain lift. For changes of representatives, compute roofs
on common K-flat resolutions and K-injective targets. On each tensor summand,
the sheaf tensor-Hom adjunction and the Hom projections commute with pre- and
postcomposition. The coproduct universal property gives the comparison identity
for evaluation. Localize it, use the naturality of the tensor model map, Hom
resolution comparison and resolution augmentation, and cancel the invertible
quasi-isomorphisms. This proves independence of representatives and the asserted
transport identity for arbitrary derived isomorphisms. If the input already has
the form in the agreement clause, use its given K-flat P. Resolve its possibly
non-K-flat L; both P tensor - and Hom(-,I(M)) invert this resolution and evaluation
commutes with it. Cancellation and ht give precisely agreement with t on that
input. The construction does not retain arbitrary values of t elsewhere. Identity
isomorphisms, zero inputs and zero complexes satisfy the same comparison; no
boundedness or naturality of the given t outside its normalized inputs is used. -/
theorem exists_tensorHomUncurry_descent_extension (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M))
    (ht : ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlat →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M) :
    letI := schemeDerivedTensorMonoidal X
    ∃ s : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      (∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlat →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          s (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv)) ∧
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      s K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ s K L M f ≫ c.hom := by
  classical
  let := schemeDerivedTensorMonoidal X
  let H := derivedInternalHom (Opens.grothendieckTopology X) X.sheaf
  let A (i : NormalizedInput X) := DerivedCategory.Q.obj i.P
  let B (i : NormalizedInput X) := DerivedCategory.Q.obj i.L
  let C (i : NormalizedInput X) := DerivedCategory.Q.obj i.M
  let n (i : NormalizedInput X) : A i ⟶ H.obj (op (B i), C i) :=
    DerivedCategory.Q.map i.φ ≫ (schemeDerivedInternalHomResolutionIso X i.L i.M).inv
  let v (i : NormalizedInput X) : A i ⊗ B i ⟶ C i :=
    pullbackTensorModelMap X i.P i.L ≫
      DerivedCategory.Q.map (schemeTensorHomUncurry X i.P i.L i.M i.φ) ≫
        schemeHomResolutionInverse X i.M
  have cover (K L M : schemeDerivedCategory X) (f : K ⟶ H.obj (op L, M)) :
      ∃ (i : NormalizedInput X) (a : A i ≅ K) (b : B i ≅ L) (c : C i ≅ M),
        n i = a.hom ≫ f ≫ H.map (b.hom.op, c.inv) := by
    obtain ⟨P, Lc, Mc, hP, a, b, c, φ, hφ⟩ := normalizedInput_exists X K L M f
    exact ⟨⟨P, Lc, Mc, hP, φ⟩, a, b, c, hφ⟩
  have coherent (i j : NormalizedInput X) (a : A i ≅ A j) (b : B i ≅ B j)
      (c : C i ≅ C j) (h : n i = a.hom ≫ n j ≫ H.map (b.hom.op, c.inv)) :
      v i = (a.hom ⊗ₘ b.hom) ≫ v j ≫ c.inv := by
    simpa only [v, Category.assoc] using
      tensorHomUncurry_normalized_comparison X i.P i.L i.M j.P j.L j.M
        i.hP j.hP i.φ j.φ a b c (by simpa only [n, Category.assoc] using h)
  obtain ⟨s, hs, hi⟩ := extendNormalizedValues H A B C n v cover coherent
  refine ⟨s, ?_, hi⟩
  intro P L M hP φ
  exact (hs ⟨P, L, M, hP, φ⟩).trans (ht P L M hP φ).symm

end AlgebraicGeometry
