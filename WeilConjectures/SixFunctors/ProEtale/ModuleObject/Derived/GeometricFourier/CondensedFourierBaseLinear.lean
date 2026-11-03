/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.DualBundlePairing
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierPullback
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GeometricFourier.CondensedBaseLinearIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GeometricFourier.CondensedDatumNaturality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GeometricFourier.CondensedFourierGeometricModel

/-! # Base linearity of the condensed Fourier--Deligne transform

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/prop-base-linear.md
and prop-base-linear.proof.md (blueprint: prop-base-linear).

The natural isomorphism is in both variables on the actual bounded constructible
categories. The final equation uses the specified descent Frobenius on the transform
and the root-normalized signed Tate structures, including negative twists.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier

open PurityTransport

variable (D : WeilConjectures.FiniteFieldDatum.{u})

/-- Geometric base change, with no superfluous finite-type hypothesis on this construction.
Source: def-fd-transform.md, geometric application (blueprint: prop-base-linear). -/
abbrev fiber (X : Over (Spec (.of D.k₀))) : Scheme.{u} :=
  pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The actual first projection to the arithmetic model.
Source: def-fd-transform.md, geometric application (blueprint: prop-base-linear). -/
abbrev projection (X : Over (Spec (.of D.k₀))) : fiber D X ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Base change of an actual morphism of finite-field models.
Source: def-fd-transform.md, geometric application (blueprint: prop-base-linear). -/
abbrev map {X Y : Over (Spec (.of D.k₀))} (f : X ⟶ Y) : fiber D X ⟶ fiber D Y :=
  pullback.map X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    Y.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    f.left (𝟙 _) (𝟙 _) (by simp only [Category.comp_id]; exact f.w.symm) (by simp)

/-- The arithmetic Fourier product with its inherited finite-field model.
Source: def-fd-kernel.md, Fourier square (blueprint: prop-base-linear). -/
abbrev square {S V V' : Over (Spec (.of D.k₀))} (p : V ⟶ S) (p' : V' ⟶ S) :
    Over (Spec (.of D.k₀)) :=
  Over.mk (pullback.fst p.left p'.left ≫ V.hom)

/-- The first Fourier projection as an arithmetic morphism.
Source: def-fd-transform.md, p1 (blueprint: prop-base-linear). -/
def fst {S V V' : Over (Spec (.of D.k₀))} (p : V ⟶ S) (p' : V' ⟶ S) :
    square D p p' ⟶ V :=
  Over.homMk (pullback.fst p.left p'.left) rfl

/-- The second Fourier projection as an arithmetic morphism.
Source: def-fd-transform.md, p2 (blueprint: prop-base-linear). -/
def snd {S V V' : Over (Spec (.of D.k₀))} (p : V ⟶ S) (p' : V' ⟶ S) :
    square D p p' ⟶ V' :=
  Over.homMk (pullback.snd p.left p'.left)
    (by
      change pullback.snd p.left p'.left ≫ V'.hom =
        pullback.fst p.left p'.left ≫ V.hom
      rw [← p'.w, ← Category.assoc, ← pullback.condition, Category.assoc, p.w])

/-- The geometric square is the same fibre product as the literal geometric Fourier square.
Source: def-fd-transform.md, geometric application (blueprint: prop-base-linear).
Proof: apply the field-extension pullback functor to the arithmetic pullback cone.
Pullback preserves limits. Equivalently, the two projections and their compatibility
give the universal lift, uniquely on the two arithmetic and field projections. -/
theorem square_isPullback {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) :
    IsPullback (map D (fst D p p')) (map D (snd D p p')) (map D p) (map D p') := by
  have houter := ((map_properties D (fst D p p') (𝟙 _)).1.flip).paste_vert
    (IsPullback.of_hasPullback p.left p'.left)
  apply IsPullback.of_bot (t := (map_properties D p' (𝟙 _)).1.flip)
  · simpa [map, fst, snd, projection] using houter
  · apply pullback.hom_ext <;> simp [map, fst, snd, Category.assoc]

/-- The middle arithmetic model of the chosen compactification.
Source: def-fd-transform.md, chosen compactification (blueprint: prop-base-linear). -/
abbrev middle {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) : Over (Spec (.of D.k₀)) :=
  Over.mk (c.g ≫ Y.hom)

/-- The arithmetic open immersion of the chosen compactification.
Source: def-fd-transform.md, chosen compactification (blueprint: prop-base-linear). -/
def openMap {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) : X ⟶ middle D c :=
  Over.homMk c.i (by
    change c.i ≫ (c.g ≫ Y.hom) = X.hom
    rw [← Category.assoc, ← c.comm, f.w])

/-- The arithmetic proper morphism of the chosen compactification.
Source: def-fd-transform.md, chosen compactification (blueprint: prop-base-linear). -/
def properMap {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) : middle D c ⟶ Y :=
  Over.homMk c.g rfl

/-- Base change of the chosen arithmetic compactification, with its actual middle scheme.
Source: def-fd-transform.md, geometric application (blueprint: prop-base-linear). -/
def compactification {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) : Compactification (map D f) where
  Z := fiber D (middle D c)
  i := map D (openMap D c)
  g := map D (properMap D c)
  comm := (compactification_properties D c).1
  isProper := (compactification_properties D c).2.1
  isOpenImmersion := (compactification_properties D c).2.2.1

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ambient ordinary condensed coefficient category on the geometric fibre.
Source: def-fd-transform.md, coefficient category (blueprint: prop-base-linear). -/
abbrev category (X : Over (Spec (.of D.k₀))) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (fiber D X)) Ab.{u + 1})
    (condensedRingObj Λ (fiber D X)))

/-- The actual degree-zero arithmetic kernel, with the product's inherited base structure.
Source: def-fd-kernel.md, finite-field application (blueprint: prop-base-linear). -/
def arithmeticKernel {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤)) :=
  letI := Fintype.ofFinite D.k₀
  letI : (pullback p.left p'.left).Over (Spec (.of D.k₀)) := ⟨(square D p p').hom⟩
  condensedFourierKernel Λ D.k₀ p.left p'.left ψ b

/-- Pullback of the arithmetic kernel, placed in degree zero. By pullback composition this
is b-geometric-star of the same Artin--Schreier sheaf, not a new choice of kernel.
Source: def-fd-transform.md, geometric application (blueprint: prop-base-linear). -/
def kernel {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤)) : category D Λ (square D p p') :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((upperStar Λ (projection D (square D p p'))).obj (arithmeticKernel D Λ p p' ψ b))

/-- The same Fourier formula on the geometric Cartesian cone, with its base-changed
compactification. square_isPullback identifies this with the literal-product definition;
exact pullback composition identifies kernel with its prescribed geometric pairing kernel.
Source: def-fd-transform.md, geometric application (blueprint: prop-base-linear). -/
def transform {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤))
    (c : Compactification (pullback.snd p.left p'.left)) (r : ℤ) :
    category D Λ V ⥤ category D Λ V' :=
  (upperStar Λ (map D (fst D p p'))).leftDerivedFunctor ⋙
    tensorRight (kernel D Λ p p' ψ b) ⋙
    rightDerivedLowerShriekOfCompactification Λ (compactification D (f := snd D p p') c) ⋙
    shiftFunctor _ r


/-- Tensor on the right by a complex pulled back from the base, as a functor in that
base complex and in the other tensor factor. This is the existing curried derived tensor.
Source: prop-base-linear.md, main formula (blueprint: prop-base-linear). -/
def baseTensor {S V : Over (Spec (.of D.k₀))} (p : V ⟶ S) :
    ConstantModelBoundedConstructible Λ (fiber D S) ⥤
      (category D Λ V ⥤ category D Λ V) :=
  (constantModelBoundedConstructible Λ (fiber D S)).ι ⋙
    (upperStar Λ (map D p)).leftDerivedFunctor ⋙ (curriedTensor (category D Λ V)).flip

set_option Elab.async false in
set_option maxHeartbeats 400000 in -- Kernel checking the natural functor comparisons.
end AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier

namespace AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier

private theorem unitLinearity
    {C D B : Type*} [Category C] [Category D] [Category B]
    [MonoidalCategory C] [MonoidalCategory D]
    (P : ObjectProperty C) (hP : P (𝟙_ C))
    (Q : B ⥤ C) (Q' : B ⥤ D) (F : C ⥤ D)
    (e : Q ⋙ (curriedTensor C).flip ⋙ (Functor.whiskeringRight _ _ _).obj F ⋙
        (Functor.whiskeringLeft _ _ _).obj P.ι ≅
      Q' ⋙ (curriedTensor D).flip ⋙ (Functor.whiskeringLeft _ _ _).obj F ⋙
        (Functor.whiskeringLeft _ _ _).obj P.ι) :
    Nonempty (Q ⋙ F ≅ Q' ⋙ (curriedTensor D).flip ⋙
      (evaluation _ _).obj (F.obj (𝟙_ C))) := by
  let K₀ : P.FullSubcategory := ⟨𝟙_ C, hP⟩
  let unitIso : (curriedTensor C).flip ⋙ (evaluation _ _).obj (𝟙_ C) ≅ 𝟭 C :=
    NatIso.ofComponents (fun M ↦ λ_ M) (fun f ↦ leftUnitor_naturality f)
  exact ⟨Functor.isoWhiskerRight (Functor.isoWhiskerLeft Q unitIso.symm) F ≪≫
    Functor.isoWhiskerRight e ((evaluation _ _).obj K₀)⟩

private instance fiberLocallyNoetherian (D : WeilConjectures.FiniteFieldDatum.{u})
    (X : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X.hom] :
    IsLocallyNoetherian (fiber D X) :=
  LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))

private instance fiberCompactSpace (D : WeilConjectures.FiniteFieldDatum.{u})
    (X : Over (Spec (.of D.k₀))) [QuasiCompact X.hom] :
    CompactSpace (fiber D X) :=
  QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))

/-- Base linearity, its unit specialization, and every integral Tate twist, with the
same isomorphism respecting the specified Weil data. The three models and bundle data
are arithmetic; fiber, map and transform take their geometric base changes. No triviality
of the bundle, positive rank, nonzero complex, or chosen primitive root is assumed.

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-fourier-inversion/sk-thm-inversion/prop-base-linear.md, all clauses
(blueprint: prop-base-linear).

Proof, following the six DAG steps.
1. For pi = p p1 = p' p2, monoidal pullback and its compositor identify
   p1*(K tensor p*N) with p1*K tensor p2*p'*N.
2. Tensor with the prescribed arithmetic-descent kernel and use associativity and
   symmetry to place p2*p'*N last. These are the existing derived tensor constraints.
3. The first factor is bounded constructible, since the kernel is lisse rank one
   (prop-kernel-lisse). The second factor has finite Tor amplitude, since E is a field.
   Apply clause (5) of prop-functor-package to the separated finite-type second projection.
4. Commute the rank shift with tensor. Expanding def-fd-transform identifies the two
   sides. Each constituent is natural in both arguments, giving the bifunctor isomorphism.
5. Specialize K to the coefficient unit and compose with its left unitor. This gives
   the natural isomorphism in clause (1), with no choice of a basis of the unit.
6. By lem-fd-tate-twist-pullback the specified E(m) on either bundle is the pullback
   of E_S(m), for all integers m. Nonnegative powers use root-normalized tensor maps;
   negative powers use inverse transposes under evaluation. Substitute N=E_S(m) in
   step 4. The root pullback comparisons intertwine the actual Tate Weil data.
   The coherence/equivariance of prop-functor-package makes reassociation, projection
   and shift commute with Frobenius. Expanding transformDatum and tensorDatum gives
   exactly the final displayed morphism equation; hence this same isomorphism is a
   Weil isomorphism. In the Lean reduction the two unfinished compatibility arguments
   are fourier_tate_kernel_comparison and fourier_tate_support_comparison. Whisker the
   first comparison with compact support and shift, use supportPartDatum_natural to
   transport its Weil square, and compose with the second comparison and its square.
   The chosen arithmetic compactification gives the actual geometric model. -/
theorem condensedFourier_base_linear
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D.p)]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {S V V' : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (p : V ⟶ S) (p' : V' ⟶ S) (r : ℕ)
    (b : Γ(pullback p.left p'.left, ⊤)) (bundle : DualBundlePairing p.left p'.left r b)
    (ψ : AddChar D.k₀ (MonObj.Γ (Coefficient.rational E |>.obj ell)))
    (c : Compactification (pullback.snd p.left p'.left)) :
    Nonempty (
      baseTensor D (Coefficient.rational E |>.obj ell) p ⋙
          (Functor.whiskeringRight _ _ _).obj
            (transform D (Coefficient.rational E |>.obj ell) p p' ψ b c (r : ℤ)) ⋙
          (Functor.whiskeringLeft _ _ _).obj
            (constantModelBoundedConstructible
              (Coefficient.rational E |>.obj ell) (fiber D V)).ι ≅
      baseTensor D (Coefficient.rational E |>.obj ell) p' ⋙
          (Functor.whiskeringLeft _ _ _).obj
            (transform D (Coefficient.rational E |>.obj ell) p p' ψ b c (r : ℤ)) ⋙
          (Functor.whiskeringLeft _ _ _).obj
            (constantModelBoundedConstructible
              (Coefficient.rational E |>.obj ell) (fiber D V)).ι) ∧
    Nonempty (
      (constantModelBoundedConstructible
          (Coefficient.rational E |>.obj ell) (fiber D S)).ι ⋙
        (upperStar (Coefficient.rational E |>.obj ell)
          (map D p)).leftDerivedFunctor ⋙
        transform D (Coefficient.rational E |>.obj ell) p p' ψ b c (r : ℤ) ≅
      baseTensor D (Coefficient.rational E |>.obj ell) p' ⋙
        (evaluation _ _).obj
          ((transform D (Coefficient.rational E |>.obj ell) p p' ψ b c (r : ℤ)).obj (𝟙_ _))) ∧
    ∀ m : ℤ, ∃ e :
      (constantModelBoundedConstructible
          (Coefficient.rational E |>.obj ell) (fiber D V)).ι ⋙
        twist D ell E V m ⋙
        transform D (Coefficient.rational E |>.obj ell) p p' ψ b c (r : ℤ) ≅
      (constantModelBoundedConstructible
          (Coefficient.rational E |>.obj ell) (fiber D V)).ι ⋙
        transform D (Coefficient.rational E |>.obj ell) p p' ψ b c (r : ℤ) ⋙
        twist D ell E V' m,
      ∀ (K : ConstantModelBoundedConstructible
          (Coefficient.rational E |>.obj ell) (fiber D V))
        (φ : (StrictWeilCondensed.action (Coefficient.rational E |>.obj ell)
          (StrictWeilCondensed.modelFrobenius D V)).obj K.obj ≅ K.obj),
        (StrictWeilCondensed.action (Coefficient.rational E |>.obj ell)
            (StrictWeilCondensed.modelFrobenius D V')).map (e.hom.app K) ≫
          (StrictWeilCondensed.tensorDatum (Coefficient.rational E |>.obj ell)
            (StrictWeilCondensed.modelFrobenius D V')
            (transformDatum D (Coefficient.rational E |>.obj ell)
              p p' ψ b c (r : ℤ) K.obj φ)
            (StrictWeilCondensed.tateDatum ell (.rational E)
              (StrictWeilCondensed.modelFrobenius D V') m)).hom =
        (transformDatum D (Coefficient.rational E |>.obj ell)
          p p' ψ b c (r : ℤ) ((twist D ell E V m).obj K.obj)
          (StrictWeilCondensed.tensorDatum (Coefficient.rational E |>.obj ell)
            (StrictWeilCondensed.modelFrobenius D V) φ
            (StrictWeilCondensed.tateDatum ell (.rational E)
              (StrictWeilCondensed.modelFrobenius D V) m))).hom ≫
          e.hom.app K := by
  let := PadicAlgCl.normedFieldOfAlgebra ell E
  let Λ := (Coefficient.rational E).obj ell
  obtain ⟨e₀⟩ := baseLinearIso D ell E p p' r b bundle ψ c
  refine ⟨⟨e₀⟩, ?_, ?_⟩
  · exact unitLinearity
      (P := constantModelBoundedConstructible Λ (fiber D V))
      (hP := by
        rw [← (adicConstructibilityPredicateComparison ell _ Λ (.continuous E)).2]
        exact boundedConstructible_tensorUnit Λ (fiber D V))
      (C := category D Λ V)
      (D := category D Λ V')
      (B := (constantModelBoundedConstructible Λ (fiber D S)).FullSubcategory)
      (Q := (constantModelBoundedConstructible Λ (fiber D S)).ι ⋙
        (upperStar Λ (map D p)).leftDerivedFunctor)
      (Q' := (constantModelBoundedConstructible Λ (fiber D S)).ι ⋙
        (upperStar Λ (map D p')).leftDerivedFunctor)
      (F := transform D Λ p p' ψ b c (r : ℤ)) e₀
  · intro m
    have : LocallyOfFiniteType (p'.left ≫ S.hom) := by rw [p'.w]; infer_instance
    have : LocallyOfFiniteType p'.left := locallyOfFiniteType_of_comp p'.left S.hom
    have : QuasiCompact (p'.left ≫ S.hom) := by rw [p'.w]; infer_instance
    have : QuasiCompact p'.left := QuasiCompact.of_comp p'.left S.hom
    have : LocallyOfFiniteType (square D p p').hom := by dsimp [square]; infer_instance
    have : QuasiCompact (square D p p').hom := by dsimp [square]; infer_instance
    obtain ⟨e₁, h₁⟩ := fourier_tate_kernel_comparison D ell E p p' ψ b m
    obtain ⟨e₂, h₂⟩ := fourier_tate_support_comparison D ell E p p' ψ b c (r : ℤ) m
    have hsq : (snd D p p').left = pullback.snd p.left p'.left := by
      rfl
    cases hsq
    let T : category D Λ (square D p p') ⥤ category D Λ V' :=
      supportPart D Λ (f := snd D p p') c (r : ℤ)
    let e := Functor.isoWhiskerRight e₁ T ≪≫ e₂
    refine ⟨e, ?_⟩
    intro K φ
    let G : category D Λ V' ⥤ category D Λ V' :=
      StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D V')
    have hn := supportPartDatum_natural D Λ (f := snd D p p') c (r : ℤ)
      _ _ (e₁.hom.app K) (h₁ K φ)
    have hn' := hn
    simp only [Functor.comp_obj] at hn'
    dsimp [e]
    change G.map (T.map (e₁.hom.app K) ≫ e₂.hom.app K) ≫ _ = _
    have h₂' := h₂ K φ
    change G.map (e₂.hom.app K) ≫ _ = _ at h₂'
    rw [Functor.map_comp, Category.assoc, h₂', ← Category.assoc]
    have hdef :
        transformDatum D Λ p p' ψ b c (r : ℤ)
            ((twist D ell E V m).obj K.obj)
            (StrictWeilCondensed.tensorDatum Λ
              (StrictWeilCondensed.modelFrobenius D V) φ
              (StrictWeilCondensed.tateDatum ell (.rational E)
                (StrictWeilCondensed.modelFrobenius D V) m)) =
          supportPartDatum D Λ (f := snd D p p') c (r : ℤ)
            ((kernelPart D Λ p p' ψ b).obj ((twist D ell E V m).obj K.obj))
            (kernelPartDatum D Λ p p' ψ b ((twist D ell E V m).obj K.obj)
              (StrictWeilCondensed.tensorDatum Λ
                (StrictWeilCondensed.modelFrobenius D V) φ
                (StrictWeilCondensed.tateDatum ell (.rational E)
                  (StrictWeilCondensed.modelFrobenius D V) m))) := by
      rfl
    rw [hdef]
    simpa [G, T, Category.assoc] using
      congrArg (fun q ↦ q ≫ e₂.hom.app K) hn'

end AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier
