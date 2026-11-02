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
