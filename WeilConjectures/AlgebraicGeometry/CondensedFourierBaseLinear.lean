/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.FourierTransform.DualBundlePairing
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
import WeilConjectures.SixFunctors.FrobeniusSquareCartesian

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

/-- The base-change square, its composition law, and its Frobenius square.
Source: def-fd-transform.md, base change of the defining square
(blueprint: prop-base-linear).
Proof: the pullback projections define map. Pasting their defining Cartesian squares
cancels the common field-extension square. Functoriality gives composition. Naturality
of id times geometric Frobenius gives the last equality, checked on both projections. -/
theorem map_properties {X Y Z : Over (Spec (.of D.k₀))} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsPullback (projection D X) (map D f) f.left (projection D Y) ∧
    map D (f ≫ g) = map D f ≫ map D g ∧
    (StrictWeil.modelFrobenius D X).hom ≫ map D f =
      map D f ≫ (StrictWeil.modelFrobenius D Y).hom := by
  let _ := Fintype.ofFinite D.k₀
  let B := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have hpb : IsPullback (projection D X) (map D f) f.left (projection D Y) := by
    let e := pullback.congrHom f.w.symm rfl ≪≫
      (pullbackRightPullbackFstIso Y.hom B f.left).symm
    apply IsPullback.of_iso_pullback ⟨by simp [map, B]⟩ e
    · simp [e, B]
    · apply pullback.hom_ext <;> simp [e, map, B]
  refine ⟨hpb, ?_, ?_⟩
  · apply pullback.hom_ext <;> simp [map]
  · exact WeilConjectures.FiniteFieldDatum.frobenius_square_cartesian D X Y f |>.2.2.2.2.1

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
  · apply pullback.hom_ext <;> simp [map, fst, snd, Category.assoc, pullback.condition]

/-- The canonical identification of the base-changed arithmetic cone with the literal
geometric fibre product, defined by its two projections.
Source: prop-base-linear.proof.md, Fourier square (blueprint: prop-base-linear). -/
def productComparison {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) :
    fiber D (square D p p') ≅ pullback (map D p) (map D p') :=
  (square_isPullback D p p').isoPullback

/-- The actual base-changed pairing on the literal geometric Fourier product.
Source: prop-base-linear.md, transform of def-fd-transform
(blueprint: prop-base-linear). -/
def literalPairing {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (b : Γ(pullback p.left p'.left, ⊤)) :
    Γ(pullback (map D p) (map D p'), ⊤) :=
  ((productComparison D p p').inv ≫ projection D (square D p p')).appTop b

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

/-- The defining properties needed by the concrete base-changed compactification.
Source: def-fd-transform.md, compactification and geometric application
(blueprint: prop-base-linear).
Proof: the first clause is the image of c.comm under base change. The base-change
squares in map_properties transport properness and the open immersion from c.
The last clause is naturality of Frobenius for the open immersion; both horizontal
maps are isomorphisms, so its commuting square is Cartesian. -/
theorem compactification_properties {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) :
    map D f = map D (openMap D c) ≫ map D (properMap D c) ∧
    IsProper (map D (properMap D c)) ∧ IsOpenImmersion (map D (openMap D c)) ∧
    IsPullback (StrictWeil.modelFrobenius D X).hom (map D (openMap D c))
      (map D (openMap D c)) (StrictWeil.modelFrobenius D (middle D c)).hom := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : f = openMap D c ≫ properMap D c :=
      Over.OverMorphism.ext c.comm
    exact (congrArg (map D) hc).trans
      (map_properties D (openMap D c) (properMap D c)).2.1
  · exact MorphismProperty.of_isPullback (P := @IsProper)
      (map_properties D (properMap D c) (𝟙 _)).1 c.isProper
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (map_properties D (openMap D c) (𝟙 _)).1 c.isOpenImmersion
  · exact IsPullback.of_horiz_isIso
      ⟨(map_properties D (openMap D c) (𝟙 _)).2.2⟩

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

/-- The actual Frobenius diagram on this compactification. No lift is supplied as a hypothesis.
Source: def-fd-transform.md and prop-base-linear.md, Weil clause
(blueprint: prop-base-linear). -/
def frobeniusSquare {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) :
    CompactificationReindexing.Square (compactification D c) (compactification D c)
      (StrictWeil.modelFrobenius D X).hom (StrictWeil.modelFrobenius D Y).hom where
  middle := (StrictWeil.modelFrobenius D (middle D c)).hom
  openSquare := (compactification_properties D c).2.2.2
  properSquare := ⟨(map_properties D (properMap D c) (𝟙 Y)).2.2⟩

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

/-- Descent of an arithmetic module to the fibre under a map fixing its projection.
This generic construction keeps the module pullback comparison independent of the
size of the geometric Fourier square.
Source: def-fd-transform.md, arithmetic descent (blueprint: prop-base-linear). -/
def modelDescent {X Y : Scheme.{u}} (π : X ⟶ Y) (g : X ≅ X)
    (h : g.hom ≫ π = π)
    (A : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (StrictWeil.action Λ g).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ π).obj A)) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ π).obj A) :=
  ((upperStar Λ g.hom).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (((upperStarComp Λ g.hom π).app A).symm ≪≫
        eqToIso (congrArg (fun t ↦ (upperStar Λ t).obj A) h))

/-- The normalized descent datum on the geometric kernel, obtained by composition of
ordinary module pullbacks and the identity Frobenius followed by the model projection.
Source: def-fd-transform.md and prop-base-linear.md, Weil clause
(blueprint: prop-base-linear). -/
def kernelDatum {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤)) :
    (StrictWeil.action Λ (StrictWeil.modelFrobenius D (square D p p'))).obj
      (kernel D Λ p p' ψ b) ≅ kernel D Λ p p' ψ b := by
  letI := Fintype.ofFinite D.k₀
  exact modelDescent Λ (projection D (square D p p'))
    (StrictWeil.modelFrobenius D (square D p p'))
    (D.galoisMap_projections (square D p p').hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).1
    (arithmeticKernel D Λ p p' ψ b)

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


/-- The landed condensedFourierTransform applied to the geometric fibres. This is only
an instantiation of that declaration, with its actual base-changed pairing and coefficient
structure; its formula is not redefined. The compactification is any chosen geometric one.
Source: prop-base-linear.md, transform of def-fd-transform
(blueprint: prop-base-linear). -/
def literalTransform {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤))
    (d : Compactification (pullback.snd (map D p) (map D p'))) (r : ℤ) :
    category D Λ V ⥤ category D Λ V' :=
  letI := Fintype.ofFinite D.k₀
  letI : (pullback (map D p) (map D p')).Over (Spec (.of D.k₀)) :=
    ⟨(productComparison D p p').inv ≫ projection D (square D p p') ≫
      (square D p p').hom⟩
  condensedFourierTransform Λ D.k₀ (map D p) (map D p') ψ (literalPairing D p p' b) d r


/-- Tensor on the right by a complex pulled back from the base, as a functor in that
base complex and in the other tensor factor. This is the existing curried derived tensor.
Source: prop-base-linear.md, main formula (blueprint: prop-base-linear). -/
def baseTensor {S V : Over (Spec (.of D.k₀))} (p : V ⟶ S) :
    ConstantModelBoundedConstructible Λ (fiber D S) ⥤
      (category D Λ V ⥤ category D Λ V) :=
  (constantModelBoundedConstructible Λ (fiber D S)).ι ⋙
    (upperStar Λ (map D p)).leftDerivedFunctor ⋙ (curriedTensor (category D Λ V)).flip

/-- Pullback of a specified Weil structure, with the actual derived square comparison.
Source: prop-base-linear.proof.md, first and last paragraphs
(blueprint: prop-base-linear). -/
def pullDatum {X Y : Over (Spec (.of D.k₀))} (f : X ⟶ Y)
    (K : category D Λ Y)
    (φ : (StrictWeil.action Λ (StrictWeil.modelFrobenius D Y)).obj K ≅ K) :
    (StrictWeil.action Λ (StrictWeil.modelFrobenius D X)).obj
      ((upperStar Λ (map D f)).leftDerivedFunctor.obj K) ≅
      (upperStar Λ (map D f)).leftDerivedFunctor.obj K :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ (StrictWeil.modelFrobenius D X).hom).symm.app _ ≪≫
    (pullbackSquareComparison Λ
      (⟨(map_properties D f (𝟙 Y)).2.2⟩ :
        CommSq (StrictWeil.modelFrobenius D X).hom (map D f) (map D f)
          (StrictWeil.modelFrobenius D Y).hom)).symm.app K ≪≫
    (upperStar Λ (map D f)).leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ
        (StrictWeil.modelFrobenius D Y).hom).app K ≪≫ φ)

/-- The compact-support Frobenius structure is the proper/open exchange on the actual
base-changed arithmetic compactification, followed by the direct image of the input datum.
Source: prop-base-linear.proof.md, final paragraph (blueprint: prop-base-linear). -/
def pushDatum {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) (K : category D Λ X)
    (φ : (StrictWeil.action Λ (StrictWeil.modelFrobenius D X)).obj K ≅ K) :
    (StrictWeil.action Λ (StrictWeil.modelFrobenius D Y)).obj
      ((rightDerivedLowerShriekOfCompactification Λ (compactification D c)).obj K) ≅
      (rightDerivedLowerShriekOfCompactification Λ (compactification D c)).obj K := by
  let s := frobeniusSquare D c
  letI : IsIso s.middle := inferInstanceAs
    (IsIso (StrictWeil.modelFrobenius D (middle D c)).hom)
  let sq : CommSq (StrictWeil.modelFrobenius D X).hom (map D f) (map D f)
      (StrictWeil.modelFrobenius D Y).hom := ⟨(map_properties D f (𝟙 Y)).2.2⟩
  letI := (CompactificationReindexing.square_isIso Λ s sq).2
  exact (leftDerivedUpperStarIsoMapDerivedCategory Λ
      (StrictWeil.modelFrobenius D Y).hom).symm.app _ ≪≫
    (asIso (CompactificationReindexing.squareExchange Λ s)).app K ≪≫
    (rightDerivedLowerShriekOfCompactification Λ (compactification D c)).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ
        (StrictWeil.modelFrobenius D X).hom).app K ≪≫ φ)

/-- Frobenius on the Fourier transform: monoidal pullback, arithmetic-kernel descent,
proper/open compact exchange and the exact shift comparison, in that order.
Source: prop-base-linear.md, Weil clause and its final proof paragraph
(blueprint: prop-base-linear). -/
def transformDatum {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤))
    (c : Compactification (pullback.snd p.left p'.left)) (r : ℤ)
    (K : category D Λ V)
    (φ : (StrictWeil.action Λ (StrictWeil.modelFrobenius D V)).obj K ≅ K) :
    (StrictWeil.action Λ (StrictWeil.modelFrobenius D V')).obj
      ((transform D Λ p p' ψ b c r).obj K) ≅ (transform D Λ p p' ψ b c r).obj K :=
  ((StrictWeil.action Λ (StrictWeil.modelFrobenius D V')).commShiftIso r).app _ ≪≫
    (shiftFunctor _ r).mapIso
      (pushDatum D Λ (f := snd D p p') c _
        (StrictWeil.tensorDatum Λ (StrictWeil.modelFrobenius D (square D p p'))
          (pullDatum D Λ (fst D p p') K φ) (kernelDatum D Λ p p' ψ b)))

/-- Invertibility of the coefficient prime on the geometric fibre, transported from the
recorded finite-field prime-invertibility theorem. This is inherited data, not a hypothesis.
Source: prop-base-linear.md, standing coefficient convention (blueprint: prop-base-linear). -/
instance tatePrimeInvertible (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D.p)]
    (X : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    ∀ x : fiber D X, Invertible (ell : (fiber D X).residueField x) := by
  have h : ∀ x : fiber D X, IsUnit (ell : (fiber D X).residueField x) := by
    simpa only [WeilConjectures.FiniteFieldDatum.geometricFiber, Over.pullback_obj_left,
      fiber] using D.geometricFiber_coefficientPrimeInvertible ell Fact.out X
  exact fun x ↦ (h x).invertible

/-- The existing signed Tate-twist functor with actual condensed E coefficients.
Source: prop-base-linear.md, clause (2); sk-def-sp-tate-twist
(blueprint: prop-base-linear). -/
def twist (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (X : Over (Spec (.of D.k₀))) (m : ℤ) :
    category D (Coefficient.rational E |>.obj ell) X ⥤
      category D (Coefficient.rational E |>.obj ell) X :=
  tensorRight (StrictWeil.derivedTateLine ell (.rational E) (fiber D X) m)

/-- The arithmetic-cone helper is naturally isomorphic on bounded constructible inputs
to the landed condensedFourierTransform over the geometric fibres, for every geometric
compactification. In particular the cone notation in condensedFourier_base_linear denotes
the very transform used by the other Fourier nodes, not an independent transform.

Source: prop-base-linear.md, reference to def-fd-transform, and the Cartesian Fourier
square in prop-base-linear.proof.md (blueprint: prop-base-linear).

Proof: productComparison is the unique Cartesian-cone isomorphism, so it identifies
both projections. Pullback of sections identifies its pairing with literalPairing.
The Artin--Schreier kernel is inverse image of the fixed character sheaf under that
pairing; inverse-image composition therefore identifies its geometric pullback with
the kernel in condensedFourierTransform. Monoidality and pullback composition identify
the tensor factors naturally in K. Transport the base-changed arithmetic compactification
along productComparison. The proper/open exchange for this isomorphism identifies its
compact-support direct image with the cone direct image. Finally canonical
compactification independence on bounded constructible objects identifies the transported
compactification with d. The kernel is lisse rank one, so the first pullback-tensor
factor is bounded constructible. Whisker these comparisons by the rank shift to obtain
the claimed natural isomorphism. No comparison map is an extra hypothesis. -/
theorem transform_comparison
    (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D.p)]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {S V V' : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (p : V ⟶ S) (p' : V' ⟶ S)
    (ψ : AddChar D.k₀ (MonObj.Γ (Coefficient.rational E |>.obj ell)))
    (b : Γ(pullback p.left p'.left, ⊤))
    (c : Compactification (pullback.snd p.left p'.left))
    (d : Compactification (pullback.snd (map D p) (map D p'))) (r : ℤ) :
    Nonempty (
      (constantModelBoundedConstructible
          (Coefficient.rational E |>.obj ell) (fiber D V)).ι ⋙
        transform D (Coefficient.rational E |>.obj ell) p p' ψ b c r ≅
      (constantModelBoundedConstructible
          (Coefficient.rational E |>.obj ell) (fiber D V)).ι ⋙
        literalTransform D (Coefficient.rational E |>.obj ell) p p' ψ b d r) := by
  sorry

/-- Base linearity, its unit specialization, and every integral Tate twist, with the
same isomorphism respecting the specified Weil data. The three models and bundle data
are arithmetic; fiber, map and transform take their geometric base changes. No triviality
of the bundle, positive rank, nonzero complex, or chosen primitive root is assumed.

Source: latest blueprint, prop-base-linear.md, all clauses
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
   Weil isomorphism. The chosen arithmetic compactification gives the actual geometric
   model, and compactification independence identifies it with any other model. -/
theorem condensedFourier_base_linear
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
        (φ : (StrictWeil.action (Coefficient.rational E |>.obj ell)
          (StrictWeil.modelFrobenius D V)).obj K.obj ≅ K.obj),
        (StrictWeil.action (Coefficient.rational E |>.obj ell)
            (StrictWeil.modelFrobenius D V')).map (e.hom.app K) ≫
          (StrictWeil.tensorDatum (Coefficient.rational E |>.obj ell)
            (StrictWeil.modelFrobenius D V')
            (transformDatum D (Coefficient.rational E |>.obj ell)
              p p' ψ b c (r : ℤ) K.obj φ)
            (StrictWeil.tateDatum ell (.rational E) (StrictWeil.modelFrobenius D V') m)).hom =
        (transformDatum D (Coefficient.rational E |>.obj ell)
          p p' ψ b c (r : ℤ) ((twist D ell E V m).obj K.obj)
          (StrictWeil.tensorDatum (Coefficient.rational E |>.obj ell)
            (StrictWeil.modelFrobenius D V) φ
            (StrictWeil.tateDatum ell (.rational E) (StrictWeil.modelFrobenius D V) m))).hom ≫
          e.hom.app K := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier
