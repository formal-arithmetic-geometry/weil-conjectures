/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian

/-! # Native geometric Fourier model and specified descent

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-fourier-inversion/sk-thm-inversion/
lem-wft-fourier-weil.proof.md, first paragraph, and lem-fd-stalk-formula.proof.md,
first paragraph (blueprint: def-fd-geometric-fourier-model).

All coefficient rings are the actual condensedRingObj Lambda T = p_T^* Lambda.
The category is the ordinary unbounded derived category of internal modules.
The geometric cone and compactification are actual base changes of the arithmetic
models, for arbitrary models. Kernel descent, pullback, tensor, native compact-support
exchange and shift specify every Frobenius map; no isomorphism is chosen from existence.
The three named geometric well-definedness lemmas are proved.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativeGeometricFourier

variable (D : WeilConjectures.FiniteFieldDatum.{u})

/-- Geometric base change, with no superfluous finite-type hypothesis on this construction.
Source: def-fd-transform.md, geometric application (blueprint: def-fd-geometric-fourier-model). -/
abbrev fiber (X : Over (Spec (.of D.k₀))) : Scheme.{u} :=
  pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The actual first projection to the arithmetic model.
Source: def-fd-transform.md, geometric application (blueprint: def-fd-geometric-fourier-model). -/
abbrev projection (X : Over (Spec (.of D.k₀))) : fiber D X ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Base change of an actual morphism of finite-field models.
Source: def-fd-transform.md, geometric application (blueprint: def-fd-geometric-fourier-model). -/
abbrev map {X Y : Over (Spec (.of D.k₀))} (f : X ⟶ Y) : fiber D X ⟶ fiber D Y :=
  pullback.map X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    Y.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    f.left (𝟙 _) (𝟙 _) (by simp only [Category.comp_id]; exact f.w.symm) (by simp)

/-- The base-change square, its composition law, and its Frobenius square.
Source: def-fd-transform.md, base change of the defining square
(blueprint: def-fd-geometric-fourier-model).
Proof: the pullback projections define map. Pasting their defining Cartesian squares
cancels the common field-extension square. Functoriality gives composition. Naturality
of id times geometric Frobenius gives the last equality, checked on both projections. -/
theorem map_properties {X Y Z : Over (Spec (.of D.k₀))} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsPullback (projection D X) (map D f) f.left (projection D Y) ∧
    map D (f ≫ g) = map D f ≫ map D g ∧
    (StrictWeilCondensed.modelFrobenius D X).hom ≫ map D f =
      map D f ≫ (StrictWeilCondensed.modelFrobenius D Y).hom := by
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
Source: def-fd-kernel.md, Fourier square (blueprint: def-fd-geometric-fourier-model). -/
abbrev square {S V V' : Over (Spec (.of D.k₀))} (p : V ⟶ S) (p' : V' ⟶ S) :
    Over (Spec (.of D.k₀)) :=
  Over.mk (pullback.fst p.left p'.left ≫ V.hom)

/-- The first Fourier projection as an arithmetic morphism.
Source: def-fd-transform.md, p1 (blueprint: def-fd-geometric-fourier-model). -/
def fst {S V V' : Over (Spec (.of D.k₀))} (p : V ⟶ S) (p' : V' ⟶ S) :
    square D p p' ⟶ V :=
  Over.homMk (pullback.fst p.left p'.left) rfl

/-- The second Fourier projection as an arithmetic morphism.
Source: def-fd-transform.md, p2 (blueprint: def-fd-geometric-fourier-model). -/
def snd {S V V' : Over (Spec (.of D.k₀))} (p : V ⟶ S) (p' : V' ⟶ S) :
    square D p p' ⟶ V' :=
  Over.homMk (pullback.snd p.left p'.left)
    (by
      change pullback.snd p.left p'.left ≫ V'.hom =
        pullback.fst p.left p'.left ≫ V.hom
      rw [← p'.w, ← Category.assoc, ← pullback.condition, Category.assoc, p.w])

/-- The geometric square is the same fibre product as the literal geometric Fourier square.
Source: def-fd-transform.md, geometric application (blueprint: def-fd-geometric-fourier-model).
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
Source: prop-base-linear.proof.md, Fourier square (blueprint: def-fd-geometric-fourier-model). -/
def productComparison {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) :
    fiber D (square D p p') ≅ pullback (map D p) (map D p') :=
  (square_isPullback D p p').isoPullback

/-- The actual base-changed pairing on the literal geometric Fourier product.
Source: prop-base-linear.md, transform of def-fd-transform
(blueprint: def-fd-geometric-fourier-model). -/
def literalPairing {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (b : Γ(pullback p.left p'.left, ⊤)) :
    Γ(pullback (map D p) (map D p'), ⊤) :=
  ((productComparison D p p').inv ≫ projection D (square D p p')).appTop b

/-- The middle arithmetic model of the chosen compactification.
Source: def-fd-transform.md, chosen compactification (blueprint: def-fd-geometric-fourier-model). -/
abbrev middle {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) : Over (Spec (.of D.k₀)) :=
  Over.mk (c.g ≫ Y.hom)

/-- The arithmetic open immersion of the chosen compactification.
Source: def-fd-transform.md, chosen compactification (blueprint: def-fd-geometric-fourier-model). -/
def openMap {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) : X ⟶ middle D c :=
  Over.homMk c.i (by
    change c.i ≫ (c.g ≫ Y.hom) = X.hom
    rw [← Category.assoc, ← c.comm, f.w])

/-- The arithmetic proper morphism of the chosen compactification.
Source: def-fd-transform.md, chosen compactification (blueprint: def-fd-geometric-fourier-model). -/
def properMap {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) : middle D c ⟶ Y :=
  Over.homMk c.g rfl

/-- The defining properties needed by the concrete base-changed compactification.
Source: def-fd-transform.md, compactification and geometric application
(blueprint: def-fd-geometric-fourier-model).
Proof: the first clause is the image of c.comm under base change. The base-change
squares in map_properties transport properness and the open immersion from c.
The last clause is naturality of Frobenius for the open immersion; both horizontal
maps are isomorphisms, so its commuting square is Cartesian. -/
theorem compactification_properties {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) :
    map D f = map D (openMap D c) ≫ map D (properMap D c) ∧
    IsProper (map D (properMap D c)) ∧ IsOpenImmersion (map D (openMap D c)) ∧
    IsPullback (StrictWeilCondensed.modelFrobenius D X).hom (map D (openMap D c))
      (map D (openMap D c)) (StrictWeilCondensed.modelFrobenius D (middle D c)).hom := by
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
Source: def-fd-transform.md, geometric application (blueprint: def-fd-geometric-fourier-model). -/
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
(blueprint: def-fd-geometric-fourier-model). -/
def frobeniusSquare {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) :
    CompactificationReindexing.Square (compactification D c) (compactification D c)
      (StrictWeilCondensed.modelFrobenius D X).hom
      (StrictWeilCondensed.modelFrobenius D Y).hom where
  middle := (StrictWeilCondensed.modelFrobenius D (middle D c)).hom
  openSquare := (compactification_properties D c).2.2.2
  properSquare := ⟨(map_properties D (properMap D c) (𝟙 Y)).2.2⟩

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ambient ordinary condensed coefficient category on the geometric fibre.
Source: def-fd-transform.md, coefficient category (blueprint: def-fd-geometric-fourier-model). -/
abbrev category (X : Over (Spec (.of D.k₀))) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (fiber D X)) Ab.{u + 1})
    (condensedRingObj Λ (fiber D X)))

/-- The actual degree-zero arithmetic kernel, with the product's inherited base structure.
Source: def-fd-kernel.md, finite-field application (blueprint: def-fd-geometric-fourier-model). -/
def arithmeticKernel {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤)) :=
  letI := Fintype.ofFinite D.k₀
  letI : (pullback p.left p'.left).Over (Spec (.of D.k₀)) := ⟨(square D p p').hom⟩
  condensedFourierKernel Λ D.k₀ p.left p'.left ψ b

/-- Pullback of the arithmetic kernel, placed in degree zero. By pullback composition this
is b-geometric-star of the same Artin--Schreier sheaf, not a new choice of kernel.
Source: def-fd-transform.md, geometric application (blueprint: def-fd-geometric-fourier-model). -/
def kernel {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤)) : category D Λ (square D p p') :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((upperStar Λ (projection D (square D p p'))).obj (arithmeticKernel D Λ p p' ψ b))

/-- Descent of an arithmetic module to the fibre under a map fixing its projection.
This generic construction keeps the module pullback comparison independent of the
size of the geometric Fourier square.
Source: def-fd-transform.md, arithmetic descent (blueprint: def-fd-geometric-fourier-model). -/
def modelDescent {X Y : Scheme.{u}} (π : X ⟶ Y) (g : X ≅ X)
    (h : g.hom ≫ π = π)
    (A : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (StrictWeilCondensed.action Λ g).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ π).obj A)) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ π).obj A) :=
  ((upperStar Λ g.hom).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (((upperStarComp Λ g.hom π).app A).symm ≪≫
        eqToIso (congrArg (fun t ↦ (upperStar Λ t).obj A) h))

/-- The normalized descent datum on the geometric kernel, obtained by composition of
ordinary module pullbacks and the identity Frobenius followed by the model projection.
Source: def-fd-transform.md and prop-base-linear.md, Weil clause
(blueprint: def-fd-geometric-fourier-model). -/
def kernelDatum {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤)) :
    (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D (square D p p'))).obj
      (kernel D Λ p p' ψ b) ≅ kernel D Λ p p' ψ b := by
  letI := Fintype.ofFinite D.k₀
  exact modelDescent Λ (projection D (square D p p'))
    (StrictWeilCondensed.modelFrobenius D (square D p p'))
    (D.galoisMap_projections (square D p p').hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).1
    (arithmeticKernel D Λ p p' ψ b)

/-- The same Fourier formula on the geometric Cartesian cone, with its base-changed
compactification. square_isPullback identifies this with the literal-product definition;
exact pullback composition identifies kernel with its prescribed geometric pairing kernel.
Source: def-fd-transform.md, geometric application (blueprint: def-fd-geometric-fourier-model). -/
def transform {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤))
    (c : Compactification (pullback.snd p.left p'.left)) (r : ℤ) :
    category D Λ V ⥤ category D Λ V' :=
  (upperStar Λ (map D (fst D p p'))).leftDerivedFunctor ⋙
    tensorRight (kernel D Λ p p' ψ b) ⋙
    rightDerivedLowerShriekOfCompactification Λ (compactification D (f := snd D p p') c) ⋙
    shiftFunctor _ r


/-- Pullback of a specified Weil structure, with the actual derived square comparison.
Source: prop-base-linear.proof.md, first and last paragraphs
(blueprint: def-fd-geometric-fourier-model). -/
def pullDatum {X Y : Over (Spec (.of D.k₀))} (f : X ⟶ Y)
    (K : category D Λ Y)
    (φ : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D Y)).obj K ≅ K) :
    (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D X)).obj
      ((upperStar Λ (map D f)).leftDerivedFunctor.obj K) ≅
      (upperStar Λ (map D f)).leftDerivedFunctor.obj K :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ
    (StrictWeilCondensed.modelFrobenius D X).hom).symm.app _ ≪≫
    (pullbackSquareComparison Λ
      (⟨(map_properties D f (𝟙 Y)).2.2⟩ :
        CommSq (StrictWeilCondensed.modelFrobenius D X).hom (map D f) (map D f)
          (StrictWeilCondensed.modelFrobenius D Y).hom)).symm.app K ≪≫
    (upperStar Λ (map D f)).leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ
        (StrictWeilCondensed.modelFrobenius D Y).hom).app K ≪≫ φ)

/-- The compact-support Frobenius structure is the proper/open exchange on the actual
base-changed arithmetic compactification, followed by the direct image of the input datum.
Source: prop-base-linear.proof.md, final paragraph (blueprint: def-fd-geometric-fourier-model). -/
def pushDatum {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) (K : category D Λ X)
    (φ : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D X)).obj K ≅ K) :
    (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D Y)).obj
      ((rightDerivedLowerShriekOfCompactification Λ (compactification D c)).obj K) ≅
      (rightDerivedLowerShriekOfCompactification Λ (compactification D c)).obj K := by
  let s := frobeniusSquare D c
  letI : IsIso s.middle := inferInstanceAs
    (IsIso (StrictWeilCondensed.modelFrobenius D (middle D c)).hom)
  let sq : CommSq (StrictWeilCondensed.modelFrobenius D X).hom (map D f) (map D f)
      (StrictWeilCondensed.modelFrobenius D Y).hom := ⟨(map_properties D f (𝟙 Y)).2.2⟩
  letI := (CompactificationReindexing.square_isIso Λ s sq).2
  exact (leftDerivedUpperStarIsoMapDerivedCategory Λ
      (StrictWeilCondensed.modelFrobenius D Y).hom).symm.app _ ≪≫
    (asIso (CompactificationReindexing.squareExchange Λ s)).app K ≪≫
    (rightDerivedLowerShriekOfCompactification Λ (compactification D c)).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ
        (StrictWeilCondensed.modelFrobenius D X).hom).app K ≪≫ φ)

/-- Frobenius on the Fourier transform: monoidal pullback, arithmetic-kernel descent,
proper/open compact exchange and the exact shift comparison, in that order.
Source: prop-base-linear.md, Weil clause and its final proof paragraph
(blueprint: def-fd-geometric-fourier-model). -/
def transformDatum {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤))
    (c : Compactification (pullback.snd p.left p'.left)) (r : ℤ)
    (K : category D Λ V)
    (φ : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D V)).obj K ≅ K) :
    (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D V')).obj
      ((transform D Λ p p' ψ b c r).obj K) ≅ (transform D Λ p p' ψ b c r).obj K :=
  ((StrictWeilCondensed.action Λ
    (StrictWeilCondensed.modelFrobenius D V')).commShiftIso r).app _ ≪≫
    (shiftFunctor _ r).mapIso
      (pushDatum D Λ (f := snd D p p') c _
        (StrictWeilCondensed.tensorDatum Λ (StrictWeilCondensed.modelFrobenius D (square D p p'))
          (pullDatum D Λ (fst D p p') K φ) (kernelDatum D Λ p p' ψ b)))

end AlgebraicGeometry.ProEtale.CondensedRing.NativeGeometricFourier
