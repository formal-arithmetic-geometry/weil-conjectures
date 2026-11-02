/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.CondensedCurvePerverseStatement
public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Perverse exactness of the condensed Fourier transform on the affine line

Source: latest blueprint, part-weights-riemann-hypothesis/sec-fourier-transform/
sec-perverse-t-exactness-of-the-fourier-transform/sk-p-dl-a1-perverse/_section.md
and sk-p-dl-a1-perverse.proof.md; the retained geometric formulation
and thirteen proof steps of the live DAG node (blueprint: sk-p-dl-a1-perverse).

All categories are ordinary derived categories of the pulled-back condensed ring.
The geometric line and Fourier product are base changes of their finite-field models.
The Frobenius component is prescribed by arithmetic kernel descent, the native monoidal
pullback comparison, and the proper/open exchange of the chosen compactification.
The equivalences below are pinned to these functors by natural isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedFourierPerverse

open CondensedCurvePerverse

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory CondensedRing.leftDerivedUpperStarTensor
  CondensedRing.leftDerivedUpperStarComp CondensedRing.pullbackSquareComparison

variable (D : WeilConjectures.FiniteFieldDatum.{u})

/-- The finite-field affine line, with its prescribed structure map.
Source: affine-line application in the source (blueprint: sk-p-dl-a1-perverse). -/
abbrev lineModel : Over (Spec (.of D.k₀)) :=
  Over.mk (AffineSpace PUnit (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))

/-- The Fourier product over the finite field, with its first-projection base map.
Source: the source's Fourier square (blueprint: sk-p-dl-a1-perverse). -/
abbrev productModel : Over (Spec (.of D.k₀)) :=
  Over.mk (pullback.fst (lineModel D).hom (lineModel D).hom ≫ (lineModel D).hom)

/-- The arithmetic first projection of the Fourier product.
Source: the defining transform formula (blueprint: sk-p-dl-a1-perverse). -/
def firstModel : productModel D ⟶ lineModel D :=
  Over.homMk (pullback.fst _ _) rfl

/-- The arithmetic second projection of the Fourier product.
Source: the defining transform formula (blueprint: sk-p-dl-a1-perverse). -/
def secondModel : productModel D ⟶ lineModel D :=
  Over.homMk (pullback.snd _ _) pullback.condition.symm

/-- The existing geometric base-change functor at the fixed field inclusion.
Source: geometric reduction in the source (blueprint: sk-p-dl-a1-perverse). -/
abbrev geometric :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The geometric affine line, using the fixed finite-field datum's fibre convention.
Source: geometric reduction in the source (blueprint: sk-p-dl-a1-perverse). -/
abbrev line : Scheme.{u} := ((geometric D).obj (lineModel D)).left

/-- The geometric Fourier product, with both projections supplied by base change.
Source: geometric reduction in the source (blueprint: sk-p-dl-a1-perverse). -/
abbrev product : Scheme.{u} := ((geometric D).obj (productModel D)).left

/-- The geometric first projection, the base change of the arithmetic projection.
Source: the defining transform formula (blueprint: sk-p-dl-a1-perverse). -/
abbrev first : product D ⟶ line D := ((geometric D).map (firstModel D)).left

/-- The geometric second projection, the base change of the arithmetic projection.
Source: the defining transform formula (blueprint: sk-p-dl-a1-perverse). -/
abbrev second : product D ⟶ line D := ((geometric D).map (secondModel D)).left

/-- The geometric line's Frobenius is the recorded id times inverse field Frobenius.
Source: geometric/Weil reduction in the source (blueprint: sk-p-dl-a1-perverse). -/
abbrev frobenius := D.geometricFrobenius (lineModel D)

/-- Geometric base change of the chosen arithmetic compactification. The middle model
is retained, so Frobenius also has a specified lift to that model.
Source: canonical Frobenius compatibility in the source
(blueprint: sk-p-dl-a1-perverse). -/
def compactification (c : Compactification (secondModel D).left) :
    Compactification (second D) := by
  let Z : Over (Spec (.of D.k₀)) := Over.mk (c.g ≫ (lineModel D).hom)
  letI : LocallyOfFiniteType Z.hom := by dsimp [Z]; infer_instance
  letI : QuasiCompact Z.hom := by dsimp [Z]; infer_instance
  let i : productModel D ⟶ Z := Over.homMk c.i (by
    change c.i ≫ (c.g ≫ (lineModel D).hom) = (productModel D).hom
    rw [← Category.assoc, ← c.comm]
    exact (secondModel D).w)
  let g : Z ⟶ lineModel D := Over.homMk c.g rfl
  let B := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have square {X Y : Over (Spec (.of D.k₀))} (f : X ⟶ Y) :
      IsPullback (pullback.fst X.hom B) ((geometric D).map f).left f.left
        (pullback.fst Y.hom B) := by
    let e := pullback.congrHom f.w.symm rfl ≪≫
      (pullbackRightPullbackFstIso Y.hom B f.left).symm
    apply IsPullback.of_iso_pullback ⟨by simp [geometric, B]⟩ e
    · simp [e, B]
    · apply pullback.hom_ext <;>
        simp [e, geometric, B]
  refine
    { Z := ((geometric D).obj Z).left
      i := ((geometric D).map i).left
      g := ((geometric D).map g).left
      comm := ?_
      isProper := MorphismProperty.of_isPullback (P := @IsProper) (square g) c.isProper
      isOpenImmersion :=
        MorphismProperty.of_isPullback (P := @IsOpenImmersion) (square i) c.isOpenImmersion }
  have h : secondModel D = i ≫ g := Over.OverMorphism.ext c.comm
  exact congrArg (fun f ↦ f.left) ((congrArg (fun f ↦ (geometric D).map f) h).trans
    ((geometric D).map_comp i g))

/-- Frobenius on the compactification is the arithmetic middle model's geometric
Frobenius. Its open square is Cartesian and its proper square is the prescribed
commuting square. Source: canonical Frobenius compatibility in the source
(blueprint: sk-p-dl-a1-perverse). -/
def compactificationSquare (c : Compactification (secondModel D).left) :
    CondensedRing.CompactificationReindexing.Square
      (compactification D c) (compactification D c)
      (D.geometricFrobenius (productModel D)).hom (frobenius D).hom := by
  let Z : Over (Spec (.of D.k₀)) := Over.mk (c.g ≫ (lineModel D).hom)
  letI : LocallyOfFiniteType Z.hom := by dsimp [Z]; infer_instance
  letI : QuasiCompact Z.hom := by dsimp [Z]; infer_instance
  let i : productModel D ⟶ Z := Over.homMk c.i (by
    change c.i ≫ (c.g ≫ (lineModel D).hom) = (productModel D).hom
    rw [← Category.assoc, ← c.comm]
    exact (secondModel D).w)
  let g : Z ⟶ lineModel D := Over.homMk c.g rfl
  refine
    { middle := (D.geometricFrobenius Z).hom
      openSquare := ?_
      properSquare := ?_ }
  · exact (D.frobenius_square_cartesian (productModel D) Z i).2.2.2.2.2.1
  · exact ⟨(D.frobenius_square_cartesian Z (lineModel D) g).2.2.2.2.1⟩

variable (ell : ℕ) [Fact ell.Prime]

/-- The ordinary geometric coefficient-derived category, using the recorded modules.
Source: geometric category in the source (blueprint: sk-p-dl-a1-perverse). -/
abbrev category := DerivedCategory (Modules (Profinite.padicAlgClRingObj ell) (line D))

/-- The geometric perverse heart, with the dependency's actual geometric morphisms.
Source: geometric heart in the source (blueprint: sk-p-dl-a1-perverse). -/
abbrev perverse := (heart (Profinite.padicAlgClRingObj ell) (line D)).FullSubcategory

/-- The ordinary derived Frobenius inverse image used in that fixed-pair heart.
Source: canonical Frobenius compatibility in the source
(blueprint: sk-p-dl-a1-perverse). -/
abbrev action := (CondensedRing.upperStar
  (Profinite.padicAlgClRingObj ell) (frobenius D).hom).mapDerivedCategory

/-- The existing degree-q kernel on the arithmetic affine-line product.
Source: the defining kernel in the source (blueprint: sk-p-dl-a1-perverse). -/
@[irreducible] def arithmeticKernel
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell))) :
    Modules (Profinite.padicAlgClRingObj ell) (productModel D).left :=
  letI := Fintype.ofFinite D.k₀
  letI : (pullback (lineModel D).hom (lineModel D).hom).Over (Spec (.of D.k₀)) :=
    ⟨(productModel D).hom⟩
  condensedFourierKernel (Profinite.padicAlgClRingObj ell) D.k₀
    (lineModel D).hom (lineModel D).hom ψ
    (AffineSpace.stdPairing PUnit (Spec (.of D.k₀)))

/-- The native descent compositor for a sheaf pulled back along an invariant map.
The displayed equation fixes the final comparison; no isomorphism is chosen.
Source: arithmetic kernel descent in the source (blueprint: sk-p-dl-a1-perverse). -/
@[irreducible] def sheafDescent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    (g : X ≅ X) (π : X ⟶ Y) (h : g.hom ≫ π = π) (A : Modules Λ Y) :
    (CondensedRing.upperStar Λ g.hom).obj ((CondensedRing.upperStar Λ π).obj A) ≅
      (CondensedRing.upperStar Λ π).obj A :=
  ((CondensedRing.upperStarComp Λ g.hom π).app A).symm ≪≫
    eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj A) h)

/-- Degree-zero transport of a specified sheaf descent by the exact inverse image.
Source: the canonical Fourier Frobenius compatibility
(blueprint: sk-p-dl-a1-perverse). -/
@[irreducible] def singleDescent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (g : X ≅ X) (A : Modules Λ X)
    (e : (CondensedRing.upperStar Λ g.hom).obj A ≅ A) :
    (CondensedRing.upperStar Λ g.hom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj A) ≅
      (DerivedCategory.singleFunctor _ 0).obj A :=
  ((CondensedRing.upperStar Λ g.hom).mapDerivedCategorySingleFunctor 0).app A ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

/-- Bundle the pullback sheaf with its specified invariant-map descent. This is
ordinary sheaf-level data in the existing category of algebras with invertible action.
Source: arithmetic kernel descent (blueprint: sk-p-dl-a1-perverse). -/
@[irreducible] def sheafDescentObject
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    (g : X ≅ X) (π : X ⟶ Y) (h : g.hom ≫ π = π) (A : Modules Λ Y) :
    Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ g.hom) :=
  Endofunctor.IsoAlgebra.mk ((CondensedRing.upperStar Λ π).obj A)
    (sheafDescent Λ g π h A)

/-- The actual arithmetic Fourier kernel and its canonical geometric Frobenius descent,
bundled so their carrier and structure are shared by definition.
Source: canonical Fourier Frobenius compatibility
(blueprint: sk-p-dl-a1-perverse). -/
@[irreducible] def kernelData
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell))) :
    Endofunctor.IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius (productModel D)).hom) := by
  letI := Fintype.ofFinite D.k₀
  exact sheafDescentObject (Profinite.padicAlgClRingObj ell)
    (D.geometricFrobenius (productModel D))
    (pullback.fst (productModel D).hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (D.galoisMap_projections (productModel D).hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).1
    (arithmeticKernel D ell ψ)

/-- The existing degree-q Fourier kernel, pulled back from the arithmetic Fourier square.
It is the carrier of the explicitly constructed arithmetic descent, not a chosen line.
Source: defining transform and geometric reduction in the source
(blueprint: sk-p-dl-a1-perverse). -/
def kernel (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell))) :
    Modules (Profinite.padicAlgClRingObj ell) (product D) :=
  (kernelData D ell ψ).carrier

/-- The affine-line application of the defining transform on the geometric Cartesian
cone: Rp₂! (Lp₁* K tensor Kψ)[1]. All operations and the degree-q kernel are recorded
constructions, with the arithmetic compactification base changed to k.
Source: defining transform and geometric reduction in the source
(blueprint: sk-p-dl-a1-perverse). -/
def transform (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell)))
    (c : Compactification (secondModel D).left) : category D ell ⥤ category D ell :=
  (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) (first D)).leftDerivedFunctor ⋙
    tensorRight ((DerivedCategory.singleFunctor _ 0).obj (kernel D ell ψ)) ⋙
    CondensedRing.rightDerivedLowerShriekOfCompactification
      (Profinite.padicAlgClRingObj ell) (compactification D c) ⋙ shiftFunctor _ (1 : ℤ)

/-- Arithmetic kernel descent on sheaves: the specified structure in `kernelData`.
The kernel and its descent are projections of the same constructed object.
Source: canonical Frobenius compatibility in the source
(blueprint: sk-p-dl-a1-perverse). -/
@[irreducible] def kernelSheafDatum
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell))) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius (productModel D)).hom).obj (kernel D ell ψ) ≅
      kernel D ell ψ :=
  (kernelData D ell ψ).str

/-- The prescribed sheaf descent transported by the single functor into degree zero.
Source: canonical Frobenius compatibility in the source
(blueprint: sk-p-dl-a1-perverse). -/
@[irreducible] def kernelDatum
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell))) :
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius (productModel D)).hom).mapDerivedCategory).obj
        ((DerivedCategory.singleFunctor _ 0).obj (kernel D ell ψ)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (kernel D ell ψ) :=
  singleDescent (Profinite.padicAlgClRingObj ell)
    (D.geometricFrobenius (productModel D)) (kernel D ell ψ) (kernelSheafDatum D ell ψ)

set_option maxHeartbeats 1200000 in
-- Native derived pullback and compactification endpoint identifications are large.
/-- The prescribed Frobenius comparison at a geometric complex. The factors are the
shift comparison, proper/open exchange, tensorator, pullback-square comparison and
arithmetic kernel descent, in that order. This fixes the action independently of
any eventual heart equivalence.
Source: canonical Frobenius compatibility in the source
(blueprint: sk-p-dl-a1-perverse). -/
@[irreducible] def frobeniusComponent
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj ell)))
    (c : Compactification (secondModel D).left) (K : category D ell) :
    (action D ell).obj ((transform D ell ψ c).obj K) ≅
      (transform D ell ψ c).obj ((action D ell).obj K) := by
  let Λ := Profinite.padicAlgClRingObj ell
  let g := frobenius D
  let h := D.geometricFrobenius (productModel D)
  let P := (CondensedRing.upperStar Λ (first D)).leftDerivedFunctor
  let R := CondensedRing.rightDerivedLowerShriekOfCompactification Λ (compactification D c)
  let L := (DerivedCategory.singleFunctor _ 0).obj (kernel D ell ψ)
  let s := compactificationSquare D c
  let sq : CommSq h.hom (second D) (second D) g.hom :=
    ⟨(D.frobenius_square_cartesian (productModel D) (lineModel D)
      (secondModel D)).2.2.2.2.1⟩
  letI : LocallyOfFiniteType (Over.mk (c.g ≫ (lineModel D).hom)).hom := by
    dsimp; infer_instance
  letI : QuasiCompact (Over.mk (c.g ≫ (lineModel D).hom)).hom := by
    dsimp; infer_instance
  letI : IsIso s.middle := inferInstanceAs
    (IsIso (D.geometricFrobenius
      (Over.mk (c.g ≫ (lineModel D).hom))).hom)
  letI := (CondensedRing.CompactificationReindexing.square_isIso Λ s sq).2
  let sq' : CommSq h.hom (first D) (first D) g.hom :=
    ⟨(D.frobenius_square_cartesian (productModel D) (lineModel D)
      (firstModel D)).2.2.2.2.1⟩
  exact ((action D ell).commShiftIso (1 : ℤ)).app _ ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g.hom).symm.app _ ≪≫
        (asIso (CondensedRing.CompactificationReindexing.squareExchange Λ s)).app _ ≪≫
        R.mapIso
          (((CondensedRing.leftDerivedUpperStarTensorIso Λ h.hom).app (P.obj K)).app L ≪≫
            tensorIso
              ((CondensedRing.pullbackSquareComparison Λ sq').symm.app K ≪≫
                P.mapIso ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                  Λ g.hom).app K))
              ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ h.hom).app L ≪≫
                kernelDatum D ell ψ)))

set_option maxHeartbeats 1200000 in
-- Elaborate the restrictions and the two canonical forgetful squares in one statement.
end AlgebraicGeometry.ProEtale.CondensedFourierPerverse
