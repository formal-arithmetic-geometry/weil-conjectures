/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteOpenProductSwap

/-! # Coherence of the published finite tensor and exact pullback

Source: Stacks 07A4 and the signed total tensor construction, blueprint open-extension
symmetry calculation (blueprint: lem-pur-finite-tensor-pull-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization
namespace WeilConjectures.FiniteOpenProduct

/-- The signed symmetry is involutive and natural, exact pullback respects it, and
its specified tensor comparison is natural and compatible with composition.
Source: Stacks 07A4, sites-cohomology.tex, lemma-pullback-tensor-product; the finite
cochain calculation in lem-pur-derived-pullback-tensor-iso, Steps 2--3
(blueprint: lem-pur-finite-tensor-pull-coherence).

Proof: use flat-term K-flat representatives for both arguments. The published
proetSigma is the descent of the Koszul swap. Two swaps multiply by
(-1)^(pq+qp)=1 on a summand of degrees p,q. Its naturality is termwise naturality
of the module tensor swap. The pullback comparison sends a simple tensor to the
tensor of its two inverse images, so commutes with this signed swap. It commutes
with a pair of maps for the same reason. For composable pullbacks both routes
send a simple tensor to its two iterated inverse images, under upperStarComp.
Totalize, retaining direct sums in unbounded degrees. The uniqueness of descent
from K-flat resolving pairs extends all five equations to the actual published
derived maps. Transport along leftDerivedUpperStarIsoMapDerivedCategory in both
arguments; its naturality and the exact pullback compositor give the last two
equations with tensorPullIso and pullComp exactly as defined here. -/
theorem finiteTensorPullCoherence (A : Type (u + 1)) [CommRing A] [Finite A] :
    (∀ (Y : Scheme.{u}) (M N : FiniteD A Y),
      sigma A Y M N ≫ sigma A Y N M = 𝟙 (tensor A Y M N)) ∧
    (∀ (Y : Scheme.{u}) {M M' N N' : FiniteD A Y} (a : M ⟶ M') (b : N ⟶ N'),
      tensorMap A Y a b ≫ sigma A Y M' N' =
        sigma A Y M N ≫ tensorMap A Y b a) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : FiniteD A Y),
      (pull A f).map (sigma A Y M N) ≫ (tensorPullIso A f N M).hom =
        (tensorPullIso A f M N).hom ≫
          sigma A X ((pull A f).obj M) ((pull A f).obj N)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {M M' N N' : FiniteD A Y}
      (a : M ⟶ M') (b : N ⟶ N'),
      (pull A f).map (tensorMap A Y a b) ≫ (tensorPullIso A f M' N').hom =
        (tensorPullIso A f M N).hom ≫
          tensorMap A X ((pull A f).map a) ((pull A f).map b)) ∧
    (∀ {W V Y : Scheme.{u}} (w : W ⟶ V) (v : V ⟶ Y) (M N : FiniteD A Y),
      (pullComp A w v).hom.app (tensor A Y M N) ≫
          (pull A w).map (tensorPullIso A v M N).hom ≫
          (tensorPullIso A w ((pull A v).obj M) ((pull A v).obj N)).hom =
        (tensorPullIso A (w ≫ v) M N).hom ≫
          tensorMap A W ((pullComp A w v).hom.app M)
            ((pullComp A w v).hom.app N)) := by sorry

end WeilConjectures.FiniteOpenProduct
