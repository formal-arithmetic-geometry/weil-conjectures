/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.ConstructedCompositionModelData

/-! # Integral models and prescribed scalar comparison squares

Source: sk-prop-sp-composition.proof.md, coefficient passage
(blueprint: lem-pur-general-constructed-scalar-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeneralPurityTransport

variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] (hk : Finite k ∨ IsAlgClosed k) (hEll : IsUnit (ell : k))

set_option maxHeartbeats 2000000 in
-- These fields compare literal derived functors and their restricted compositors.
/-- Scalar models with actual scalar functors, actual source/support compositors,
and normalized comparison components. There is no composition equation for counits
in these fields. Source: the scalar pasting in the coefficient passage
(blueprint: lem-pur-general-constructed-scalar-models). -/
structure ConstructedScalarModels {I : Type} (c : I → Coefficient ell)
    (c' : Coefficient ell) where
  a : ∀ i, (c i).bundled.{u} ell ⟶ c'.bundled ell
  listed : ∀ i, IsListedScalarCoefficientMap ell (a i)
  preserves : ∀ (i : I) (T : Over (Spec (.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (K : (c i).ctf ell T.left),
    property ell c' T.left ((scalarSixChange (a i) T.left).obj K.obj)
  coherent : ∀ i, Nonempty (CompactSupportComposition.CoherentData ((c i).obj.{u} ell) k)
  unit : ∀ i, (c i).integralMap ell ≫ (a i).hom.hom = c'.integralMap ell
  coordinates : ∀ i (s : SmoothDatum k), ScalarLineCoordinates ell (a i) (unit i) s.X.left
  A : ∀ i (s : SmoothDatum k),
    modelSource ell k hk hEll (c i) s ⋙ modelChange ell k (a i) s.X (preserves i s.X) ≅
      modelChange ell k (a i) s.Y (preserves i s.Y) ⋙ modelSource ell k hk hEll c' s
  B : ∀ i (s : SmoothDatum k),
    modelSupport ell k hk hEll (c i) s ⋙ modelChange ell k (a i) s.Y (preserves i s.Y) ≅
      modelChange ell k (a i) s.X (preserves i s.X) ⋙ modelSupport ell k hk hEll c' s
  source_component : ∀ i (s : SmoothDatum k) (K : (c i).ctf ell s.Y.left),
    ((A i s).hom.app K).hom = sourceScalar ell (a i) s.map s.dim (unit i)
      (coordinates i s) K.obj
  support_component : ∀ i (s : SmoothDatum k) (M : (c i).ctf ell s.X.left),
    ((B i s).hom.app M).hom = (scalarSupportMap (a i) s.compactification).app M.obj
  support_square : ∀ i (s : SmoothDatum k) (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (ch : Compactification (s.map ≫ g))
    (H : CompactSupportComposition.CoherentData ((c i).obj.{u} ell) k)
    (H' : CompactSupportComposition.CoherentData (c'.obj.{u} ell) k)
    (M : (c i).ctf ell s.X.left),
    (modelChange ell k (a i) Z (preserves i Z)).map
        ((modelSupportIso ell k hk hEll s Z g e (c i) cg ch H).hom.app M) ≫
      (B i (modelTotal k s Z g e ch)).hom.app M =
    (B i (modelSecond k s Z g e cg)).hom.app
        ((modelSupport ell k hk hEll (c i) s).obj M) ≫
      (modelSupport ell k hk hEll c' (modelSecond k s Z g e cg)).map
        ((B i s).hom.app M) ≫
      (modelSupportIso ell k hk hEll s Z g e c' cg ch H').hom.app
        ((modelChange ell k (a i) s.X (preserves i s.X)).obj M)
  source_square : ∀ i (s : SmoothDatum k) (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (ch : Compactification (s.map ≫ g))
    (p : LinePullCoordinates ell (c i) s.map) (p' : LinePullCoordinates ell c' s.map)
    (K : (c i).ctf ell Z.left),
    (modelChange ell k (a i) s.X (preserves i s.X)).map
        ((modelSourceIso ell k hk hEll s Z g e (c i) cg ch p).hom.app K) ≫
      (A i s).hom.app ((modelSource ell k hk hEll (c i)
        (modelSecond k s Z g e cg)).obj K) ≫
      (modelSource ell k hk hEll c' s).map
        ((A i (modelSecond k s Z g e cg)).hom.app K) =
    (A i (modelTotal k s Z g e ch)).hom.app K ≫
      (modelSourceIso ell k hk hEll s Z g e c' cg ch p').hom.app
        ((modelChange ell k (a i) Z (preserves i Z)).obj K)
  models : ∀ (s : SmoothDatum k) (K : c'.ctf ell s.Y.left),
    ∃ (i : I) (K₀ : (c i).ctf ell s.Y.left),
      Nonempty ((modelChange ell k (a i) s.Y (preserves i s.Y)).obj K₀ ≅ K)

/-- Integral models and normalized scalar squares for each of the field coefficient
presentations. The conclusion asserts no trace transitivity and contains no
finite, integral or rational composition hypothesis.

Source: sk-prop-sp-composition.proof.md, inversion of ell and finite descent
(blueprint: lem-pur-general-constructed-scalar-models).

Proof. For each rational E use integral E and its localization map. The rational
Hom theorem gives integral models on every standing scheme; the integral finite-Tor
criterion puts them in Dctf. For the separate rationals presentation compose this
localization with the specified base-field coefficient isomorphism. For the closure
use the integral-to-E-to-closure maps, and descend each object to a finite E before
choosing its integral model. Scalar-six preservation restricts these actual scalar
functors. Flat localization and field extension make their balanced tensor maps
invertible. The normalized first Tate comparison and its tensor recursion give A;
the proper direct-image mate followed by open extension gives B. Root normalization
fixes their components, including zero powers. The scalar pullback and
symmetric monoidal comparison laws give source_square: the product and pullback
Tate squares hold on roots, then by induction on ordered powers; all shifts are even.
The compact-support composition law gives support_square on a dense composite
model. Scalar refinement compatibility and the normalized refinement cocycles carry
it to each arbitrary total compactification and coherent support system. Coherent
support systems exist for every listed coefficient. None of these constructions
uses composition of smooth counits. -/
theorem constructedFieldScalarModels :
    (∃ (I : Type) (E : I → PadicAlgCl.FiniteIntermediateField ell),
      Nonempty (ConstructedScalarModels ell k hk hEll
        (fun i ↦ .integral (E i)) .rationals)) ∧
    (∀ F : PadicAlgCl.FiniteIntermediateField ell,
      ∃ (I : Type) (E : I → PadicAlgCl.FiniteIntermediateField ell),
        Nonempty (ConstructedScalarModels ell k hk hEll
          (fun i ↦ .integral (E i)) (.rational F))) ∧
    (∃ (I : Type) (E : I → PadicAlgCl.FiniteIntermediateField ell),
      Nonempty (ConstructedScalarModels ell k hk hEll
        (fun i ↦ .integral (E i)) .closure)) := by
  sorry

end AlgebraicGeometry.ProEtale.GeneralPurityTransport
