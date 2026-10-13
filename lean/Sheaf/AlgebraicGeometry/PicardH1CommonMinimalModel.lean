/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial

/-! # Common trivializations and a minimal source model

Source: Stacks Project, Tag 0BF2, through the first displayed source complex.
(blueprint: lem-sc-picard-h1-common-minimal-model)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Choose a common affine neighbourhood with trivial target bundles and a minimal
finite-free representative of the source direct image.
Source: Stacks Project, Tag 0BF2, first two proof paragraphs; Tags 0B91 and 0BCD.
(blueprint: lem-sc-picard-h1-common-minimal-model)

Proof: For each target, the universal structure adjunction unit on the residue field
excludes an empty fibre. Pull a local finite-free presentation of its descended N to
one fibre point. The invertible pullback has rank one over the nonzero residue field,
so the rank of N at w is one. Trivialize the finitely many N on a common neighbourhood.
Their descent isomorphisms and pullback of the structure module trivialize the target
bundles there. The source fibre descent gives a trivial source bundle by the field
rank-one lemma and the nonempty source fibre. The immersion identifies the two marked
residue fields. Apply perfect direct-image base change to the base-changed invertible
source module, which is finitely presented and relatively flat. Its derived residue
cohomology is the cohomology of the trivial bundle on the marked fibre. Negative
cohomology vanishes, and H-zero has dimension one by the structure adjunction unit.
Apply the finite-free residue-model theorem at w and refine inside the common target
neighbourhood. Its term ranks are precisely these fibre Betti numbers. The zero-degree
term is free of rank one; choose its section basis e0, and the degree-one basis e1 with
m equal to its rank. In the finite-dimensional residue complex, equality of every term
dimension with the corresponding cohomology dimension forces every differential to
vanish (dimension of a term is dimension of cohomology plus the two adjacent ranks).
Thus evaluating every coordinate of d-zero(e0 inverse(1)) gives zero. The boundedness
and all term-rank isomorphisms are retained, rather than just their two low degrees.
For no targets the common neighbourhood restriction is vacuous. For m zero use the
unique basis of the zero module. No injectivity on H-one is used. -/
theorem picard_h1_common_minimal_model
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLi : ∀ i, ∃ (N : W.Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        (Modules.tensorPullback (pullback.snd (fi i) k)).obj N))
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N)) :
    let E := ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L)))
    ∃ (U : W.Opens) (hwU : w ∈ U), IsAffineOpen U ∧
      (∀ i, Nonempty
        ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
          ((Modules.tensorPullback (ui i)).obj L) ≅
          SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf)) ∧
      ∃ (m : ℕ) (K : CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ),
        (∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j)) ∧
        (∀ j : ℤ, j < 0 → derivedFiberBetti W E j w = 0) ∧
        (∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
          (R := (moduleRings W.toRingedSpace).over U)
          (ULift.{v} (Fin (derivedFiberBetti W E j w))))) ∧
        ∃ (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
          (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U))),
          Nonempty ((SheafOfModules.overFunctor.{v}
            (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
              DerivedCategory.Q.obj K) ∧
          ∀ i, W.evaluation U w hwU
            (e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm 1)) i) = 0 := by sorry

end AlgebraicGeometry.Scheme
