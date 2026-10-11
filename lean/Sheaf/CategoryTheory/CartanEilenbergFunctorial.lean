/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# Comparison maps of Cartan–Eilenberg resolutions

Source: Stacks Project, Tags 015H, 015I and 015K
(blueprint: lem-weil-pbc-cartesian-eilenberg-functorial).

Cartan–Eilenberg resolutions are stated in the form of
`CategoryTheory.exists_cartanEilenberg_resolution` (lem-sp-cartan-eilenberg-exists):
a bicomplex `HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)` whose first
index is the complex degree and whose second (natural) index is the resolution degree,
so the node's condition (2) is built into the shape; its augmentation is one bicomplex
morphism `e` from the complex placed in resolution degree zero. The column over complex
degree `p` (the node's row over `q`) resolves `K^p`: injective terms and `QuasiIso (e.f p)`,
the fields of `InjectiveResolution`. Cycles, boundaries `image (I.d (p - 1) p)` (resolving
`B^p = Im(d_K^(p-1))`, all `p`) and cohomology in the first direction are resolved via
`cyclesMap`, `image.map` and `homologyMap` of the same `e`. Total complexes are formed
after extending the natural resolution degree by zero to `ℤ`, so that the landed filtrations
of def-sp-double-complex-total apply; the filtration by the complex degree is then
`firstFiltration`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An exact additive functor and a chain map admit a comparison of given
Cartan–Eilenberg resolutions, whose total map preserves the filtration by the complex degree.
Source: Stacks Tags 015H, 015I and 015K
(blueprint: lem-weil-pbc-cartesian-eilenberg-functorial).

The augmentation identity `φ ∘ F(e_K) = e_L ∘ u` is stated on the resolution-degree-zero
components (identified with `K^p`, `L^p` by `singleObjXSelf`), which determine a
morphism out of a complex concentrated in degree zero.

Proof: decompose each degree into the cycle, boundary and homology short exact sequences.
Exactness carries these sequences and the augmented resolution columns through `F`.
Induct on the complex degree, starting with the zero boundary column below the common bound.
Given the boundary-column map, lift the homology-column map using
lem-weil-pbc-lift-along-injective-quasi-iso. Use
lem-weil-pbc-horseshoe-morphism-lift-exact-source to extend these endpoint maps to the
cycle column. Lift the next boundary column by the same quasi-isomorphism comparison, then
use the exact-source horseshoe lift to obtain the original-object column map. Choose
these maps only once, retaining all endpoint compatibilities. The complex-degree differential
factors through boundaries and cycles, so these compatibilities make the column maps
commute with it. They already commute with the resolution differential. The maps thus
assemble into a bicomplex morphism with the augmentation identity. Finally, totalize
the bidegree-preserving components. Finite diagonal sums exist by the two bounds;
the total differential preserves or raises the complex degree, and each component
preserves that degree. Hence both filtrations are subcomplexes and the total
map preserves their steps, as asserted in def-sp-double-complex-total and def-sp-filtration. -/
theorem cartanEilenberg_lift
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hK : ∃ i : ℤ, ∀ p : ℤ, p < i → IsZero (K.X p))
    (hL : ∃ i : ℤ, ∀ p : ℤ, p < i → IsZero (L.X p))
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIbelow : ∃ i : ℤ, ∀ p : ℤ, p < i → IsZero (I.X p))
    (hIcol : ∀ p : ℤ, QuasiIso (eI.f p))
    (hIinj : ∀ (p : ℤ) (q : ℕ), Injective ((I.X p).X q))
    (hIinj' : ∀ (p : ℤ) (q : ℕ),
      Injective ((I.cycles p).X q) ∧
      Injective ((image (I.d (p - 1) p)).X q) ∧
      Injective ((I.homology p).X q))
    (hIres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJbelow : ∃ i : ℤ, ∀ p : ℤ, p < i → IsZero (J.X p))
    (hJcol : ∀ p : ℤ, QuasiIso (eJ.f p))
    (hJinj : ∀ (p : ℤ) (q : ℕ), Injective ((J.X p).X q))
    (hJinj' : ∀ (p : ℤ) (q : ℕ),
      Injective ((J.cycles p).X q) ∧
      Injective ((image (J.d (p - 1) p)).X q) ∧
      Injective ((J.homology p).X q))
    (hJres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p)) :
    let FI : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ) :=
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I
    let E := (ComplexShape.embeddingUpNat.extendFunctor B).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let FIZ : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) := E.obj FI
    let JZ : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) := E.obj J
    ∃ (tI : FIZ.HasTotal (ComplexShape.up ℤ))
      (tJ : JZ.HasTotal (ComplexShape.up ℤ)),
      letI := tI
      letI := tJ
      ∃ φ : FI ⟶ J,
        (∀ p : ℤ,
          F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫
              (eI.f p).f 0) ≫ (φ.f p).f 0 =
            u.f p ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
              (eJ.f p).f 0) ∧
        (∀ r n : ℤ,
          (∃ d : ((FIZ.firstFiltration n).step r : B) ⟶
              ((FIZ.firstFiltration (n + 1)).step r : B),
            d ≫ ((FIZ.firstFiltration (n + 1)).step r).arrow =
              ((FIZ.firstFiltration n).step r).arrow ≫
                (FIZ.total (ComplexShape.up ℤ)).d n (n + 1)) ∧
          (∃ d : ((JZ.firstFiltration n).step r : B) ⟶
              ((JZ.firstFiltration (n + 1)).step r : B),
            d ≫ ((JZ.firstFiltration (n + 1)).step r).arrow =
              ((JZ.firstFiltration n).step r).arrow ≫
                (JZ.total (ComplexShape.up ℤ)).d n (n + 1)) ∧
          (∃ f : ((FIZ.firstFiltration n).step r : B) ⟶
              ((JZ.firstFiltration n).step r : B),
            f ≫ ((JZ.firstFiltration n).step r).arrow =
              ((FIZ.firstFiltration n).step r).arrow ≫
                (HomologicalComplex₂.total.map (show FIZ ⟶ JZ from E.map φ)
                  (ComplexShape.up ℤ)).f n)) := by
  sorry

end CategoryTheory
