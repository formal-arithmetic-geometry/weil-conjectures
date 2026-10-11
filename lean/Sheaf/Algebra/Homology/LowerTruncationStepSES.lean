/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Successive canonical lower truncations

Source: Stacks Project, Homology, Section 12.15 (Tag 0118), and Derived Categories,
Remark 13.12.4 (Tag 08J5) (blueprint: lem-pc-derived-lower-truncation-step-ses).
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- (blueprint: lem-pc-derived-lower-truncation-step-ses) Stacks, Tag 0118 and Tag 08J5.
For an abelian category and any integer `m`, the transition from the canonical lower
truncation at `m` to that at `m + 1` is the quotient in degree `m + 1`, zero in degree
`m`, and the identity in higher degrees. Its kernel is the two-term complex with
`K.opcycles m = K^m / im(d^(m-1))` in degree `m` and `im(d^m)` in degree `m + 1`;
the differential is induced by `d^m`. The kernel inclusion and transition form a
degreewise short exact sequence. The canonical map from the complex concentrated
in degree `m` with value `H^m(K)` is a quasi-isomorphism, since the kernel's
cohomology is `H^m(K)` in degree `m` and zero in degree `m + 1`. For a chain map,
the maps on images and quotients give a map between these sequences, commuting
with the canonical maps from cohomology.
Proof steps (Stacks Tag 0118). First, in degrees below `m`, at `m`, at `m + 1`, and
above `m + 1`, the displayed kernel sequence is respectively zero, the identity on
`K.opcycles m`, the inclusion of `im (d^m)` as the kernel of the quotient, and the
identity. The composites are chain maps because the differential is induced by `d^m`
and `d^(m+1) d^m = 0`, so the sequence is degreewise short exact. Second, the map from
`H^m(K)[-m]` is the inclusion of cycles modulo boundaries in degree `m`; the kernel
has cohomology `H^m(K)` in degree `m`, zero in degree `m + 1`, and zero elsewhere, so
this map is a quasi-isomorphism. Third, a chain map preserves cycles and boundaries,
therefore induces the maps on images, quotients, truncations, kernels, and cohomology;
these induced maps commute with the short exact sequences and the canonical maps.
-/
theorem exists_lowerTruncationStepSES {C : Type u} [Category.{v} C] [Abelian C] :
    ∃ (q : ∀ (K : CochainComplex C ℤ) (m : ℤ),
          K.truncGE m ⟶ K.truncGE (m + 1)),
      ∃ (φ : ∀ (K : CochainComplex C ℤ) (m : ℤ),
            ((singleFunctor C m).obj (K.homology m)) ⟶
              kernel (q K m)),
        (∀ (K : CochainComplex C ℤ) (m : ℤ),
          K.πTruncGE m ≫ q K m = K.πTruncGE (m + 1)) ∧
        (∀ (K : CochainComplex C ℤ) (m : ℤ),
          (ShortComplex.mk (kernel.ι (q K m)) (q K m)
            (kernel.condition (q K m))).ShortExact) ∧
        (∀ (K : CochainComplex C ℤ) (m : ℤ),
          ∃ (e₀ : (kernel (q K m)).X m ≅ K.opcycles m)
            (e₁ : (kernel (q K m)).X (m + 1) ≅
              Abelian.image (K.d m (m + 1))),
            e₀.inv ≫ (kernel.ι (q K m)).f m =
              (K.truncGEXIsoOpcycles m).inv ∧
            e₁.inv ≫ (kernel.ι (q K m)).f (m + 1) ≫
              (K.truncGEXIso m (m + 1)).hom =
                Abelian.image.ι (K.d m (m + 1)) ∧
            e₀.inv ≫ (kernel (q K m)).d m (m + 1) ≫ e₁.hom ≫
              Abelian.image.ι (K.d m (m + 1)) =
                K.fromOpcycles m (m + 1) ∧
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m
                (K.homology m)).inv ≫ (φ K m).f m ≫ e₀.hom =
                  K.homologyι m) ∧
        (∀ (K : CochainComplex C ℤ) (m r : ℤ),
          r ≠ m → r ≠ m + 1 → IsZero ((kernel (q K m)).X r)) ∧
        (∀ (K : CochainComplex C ℤ) (m : ℤ),
          (q K m).f m = 0 ∧
          (K.truncGEXIso m (m + 1)).inv ≫ (q K m).f (m + 1) =
            (K.πTruncGE (m + 1)).f (m + 1)) ∧
        (∀ (K : CochainComplex C ℤ) (m r : ℤ) (hr : m + 1 < r),
          (K.truncGEXIso m r (by omega)).inv ≫ (q K m).f r ≫
            (K.truncGEXIso (m + 1) r (by omega)).hom = 𝟙 (K.X r)) ∧
        (∀ (K : CochainComplex C ℤ) (m : ℤ), QuasiIso (φ K m)) ∧
        (∀ {K L : CochainComplex C ℤ} (f : K ⟶ L) (m : ℤ),
          truncGEMap f m ≫ q L m = q K m ≫ truncGEMap f (m + 1) ∧
          ∃ (g : kernel (q K m) ⟶ kernel (q L m)),
            g ≫ kernel.ι (q L m) =
              kernel.ι (q K m) ≫ truncGEMap f m ∧
            (singleFunctor C m).map (HomologicalComplex.homologyMap f m) ≫
              φ L m = φ K m ≫ g) := by
  sorry

end CochainComplex
