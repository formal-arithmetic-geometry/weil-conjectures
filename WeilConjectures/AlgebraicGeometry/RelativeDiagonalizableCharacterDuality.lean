/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingDiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Relative character duality for split diagonalizable groups

Source: Conrad, Reductive group schemes, Appendix B.1 and Remark B.1.2, pp.280--281;
Milne, Algebraic Groups (2017), Lemma 12.4, Remark 12.6 and Theorem 12.9, pp.232--234,
with the relative coefficient argument recorded in the DAG
(blueprint: lem-sfb-relative-diagonalizable-character-duality).

The range subfunctor is the pointwise image. Its displayed universal arrow is its
fppf sheafification. IsFppfGroupQuotient uses the pointwise coset coequalizer and its
sheafification universal arrow. All kernel, image and quotient statements are made
also after pullback to an arbitrary base scheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- Local character classification, closed immersions, kernels, fppf images and quotients,
with arbitrary base change and geometric-fibre detection.

Source: Conrad, Reductive group schemes, Appendix B.1 and Remark B.1.2, pp.280--281;
Milne, Algebraic Groups (2017), Lemma 12.4, Remark 12.6 and Theorem 12.9, pp.232--234,
extended to rings by the following relative argument
(blueprint: lem-sfb-relative-diagonalizable-character-duality).

Proof:
1. The affine adjunction and affine tensor pushout translate group homomorphisms into
   Hopf maps A[N] → A[M]. The tensor basis identifies A[M] tensor A[M] with A[M × M].
   A monomial map sends e_n to e_(u n) and respects all three Hopf operations.
2. Compare the coefficients in Δz = z tensor z and εz = 1. They are orthogonal
   idempotents summing to 1, hence give a finite clopen partition by the
   spec-clopen-idempotent lemma. On each nonempty part z is exactly one basis vector.
3. Apply this to finitely many generators of N and refine their finite partitions.
   Relations and basis independence on each nonzero piece give a unique u : N → M.
   The maps agree on overlaps, yielding the unique locally constant character map.
4. The image of the coordinate map is the span of e_m for m in the image of u.
   Basis independence and the closed-immersion affine-cover criterion give precisely
   surjectivity of the local character homomorphisms.
5. On every test algebra B the points are Hom(M,Bˣ). The kernel consists of the
   characters trivial on the image of u, equivalently those factoring uniquely through
   M/range(u). The affine adjunction and tensor pushout give the displayed kernel square.
6. The subgroup-algebra-coset-presentation lemma makes A[M] free over A[L] with a
   nonempty coset basis, and finitely presented as an algebra. Tensoring with that free
   module detects exactness, so the inclusion is faithfully flat. The affine flatness
   criterion and faithful-flat spectrum surjectivity give a flat surjective finitely
   presented quotient map, hence a singleton fppf cover.
7. Representable fpqc descent makes the targets fppf sheaves. The pointwise coset
   quotient maps injectively to D(L); sections lift on the base-changed cover from
   step 6. The local-bijection sheafification criterion gives IsFppfGroupQuotient.
   Its torsor isomorphism sends (g,h) to (g,gh), with inverse (g,g') ↦ (g,g⁻¹g').
8. Factor u as N → range(u) → M. The first gives the closed immersion D(range(u))
   into D(N), the second an fppf cover onto D(range(u)). The pointwise image therefore
   maps locally bijectively to that representable sheaf, giving its stated universal arrow.
9. The canonical tensor identification B tensor A[M] = B[M] sends b tensor e_m to b e_m.
   It respects all monomial maps and Hopf operations. The affine fibre-product formula
   gives the specified natural group isomorphisms under every ring map, including B = 0.
   Apply the previous steps on affine opens of an arbitrary base change and glue.
   Finally refine the clopen partitions of two maps. A geometric point on each nonempty
   part detects the same basis indices, hence the same maps; scheme-morphism gluing
   gives equality. Empty generating sets, torsion and nilpotents cause no exceptions.
-/
theorem relative_diagonalizable_character_duality
    (A : Type u) [CommRing A] [Nontrivial A]
    (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    [AddGroup.FG M] [AddGroup.FG N] :
    (∀ f : ringDiagonalizableGroup A M ⟶ ringDiagonalizableGroup A N,
      ∃! χ : LocallyConstant (Spec (.of A)) (N →+ M),
        (∀ x : Spec (.of A), ∃ U : (Spec (.of A)).Opens,
          x ∈ U ∧ (∀ y ∈ U, χ y = χ x) ∧
          (Over.pullback U.ι).map f.hom.hom =
            (Over.pullback U.ι).map (ringDiagonalizableGroupMap A (χ x)).hom.hom) ∧
        (∀ (x : Spec (.of A)) (U : (Spec (.of A)).Opens), x ∈ U →
          ∀ v : N →+ M,
            (Over.pullback U.ι).map f.hom.hom =
              (Over.pullback U.ι).map (ringDiagonalizableGroupMap A v).hom.hom →
            v = χ x) ∧
        (IsClosedImmersion f.hom.hom.left ↔ ∀ x, Function.Surjective (χ x))) ∧
    (∀ (u : N →+ M) (T : Over (Spec (.of A))),
      IsPullback
        ((Over.pullback T.hom).map
          (ringDiagonalizableGroupMap A (QuotientAddGroup.mk' u.range)).hom.hom)
        (toUnit ((Over.pullback T.hom).mapGrp.obj
          (ringDiagonalizableGroup A (M ⧸ u.range))).X)
        ((Over.pullback T.hom).map (ringDiagonalizableGroupMap A u).hom.hom)
        η[((Over.pullback T.hom).mapGrp.obj (ringDiagonalizableGroup A N)).X] ∧
      IsClosedImmersion
        ((Over.pullback T.hom).map
          (ringDiagonalizableGroupMap A u.rangeRestrict).hom.hom).left ∧
      ((Over.pullback T.hom).map
          (ringDiagonalizableGroupMap A u.range.subtype).hom.hom) ≫
        ((Over.pullback T.hom).map
          (ringDiagonalizableGroupMap A u.rangeRestrict).hom.hom) =
        (Over.pullback T.hom).map (ringDiagonalizableGroupMap A u).hom.hom ∧
      Presheaf.IsSheaf (Scheme.fppfTopology.over T.left)
        (yoneda.obj ((Over.pullback T.hom).mapGrp.obj
          (ringDiagonalizableGroup A u.range)).X) ∧
      (∃ ηi : (Subfunctor.range (yoneda.map
            ((Over.pullback T.hom).map (ringDiagonalizableGroupMap A u).hom.hom))).toFunctor
          ⟶ yoneda.obj ((Over.pullback T.hom).mapGrp.obj
            (ringDiagonalizableGroup A u.range)).X,
        ηi ≫ yoneda.map ((Over.pullback T.hom).map
            (ringDiagonalizableGroupMap A u.rangeRestrict).hom.hom) =
          (Subfunctor.range (yoneda.map
            ((Over.pullback T.hom).map (ringDiagonalizableGroupMap A u).hom.hom))).ι ∧
        ∀ Z : Sheaf (Scheme.fppfTopology.over T.left) (Type u),
          Function.Bijective (fun h : yoneda.obj ((Over.pullback T.hom).mapGrp.obj
              (ringDiagonalizableGroup A u.range)).X ⟶ Z.obj ↦ ηi ≫ h))) ∧
    (∀ (L : AddSubgroup M) (T : Over (Spec (.of A))),
      IsFppfGroupQuotient
        ((Over.pullback T.hom).mapGrp.map
          (ringDiagonalizableGroupMap A (QuotientAddGroup.mk' L)))
        ((Over.pullback T.hom).mapGrp.map (ringDiagonalizableGroupMap A L.subtype)) ∧
      Flat ((Over.pullback T.hom).map
        (ringDiagonalizableGroupMap A L.subtype).hom.hom).left ∧
      Surjective ((Over.pullback T.hom).map
        (ringDiagonalizableGroupMap A L.subtype).hom.hom).left ∧
      LocallyOfFinitePresentation ((Over.pullback T.hom).map
        (ringDiagonalizableGroupMap A L.subtype).hom.hom).left ∧
      QuasiCompact ((Over.pullback T.hom).map
        (ringDiagonalizableGroupMap A L.subtype).hom.hom).left ∧
      QuasiSeparated ((Over.pullback T.hom).map
        (ringDiagonalizableGroupMap A L.subtype).hom.hom).left) ∧
    (∀ (B : Type u) [CommRing B] (ρ : A →+* B),
      ∃ e : ∀ (P : Type u) [AddCommGroup P] [AddGroup.FG P],
        (Over.pullback (Spec.map (CommRingCat.ofHom ρ))).mapGrp.obj
          (ringDiagonalizableGroup A P) ≅ ringDiagonalizableGroup B P,
        (∀ (P : Type u) [AddCommGroup P] [AddGroup.FG P],
          (e P).inv.hom.hom.left ≫
              pullback.fst (ringDiagonalizableGroup A P).X.hom
                (Spec.map (CommRingCat.ofHom ρ)) =
            Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom P ρ))) ∧
        (∀ (P Q : Type u) [AddCommGroup P] [AddCommGroup Q]
            [AddGroup.FG P] [AddGroup.FG Q] (v : P →+ Q),
          ((Over.pullback (Spec.map (CommRingCat.ofHom ρ))).mapGrp.map
              (ringDiagonalizableGroupMap A v)) ≫ (e P).hom =
            (e Q).hom ≫ ringDiagonalizableGroupMap B v)) ∧
    (∀ f g : ringDiagonalizableGroup A M ⟶ ringDiagonalizableGroup A N,
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of A)),
        (Over.pullback s).map f.hom.hom = (Over.pullback s).map g.hom.hom) → f = g) := by
  sorry

end AlgebraicGeometry
