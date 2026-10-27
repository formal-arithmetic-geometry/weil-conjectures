/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationSmoothPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Potential smooth cover of an almost homogeneous scheme

Source: Anantharaman, Schémas en groupes, Proposition 4.2.3, pp.58–59,
and Appendix II, Corollaries 2–3, p.73
(blueprint: lem-sfb-almost-homogeneous-potential-smooth-cover).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- An almost homogeneous flat scheme over a semilocal Dedekind base has an integral
surjective cover with finite underlying fibres by a smooth scheme, after a finite
fraction-field extension. The smooth acting group has connected field fibres.

The final equivalence says that each open piece is exactly an orbit on points over
any algebraically closed extension, and includes invariance as well as transitivity.

Source: Anantharaman, Proposition 4.2.3, pp.58–59, and Appendix II, Corollaries 2–3,
p.73 (blueprint: lem-sfb-almost-homogeneous-potential-smooth-cover).

Proof:
1. Make the reduced generic fibres geometrically reduced by a finite purely inseparable
   extension (lem-pur-finite-inseparable-geometric-reduction). Normalize the base;
   lem-sc-integral-closure-dedekind-surjective-fibres gives a semilocal Dedekind base.
2. Reduce both models. Over each DVR, the quotient by the nilradical is torsion free,
   hence flat by lem-weil-pbc-pid-torsion-free-module-flat. Products remain reduced
   by lem-sfb-flat-geometrically-reduced-pullback. Reduced-source factorization
   restricts the group operations and action and gives their identities.
3. Reduction preserves geometric points. Fppf surjectivity and Zariski's lemma give
   transitivity of the inherited opens. Geometrically reduced groups are smooth;
   lem-sfb-finite-equivariant-open-orbits makes the generic space smooth as well.
4. Apply lem-sfb-semitrait-potential-reduced-normalization simultaneously to both
   models. Their normalizations are finite surjective, flat, separated and finite type,
   with geometrically reduced fibres and unchanged generic fibres. Integrality is
   transitive, so the new base is the integral closure of the original ring.
5. On the open traits apply lem-sfb-trait-normalization-group-structure; uniqueness
   on the generic overlaps glues the group laws. Smooth fibres and the flat finite
   presentation criterion sbc-lem-smooth-criterion make the normalized group smooth.
6. Projection and action are smooth, related by (g,z) ↦ (g,gz). Apply
   lem-sfb-componentwise-normalization-smooth-pullback to lift the action. Its identities
   extend from the generic fibre by separatedness and schematic density of that fibre.
7. On every field fibre use lem-sfb-finite-equivariant-open-orbits with the finite
   surjective normalized group and space maps. It makes the space smooth and identifies
   the neutral group's open orbits with its connected components. The fibre criterion
   then makes the whole normalized space smooth.
8. Glue the relative neutral open subgroups on the open traits using
   lem-sfb-smooth-group-relative-neutral-open. Noetherianness makes the open subgroup
   quasi-compact, hence finite type; it is smooth, separated and has connected field
   fibres. Restrict the lifted action to it.
9. Compose the finite normalization and reduction maps to X_T, then the integral base
   change X_T → X. This gives an integral surjective composite.
10. Over a point of X, the normalized base has finitely many points with finite residue
    extensions. The tensor products of these residue fields have finite spectra;
    finiteness of the normalization then gives finite underlying fibres of the composite.
    Every construction allows empty spaces, empty fibres and generic-only pieces. -/
theorem exists_almostHomogeneous_potential_smooth_cover
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R = 1) (hmax : Set.Finite {m : Ideal R | m.IsMaximal})
    (G X : Over (Spec (.of R))) [GrpObj G] [ModObj G X]
    [IsSeparated G.hom] [Flat G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsSeparated X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    [QuasiCompact X.hom]
    (n : ℕ) (V : Fin n → Over (Spec (.of R)))
    [∀ j, ModObj G (V j)] (inc : ∀ j, V j ⟶ X)
    [∀ j, IsModHom G (inc j)] [∀ j, IsOpenImmersion (inc j).left]
    (hcover : ∀ x : X.left, ∃ j, x ∈ Set.range (inc j).left)
    (hhomogeneous : ∀ j, Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (Spec (.of R))) (yoneda.map (ModObj.leftSMul G (V j)))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra (FractionRing R) L)
      (_ : Algebra R L) (_ : IsScalarTower R (FractionRing R) L),
      FiniteDimensional (FractionRing R) L ∧
      IsNoetherianRing (integralClosure R L) ∧ IsIntegrallyClosed (integralClosure R L) ∧
      ringKrullDim (integralClosure R L) = 1 ∧
      Set.Finite {m : Ideal (integralClosure R L) | m.IsMaximal} ∧
      ∃ (H Y : Over (Spec (.of (integralClosure R L))))
        (_ : GrpObj H) (_ : ModObj H Y),
        Smooth H.hom ∧ IsSeparated H.hom ∧
        LocallyOfFiniteType H.hom ∧ QuasiCompact H.hom ∧
        (∀ (Ω : Type u) [Field Ω] (t : Spec (.of Ω) ⟶ Spec (.of (integralClosure R L))),
          ConnectedSpace (pullback (C := Scheme.{u}) H.hom t)) ∧
        Smooth Y.hom ∧ IsSeparated Y.hom ∧
        LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
        ∃ p : Y ⟶ (Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))))).obj X,
          IsIntegralHom (p.left ≫ pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))))) ∧
          Surjective (p.left ≫ pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))))) ∧
          (∀ x : X.left, Set.Finite ((p.left ≫ pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))))) ⁻¹' {x})) ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (t : Spec (.of Ω) ⟶ Spec (.of (integralClosure R L))),
            ∃ (m : ℕ) (U : Fin m → (pullback (C := Scheme.{u}) Y.hom t).Opens),
              (∀ z : pullback (C := Scheme.{u}) Y.hom t, ∃ j, z ∈ U j) ∧
              Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
              ∀ (E : Type u) [Field E] [IsAlgClosed E] (c : Spec (.of E) ⟶ Spec (.of Ω))
                (j : Fin m) (x : Over.mk (c ≫ t) ⟶ Y),
                (∃ a : Spec (.of E) ⟶ pullback (C := Scheme.{u}) Y.hom t,
                  a ≫ pullback.snd Y.hom t = c ∧ a ≫ pullback.fst Y.hom t = x.left ∧
                  ∀ z : Spec (.of E), a z ∈ U j) →
                ∀ y : Over.mk (c ≫ t) ⟶ Y,
                  (∃ b : Spec (.of E) ⟶ pullback (C := Scheme.{u}) Y.hom t,
                    b ≫ pullback.snd Y.hom t = c ∧ b ≫ pullback.fst Y.hom t = y.left ∧
                    ∀ z : Spec (.of E), b z ∈ U j) ↔
                  ∃ g : Over.mk (c ≫ t) ⟶ H, g • x = y := by
  sorry

end AlgebraicGeometry
