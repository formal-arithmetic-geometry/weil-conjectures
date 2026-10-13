/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.InvertSCOhomology

/-! # Denominators for raw section cohomology

Source: Stacks Project, Tags 09MR and 01E4.
(blueprint: lem-pc-section-cohomology-principal-denominators).
-/

@[expose] public section

universe u
set_option autoImplicit false

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A class on a principal open lifts after multiplication by a power of its defining
function. This asserts only denominator lifting, not the kernel of restriction.

Source: Stacks Project, Tag 09MR, Lemma 30.17.3, surjectivity of the canonical map;
Tag 01E4, Lemma 20.7.3, computation by the section complex.
(blueprint: lem-pc-section-cohomology-principal-denominators).

Proof: Set Y = f⁻¹W and let b be the pullback of a to Y. Since W is affine and
f is quasi-compact and quasi-separated, Y is quasi-compact and quasi-separated.
The restricted coefficient module is quasi-coherent. Restriction of an injective
resolution to an open preserves injectivity, so the sections of I on Y and on
f⁻¹D(a) compute their module cohomology. Evaluation of pushforward identifies
these section complexes with K(W) and K(D(a)), respectively. These identifications
commute with restriction and with multiplication by functions, degree by degree,
and hence on homology. The inverse image f⁻¹D(a) is the nonvanishing open of b.
Apply invertS_cohomology on Y with the tensor unit as invertible module and b
as its section. Its surjective comparison expresses a class on D(b) as a finite
sum of images of fractions [n, xi]. Move their finitely many degrees to a common
N with the fraction transition relations and add numerators. The resulting single
fraction [N, xi] maps to the original class. The canonical equation of
invertS_cohomology says that multiplication of this image by b^N is the
restriction of xi. Tensor powers of the unit and their products with F identify
with F; their section multiplication maps become multiplication by b^N.
Transport the equation through the section-complex identifications above.
Multiplication by b is exactly the a-action restricted along the displayed
structure-sheaf map, so the result is a^N times the original class equals the
restriction of its numerator. For a=0 the open is empty and every target class
is zero (take N=0 and numerator zero); for a a unit the restriction is already
invertible (N=0). Degree zero, empty W, and the zero module require no exceptions. -/
theorem sectionCohomologyPresheaf_pow_lifts {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (hW : IsAffineOpen W) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let : Module Γ(T, W) (P.obj (op (T.basicOpen a))) :=
      Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
    ∀ x : P.obj (op (T.basicOpen a)), ∃ (n : ℕ) (y : P.obj (op W)),
      a ^ n • x = (P.map (homOfLE (T.basicOpen_le a)).op).hom y := by sorry

end AlgebraicGeometry.Scheme.Modules
