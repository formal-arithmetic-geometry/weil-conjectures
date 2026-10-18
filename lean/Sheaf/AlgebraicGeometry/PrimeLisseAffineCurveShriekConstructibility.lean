/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D9
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-!
# Prime-torsion lisse coefficients on an affine smooth relative curve

The affine prime-torsion part of Stacks Project, Tags 0GKY and 0GKX.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Prime-torsion lisse coefficients on an affine smooth relative curve have constructible
compactly supported cohomology over an affine finite-type integer base.
Source: Stacks Project, Tag 0GKY, `lemma-loc-constant-shriek-rel-dim-1`, its prime-torsion
finite-etale-cover argument, together with Tag 0GKX, `lemma-constant-shriek-rel-dim-1`.
(blueprint: lem-weil-pbc-prime-lisse-affine-curve-shriek-constructibility).

Proof:
The base is Noetherian because it is of finite type over the integers. Smoothness makes X
locally of finite type over this base, hence locally Noetherian; X is affine, hence Noetherian.
Identify X with the spectrum of its coordinate ring. Pullback along this isomorphism preserves
finite local constancy and the equation p times the identity equals zero. Apply the lisse
finite-etale filtration theorem with exponent one. It gives a finite etale surjection g:T -> X
of constant positive degree d prime to p, and a finite disjoint affine clopen cover of T on
which g^*F has finite filtrations with finite constant successive quotients.

The trace composed with the unit F -> g_*g^*F is multiplication by d. To compare the geometric
fibre degree convention with the separably closed convention of the trace theorem, note that
a finite etale algebra over a separably closed field is a product of copies of that field.
After extension to its algebraic closure the same number of factors remains; the prescribed
geometric degree therefore gives degree d over the separably closed field too. Choose integers
a,b with a*d + b*p = 1. The map a times the trace retracts the unit because p annihilates F.
This works for a zero sheaf and for an empty source as well.

A finite map is proper and has exact direct image on etale module sheaves, so its derived
compactified shriek is direct image. Composition and compactification independence identify
the shriek of g^*F over the base with the shriek of g_*g^*F over X. Thus the given compactly
supported object is a retract of that of g^*F on T.

Each affine clopen component of T is affine over the affine base. Its structural morphism
is smooth of relative dimension one by composition of the etale morphism with f; it is also
separated. A proper compactification over the Noetherian base has Noetherian ambient scheme,
so its open immersion is quasi-compact, as required by the constant-coefficient theorem.
Tag 0GKX gives constructible compact-support cohomology for every constant finite
module on this component. For each finite filtration, apply the shriek functor to its
short-exact triangles. Induction on the filtration, starting at zero, and the Serre property
of constructible sheaves show that all cohomology sheaves remain constructible. Equivalently,
the property of having constructible cohomology is a triangulated subcategory of the derived
category. The finite disjoint-open biproduct decomposition and composition identify the sum
of these compact-support objects with that of g^*F on T; additivity and closure under finite
sums give its constructibility. Finally homology preserves the retraction. A retract of a
constructible sheaf is constructible (it is the kernel of one minus its projector), giving
the conclusion for the prescribed compactification and every integer q. -/
theorem isConstructibleEtaleModuleSheaf_prime_lisse_affine_curve_shriek
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsAffine X] [IsAffineHom f] [SmoothOfRelativeDimension 1 f]
    (p : ℕ) (hp : p.Prime)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsFiniteLocallyConstantSheaf F) (hkill : p • 𝟙 F = 0)
    (c : Compactification f) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F))) := by sorry

end AlgebraicGeometry.Etale
