/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension

/-!
# Finiteness for ordinary finite-coefficient direct images

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ctf-finite-geometric-restriction/
sk-cor-sf-direct-image-ctf/det-prop-sf-finiteness.md and its companion proof;
Stacks Project, Tags 0GL0 and 03QU (blueprint: det-prop-sf-finiteness).

The two sites use ordinary fixed-coefficient derived functors. On the pro-etale site,
boundedness and the intrinsic constructibility of every cohomology sheaf are written
separately, using the recorded fixed-module sheaf predicate. No etale-origin condition
or adic completeness condition is imposed on the inputs.

The torsion-dimension clauses are the publicly imported exact declarations
`Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_finiteType` and
`Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Ordinary etale direct image preserves bounded constructibility without separatedness.
Source: blueprint det-prop-sf-finiteness, first assertion; Stacks Project, Tag 0GL0
(blueprint: det-prop-sf-finiteness).

Proof:
1. If X is empty, all sheaves and complexes on its small site are zero, so the assertion
follows from preservation of zero by derived direct image.
2. Otherwise the positive annihilator supplied by HasInvertibleExponent is invertible
in k: evaluate it in the residue field at a point of X and use injectivity of the field
map. This is exactly the coefficient convention sbc-def-coefficient-conventions.
3. Quasi-compactness of f and Y makes X quasi-compact. Both structure morphisms are
therefore finite type. Apply thm-dg-finite-type-constructibility, which allows arbitrary
nonseparated k-morphisms. Its finite-cover argument combines finitely many cohomological
bounds and constructible cohomology sheaves, giving the displayed recorded predicate. -/
theorem finiteCoefficientFiniteness_etale_directImage
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [HasInvertibleExponent Λ X]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hf : f ≫ aY = aX) (K : Etale.DerivedCategoryModule Λ X)
    (hK : Etale.DerivedCategory.isBoundedConstructible Λ X K) :
    Etale.DerivedCategory.isBoundedConstructible Λ Y
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K) := by
  sorry

/-- Ordinary pro-etale direct image preserves bounded intrinsically constructible complexes.
Source: blueprint det-prop-sf-finiteness, first assertion on both sites
(blueprint: det-prop-sf-finiteness).

Proof:
1. Handle the empty source by zero sheaves. Otherwise descend the invertible annihilator
to k. Quasi-compactness makes X and Y finite type over k, hence Noetherian; f is qcqs.
2. Apply lem-weil-pbc-finite-ring-constructible-derived-origin and the canonical exact
realization equivalence between fixed-module sheaves and constant-ring module sheaves.
The intrinsic cohomology predicate and boundedness give a bounded constructible etale
complex L with nu_X^* L isomorphic to K; no Tor condition is involved.
3. The ordinary direct-image comparison prop-weil-pbc-comparison-direct-image on D+
identifies Rf_proet,* K with nu_Y^* Rf_et,* L. Apply the etale assertion just stated.
4. Exact comparison and the intrinsic constructible equivalence transfer every cohomology
sheaf and its finite interval of vanishing, giving both displayed conclusions. -/
theorem finiteCoefficientFiniteness_proetale_directImage
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [HasInvertibleExponent Λ X]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hf : f ≫ aY = aX)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hKb : DerivedCategory.TStructure.t.bounded K)
    (hKc : ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X Λ
      ((DerivedCategory.homologyFunctor _ q).obj K)) :
    DerivedCategory.TStructure.t.bounded
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K) ∧
    ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf Y Λ
      ((DerivedCategory.homologyFunctor _ q).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K)) := by
  sorry

/-- Compactly supported direct images preserve bounded constructibility on both sites,
and vanish above twice the dimension of the original geometric fibres on sheaves.
Source: blueprint det-prop-sf-finiteness, compact-support and original-fibre clauses;
Stacks Project, Tag 0GL0 (blueprint: det-prop-sf-finiteness).

Proof:
1. The empty source gives zero. Otherwise descend the invertible annihilator to k.
Quasi-compactness plus HasCompactification is precisely the node's compactifiability:
for every library compactification c, c.i is quasi-compact iff f is quasi-compact.
Choose c = (j,r). Properness gives finite type for r, and j is a quasi-compact open
immersion. X, its compactification and Y are finite type over k and Noetherian.
The factorization also makes f separated.
2. Extension by zero j_! is exact and preserves constructible sheaves by
lem-weil-pbc-extension-by-zero-exact and lem-fin-extension-by-zero. Thus Dj_! preserves
bounded constructibility. Apply lem-fin-proper-bounded-constructible to r.
The resulting Rr_* Dj_! is the candidate of def-amb-etale-compact-support;
lem-amb-etale-compact-comparisons identifies it with the chosen Rf_! on D+.
3. For every etale sheaf F, apply lem-dg-compact-support-amplitude with the stated
bound on the original geometric fibres of f. This kills cohomology above 2e;
no constructibility of F or bound on the fibres of r is used.
4. For bounded intrinsically constructible pro-etale K, use the exact realization
and lem-weil-pbc-finite-ring-constructible-derived-origin to descend to an etale L.
The comparison lem-amb-compact-support-site-comparison-open identifies the two
compact-support expressions on D+. Step 2 and exact cohomology comparison give the
pro-etale boundedness and intrinsic constructibility assertions.
5. A constructible pro-etale sheaf descends to an etale complex concentrated in
[0,0], because the origin equivalence preserves and reflects each interval. Apply
step 3 and exact comparison to obtain the final pro-etale sheaf vanishing clause.
All bounds concern sheaves in degree zero, so no restriction on shifted complexes
has been silently imposed. -/
theorem finiteCoefficientFiniteness_compactSupport
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [HasInvertibleExponent Λ X]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hf : f ≫ aY = aX) :
    (∀ K : Etale.DerivedCategoryModule Λ X,
      Etale.DerivedCategory.isBoundedConstructible Λ X K →
        Etale.DerivedCategory.isBoundedConstructible Λ Y
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K)) ∧
    (∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)),
      DerivedCategory.TStructure.t.bounded K →
      (∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X Λ
        ((DerivedCategory.homologyFunctor _ q).obj K)) →
      DerivedCategory.TStructure.t.bounded
        ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K) ∧
      ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf Y Λ
        ((DerivedCategory.homologyFunctor _ q).obj
          ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K))) ∧
    ∀ (e : ℕ),
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) →
      (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (q : ℤ), (2 * e : ℤ) < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) ∧
      (∀ (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)),
        Scheme.IsConstructibleProEtaleFixedModuleSheaf X Λ F →
        ∀ q : ℤ, (2 * e : ℤ) < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj
            ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
              ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
  sorry

end AlgebraicGeometry
