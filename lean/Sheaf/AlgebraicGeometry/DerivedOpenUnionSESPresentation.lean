/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # Short exact presentation on an arbitrary open union

Source: Stacks Project, Tag 08BV, applied on the open union and pushed to X.
(blueprint: lem-sc-derived-open-union-ses-presentation).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
namespace AlgebraicGeometry

/-- A short exact sequence of complexes representing the three direct-image terms
on an arbitrary open union, with the first arrow identified by adjunction.
No connecting morphism, integer shift, or distinguished triangle is asserted.

Source: Stacks Project, Tag 08BV (lemma-exact-sequence-j-star), its short exact
sequence of complexes applied on the union; Tag 079W (lemma-adjoint).
(blueprint: lem-sc-derived-open-union-ses-presentation).

Proof: Write W = U union V and O = U intersect V. Choose a K-injective
representative I of E with injective terms. Exact restriction to each open
preserves K-injectivity, because extension by zero is an exact left adjoint.
For T = W, U, V, O, form J_T by applying the ordinary open direct image to
I restricted to T, term by term. Thus J_T represents the right derived direct
image of the restriction of E. Take S to have terms J_W, J_U direct-sum J_V,
and J_O, with first map the pair of restrictions and second map their difference.
On any open Z, its degree n sequence is the section sequence on Z intersect W,
Z intersect U, Z intersect V, and Z intersect O. Since U and V cover W,
sheaf gluing gives injectivity and exactness at the middle. The last map is
surjective: injectivity implies flasqueness and a section on Z intersect O
lifts to Z intersect U. Hence S is short exact in every degree.
Compare localized-site restriction with restriction to the open subscheme by
Modules.overEquiv and exact derived factorization. The derived direct-image
adjunction then identifies Q(J_T) with G_T R_T(E) by uniqueness of right
adjoints, giving eA, eB, eC (using the biproduct comparison for eB).
These comparisons are compatible with counits. The union counit is the
transpose of identity on G_W R_W(E). Its restriction to U is obtained by
conjugating the image under nested restriction by the canonical composition
comparison, exactly derivedOpenHomRestriction. The adjunction mate is the
U component of the first map; the same argument gives its V component.
The biproduct universal property gives the displayed equality. This
construction uses no compactness or quasi-coherence. When either open is
empty the corresponding direct-image term is zero; when U = V the sequence
is the diagonal/difference split sequence. Thus these edge cases need no
additional hypotheses. -/
theorem derived_open_union_ses_presentation
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (U V : X.Opens)
    (G : ∀ W : X.Opens,
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W)) ⥤
        schemeDerivedCategory X)
    (adj : ∀ W : X.Opens,
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory ⊣
        G W)
    (E : schemeDerivedCategory X) :
    let R := fun W : X.Opens ↦
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    let A := (G (U ⊔ V)).obj ((R (U ⊔ V)).obj E)
    let B := (G U).obj ((R U).obj E) ⊞ (G V).obj ((R V).obj E)
    let C := (G (U ⊓ V)).obj ((R (U ⊓ V)).obj E)
    let β := ((adj (U ⊔ V)).homEquiv A ((R (U ⊔ V)).obj E)).symm (𝟙 A)
    let b := biprod.lift
      ((adj U).homEquiv A ((R U).obj E)
        (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_left) β))
      ((adj V).homEquiv A ((R V).obj E)
        (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_right) β))
    ∃ (S : ShortComplex
        (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ))
      (eA : DerivedCategory.Q.obj S.X₁ ≅ A)
      (eB : DerivedCategory.Q.obj S.X₂ ≅ B)
      (eC : DerivedCategory.Q.obj S.X₃ ≅ C),
      S.ShortExact ∧ DerivedCategory.Q.map S.f ≫ eB.hom = eA.hom ≫ b := by sorry

end AlgebraicGeometry
