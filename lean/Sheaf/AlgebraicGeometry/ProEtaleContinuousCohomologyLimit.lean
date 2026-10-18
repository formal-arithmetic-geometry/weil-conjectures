/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic
public import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence

/-!
# Derived sections of epimorphic inverse limits on the pro-etale site

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
sk-prop-pe-continuous-cohomology/sk-prop-pe-continuous-cohomology-limit.md;
Bhatt--Scholze, Propositions 3.1.9 and 3.1.10
(blueprint: det-pe-continuous-cohomology-limit).

Abelian sheaves are represented by modules over the constant integer ring sheaf.
The abbreviations below specialize the recorded constant-sheaf, module-sheaf and
K-injective derived-sections constructions. No coefficient action is supplied as
an additional hypothesis: the integer action on an abelian sheaf is unique.
-/

@[expose] public section

set_option autoImplicit false

universe t w w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Register the existing locally-bijective criterion at the standard coefficient size.
The explicit universe argument prevents the imported max-universe instance from leaving
an undetermined auxiliary universe. This is the existing site-transport proof.
Source: Stacks Project, Tag 03DA; blueprint main-20261015,
det-pe-continuous-cohomology-limit, the category of abelian sheaves
(blueprint: det-pe-continuous-cohomology-limit). -/
noncomputable instance (priority := 3000) continuousCohomology_locallyBijective
    (X : Scheme.{t}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} X

/-- The constant integer ring sheaf on the unchanged small pro-etale site.
Source: blueprint main-20261015, det-pe-continuous-cohomology-limit, first proof paragraph
(blueprint: det-pe-continuous-cohomology-limit). -/
noncomputable abbrev continuousCohomologyIntegerSheaf (X : Scheme.{t}) :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{t + 1}).obj
    (CommRingCat.of (ULift.{t + 1} ℤ))

/-- Abelian sheaves, presented as modules over the constant integer sheaf.
The integer action on any abelian sheaf extends uniquely to locally constant integer
sections, so this imposes no additional structure on the abelian sheaves of the statement.
Source: blueprint main-20261015, det-pe-continuous-cohomology-limit, first proof paragraph
(blueprint: det-pe-continuous-cohomology-limit). -/
noncomputable abbrev continuousCohomologyAbelianSheaves (X : Scheme.{t}) :=
  ringedSiteModules.{t + 1}
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj
        (continuousCohomologyIntegerSheaf X))


/-- Derived sections over an arbitrary site object, on sheaves placed in degree zero.
This is exactly the recorded unbounded derived-sections functor, computed on K-injective
resolutions, precomposed with the existing degree-zero embedding.
Source: blueprint main-20261015, det-pe-continuous-cohomology-limit, second proof paragraph
(blueprint: det-pe-continuous-cohomology-limit). -/
noncomputable abbrev continuousCohomologySheafSections (X : Scheme.{t}) (W : X.ProEt)
    [HasDerivedCategory.{w} (continuousCohomologyAbelianSheaves X)]
    [HasDerivedCategory.{w'} AddCommGrpCat.{t + 1}] :
    continuousCohomologyAbelianSheaves X ⥤ DerivedCategory AddCommGrpCat.{t + 1} :=
  DerivedCategory.singleFunctor _ 0 ⋙
    siteModuleDerivedSections.{t + 1, t, t, w, w'} (Scheme.ProEt.topology X)
      (continuousCohomologyIntegerSheaf X) W

/-- The canonical ordinary-to-derived-limit map is an isomorphism for an epimorphic
abelian-sheaf tower, and derived sections over every pro-etale object identify its
ordinary limit with the derived limit of its derived sections.

Here `IsDerivedLimit` says precisely that the object is a fibre of `1 - shift` on
the product in the derived category. Thus the second conjunct states the displayed
isomorphism in the source without choosing a noncanonical fibre object. The first
conjunct uses the actual canonical map into the recorded `Cone(1 - T)[-1]` model.
The natural-number index `n` represents the source's positive index `n + 1`.

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-pe-continuous-cohomology/sk-prop-pe-continuous-cohomology-limit.md
(blueprint: det-pe-continuous-cohomology-limit).

Proof:
1. Regard the abelian sheaves as modules over the constant integer sheaf
   (def-weil-pbc-constant-sheaf, def-weil-sheaf-of-modules-category).
   By det-pe-products-derived the termwise product is the derived product.
   Therefore the recorded Roos model of det-pe-milnor-sequence is the fibre of
   `1 - shift` specified by the statement. Apply det-pe-milnor-epimorphic to obtain
   invertibility of the canonical map from the ordinary limit in degree zero.
2. Compose the rotated cone triangle with this isomorphism. Its product arrow has
   coordinates the ordinary limit projections (def-pur-sheaf-inverse-limit), so
   it is a Roos triangle in the sense of def-weil-derived-limit.
3. Apply lem-kun-site-rgamma-derived-limit with the constant integer ring sheaf
   and the arbitrary object W. The recorded K-injective derived-sections functor
   preserves the product and sends this Roos triangle to a Roos triangle.
   Hence the derived sections of the ordinary limit form a fibre of `1 - shift`
   on the product of the derived sections of the tower terms, as required. -/
theorem continuousCohomology_limit
    (X : Scheme.{t})
    [HasDerivedCategory.{w} (continuousCohomologyAbelianSheaves X)]
    [HasDerivedCategory.{w'} AddCommGrpCat.{t + 1}]
    (F : ℕᵒᵖ ⥤ continuousCohomologyAbelianSheaves X)
    (ht : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) :
    IsIso (DerivedCategory.Q.{w}.map (milnorLimitComparison F)) ∧
      ∀ W : X.ProEt,
        IsDerivedLimit
          (K := fun n : ℕ ↦ (continuousCohomologySheafSections X W).obj (F.obj (op n)))
          (fun n : ℕ ↦ (continuousCohomologySheafSections X W).map
            (F.map (homOfLE (Nat.le_succ n)).op))
          ((continuousCohomologySheafSections X W).obj (limit F)) := by
  sorry

end AlgebraicGeometry.ProEtale
