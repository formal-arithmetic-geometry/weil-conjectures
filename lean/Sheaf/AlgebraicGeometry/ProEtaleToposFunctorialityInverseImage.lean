/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Sheaf.CategoryTheory.SitePullbackAbelianUnderlying

/-!
# Functoriality of the inverse image on small pro-étale topoi

Source: Weil conjectures blueprint, `det-pe-topos-functoriality-inverse-image`, clauses 1–5
(blueprint: det-pe-topos-functoriality-inverse-image).

## Main definitions

* `setPullback`: the sheafified left Kan extension on set-valued sheaves.
* `setPullbackAdjunction`: its constructed adjunction to the existing `lowerStar` on sets.
* `setPullbackComp`: the canonical composition comparison, conjugate to `lowerStarComp`.

## Main statements

* `toposFunctorialityInverseImage`: covering families, finite limits, the adjunction,
  colimits, abelian underlying sets and exactness, and compatibility of composition.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The inverse image on set-valued sheaves, as sheafified left Kan extension.

Source: Weil conjectures blueprint, clause 2
(blueprint: det-pe-topos-functoriality-inverse-image). The direct image is the existing
`lowerStar (Type (u + 1)) f`, whose definition is restriction along base change. -/
noncomputable def setPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The constructed Kan-extension/sheafification adjunction on set-valued sheaves.

Source: Weil conjectures blueprint, clause 2
(blueprint: det-pe-topos-functoriality-inverse-image). -/
noncomputable def setPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    setPullback f ⊣ lowerStar (Type (u + 1)) f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The canonical composition comparison for set-valued inverse images.

Source: Weil conjectures blueprint, clause 5
(blueprint: det-pe-topos-functoriality-inverse-image). It is the conjugate of the existing
pushforward comparison, hence is compatible with the constructed adjunctions. The direct
image comparison in the direction of clause 5 is `(lowerStarComp (Type (u + 1)) f g).symm`.
The underlying site comparison is the canonical pullback associativity isomorphism. -/
noncomputable def setPullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    setPullback (f ≫ g) ≅ setPullback g ⋙ setPullback f :=
  (conjugateIsoEquiv ((setPullbackAdjunction g).comp (setPullbackAdjunction f))
    (setPullbackAdjunction (f ≫ g))).symm (lowerStarComp (Type (u + 1)) f g)

/-- The geometric morphism attached to an arbitrary morphism of schemes.

Source: Weil conjectures blueprint, clauses 1–5
(blueprint: det-pe-topos-functoriality-inverse-image).

Proof:
1. Base change preserves weakly étale objects and coverings by stability under base change
   (def-sfb-finite-lower-star, lem-weil-pbc-weakly-etale-composition-base-change).
   The small sites have terminal objects and fibre products
   (def-weil-pbc-small-proetale-site, def-pc-fibre-product). Their universal properties show
   that base change preserves both, hence finite limits.
2. Restriction along base change preserves the sheaf equalizer, since it preserves covers
   and fibre products. Compose the left Kan extension adjunction with sheafification
   (lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction). This is precisely
   `setPullbackAdjunction`; the same construction in abelian groups is the recorded
   `upperStarLowerStarAdjunction` (def-sfb-finite-upper-lower-star-adjunction).
3. The adjunction gives all colimits (lem-weil-pbc-left-adjoint-preserves-colimits).
   The opposite comma category at a site object is filtered, using finite limits of the
   source site and their preservation in step 1. Thus the Kan extension preserves finite
   limits of sets (lem-weil-pbc-presheaf-pullback-sets-left-exact). Inclusion of sheaves
   preserves limits (lem-weil-pbc-site-sheaf-sets-limits-sectionwise), and sheafification
   preserves finite limits (lem-weil-pbc-sheafification-sets-exact). Their composite is
   left exact, giving the geometric morphism.
4. Apply lem-weil-pbc-site-pullback-abelian-underlying, transporting the site presentation
   to its larger universe when necessary. Lifting the set adjunction to abelian group
   objects identifies the underlying sets of `upperStar AddCommGrpCat f` with set inverse
   image, including the group operations. This is the pullback of def-sfb-finite-upper-star.
   Finite limits give kernels and the abelian adjunction gives cokernels, so it is exact
   (lem-sfb-finite-upper-star-exact).
5. The canonical associativity isomorphism for fibre products gives `lowerStarComp` on
   sections, naturally in the site object and sheaf (def-sfb-finite-lower-star-comp).
   Compose adjunctions (def-weil-pbc-composite-adjunction). Taking the conjugate of the
   direct image comparison gives `setPullbackComp`, exactly as for abelian pullback
   (def-sfb-finite-upper-star-comp). The conjugation unit equation
   (lem-weil-pbc-conjugate-iso-unit-equation) gives the last displayed equality, proving
   compatibility with the adjunctions and thus composition of geometric morphisms. -/
theorem toposFunctorialityInverseImage {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (PreservesFiniteLimits (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) ∧
      ∀ (V : Y.ProEt) (R : Presieve V), R ∈ Scheme.ProEt.precoverage Y V →
        Presieve.map (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) R ∈
          Scheme.ProEt.precoverage X
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V)) ∧
    Nonempty (setPullback f ⊣ lowerStar (Type (u + 1)) f) ∧
    PreservesColimits (setPullback f) ∧
    PreservesFiniteLimits (setPullback f) ∧
    (Nonempty (upperStar AddCommGrpCat.{u + 1} f ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1}) ⋙
        setPullback f) ∧
      PreservesFiniteLimits (upperStar AddCommGrpCat.{u + 1} f) ∧
      PreservesFiniteColimits (upperStar AddCommGrpCat.{u + 1} f)) ∧
    ∀ F : Sheaf (Scheme.ProEt.topology Z) (Type (u + 1)),
      (setPullbackAdjunction (f ≫ g)).unit.app F ≫
          (lowerStar (Type (u + 1)) (f ≫ g)).map ((setPullbackComp f g).hom.app F) =
        ((setPullbackAdjunction g).comp (setPullbackAdjunction f)).unit.app F ≫
          (lowerStarComp (Type (u + 1)) f g).hom.app
            ((setPullback g ⋙ setPullback f).obj F) := by
  sorry

end AlgebraicGeometry.ProEtale
