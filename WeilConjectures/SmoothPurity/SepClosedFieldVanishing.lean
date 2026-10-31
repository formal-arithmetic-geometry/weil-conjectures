/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.CategoryTheory.Sites.CohomologyOverObjectLocalization

/-!
# Étale decomposition and vanishing over a separably closed field

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/sk-prop-sf-kunneth-ordinary/lem-kun-0ezp.md
and its proof, Steps 1–3
(blueprint: lem-kun-0ezp).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Every étale scheme over a separably closed field is a coproduct of copies of its
spectrum, positive étale cohomology of every abelian sheaf vanishes, and every morphism
from this spectrum has zero positive higher direct images.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/sk-prop-sf-kunneth-ordinary/lem-kun-0ezp.md,
with proof Steps 1–3
(blueprint: lem-kun-0ezp).

Proof:
1. Apply the discrete-separable-fibre lemma to an étale scheme over `Spec L` at its
unique point. Its fibre is the scheme itself. Every singleton is open and closed and
is the spectrum of a finite separable extension of `L`. Since `L` is separably closed,
the structure map of each such extension is an isomorphism. The singleton open
subschemes therefore exhibit the scheme as a coproduct of copies of `Spec L`, over
`Spec L`.
2. Every covering of the terminal object has a summand isomorphic to it. The
separably-closed-sections epi-preservation lemma consequently makes global sections
preserve epimorphisms. Since global sections is left exact, it is exact. Applying it
to a K-injective resolution of an abelian sheaf in degree zero gives cohomology only
in degree zero, proving positive-degree vanishing.
3. For any `f : Spec L ⟶ Y` and any étale `V ⟶ Y`, the base change is étale over
`Spec L`, hence a coproduct of copies of `Spec L` by Step 1. Cohomology over this
object agrees with cohomology on the localized site; the étale-site localization
equivalence identifies that with the small étale site of the base change. The
coproduct-cohomology lemma identifies it with the product of the cohomologies of
the restrictions to the summands. Every positive-degree factor is zero by Step 2,
including the empty coproduct case. Thus the presheaf computing positive higher
direct images is zero. The higher-direct-image sheafification lemma identifies its
sheafification with the required higher direct image, which is therefore zero. -/
theorem separablyClosedField_etale_decomposition_and_vanishing
    (L : Type u) [Field L] [IsSepClosed L] :
    (∀ U : (Spec (.of L)).Etale,
      ∃ (I : Type u) (ι : I → (Spec (.of L) ⟶ U.left)),
        (∀ i, ι i ≫ U.hom = 𝟙 (Spec (.of L))) ∧
          Nonempty (IsColimit (Cofan.mk U.left ι))) ∧
    (∀ (F : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (q : ℤ), 0 < q →
      IsZero ((cohomology AddCommGrpCat.{u + 1} (Spec (.of L)) q).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) ∧
    (∀ (Y : Scheme.{u}) (f : Spec (.of L) ⟶ Y)
      (F : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (q : ℤ), 0 < q →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)))) := by
  sorry

end AlgebraicGeometry.Etale
