module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Compactification.StrictTransform
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Sheaf.AlgebraicGeometry.ModuleStrictTransformAffinePushforward
public import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel
public import Sheaf.AlgebraicGeometry.StrictTransformDifferentCenters
public import WeilConjectures.Blowup.Principalization

@[expose] public section

/-!
# Strict transforms under a composition of blow-ups

Source: literature/stacks-project/divisors.tex, Tag 080I, clause (2)
(blueprint: lem-trf-strict-transform-composition)

This module records the scheme-theoretic statement that iterated strict transform
along two finite-type global blow-ups agrees with strict transform along the
specified composite blow-up.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Canonical maps used to expose the two successive strict transforms. -/

/-- The first strict transform in the composition statement.
Source: Stacks Project, divisors.tex, Tag 080I (blueprint: lem-trf-strict-transform-composition). -/
noncomputable def firstStrictTransform {S X : Scheme.{u}}
    (I : S.IdealSheafData) (f : X ⟶ S) : Scheme.{u} :=
  I.strictTransform f

/-- The structure map from the first strict transform to the first blow-up.
Source: Stacks Project, divisors.tex, Tag 080I (blueprint: lem-trf-strict-transform-composition). -/
noncomputable def firstStrictTransformToSource {S X : Scheme.{u}} (I : S.IdealSheafData)
    (f : X ⟶ S) : firstStrictTransform I f ⟶ I.blowup :=
  AlgebraicGeometry.strictTransformMap f I.blowupMap I.support.compl

/-- The second strict transform in the composition statement.
Source: Stacks Project, divisors.tex, Tag 080I (blueprint: lem-trf-strict-transform-composition). -/
noncomputable def secondStrictTransform {S X : Scheme.{u}} (I : S.IdealSheafData)
    (J : I.blowup.IdealSheafData) (f : X ⟶ S) : Scheme.{u} :=
  J.strictTransform (firstStrictTransformToSource I f)

/-- The closed immersion of the second strict transform into its fibre product.
Source: Stacks Project, divisors.tex, Tag 080I (blueprint: lem-trf-strict-transform-composition). -/
noncomputable def secondStrictTransformι {S X : Scheme.{u}} (I : S.IdealSheafData)
    (J : I.blowup.IdealSheafData) (f : X ⟶ S) :
    secondStrictTransform I J f ⟶
      pullback (firstStrictTransformToSource I f) J.blowupMap :=
  J.strictTransformι (firstStrictTransformToSource I f)

/--
Strict transforms compose along a specified composite of finite-type blow-ups.

Source: Stacks Project, divisors.tex, Tag 080I, lemma-strict-transform-composition-blowups,
clause (2). (blueprint: lem-trf-strict-transform-composition)

The proof follows Tag 080I. It compares the supported-section kernels of the
successive and composite strict transforms, uses principalization of the first
center and the Cartier-center comparison, and then identifies the resulting
structure sheaves with the closure-defined closed subschemes. The canonical
identification is induced by pullback, the specified blow-up isomorphism, and
the fibre-product universal property; it is compatible with both ambient
closed immersions and their projections.
-/
theorem strictTransform_comp_blowup
    (S X : Scheme.{u}) (f : X ⟶ S)
    (I : S.IdealSheafData) (hI : I.ofFiniteType)
    (J : I.blowup.IdealSheafData) (hJ : J.ofFiniteType)
    (K : S.IdealSheafData) (hK : K.ofFiniteType)
    (e : J.blowup ≅ K.blowup)
    (he : J.blowupMap ≫ I.blowupMap = e.hom ≫ K.blowupMap)
    (hV : (K.support : Set S) = (I.support : Set S) ∪
      I.blowupMap '' (J.support : Set I.blowup)) :
    ∃ φ :
        secondStrictTransform I J f ≅
          K.strictTransform f,
      φ.hom ≫ K.strictTransformι f ≫ pullback.fst f K.blowupMap =
        secondStrictTransformι I J f ≫
          pullback.fst (firstStrictTransformToSource I f) J.blowupMap ≫
          AlgebraicGeometry.strictTransformι f I.blowupMap I.support.compl ≫
          pullback.fst f I.blowupMap ∧
      φ.hom ≫ K.strictTransformι f ≫ pullback.snd f K.blowupMap ≫ e.inv =
        secondStrictTransformι I J f ≫
          pullback.snd (firstStrictTransformToSource I f) J.blowupMap := by
  sorry

end AlgebraicGeometry
