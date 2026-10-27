/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSetoidSpace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest

/-! # Étale quotients by open equivalence relations

Source: Stacks Project, stacks-morphisms.tex, Tag 0DU1, lemma-quotient-etale
(blueprint: lem-sfb-open-relation-etale-quotient).

The quotient stack is specified by its existing fppf groupoid presentation. The orbit
presheaf is the sectionwise coequalizer of source and target. Its sheafification is taken
in the larger universe and identified, compatibly with the quotient projection, with the
lift of an algebraic space in the original universe. No representative is chosen by a def.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An open relation on a flat locally finitely presented space has an étale space quotient.
The equivalence of stacks and the sheafification comparison both respect the projection
from `U`. The map `f` is the induced map to `Y`, as expressed by `q ≫ f = p`.

Source: Stacks Project, stacks-morphisms.tex, Tag 0DU1, lemma-quotient-etale
(blueprint: lem-sfb-open-relation-etale-quotient).

Proof:
1. The open relation map j is representable étale by open-immersion étaleness.
   The projections U ×_Y U → U are flat and locally finitely presented by base change;
   composing with j gives these properties for s and t, using
   lem-sfb-stack-chartwise-smooth-etale-calculus.
2. Apply lem-sfb-flat-groupoid-algebraic-quotient. The quotient stack F is algebraic,
   U → F is surjective flat locally finitely presented, and R is its self-relation.
3. An open immersion is injective on sections of every test scheme. Thus an object
   coming from U has only its identity automorphism. Every object is fppf locally of
   this form by lem-sfb-groupoid-stackification-local-description; the isomorphism-sheaf
   axiom makes its automorphisms globally trivial. Apply lem-sfb-algebraic-setoid-space
   to get a space X and the displayed equivalence. The groupoid's map to Y descends,
   giving f and q with q followed by f equal to p.
4. The coequalizer is the pointwise orbit quotient, since arrow existence is already
   an equivalence relation by the groupoid laws. Its map to X extends uniquely across
   sheafification. Conversely lift a section of X fppf locally to U. On overlaps the
   two representatives are related by R, so their orbit classes glue. A common cover
   proves independence of all choices and compatibility with restrictions. The maps
   are inverse locally and hence globally. This gives the displayed isomorphism and
   its normalization on U, using def-weil-pbc-sheafification.
5. Descend flatness and local finite presentation of f along U → X, using
   lem-sfb-representable-fppf-etale-open-descent with the identity target cover.
   No surjectivity of p:U → Y is used.
6. The product cover U ×_Y U → X ×_Y X factors into two base changes of U → X;
   hence it is surjective flat locally finitely presented. The pullback of the
   relative diagonal of f is j:R → U ×_Y U. Target descent in
   lem-sfb-representable-fppf-etale-open-descent makes that diagonal an open immersion.
7. Local finite presentation gives local finite type. Apply
   lem-sfb-space-unramified-open-diagonal. On compatible surjective étale scheme charts,
   lem-sfb-space-local-properties-chart-test gives flatness and local finite
   presentation, and lem-sfb-unramified-etale-compatible-charts gives unramifiedness.
   The scheme morphism is étale by def-weil-etale-morphism. The compatible-chart
   criterion then gives MapIsLocally Etale f. -/
theorem open_relation_etale_quotient {S : Scheme.{u}} {Y U R : AlgebraicSpace S}
    (p : U ⟶ Y) (s t : R.obj.obj ⟶ U.obj.obj)
    (e : U.obj.obj ⟶ R.obj.obj) (i : R.obj.obj ⟶ R.obj.obj)
    (c : Limits.pullback s t ⟶ R.obj.obj)
    (hY : t ≫ p.hom.hom = s ≫ p.hom.hom)
    (hflat : MapIsFlat p) (hlfp : MapIsLocallyOfFinitePresentation p)
    (hopen : IsRepresentableWith (fun _ _ a ↦ IsOpenImmersion a.left)
      (pullback.lift t s hY))
    (F : BasedCategory.{v, w} (Over S))
    (a : BasedFunctor (discreteModuli U.obj.obj) F)
    (presentation : SpaceGroupoidQuotientPresentation s t e i c F a) :
    ∃ (X : AlgebraicSpace S) (f : X ⟶ Y) (q : U.obj.obj ⟶ X.obj.obj)
      (E : BasedFunctor (discreteModuli X.obj.obj) F),
      E.toFunctor.IsEquivalence ∧
      Nonempty (ModuliTwoIso ((discreteModuliMap q).comp E) a) ∧
      q ≫ f.hom.hom = p.hom.hom ∧
      (∃ η : sheafify (Scheme.fppfTopology.over S)
          (coequalizer s t ⋙ uliftFunctor.{u + 1, u}) ≅
            X.obj.obj ⋙ uliftFunctor.{u + 1, u},
        Functor.whiskerRight (coequalizer.π s t) uliftFunctor.{u + 1, u} ≫
            toSheafify (Scheme.fppfTopology.over S)
              (coequalizer s t ⋙ uliftFunctor.{u + 1, u}) ≫ η.hom =
          Functor.whiskerRight q uliftFunctor.{u + 1, u}) ∧
      MapIsLocally (@Etale) f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
