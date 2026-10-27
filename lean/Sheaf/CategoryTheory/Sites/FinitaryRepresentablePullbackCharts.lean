/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.CoherentTopos
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.TraceFormula.SiteQuasicompactSheafificationCriterion
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-! # Finite representable charts for arbitrary sheaf pullbacks

Source: Stacks Project, Sites, Tags 00WK, 0D06, 00WJ and 00WS; the finite-chart
argument in the node (blueprint: lem-trf-finitary-representable-pullback-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- On a finite-limit site with a pretopology of finite covers, associated representables
are quasi-compact generators, represent evaluation, preserve finite limits, and give
finite charts for pullbacks along arbitrary sheaf morphisms.

Source: Stacks Project, Sites, Tags 00WK, 0D06, 00WJ and 00WS
(blueprint: lem-trf-finitary-representable-pullback-charts).

Proof plan, following the seven steps of the node:
1. By lem-weil-pbc-pretopology-sheaf-condition every covering sieve contains a
   K-cover. Since K is finite, the factorization of this cover through any generating
   covering family has finite index image. Apply
   lem-trf-site-quasicompact-sheafification-criterion to obtain quasi-compactness.
2. Compose the sheafification adjunction with Yoneda evaluation at the identity.
   Both bijections are natural, giving the two displayed naturality equations.
3. For every pair (T,s) with s in F(T), take the map H_T to F corresponding to s.
   Identity covers give local lifts, so lem-trf-topos-finite-cover-calculus makes
   the coproduct map epi. Quasi-compactness selects a finite subfamily.
4. Yoneda preserves limits by their objectwise universal property. Compose with
   finite-limit preservation of sheafification (lem-weil-pbc-sheafification-sets-exact).
   The empty diagram and binary products give the terminal and product cases.
5. The sections corresponding to b and c locally come from site arrows by
   lem-weil-pbc-site-sheafification-sections-local. Refine the representing covers
   to finite K-covers and compose their representatives with the refinement maps.
   Naturality of evaluation gives the two restriction equalities.
6. The covers give epi families by lem-trf-site-epimorphic-family-cover-lifts.
   Apply the two-family pullback clause of lem-trf-topos-finite-cover-calculus.
   Step 4 identifies its domains with H of the site pullbacks, respecting both
   projections. Thus the family specified by the two projection equations is epi.
7. Every chart domain is quasi-compact by step 1. The chart index set is finite,
   so lem-trf-topos-finite-cover-calculus gives quasi-compactness of the target,
   also for empty covers. No subcanonicity or global site representatives are used.
-/
theorem finitary_representable_pullback_charts
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : Pretopology C) (_hfinite : K ≤ Pretopology.finite C) :
    (∀ U : C, IsQuasiCompactObject.{max u v}
      ((uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj U)) ∧
    (∀ F : Sheaf K.toGrothendieck (Type (max u v)),
      ∃ (I : Type (max u v)) (U : I → C)
        (f : ∀ i,
          (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj (U i) ⟶ F),
        Epi (Sigma.desc f)) ∧
    (∀ F : Sheaf K.toGrothendieck (Type (max u v)),
      IsQuasiCompactObject.{max u v} F →
        ∃ (n : ℕ) (U : Fin n → C)
          (f : ∀ i,
            (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj (U i) ⟶ F),
          Epi (Sigma.desc f)) ∧
    (∃ e : ∀ (U : C) (F : Sheaf K.toGrothendieck (Type (max u v))),
        ((uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj U ⟶ F) ≃
          F.obj.obj (op U),
      (∀ (U : C) (F : Sheaf K.toGrothendieck (Type (max u v)))
        (t : (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj U ⟶ F),
        e U F t = t.hom.app (op U)
          ((toSheafify K.toGrothendieck (uliftYoneda.{u}.obj U)).app (op U) ⟨𝟙 U⟩)) ∧
      (∀ (U V : C) (r : V ⟶ U) (F : Sheaf K.toGrothendieck (Type (max u v)))
        (t : (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj U ⟶ F),
        e V F ((uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).map r ≫ t) =
          F.obj.map r.op (e U F t)) ∧
      (∀ (U : C) (F G : Sheaf K.toGrothendieck (Type (max u v)))
        (t : (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj U ⟶ F)
        (r : F ⟶ G),
        e U G (t ≫ r) = r.hom.app (op U) (e U F t))) ∧
    PreservesFiniteLimits (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))) ∧
    (∀ (U V W : C)
      (b : (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj V ⟶
        (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj U)
      (c : (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj W ⟶
        (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj U),
      ∃ (n m : ℕ) (Va : Fin n → C) (Wd : Fin m → C)
        (a : ∀ i, Va i ⟶ V) (d : ∀ j, Wd j ⟶ W)
        (va : ∀ i, Va i ⟶ U) (wd : ∀ j, Wd j ⟶ U),
        Presieve.ofArrows Va a ∈ K V ∧ Presieve.ofArrows Wd d ∈ K W ∧
        (∀ i, (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).map (a i) ≫ b =
          (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).map (va i)) ∧
        (∀ j, (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).map (d j) ≫ c =
          (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).map (wd j)) ∧
        (∃ e : ∀ ij : Fin n × Fin m,
            (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).obj
              (pullback (va ij.1) (wd ij.2)) ⟶ pullback b c,
          (∀ ij, e ij ≫ pullback.fst b c =
            (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).map
              (pullback.fst (va ij.1) (wd ij.2) ≫ a ij.1)) ∧
          (∀ ij, e ij ≫ pullback.snd b c =
            (uliftYoneda.{u} ⋙ presheafToSheaf K.toGrothendieck (Type (max u v))).map
              (pullback.snd (va ij.1) (wd ij.2) ≫ d ij.2)) ∧
          Epi (Sigma.desc e)) ∧
        IsQuasiCompactObject.{max u v} (pullback b c)) := by
  sorry

end CategoryTheory
