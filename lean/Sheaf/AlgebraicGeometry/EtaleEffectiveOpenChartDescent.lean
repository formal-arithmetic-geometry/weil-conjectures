/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-!
# Effective open charts over étale base neighbourhoods

Source: Stacks Project, Descent, Tags 023V, 023Q and 03N0; Bootstrap, Tag 04S6.
The criterion is the agent local-chart construction recorded in the DAG.
(blueprint: lem-sfb-etale-effective-open-chart-descent).

The descended space is characterized by its actual equalizer of sections. The
representation over the cover retains the prescribed transport, and the chart squares
retain the supplied effective isomorphisms, rather than just asserting an unrelated atlas.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.EtaleEffectiveOpenChartDescent

/-- The canonical map from the represented scheme to the descended presheaf.
Source: Stacks, Tag 023V, Yoneda form of the base-change identification
(blueprint: lem-sfb-etale-effective-open-chart-descent). -/
def projection {S' S : Scheme.{u}} (p : S' ⟶ S) (V : Over S')
    (F : (Over S)ᵒᵖ ⥤ Type u) (r : ((Over.map p).op ⋙ F).RepresentableBy V) :
    yoneda.obj ((Over.map p).obj V) ⟶ F :=
  yonedaEquiv.symm (r.homEquiv (𝟙 V))

/-- Restrict a section to `T ×_S S'`, then apply the specified representation by `V`.
Source: Stacks, Tags 023V and 023Q, equalizer construction
(blueprint: lem-sfb-etale-effective-open-chart-descent). -/
def sectionMap {S' S : Scheme.{u}} (p : S' ⟶ S) (V : Over S')
    (F : (Over S)ᵒᵖ ⥤ Type u) (r : ((Over.map p).op ⋙ F).RepresentableBy V)
    (T : Over S) (x : F.obj (op T)) : (Over.pullback p).obj T ⟶ V :=
  r.homEquiv.symm (F.map (Over.homMk (U := (Over.map p).obj ((Over.pullback p).obj T))
    (V := T) (pullback.fst T.hom p) pullback.condition).op x)

/-- The chart map over an étale base neighbourhood is the pair of its map to the
space and its given structure map to that neighbourhood. Products here are over `S`.
Source: Stacks, Tags 023Q and 03N0, local-chart construction
(blueprint: lem-sfb-etale-effective-open-chart-descent). -/
def relativeChartMap {S T : Scheme.{u}} (r : T ⟶ S) (Z : Over T)
    (F : (Over S)ᵒᵖ ⥤ Type u) (c : yoneda.obj (Over.mk (Z.hom ≫ r)) ⟶ F) :
    yoneda.obj (Over.mk (Z.hom ≫ r)) ⟶ F ⨯ yoneda.obj (Over.mk r) :=
  prod.lift c (yoneda.map (Over.homMk Z.hom rfl))

/-- Effective open charts over étale base neighbourhoods descend to an algebraic space.
Source: the DAG's agent local-chart criterion, using Stacks, Descent, Tags 023V, 023Q,
03N0, 02L3 and 02VN, and Bootstrap, Tag 04S6
(blueprint: lem-sfb-etale-effective-open-chart-descent).

The Cartesian squares `hpb` encode the supplied effective chart isomorphisms.
`hchart` says exactly that the open is stable under transport over `T i`, and that
its effective projection `b i` is invariant. Applying this to the reversed pair
also gives stability in the reverse direction. `r.overDescentDatum` retains alpha.
The injective `sectionMap` has precisely the matching sections as its image;
the matching equation is tested on every pair of lifts of every test scheme.

Proof:
1. Flat quasi-compact surjections are singleton fpqc covers; base changes are covers
   by lem-galois-fpqc-covering-base-change. Cocycle and invertibility give identity
   transport and inverse transport (def-pd-descent-datum).
2. Form the displayed equalizer functor. Representable fpqc descent (023Q,
   lem-weil-pbc-fpqc-representable-descent) glues its local maps and detects their
   matching equations. It is an fpqc sheaf, hence an fppf sheaf by
   lem-trf-fppf-covering-is-fpqc. Restriction is precomposition.
3. Evaluate a matching section on the graph of a lift to S'. Conversely transport
   the given V-point from that lift to the second projection. The cocycle proves
   matching; identity and cocycle prove both inverses. These formulas are natural
   and their induced transport is alpha (def-pd-descent-datum).
4. The supplied effective chart square and hchart make the map from each pulled-back
   chart to the equalizer invariant. The fpqc sheaf condition descends it to Z_i.
5. On a scheme test over T_i, pull back U_i. Stability makes this open invariant on
   the overlap. lem-weil-pbc-open-subscheme-fpqc-descent (03N0) descends it to a unique
   open W in the test scheme. Uniqueness makes W commute with further base change.
6. This W represents the chart fibre product: membership is factorization through
   U_i after the fpqc cover, using lem-weil-pbc-morphism-factors-through-open-subscheme.
   Invariance of b_i and representable fpqc descent glue the factorization to Z_i;
   uniqueness follows from the open immersion being mono. Thus the relative chart
   is representable open, and its pullback is the specified inclusion U_i into V.
7. For an arbitrary S-test take its product with T_i. The representing open W maps
   étale to the original test: an open immersion followed by a base change of r_i.
   Use lem-weil-pbc-etale-base-change-finite-limits and
   lem-weil-pbc-etale-composition-cancellation. Each chart is representable étale.
8. Glue the chart maps on the coproduct using the fppf sheaf condition: summand open
   immersions form an fppf cover. The test fibre product is the coproduct of the
   preceding representing opens, by decomposition into inverse-image summands.
   Use lem-weil-pbc-scheme-coproduct-family and lem-weil-pbc-etale-local-on-source
   to see that this atlas is representable étale.
9. Pull a test back to S'. The inverse images of all U_i cover it, and each maps to
   its representing chart fibre product. Surjectivity of the fpqc cover therefore
   proves surjectivity of the atlas on every scheme test.
10. Apply lem-sfb-fppf-space-atlas-bootstrap (04S6(4), through (3)) to the fppf sheaf
    and this surjective étale scheme atlas. Its flatness and local finite presentation
    follow from étaleness. No prior representability of the diagonal is assumed.
    Steps 3, 6 and 7 give all remaining conclusions. For an empty index type, V is
    empty and the same construction has the empty atlas and empty descended space. -/
theorem exists_algebraicSpace_of_effective_open_charts
    {S' S : Scheme.{u}} (p : S' ⟶ S) [Flat p] [QuasiCompact p] [Surjective p]
    (V : Over S') [IsSeparated V.hom] (D : Over.DescentDatum p V)
    {I : Type u} (U : I → V.left.Opens) (hcover : iSup U = ⊤)
    (T : I → Scheme.{u}) (rBase : ∀ i : I, T i ⟶ S) (q : ∀ i : I, S' ⟶ T i)
    (hp : ∀ i : I, q i ≫ rBase i = p)
    (hq : ∀ i : I, Flat (q i) ∧ QuasiCompact (q i) ∧ Surjective (q i))
    (hr : ∀ i : I, Etale (rBase i)) (Z : ∀ i : I, Over (T i))
    (b : ∀ i : I, (U i).toScheme ⟶ (Z i).left)
    (hpb : ∀ i : I, IsPullback (b i) ((U i).ι ≫ V.hom) (Z i).hom (q i))
    (hchart : ∀ (i : I) (A : Scheme.{u}) (s₀ s₁ : A ⟶ S')
      (h : s₀ ≫ q i = s₁ ≫ q i) (a : Over.mk s₀ ⟶ V) (u₀ : A ⟶ (U i).toScheme),
      u₀ ≫ (U i).ι = a.left →
      ∃ u₁ : A ⟶ (U i).toScheme,
        u₁ ≫ (U i).ι = (D.transport s₀ s₁
          (by rw [← hp i, ← Category.assoc, ← Category.assoc, h]) a).left ∧
        u₁ ≫ b i = u₀ ≫ b i) :
    ∃ (X : AlgebraicSpace S)
      (r : ((Over.map p).op ⋙ X.obj.obj).RepresentableBy V),
      (∀ (A : Scheme.{u}) (s₀ s₁ : A ⟶ S') (h : s₀ ≫ p = s₁ ≫ p)
        (a : Over.mk s₀ ⟶ V), r.overDescentDatum.transport s₀ s₁ h a =
          D.transport s₀ s₁ h a) ∧
      (∀ W : Over S,
        Function.Injective (sectionMap p V X.obj.obj r W) ∧
        ∀ y : (Over.pullback p).obj W ⟶ V,
          (∃ x : X.obj.obj.obj (op W), sectionMap p V X.obj.obj r W x = y) ↔
          ∀ (A : Scheme.{u}) (t : A ⟶ W.left) (s₀ s₁ : A ⟶ S')
            (h₀ : t ≫ W.hom = s₀ ≫ p) (h₁ : t ≫ W.hom = s₁ ≫ p),
            D.transport s₀ s₁ (h₀.symm.trans h₁)
              (Over.homMk (U := Over.mk s₀) (V := (Over.pullback p).obj W)
                (pullback.lift t s₀ h₀) (pullback.lift_snd t s₀ h₀) ≫ y) =
              Over.homMk (U := Over.mk s₁) (V := (Over.pullback p).obj W)
                (pullback.lift t s₁ h₁) (pullback.lift_snd t s₁ h₁) ≫ y) ∧
      ∃ (c : ∀ i : I, yoneda.obj (Over.mk ((Z i).hom ≫ rBase i)) ⟶ X.obj.obj)
        (atlas : yoneda.obj (Over.mk (Sigma.desc (fun i : I ↦ (Z i).hom ≫ rBase i))) ⟶
          X.obj.obj),
        AlgebraicSpace.IsEtale atlas ∧ AlgebraicSpace.IsSurjective atlas ∧
        (∀ i : I, yoneda.map (Over.homMk (Sigma.ι (fun i : I ↦ (Z i).left) i)
          (Sigma.ι_desc (fun i : I ↦ (Z i).hom ≫ rBase i) i)) ≫ atlas = c i) ∧
        (∀ i : I, AlgebraicSpace.IsEtale (c i)) ∧
        (∀ i : I, AlgebraicSpace.IsRepresentableWith
          (fun _ _ f ↦ IsOpenImmersion f.left)
          (relativeChartMap (rBase i) (Z i) X.obj.obj (c i))) ∧
        (∀ i : I, IsPullback
          (yoneda.map (Over.homMk (U := Over.mk ((U i).ι ≫ V.hom ≫ p))
            (V := Over.mk ((Z i).hom ≫ rBase i)) (b i)
            (by
              simpa only [Over.mk_hom, Category.assoc, hp] using
                congrArg (fun f ↦ f ≫ rBase i) (hpb i).w)))
          (yoneda.map (Over.homMk (U := Over.mk ((U i).ι ≫ V.hom ≫ p))
            (V := (Over.map p).obj V) (U i).ι rfl))
          (relativeChartMap (rBase i) (Z i) X.obj.obj (c i))
          (prod.lift (projection p V X.obj.obj r)
            (yoneda.map (Over.homMk (U := (Over.map p).obj V)
              (V := Over.mk (rBase i)) (V.hom ≫ q i)
              (by simp only [Over.mk_hom, Over.map_obj_hom, Category.assoc, hp]))))) := by
  sorry

end AlgebraicGeometry.EtaleEffectiveOpenChartDescent
