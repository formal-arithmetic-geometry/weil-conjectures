/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso

import Sheaf.AlgebraicGeometry.AlgebraicSpace
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAmpleLocal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient

/-! # Effective étale descent for polarized schemes

Source: Stacks Project, spaces.tex, Tag 02WW; spaces-descent.tex, Tags 0D3C and 04W8;
Descent, Tag 023Q
(blueprint: lem-trf-polarized-scheme-etale-descent).

## Main definitions

* `PolarizedSchemeEtaleDescentDatum`: etale cover, scheme and line-module descent data.
* `IsPolarizedDescentRealization`: charts induce exactly the supplied theta and lambda.
* `PolarizedDescentPairIso`: one global compatible scheme and module isomorphism.

## Main statement

* `exists_polarizedScheme_of_etaleDescent`: effective descent and unique compatible isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The overlap scheme `X_i ×_{U_i} (U_i ×_S U_j)`.
Source: Stacks Project, spaces.tex, Tag 02WW
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
noncomputable def polarizedOverlap {S : Scheme.{u}} {I : Type v} (U : I → Scheme.{u})
    (uMap : ∀ i, U i ⟶ S) (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ U i)
    (i j : I) : Scheme.{u} :=
  pullback (f i) (pullback.fst (uMap i) (uMap j))

/-- The projection of an overlap to its `X_i` chart.
Source: Stacks Project, spaces.tex, Tag 02WW
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
noncomputable def polarizedOverlapX {S : Scheme.{u}} {I : Type v}
    (U : I → Scheme.{u}) (uMap : ∀ i, U i ⟶ S) (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ U i) (i j : I) : polarizedOverlap U uMap X f i j ⟶ X i :=
  pullback.fst (f i) (pullback.fst (uMap i) (uMap j))

/-- The canonical map from an overlap to its first base-cover chart.
Source: Stacks Project, spaces.tex, Tag 02WW
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
noncomputable def polarizedOverlapUi {S : Scheme.{u}} {I : Type v}
    (U : I → Scheme.{u}) (uMap : ∀ i, U i ⟶ S) (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ U i) (i j : I) : polarizedOverlap U uMap X f i j ⟶ U i :=
  polarizedOverlapX U uMap X f i j ≫ f i

/-- The canonical map from an overlap to its second base-cover chart.
Source: Stacks Project, spaces.tex, Tag 02WW
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
noncomputable def polarizedOverlapUj {S : Scheme.{u}} {I : Type v}
    (U : I → Scheme.{u}) (uMap : ∀ i, U i ⟶ S) (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ U i) (i j : I) : polarizedOverlap U uMap X f i j ⟶ U j :=
  pullback.snd (f i) (pullback.fst (uMap i) (uMap j)) ≫
    pullback.snd (uMap i) (uMap j)

/-- The diagonal map into the self-overlap, used for the identity condition.
Source: Stacks Project, spaces.tex, Tag 02WW
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
noncomputable def polarizedOverlapDiagonal {S : Scheme.{u}} {I : Type v}
    (U : I → Scheme.{u}) (uMap : ∀ i, U i ⟶ S) (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ U i) (i : I) : X i ⟶ polarizedOverlap U uMap X f i i :=
  pullback.lift (𝟙 _) (f i ≫ pullback.diagonal (uMap i))

/-- Equality transport for the tensor pullback of a fixed module.
Source: Stacks Project, Modules, Tag 0095
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
noncomputable def polarizedModuleCongr {T X : Scheme.{u}} {a b : T ⟶ X}
    (h : a = b) (M : X.Modules) :
    (Scheme.Modules.tensorPullback a).obj M ≅ (Scheme.Modules.tensorPullback b).obj M :=
  eqToIso (congrArg (fun t ↦ (Scheme.Modules.tensorPullback t).obj M) h)

/-- Pull an overlap comparison back and normalize both ends to composite scheme maps.
Source: Stacks Project, spaces-descent.tex, Definition descent-datum-quasi-coherent,
using the canonical tensor comparison of Modules Tags 0095 and 0096
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
noncomputable def polarizedPullIso {T R X Y : Scheme.{u}}
    (a : T ⟶ R) (p : R ⟶ X) (q : R ⟶ Y) (M : X.Modules) (N : Y.Modules)
    (e : (Scheme.Modules.tensorPullback p).obj M ≅
      (Scheme.Modules.tensorPullback q).obj N) :
    (Scheme.Modules.tensorPullback (a ≫ p)).obj M ≅
      (Scheme.Modules.tensorPullback (a ≫ q)).obj N :=
  (Scheme.Modules.tensorPullbackCompositionIso a p (a ≫ p) rfl).app M ≪≫
    (Scheme.Modules.tensorPullback a).mapIso e ≪≫
    ((Scheme.Modules.tensorPullbackCompositionIso a q (a ≫ q) rfl).app N).symm

/-- Pull a local trivialization back with the canonical composition comparison.
Source: Stacks Project, spaces-descent.tex, Definition descent-datum-effective-quasi-coherent
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
noncomputable def polarizedPullLine {T X Y : Scheme.{u}}
    (a : T ⟶ X) (b : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (e : (Scheme.Modules.tensorPullback b).obj M ≅ N) :
    (Scheme.Modules.tensorPullback (a ≫ b)).obj M ≅
      (Scheme.Modules.tensorPullback a).obj N :=
  (Scheme.Modules.tensorPullbackCompositionIso a b (a ≫ b) rfl).app M ≪≫
    (Scheme.Modules.tensorPullback a).mapIso e

/-- The identity comparison pinned by the sectionwise tensor adjunction.
Source: Stacks Project, Modules, Tags 0095 and 0096
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
noncomputable def polarizedTensorIdentity (X : Scheme.{u}) :
    Scheme.Modules.tensorPullback (𝟙 X) ≅ 𝟭 X.Modules :=
  ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 X))).ofNatIsoRight
    (Scheme.Modules.pushforwardId X)).leftAdjointUniq Adjunction.id

/-- The full effective polarized étale descent datum.  Its overlap equations are expressed
using canonical pullback projections, the diagonal, and compatible test-scheme maps.
The module cocycle composes the two successive transitions after canonical comparisons.
Source: Stacks Project, spaces.tex, Tag 02WW; spaces-descent.tex, Tags 0D3C and 04W8;
Descent, Tag 023Q
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
structure PolarizedSchemeEtaleDescentDatum (S : Scheme.{u}) (I : Type v)
    (U : I → Scheme.{u}) (uMap : ∀ i, U i ⟶ S) (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ U i) (L : ∀ i, (X i).Modules)
    (hL : ∀ i, Scheme.Modules.IsInvertible (L i)) where
  isEtale : ∀ i, Etale (uMap i)
  jointlySurjective : ∀ x : S, ∃ i : I, ∃ y : U i, (uMap i).base y = x
  theta : ∀ i j, polarizedOverlap U uMap X f i j ≅ polarizedOverlap U uMap X f j i
  theta_over_left : ∀ i j,
    (theta i j).hom ≫ polarizedOverlapUi U uMap X f j i =
      polarizedOverlapUj U uMap X f i j
  theta_over_right : ∀ i j,
    (theta i j).hom ≫ polarizedOverlapUj U uMap X f j i =
      polarizedOverlapUi U uMap X f i j
  theta_identity : ∀ i,
    polarizedOverlapDiagonal U uMap X f i ≫ (theta i i).hom =
      polarizedOverlapDiagonal U uMap X f i
  theta_cocycle : ∀ i j k (T : Scheme.{u})
    (a : T ⟶ polarizedOverlap U uMap X f i j)
    (b : T ⟶ polarizedOverlap U uMap X f j k)
    (c : T ⟶ polarizedOverlap U uMap X f i k)
    (d : T ⟶ polarizedOverlap U uMap X f k i),
    (hmid : a ≫ (theta i j).hom ≫ polarizedOverlapX U uMap X f j i =
      b ≫ polarizedOverlapX U uMap X f j k) →
    c ≫ polarizedOverlapX U uMap X f i k = a ≫ polarizedOverlapX U uMap X f i j →
    c ≫ polarizedOverlapUj U uMap X f i k = b ≫ polarizedOverlapUj U uMap X f j k →
    d ≫ polarizedOverlapX U uMap X f k i =
      b ≫ (theta j k).hom ≫ polarizedOverlapX U uMap X f k j →
    d ≫ polarizedOverlapUj U uMap X f k i = a ≫ polarizedOverlapUi U uMap X f i j →
    c ≫ (theta i k).hom = d
  lambda : ∀ i j,
    (Scheme.Modules.tensorPullback
      ((theta i j).hom ≫ polarizedOverlapX U uMap X f j i)).obj (L j) ≅
    (Scheme.Modules.tensorPullback (polarizedOverlapX U uMap X f i j)).obj (L i)
  lambda_identity : ∀ i,
    polarizedPullIso (polarizedOverlapDiagonal U uMap X f i)
      ((theta i i).hom ≫ polarizedOverlapX U uMap X f i i)
      (polarizedOverlapX U uMap X f i i) (L i) (L i) (lambda i i) =
    polarizedModuleCongr (by rw [← Category.assoc, theta_identity i]) (L i)
  lambda_cocycle : ∀ i j k (T : Scheme.{u})
    (a : T ⟶ polarizedOverlap U uMap X f i j)
    (b : T ⟶ polarizedOverlap U uMap X f j k)
    (c : T ⟶ polarizedOverlap U uMap X f i k)
    (hmid : a ≫ (theta i j).hom ≫ polarizedOverlapX U uMap X f j i =
      b ≫ polarizedOverlapX U uMap X f j k)
    (hend : b ≫ (theta j k).hom ≫ polarizedOverlapX U uMap X f k j =
      c ≫ (theta i k).hom ≫ polarizedOverlapX U uMap X f k i)
    (hstart : c ≫ polarizedOverlapX U uMap X f i k =
      a ≫ polarizedOverlapX U uMap X f i j),
    polarizedPullIso c ((theta i k).hom ≫ polarizedOverlapX U uMap X f k i)
      (polarizedOverlapX U uMap X f i k) (L k) (L i) (lambda i k) =
    polarizedModuleCongr hend.symm (L k) ≪≫
      polarizedPullIso b ((theta j k).hom ≫ polarizedOverlapX U uMap X f k j)
        (polarizedOverlapX U uMap X f j k) (L k) (L j) (lambda j k) ≪≫
      polarizedModuleCongr hmid.symm (L j) ≪≫
      polarizedPullIso a ((theta i j).hom ≫ polarizedOverlapX U uMap X f j i)
        (polarizedOverlapX U uMap X f i j) (L j) (L i) (lambda i j) ≪≫
      polarizedModuleCongr hstart.symm (L i)
  ample_local : ∀ i (V : (U i).Opens), IsAffineOpen V →
    ∃ h : Scheme.Modules.IsInvertible
      ((Scheme.Modules.tensorPullback (f i ⁻¹ᵁ V).ι).obj (L i)),
      @Scheme.Modules.IsAmple (f i ⁻¹ᵁ V).toScheme
        ((Scheme.Modules.tensorPullback (f i ⁻¹ᵁ V).ι).obj (L i)) h

/-- A chart identification of a descended polarized pair with a local pair.
Source: Stacks Project, spaces.tex, Tag 02WW; spaces-descent.tex, Tag 04W8
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
structure PolarizedDescentChart {S : Scheme.{u}} {I : Type v}
    {U : I → Scheme.{u}} {uMap : ∀ i, U i ⟶ S} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ U i} {L : ∀ i, (X i).Modules}
    (Y : Scheme.{u}) (g : Y ⟶ S) (M : Y.Modules) (i : I) where
  schemeIso : pullback g (uMap i) ≅ X i
  over : schemeIso.hom ≫ f i = pullback.snd g (uMap i)
  moduleIso : (Scheme.Modules.tensorPullback (pullback.fst g (uMap i))).obj M ≅
    (Scheme.Modules.tensorPullback schemeIso.hom).obj (L i)

/-- A descended polarized pair, including its canonical chart comparisons.
Source: Stacks Project, spaces.tex, Tag 02WW; spaces-descent.tex, Tag 04W8
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
structure PolarizedDescentPair {S : Scheme.{u}} {I : Type v}
    (U : I → Scheme.{u}) (uMap : ∀ i, U i ⟶ S) (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ U i) (L : ∀ i, (X i).Modules) where
  Y : Scheme.{u}
  g : Y ⟶ S
  M : Y.Modules
  isInvertible : Scheme.Modules.IsInvertible M
  chart : ∀ i, PolarizedDescentChart (U := U) (uMap := uMap) (X := X)
    (f := f) (L := L) Y g M i

/-- The local map from `X_i` to a candidate descended scheme, determined by its chart.
Source: Stacks Project, spaces.tex, Tag 02WW, recovery of charts
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
noncomputable def polarizedChartMap {S : Scheme.{u}} {I : Type v}
    {U : I → Scheme.{u}} {uMap : ∀ i, U i ⟶ S} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ U i} {L : ∀ i, (X i).Modules}
    (d : PolarizedDescentPair U uMap X f L) (i : I) : X i ⟶ d.Y :=
  (d.chart i).schemeIso.inv ≫ pullback.fst d.g (uMap i)

/-- The chart module comparison expressed directly on `X_i`.
Source: Stacks Project, spaces-descent.tex, Definition descent-datum-effective-quasi-coherent
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
noncomputable def polarizedChartLine {S : Scheme.{u}} {I : Type v}
    {U : I → Scheme.{u}} {uMap : ∀ i, U i ⟶ S} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ U i} {L : ∀ i, (X i).Modules}
    (d : PolarizedDescentPair U uMap X f L) (i : I) :
    (Scheme.Modules.tensorPullback (polarizedChartMap d i)).obj d.M ≅ L i :=
  (Scheme.Modules.tensorPullbackCompositionIso (d.chart i).schemeIso.inv
      (pullback.fst d.g (uMap i)) (polarizedChartMap d i) rfl).app d.M ≪≫
    (Scheme.Modules.tensorPullback (d.chart i).schemeIso.inv).mapIso (d.chart i).moduleIso ≪≫
    ((Scheme.Modules.tensorPullbackCompositionIso (d.chart i).schemeIso.inv
      (d.chart i).schemeIso.hom (𝟙 (X i)) (d.chart i).schemeIso.inv_hom_id).app (L i)).symm ≪≫
    (polarizedTensorIdentity (X i)).app (L i)

/-- A candidate pair realizes the supplied scheme transitions and line transitions.
The second equation says that lambda is the composite of the two chart trivializations
through the same pulled-back global module, with equality transport for the scheme equation.
Source: Stacks Project, spaces-descent.tex, Definition descent-datum-effective-quasi-coherent,
and spaces.tex, Tag 02WW (blueprint: lem-trf-polarized-scheme-etale-descent). -/
structure IsPolarizedDescentRealization {S : Scheme.{u}} {I : Type v}
    {U : I → Scheme.{u}} {uMap : ∀ i, U i ⟶ S} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ U i} {L : ∀ i, (X i).Modules}
    {hL : ∀ i, Scheme.Modules.IsInvertible (L i)}
    (D : PolarizedSchemeEtaleDescentDatum S I U uMap X f L hL)
    (d : PolarizedDescentPair U uMap X f L) : Prop where
  theta : ∀ i j,
    polarizedOverlapX U uMap X f i j ≫ polarizedChartMap d i =
      ((D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i) ≫ polarizedChartMap d j
  lambda : ∀ i j, D.lambda i j =
    (polarizedPullLine ((D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i)
      (polarizedChartMap d j) d.M (L j) (polarizedChartLine d j)).symm ≪≫
    polarizedModuleCongr (theta i j).symm d.M ≪≫
    polarizedPullLine (polarizedOverlapX U uMap X f i j)
      (polarizedChartMap d i) d.M (L i) (polarizedChartLine d i)

/-- A global isomorphism of polarized pairs compatible with every specified chart.
It includes a single global module isomorphism; its chart equation compares the two
routes from the pullback of the second global module to the prescribed local line module.
Source: Stacks Project, Descent, Tag 023Q, and Spaces Descent, Tag 04W8, full faithfulness
(blueprint: lem-trf-polarized-scheme-etale-descent). -/
structure PolarizedDescentPairIso {S : Scheme.{u}} {I : Type v}
    {U : I → Scheme.{u}} {uMap : ∀ i, U i ⟶ S} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ U i} {L : ∀ i, (X i).Modules}
    (d d' : PolarizedDescentPair U uMap X f L) where
  schemeIso : d.Y ≅ d'.Y
  over : schemeIso.hom ≫ d'.g = d.g
  moduleIso : (Scheme.Modules.tensorPullback schemeIso.hom).obj d'.M ≅ d.M
  chart : ∀ i, polarizedChartMap d i ≫ schemeIso.hom = polarizedChartMap d' i
  line : ∀ i,
    polarizedPullLine (polarizedChartMap d i) schemeIso.hom d'.M d.M moduleIso ≪≫
      polarizedChartLine d i =
    polarizedModuleCongr (chart i) d'.M ≪≫ polarizedChartLine d' i

/-- Effective etale descent for polarized schemes.
Source: Stacks Project, spaces.tex, Tags 02WW and 02WV; spaces-descent.tex, Tags 04W8
and 0D3C; Descent, Tag 023Q (blueprint: lem-trf-polarized-scheme-etale-descent).

Proof:
1. Form the coproduct of the X_i and the coproduct of the overlaps, using
   lem-weil-pbc-scheme-coproduct-family. The source and target are etale by
   lem-weil-pbc-etale-scheme-base-change. Their map to the square is monic by the
   fibre-product universal property. The diagonal and theta cocycle give the identity,
   inverse and composition, hence an etale equivalence relation.
2. Apply lem-trf-etale-relation-quotient to obtain the algebraic space F over S with
   atlas the coproduct and kernel pair the specified overlaps (Tags 02WW and 02WV).
3. Recover F times U_i as X_i: a test section lifts etale locally to X_j; transition
   theta_ji sends it to X_i. The cocycle makes these maps agree on overlaps, and
   lem-weil-pbc-small-etale-representable-presheaf-sheaf glues them. The diagonal identity
   gives injectivity, so these constructions are inverse and realize theta.
4. Apply lem-trf-algebraic-space-invertible-descent to lambda and its identity and
   composition cocycle. It descends an invertible module and chart identifications
   whose induced overlap maps are exactly lambda (Tag 04W8).
5. The affine-inverse-image ampleness hypothesis gives relative ampleness on each chart.
   Apply lem-trf-algebraic-space-ample-local (Tag 0D3C) to make F representable; testing
   over S makes F a scheme. The descended module is an ordinary invertible module there.
6. For two realizations the chart maps to the other scheme agree by their theta equations.
   Their domains cover by lem-weil-pbc-etale-covering-base-change. Representable-sheaf
   gluing (Tag 023Q) gives a unique global map, and reversing it gives its inverse.
   The lambda equations make the prescribed local module maps agree. Full faithfulness
   in lem-trf-algebraic-space-invertible-descent glues a unique global module isomorphism.
   Faithfulness proves both inverse identities and uniqueness of the whole pair isomorphism. -/
theorem exists_polarizedScheme_of_etaleDescent (S : Scheme.{u}) (I : Type v)
    (U : I → Scheme.{u}) (uMap : ∀ i, U i ⟶ S) (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ U i) (L : ∀ i, (X i).Modules)
    (hL : ∀ i, Scheme.Modules.IsInvertible (L i))
    (D : PolarizedSchemeEtaleDescentDatum S I U uMap X f L hL) :
    ∃ d : PolarizedDescentPair U uMap X f L, IsPolarizedDescentRealization D d ∧
      ∀ d' : PolarizedDescentPair U uMap X f L, IsPolarizedDescentRealization D d' →
        ∃ e : PolarizedDescentPairIso d d', ∀ e' : PolarizedDescentPairIso d d', e' = e := by
  sorry

end AlgebraicGeometry
