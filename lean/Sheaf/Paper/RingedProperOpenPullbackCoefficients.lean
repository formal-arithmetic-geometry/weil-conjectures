/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module

public import Sheaf.Paper.RingedRefinementData

/-!
# Scalar compatibility of the clopen pullback comparison

Source: Stacks 0F7B, 08FJ, 0GL1 and the coefficient supplement, Steps 1--3
(blueprint: lem-pur-ringed-proper-open-pullback-coefficients).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization SheafOfModules.RingedRefinement

namespace SheafOfModules.RingedProperOpen

/-- The coefficient compatibility equation before either proper mate is taken.
Source: Stacks 0F7B, coefficient supplement Steps 1--3
(blueprint: def-pur-ringed-proper-open-pullback-formula). -/
structure PullbackCompatibility
    {UA VA WA ZA UB VB WB ZB : Type*}
    [Category UA] [Category VA] [Category WA] [Category ZA]
    [Category UB] [Category VB] [Category WB] [Category ZB]
    {lpA : ZA ⥤ VA} {lpB : ZB ⥤ VB} {lrA : WA ⥤ UA} {lrB : WB ⥤ UB}
    {su : UA ⥤ UB} {sv : VA ⥤ VB} {sw : WA ⥤ WB} {sz : ZA ⥤ ZB}
    {iA : WA ⥤ ZA} {iB : WB ⥤ ZB} {kA : UA ⥤ VA} {kB : UB ⥤ VB}
    (cp : sz ⋙ lpB ⟶ lpA ⋙ sv) (cr : sw ⋙ lrB ⟶ lrA ⋙ su)
    (di : iA ⋙ sz ⟶ sw ⋙ iB) (dk : kA ⋙ sv ⟶ su ⋙ kB)
    (ta : iA ⋙ lpA ⟶ lrA ⋙ kA) (tb : iB ⋙ lpB ⟶ lrB ⋙ kB) : Prop where
  equation : ∀ N, cp.app (iA.obj N) ≫ sv.map (ta.app N) ≫ dk.app (lrA.obj N) =
    lpB.map (di.app N) ≫ tb.app (sw.obj N) ≫ kB.map (cr.app N)

/-- A presentation of the scheme fibre product and its intrinsic clopen lift.
Both projection equations fix the lift uniquely. `schemePullback` ensures this
is the scheme fibre product, in addition to its presentation over the ambient base.
Source: Stacks 0F7B and 01W6
(blueprint: def-pur-ringed-proper-open-pullback-formula). -/
structure Factorization {T : Scheme.{u}} {U V W Z : Over T}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z) where
  H : Over T
  b : H ⟶ V
  q : H ⟶ W
  s : U ⟶ H
  pullback : IsPullback b q p i
  schemePullback : IsPullback b.left q.left p.left i.left
  sb : s ≫ b = k
  sq : s ≫ q = r
  [b_open : IsOpenImmersion b.left]
  [s_open : IsOpenImmersion s.left]
  clopen : IsClopen (Set.range s.left.base)

attribute [instance] Factorization.b_open Factorization.s_open

/-- The canonical open base-change map, then the identity/zero clopen projector,
then the canonical pullback and open compositors. No transformation is chosen.
Source: Stacks 0F7B, 08FJ and 0GL1
(blueprint: def-pur-ringed-proper-open-pullback-formula). -/
def t {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) (R : Rings m T) :
    o.shriek i R ⋙ (o.operation p R).left ⟶
      (o.operation r R).left ⋙ o.shriek k R :=
  (e.beta d.b d.q p i d.pullback R).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (o.operation d.q R).left (e.pi d.s d.clopen R))
      (o.shriek d.b R) ≫
    Functor.whiskerRight
      ((sp.pullComp d.s d.q R ≪≫
        eqToIso (congrArg (fun f ↦ (o.operation f R).left) d.sq)).hom)
      (o.shriek d.s R ⋙ o.shriek d.b R) ≫
    Functor.whiskerLeft (o.operation r R).left
      (sp.openFactor d.s d.b k d.sb R).hom

/-- Scalar extension preserves the normalized clopen pullback comparison, before
any proper-adjunction mate is taken.
Source: Stacks more-etale.tex Tag 0F7B, sites-cohomology.tex Tags 08FJ, 0GL1,
06YS, 06YY, 07A4; coefficient supplement Steps 1--3
(blueprint: lem-pur-ringed-proper-open-pullback-coefficients).

Proof: Split the ringed module category on H into the image of s and its open
complement. The section formula is a product of the two restrictions, with
componentwise ring actions. On a vertical site this is the same construction on
whole systems, with all transitions retained. Apply the exact equivalences to
complexes and localize; finite product localization retains the decomposition.
Consequently maps from b_!F to k_!G are determined by their restriction to U.
Identify the source by delta_i and beta_B with b_!,B q_B^* S_W N. Restrict both
composites to U. The inverse-transpose equations for beta and delta identify
them with the open units, and pi restricts to the identity. The remaining maps
are the balanced scalar/pullback compositors for sb=k, sq=r and bp=qi. On
flat-term K-flat representatives both routes send b tensor x to b tensor x,
with every intermediate scalar multiplied into b. The cochain tensor comparison
and resolving-subcategory localization descend this equality to the unbounded
derived category. Restriction injectivity proves the asserted equality; the
complementary target is zero. This uses neither a proper mate nor its coefficient
square, and works directly on the vertical site without evaluation. -/
theorem clopenPullback_coefficients {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} {o : Calculus c} (sc : ScalarComparisons o)
    {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) {A B : Rings m T} (a : A ⟶ B) :
    PullbackCompatibility
      (lpA := (o.operation p A).left) (lpB := (o.operation p B).left)
      (lrA := (o.operation r A).left) (lrB := (o.operation r B).left)
      (su := (o.scalar U a).T) (sv := (o.scalar V a).T)
      (sw := (o.scalar W a).T) (sz := (o.scalar Z a).T)
      (iA := o.shriek i A) (iB := o.shriek i B)
      (kA := o.shriek k A) (kB := o.shriek k B)
      (sc.pull p a).hom (sc.pull r a).hom (sc.delta i a).hom (sc.delta k a).hom
      (t e k r p i d A) (t e k r p i d B) := by
  sorry

end SheafOfModules.RingedProperOpen
