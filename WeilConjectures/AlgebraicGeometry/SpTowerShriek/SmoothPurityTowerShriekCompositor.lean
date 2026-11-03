/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.Compactification.CommonRefinement

/-!
# The compactification compositor of the actual tower compact-support functors

Source: Stacks Project, Tag 0F7J (lemma-shriek-composition, the compatible-compactification
construction); blueprint lem-sp-coefficient-tower-shriek-calculus, proof steps 2--3
(blueprint: def-sp-tower-shriek-compositor).

Everything is built from the fixed operations `o : Operations l E b` and the fixed open
exchange `x : OpenExchange l E b o` of the recorded shriek-level theorem; no compactification
and no comparison is chosen. For a triangle of compactifications `T`
(`Compactification.Triangle`: `cf.g ≫ cg.i = q ≫ p` cartesian, `cf.i ≫ q = cfg.i`,
`p ≫ cg.g = cfg.g`) the comparison `F_{cf} ⋙ F_{cg} ⟶ F_{cfg}` is the proper/open mate of
the open exchange, followed by the open compositor and the direct-image compositor, the latter
being the conjugate of the specified inverse-image compositor `o.comp`. Refinement
comparisons use the open base-change arrow for the identity-left square, transposed along the
proper adjunction. The general compositor for arbitrary compactifications of `f`, `g`, `f ≫ g`
uses the canonical triangle `Triangle.ofRestrict d (e.ofComp d)` and the canonical common
refinement `Compactification.inf`; it is a natural isomorphism on the full subcategory of
bounded-below towers with etale origins at every level, where the invertibility theorems
below (stated with `sorry`) apply.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The direct-image compositor: the conjugate, along the derived geometric adjunctions,
of the inverted specified inverse-image compositor `o.comp f g`.
Source: Stacks 0F7J; blueprint step 3, "the direct-image compositors are conjugates of the
coherent inverse-image compositors" (blueprint: def-sp-tower-shriek-compositor). -/
def pushComp (b : Base l E) (o : Operations l E b) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    push l E b (o.geometry f) ⋙ push l E b (o.geometry g) ≅
      push l E b (o.geometry (f ≫ g)) :=
  conjugateIsoEquiv
    ((adjunction l E b (o.geometry g)).comp (adjunction l E b (o.geometry f)))
    (adjunction l E b (o.geometry (f ≫ g))) (o.comp f g).symm

/-- Transport of the direct image along an equality of morphisms.
Source: blueprint step 3 (blueprint: def-sp-tower-shriek-compositor). -/
def pushCongr (b : Base l E) (o : Operations l E b) {X Y : Scheme.{u}}
    {f f' : X ⟶ Y} (w : f = f') :
    push l E b (o.geometry f) ≅ push l E b (o.geometry f') :=
  eqToIso (congrArg (fun h ↦ push l E b (o.geometry h)) w)

/-- Transport of the inverse image along an equality of morphisms.
Source: blueprint step 3 (blueprint: def-sp-tower-shriek-compositor). -/
def pullCongr (b : Base l E) (o : Operations l E b) {X Y : Scheme.{u}}
    {f f' : X ⟶ Y} (w : f = f') :
    pull l E b (o.geometry f) ≅ pull l E b (o.geometry f') :=
  eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) w)

/-- Transport of the exact open extension along an equality of open immersions.
Source: blueprint step 3 (blueprint: def-sp-tower-shriek-compositor). -/
def openCongr (b : Base l E) (o : Operations l E b) {U T : Scheme.{u}}
    {j j' : U ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j'] (w : j = j') :
    openD l E b (o.openOp j) ≅ openD l E b (o.openOp j') := by
  subst w
  exact Iso.refl _

/-- The open compositor `j_! ⋙ i_! ≅ (j ≫ i)_!` with a specified target open immersion:
the canonical one of the recorded open normalization, then transport.
Source: Stacks 0F7J (blueprint: def-sp-tower-shriek-compositor). -/
def openComp (b : Base l E) (o : Operations l E b) {U V T : Scheme.{u}}
    (j : U ⟶ V) (i : V ⟶ T) (k : U ⟶ T) [IsOpenImmersion j] [IsOpenImmersion i]
    [IsOpenImmersion k] (w : j ≫ i = k) :
    openD l E b (o.openOp j) ⋙ openD l E b (o.openOp i) ≅ openD l E b (o.openOp k) :=
  SpTowerCalculus.sequenceOpenComposition l E b o j i ≪≫ openCongr l E b o w

/-- The proper/open mate `r_* ⋙ i_! ⟶ k_! ⋙ p_*` of a cartesian square `r ≫ i = k ≫ p`
(`k`, `i` open): the proper-adjunction mate of the specified open exchange
`i_! ⋙ p^* ≅ r^* ⋙ k_!`. Its component at `M` is the transpose of
`p^* i_! r_* M ≅ k_! r^* r_* M ⟶ k_! M` (open exchange, then the counit of `r`).
Source: blueprint step 2 (cartesian case, where the lift `s` is an isomorphism);
Stacks 0F7J (blueprint: def-sp-tower-shriek-compositor). -/
def properOpenMate (b : Base l E) (o : Operations l E b) (x : OpenExchange l E b o)
    {V W S T : Scheme.{u}} {r : V ⟶ S} {k : V ⟶ W} {i : S ⟶ T} {p : W ⟶ T}
    [IsOpenImmersion k] [IsOpenImmersion i] (sq : IsPullback r k i p) :
    push l E b (o.geometry r) ⋙ openD l E b (o.openOp i) ⟶
      openD l E b (o.openOp k) ⋙ push l E b (o.geometry p) :=
  (mateEquiv (adjunction l E b (o.geometry r)) (adjunction l E b (o.geometry p))
    (x.exchange r k i p sq).hom).natTrans

/-- The compatible-compactification comparison `D_T : F_{cf} ⋙ F_{cg} ⟶ F_{cfg}` of a triangle
of compactifications: the proper/open mate of the cartesian square `cf.g ≫ cg.i = q ≫ p`,
whiskered by `cf.i_!` and `cg.g_*`, followed by the open compositor along `cf.i ≫ q = cfg.i`
and the direct-image compositor along `p ≫ cg.g = cfg.g`.
Source: blueprint lem-sp-coefficient-tower-shriek-calculus, step 3; Stacks 0F7J
(blueprint: def-sp-tower-shriek-compositor). -/
def triangleComparison (b : Base l E) (o : Operations l E b) (x : OpenExchange l E b o)
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S} (T : Compactification.Triangle f g) :
    F l E b o T.cf ⋙ F l E b o T.cg ⟶ F l E b o T.cfg :=
  (Functor.associator (openD l E b (o.openOp T.cf.i)) (push l E b (o.geometry T.cf.g))
      (openD l E b (o.openOp T.cg.i) ⋙ push l E b (o.geometry T.cg.g))).hom ≫
    Functor.whiskerLeft (openD l E b (o.openOp T.cf.i))
      ((Functor.associator (push l E b (o.geometry T.cf.g)) (openD l E b (o.openOp T.cg.i))
          (push l E b (o.geometry T.cg.g))).inv ≫
        Functor.whiskerRight (properOpenMate l E b o x T.isPullback)
          (push l E b (o.geometry T.cg.g)) ≫
        (Functor.associator (openD l E b (o.openOp T.q)) (push l E b (o.geometry T.p))
          (push l E b (o.geometry T.cg.g))).hom) ≫
    (Functor.associator (openD l E b (o.openOp T.cf.i)) (openD l E b (o.openOp T.q))
      (push l E b (o.geometry T.p) ⋙ push l E b (o.geometry T.cg.g))).inv ≫
    Functor.whiskerRight (openComp l E b o T.cf.i T.q T.cfg.i T.i_q).hom
      (push l E b (o.geometry T.p) ⋙ push l E b (o.geometry T.cg.g)) ≫
    Functor.whiskerLeft (openD l E b (o.openOp T.cfg.i))
      ((pushComp l E b o T.p T.cg.g).hom ≫ (pushCongr l E b o T.p_g).hom)

/-- The identity-free open base-change arrow of a refinement `r : c ⟶ d`:
`c.i_! ⟶ d.i_! ⋙ r^*`, at `M` the composite of `c.i_!` of the unit of `d.i_! ⊣ d.i^*`, the
inverse-image compositor `d.i^* ≅ r^* ⋙ c.i^*` (from `c.i ≫ r = d.i`), and the counit of
`c.i_! ⊣ c.i^*`.
Source: blueprint step 2 (open base change for the identity-left square)
(blueprint: def-sp-tower-shriek-compositor). -/
def refinementOpenArrow (b : Base l E) (o : Operations l E b) {X Y : Scheme.{u}}
    {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d) :
    openD l E b (o.openOp c.i) ⟶ openD l E b (o.openOp d.i) ⋙ pull l E b (o.geometry r.hom) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (o.openOp d.i).derivedAdjunction.unit (openD l E b (o.openOp c.i)) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (openD l E b (o.openOp d.i))
        ((pullCongr l E b o r.i_hom).inv ≫ (o.comp c.i r.hom).inv))
      (openD l E b (o.openOp c.i)) ≫
    (Functor.associator (openD l E b (o.openOp d.i))
      (pull l E b (o.geometry r.hom) ⋙ pull l E b (o.geometry c.i))
      (openD l E b (o.openOp c.i))).hom ≫
    Functor.whiskerLeft (openD l E b (o.openOp d.i))
      ((Functor.associator (pull l E b (o.geometry r.hom)) (pull l E b (o.geometry c.i))
          (openD l E b (o.openOp c.i))).hom ≫
        Functor.whiskerLeft (pull l E b (o.geometry r.hom))
          (o.openOp c.i).derivedAdjunction.counit ≫
        (Functor.rightUnitor _).hom)

/-- For a refinement whose square over `X` is cartesian, the open base-change arrow is
invertible.
Proof: by `Laws.detects` it suffices to check each level `n`. Exact evaluation carries the open
units and counits to the finite ones (`Open.unit_evaluation`, `Open.counit_evaluation`,
`openEvaluation`) and the compositor to the finite pullback compositor (`comp_evaluation`),
so the `n`-th evaluation is the finite open base-change map
`c.i_! M_n ⟶ r^* d.i_! M_n` for the cartesian square `X = c.Z ×_{d.Z} X`. It restricts to the
identity over `X ⊆ c.Z` (unit of an open immersion is invertible) and both sides vanish on the
complement, since `r⁻¹(X) = X`; hence it is invertible (Stacks 03S5, 0F7J).
Source: blueprint step 2 (blueprint: def-sp-tower-shriek-compositor). -/
theorem refinementOpenArrow_isIso (b : Base l E) (o : Operations l E b)
    (x : OpenExchange l E b o) (_laws : Laws l E b o x) {X Y : Scheme.{u}}
    {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (_hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    IsIso (refinementOpenArrow l E b o r) := by
  sorry

/-- The refinement comparison `C_r : F_d ⟶ F_c` of a refinement `r : c ⟶ d` with cartesian
square over `X`: the unit of `r^* ⊣ r_*`, the inverse of the open base-change arrow, and the
direct-image compositor along `r ≫ d.g = c.g`.
Source: blueprint step 3 (compactification refinement); Stacks 0F7J
(blueprint: def-sp-tower-shriek-compositor). -/
def refinementComparison (b : Base l E) (o : Operations l E b) (x : OpenExchange l E b o)
    (laws : Laws l E b o x) {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    F l E b o d ⟶ F l E b o c :=
  haveI := refinementOpenArrow_isIso l E b o x laws r hr
  Functor.whiskerLeft (openD l E b (o.openOp d.i))
      ((Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (adjunction l E b (o.geometry r.hom)).unit
          (push l E b (o.geometry d.g)) ≫
        (Functor.associator (pull l E b (o.geometry r.hom)) (push l E b (o.geometry r.hom))
          (push l E b (o.geometry d.g))).hom) ≫
    (Functor.associator (openD l E b (o.openOp d.i)) (pull l E b (o.geometry r.hom))
      (push l E b (o.geometry r.hom) ⋙ push l E b (o.geometry d.g))).inv ≫
    Functor.whiskerRight (inv (refinementOpenArrow l E b o r))
      (push l E b (o.geometry r.hom) ⋙ push l E b (o.geometry d.g)) ≫
    Functor.whiskerLeft (openD l E b (o.openOp c.i))
      ((pushComp l E b o r.hom d.g).hom ≫ (pushCongr l E b o r.hom_g).hom)

/-- The objects on which the compositors are invertible: bounded below towers with an etale
origin at every level, exactly the inputs of `Laws.exchange_iso`.
Source: blueprint step 1 and det-sp-tower-shriek-levels
(blueprint: def-sp-tower-shriek-compositor). -/
def Good (b : Base l E) (T : Scheme.{u}) : ObjectProperty (D l E T) :=
  fun K ↦ (∃ m : ℤ, K.IsGE m) ∧ ∀ n : ℕ, Nonempty (Origin l E b T n K)

/-- The triangle comparison is invertible on good towers.
Proof: by `Laws.detects`, check levels. Evaluation commutes with open extension, direct image
and inverse image (`openEvaluation`, `pushEvaluation`, `pullEvaluation`) compatibly with the
adjunction units and counits and with the open exchange, so the `n`-th evaluation of the
proper/open mate is the finite proper/open interchange `cg.i_! cf.g_* ⟶ p_* q_!` on the
bounded-below constructible origin of level `n`. Over `Y ⊆ cg.Z` it is the restriction
isomorphism (open restriction commutes with direct image), and over the closed complement both
sides vanish by proper base change for `p` (Stacks 095T, 0F7J), as `p⁻¹(Y) = cf.Z`. The open
and direct-image compositors are isomorphisms.
Source: blueprint step 2--3 (blueprint: def-sp-tower-shriek-compositor). -/
theorem triangleComparison_isIso (b : Base l E) (o : Operations l E b)
    (x : OpenExchange l E b o) (_laws : Laws l E b o x)
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S} [QuasiCompact f] [QuasiCompact g]
    (T : Compactification.Triangle f g) (K : D l E X) (_hK : Good l E b X K) :
    IsIso ((triangleComparison l E b o x T).app K) := by
  sorry

/-- The refinement comparison is invertible on good towers.
Proof: by `Laws.detects`, check levels. At level `n` the comparison is
`d.g_*` of `d.i_! M_n ⟶ r_* c.i_! M_n` (finite adjunction unit followed by the inverse open
base change). Over `X ⊆ d.Z` it is an isomorphism since `r⁻¹(X) = X`; over the closed
complement `r_* c.i_! M_n` vanishes by proper base change for the proper map `r`
(Stacks 095T, 0F7J).
Source: blueprint step 3 (blueprint: def-sp-tower-shriek-compositor). -/
theorem refinementComparison_isIso (b : Base l E) (o : Operations l E b)
    (x : OpenExchange l E b o) (laws : Laws l E b o x) {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (K : D l E X) (_hK : Good l E b X K) :
    IsIso ((refinementComparison l E b o x laws r hr).app K) := by
  sorry

/-- The triangle comparison as a natural isomorphism on good towers.
Source: blueprint step 3 (blueprint: def-sp-tower-shriek-compositor). -/
def triangleIso (b : Base l E) (o : Operations l E b) (x : OpenExchange l E b o)
    (laws : Laws l E b o x) {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    [QuasiCompact f] [QuasiCompact g] (T : Compactification.Triangle f g) :
    (Good l E b X).ι ⋙ (F l E b o T.cf ⋙ F l E b o T.cg) ≅
      (Good l E b X).ι ⋙ F l E b o T.cfg :=
  haveI (K : (Good l E b X).FullSubcategory) :
      IsIso ((Functor.whiskerLeft (Good l E b X).ι (triangleComparison l E b o x T)).app K) :=
    triangleComparison_isIso l E b o x laws T K.obj K.property
  haveI : IsIso (Functor.whiskerLeft (Good l E b X).ι (triangleComparison l E b o x T)) :=
    NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerLeft (Good l E b X).ι (triangleComparison l E b o x T))

/-- A refinement comparison as a natural isomorphism `F_c ≅ F_d` on good towers.
Source: blueprint step 3 (blueprint: def-sp-tower-shriek-compositor). -/
def refinementIso (b : Base l E) (o : Operations l E b) (x : OpenExchange l E b o)
    (laws : Laws l E b o x) {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (Good l E b X).ι ⋙ F l E b o c ≅ (Good l E b X).ι ⋙ F l E b o d :=
  haveI (K : (Good l E b X).FullSubcategory) :
      IsIso ((Functor.whiskerLeft (Good l E b X).ι
        (refinementComparison l E b o x laws r hr)).app K) :=
    refinementComparison_isIso l E b o x laws r hr K.obj K.property
  haveI : IsIso (Functor.whiskerLeft (Good l E b X).ι
      (refinementComparison l E b o x laws r hr)) :=
    NatIso.isIso_of_isIso_app _
  (asIso (Functor.whiskerLeft (Good l E b X).ι (refinementComparison l E b o x laws r hr))).symm

/-- The comparison between two arbitrary compactifications of a quasi-compact map,
through their canonical common refinement `Compactification.inf c d` (closure of the graph).
Source: blueprint step 3, independence of the compactification; Stacks 0F7J
(blueprint: def-sp-tower-shriek-compositor). -/
def compactificationIso (b : Base l E) (o : Operations l E b) (x : OpenExchange l E b o)
    (laws : Laws l E b o x) {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :
    (Good l E b X).ι ⋙ F l E b o c ≅ (Good l E b X).ι ⋙ F l E b o d :=
  (refinementIso l E b o x laws (Compactification.infFst c d)
      (Compactification.isPullback_infFst c d)).symm ≪≫
    refinementIso l E b o x laws (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d)

/-- The canonical compatible triangle attached to compactifications `d` of `g` and `e` of
`f ≫ g`: `Triangle.ofRestrict d (e.ofComp d)` (closure of `X` in `e.Z ×_S d.Z`).
Source: blueprint step 3, the compatible compactification tower
(blueprint: def-sp-tower-shriek-compositor). -/
abbrev canonicalTriangle {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    [QuasiCompact (f ≫ g)] (d : Compactification g) (e : Compactification (f ≫ g)) :
    Compactification.Triangle f g :=
  Compactification.Triangle.ofRestrict d (e.ofComp d)

/-- **The compositor** `α_{g,f} : F_g ∘ F_f ≅ F_{g∘f}` for arbitrary compactifications `c` of
`f`, `d` of `g` and `e` of `f ≫ g`, as a natural isomorphism on good towers: compare `c` with
the compactification of `f` in the canonical triangle, apply the triangle comparison, and
compare its compactification of `f ≫ g` with `e`.
Source: blueprint lem-sp-coefficient-tower-shriek-calculus, step 3; Stacks 0F7J
(blueprint: def-sp-tower-shriek-compositor). -/
def compositor (b : Base l E) (o : Operations l E b) (x : OpenExchange l E b o)
    (laws : Laws l E b o x) {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :
    (Good l E b X).ι ⋙ (F l E b o c ⋙ F l E b o d) ≅ (Good l E b X).ι ⋙ F l E b o e :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (compactificationIso l E b o x laws c (canonicalTriangle d e).cf) (F l E b o d) ≪≫
    Functor.associator _ _ _ ≪≫
    triangleIso l E b o x laws (canonicalTriangle d e) ≪≫
    compactificationIso l E b o x laws (canonicalTriangle d e).cfg e

end AlgebraicGeometry.ProEtale.SpTowerShriek

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
