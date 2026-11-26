/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
public import WeilConjectures.Compactification.Triangle

/-! # Geometric system projection and composition maps

## Implementation details

The compact-support compositor is the existing graph-refinement word, not a lift
chosen from its finite evaluations. The intrinsic proper/open mate fixes all comparison factors
before evaluation; no independently chosen finite lift occurs. `compositorAlong` keeps the
triangle as a parameter, which permits the word calculation without unfolding the canonical
compactification construction. Level `n` means exponent `n + 1`.

## References

* Stacks Project, Tags 0F7J, 0ATU, 0B56 and 0E8I.
* Zheng, Construction 4.1 and Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.SystemProjectionFormula

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Invert a comparison exactly on its isomorphism domain, and extend by zero elsewhere. -/
def inverseOnDomain {C : Type v} [Category.{w} C] [HasZeroMorphisms C]
    {K M : C} (b : K ⟶ M) : M ⟶ K :=
  open Classical in
  if h : IsIso b then @inv _ _ _ _ b h else 0

/-- Compact support in the specified simultaneous geometric section presentation. -/
abbrev support (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) := Operations.shriek l E o c.i ⋙ Operations.push l E o c.g

/-- Reverse refinement: the intrinsic proper/open mate and direct-image compositor. -/
def refinement (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {d e : Compactification f} (r : d.Refinement e) : support l E o e ⟶ support l E o d :=
  haveI := d.quasiCompact_openImmersion inferInstance
  haveI := e.quasiCompact_openImmersion inferInstance
  Functor.whiskerRight
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight
        (b.push l E (𝟙 X) ≪≫ ProEtale.SemilinearProperOpen.sId
          (scalarRings l E) (scalarTransitions l E) X).inv (Operations.shriek l E o e.i) ≫
      q.gamma d.i (𝟙 X) r.hom e.i (r.i_hom.trans (Category.id_comp _).symm))
      (Operations.push l E o e.g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Operations.shriek l E o d.i)
      ((c.pushComp l E r.hom e.g).hom ≫
        eqToHom (congrArg (Operations.push l E o) r.hom_g))

/-- Transport through the canonical graph common refinement, taking the actual inverse
on the comparison's isomorphism domain. -/
def change (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (d e : Compactification f) (M : System l E X) :
    (support l E o d).obj M ⟶ (support l E o e).obj M :=
  (refinement l E o c a b q (Compactification.infFst d e)).app M ≫
    inverseOnDomain
      ((refinement l E o c a b q (Compactification.infSnd d e)).app M)

/-- The actual proper/open word in a compatible triangle, including its equality casts. -/
def triangleWord (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] (T : Compactification.Triangle f g) :
    support l E o T.cf ⋙ support l E o T.cg ⟶ support l E o T.cfg :=
  haveI := T.cf.quasiCompact_openImmersion inferInstance
  haveI := T.cg.quasiCompact_openImmersion inferInstance
  haveI : QuasiCompact T.q := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    T.isPullback inferInstance
  (Functor.associator _ _ _).symm.hom ≫
    Functor.whiskerRight ((Functor.associator _ _ _).hom) _ ≫
    Functor.whiskerRight (Functor.whiskerLeft (Operations.shriek l E o T.cf.i)
      (q.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)) _ ≫
    Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
    Functor.whiskerRight (Functor.whiskerRight ((c.openComp l E T.cf.i T.q).hom ≫
      (openCongr l E o T.i_q).hom) _) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Operations.shriek l E o T.cfg.i)
      ((c.pushComp l E T.p T.cg.g).hom ≫
        eqToHom (congrArg (Operations.push l E o) T.p_g))

/-- The geometric compositor word along an explicit compatible triangle. -/
def compositorAlong (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (T : Compactification.Triangle f g) (M : System l E X) :
    (support l E o cg).obj ((support l E o cf).obj M) ⟶ (support l E o cfg).obj M :=
  (support l E o cg).map (change l E o c a b q cf T.cf M) ≫
    change l E o c a b q cg T.cg ((support l E o T.cf).obj M) ≫
    (triangleWord l E o c a b q T).app M ≫ change l E o c a b q T.cfg cfg M

/-- The proper counit projection followed by the open tensor comparison, in the same
simultaneous geometric section model. -/
def projection (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f)
    (M : System l E X) (N : System l E Y) :=
  compactificationProjection l E o c a d M N

end WeilConjectures.SystemProjectionFormula
