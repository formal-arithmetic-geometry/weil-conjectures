/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory

/-! # A single-point obstruction to versality

Source: Stacks Project, artin.tex, Tag 0G2J (lemma-single-point), over an affine
Noetherian base (blueprint: lem-sfb-artin-single-point-obstruction).

All objects and arrows are in the existing total category over the big fppf site's
underlying category. No descent hypothesis is imposed. The square-zero gluing
hypothesis is expressed by pushouts of lifted spans: for a fibred groupoid this is
exactly equivalence with the groupoid of triples, including its specified isomorphism
and compatible arrows. The versality test and obstruction likewise retain actual
arrows, hence the specified restriction isomorphisms, without choosing a cleavage.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Failure of versality at a finite type point produces an affine square-zero
thickening with ideal the residue field and no local retraction of the object.
The inline negated lifting condition is versality with its specified isomorphism.
Surjective residue maps from local rings identify their residue fields; composing
with the nilpotent surjection supplies the common marking for the larger test ring.

The additive equivalence `e` and its scalar equation express the isomorphism of
`ker p` with the residue field as an `R₀`-module. Its scalar action descends from `R`
because the kernel squares to zero and `p` is onto. Evaluation on `R₀` is the actual
ring map contravariantly corresponding to the canonical residue-field point.

The final arrow equation is the equivalent formulation in the node and source:
`aW` restricts `y` to `W`, and the two arrows from `z` restrict `x → y` to `U ∩ W`.
An arrow `beta` determines its base map `r : W → U`; the equation forces `r` to
restrict to the inclusion and forces its pullback isomorphism to restrict to
`theta⁻¹`. Conversely such an `r` and isomorphism give exactly this arrow.

Source: Stacks Project, artin.tex, Tag 0G2J (lemma-single-point)
(blueprint: lem-sfb-artin-single-point-obstruction).

Proof:
1. Put k = kappa(u). Its finite type over R₀ and that of R₀ over Lambda make it
   finite type over Lambda. Negating versality gives an unsolvable test problem.
   Factor its surjection into small extensions by lem-sfb-artin-local-test-algebra
   in def-sfb-artin-deformation-test-category. Successive lifting would solve the
   original problem, so one small extension B → A is unsolvable. Its kernel J is
   k and is annihilated by the maximal ideal, hence J² = 0.
2. Form R = R₀ ×_A B with coordinatewise operations. Projection p onto R₀ is onto,
   its kernel is J, and multiplication on J factors through evaluation at u.
   This gives the displayed additive equivalence and scalar equation. The affine
   closed-immersion description (def-weil-closed-immersion) and
   def-sbc-first-order-thickening give the first-order thickening j and the map
   h : Spec B → Spec R whose restriction is j composed with the test map.
3. Apply the assumed gluing equivalence to R₀ → A ← B. The given objects and their
   specified identification glue to y and the arrow c : x → y, compatibly with
   the identification on Spec B. This is precisely essential surjectivity of
   the groupoid equivalence, with its compatibility retained.
4. If a neighbourhood and beta existed, the nilpotent maximal ideal of B from
   lem-sfb-artin-local-test-algebra makes Spec B a single point mapping to u.
   Thus h factors through W. Pulling beta back along h solves the small-extension
   problem, including its prescribed reduction isomorphism, a contradiction.
   Every arrow is cartesian in a fibred groupoid, so the arrow and isomorphism
   formulations of the conclusion agree. -/
theorem artin_single_point_obstruction
    (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    (F : BasedCategory.{v, w} (Over (Spec (.of Λ))))
    (hF : IsFibredInGroupoids F)
    (hglue : ∀ (A B B' : CommAlgCat.{u} Λ) (f : A ⟶ B) (q : B' ⟶ B),
      Function.Surjective q.hom → RingHom.ker q.hom.toRingHom ^ 2 = ⊥ →
      ∀ (P : Over (Spec (.of Λ)))
        (i : (algSpec (.of Λ)).obj (op A) ⟶ P)
        (j : (algSpec (.of Λ)).obj (op B') ⟶ P),
        IsPushout ((algSpec (.of Λ)).map f.op) ((algSpec (.of Λ)).map q.op) i j →
        ∀ (z : Functor.Fiber F.p ((algSpec (.of Λ)).obj (op B)))
          (xA : Functor.Fiber F.p ((algSpec (.of Λ)).obj (op A)))
          (xB' : Functor.Fiber F.p ((algSpec (.of Λ)).obj (op B')))
          (a : z.val ⟶ xA.val) (b : z.val ⟶ xB'.val),
          F.p.IsHomLift ((algSpec (.of Λ)).map f.op) a →
          F.p.IsHomLift ((algSpec (.of Λ)).map q.op) b →
          ∃ (yP : Functor.Fiber F.p P) (c : xA.val ⟶ yP.val) (d : xB'.val ⟶ yP.val),
            F.p.IsHomLift i c ∧ F.p.IsHomLift j d ∧ IsPushout a b c d)
    (R₀ : CommAlgCat.{u} Λ)
    [LocallyOfFiniteType ((algSpec (.of Λ)).obj (op R₀)).hom]
    [QuasiCompact ((algSpec (.of Λ)).obj (op R₀)).hom]
    (x : Functor.Fiber F.p ((algSpec (.of Λ)).obj (op R₀)))
    (u₀ : Spec (.of R₀))
    (hft : LocallyOfFiniteType ((Spec (.of R₀)).fromSpecResidueField u₀) ∧
      QuasiCompact ((Spec (.of R₀)).fromSpecResidueField u₀))
    (hnonversal : ¬ (∀ (A' A : CommRingCat.{u})
      [IsArtinianRing A'] [IsLocalRing A'] [IsArtinianRing A] [IsLocalRing A]
      (q : A' ⟶ A), Function.Surjective q.hom → IsNilpotent (RingHom.ker q.hom) →
      ∀ (ρ : A ⟶ (Spec (.of R₀)).residueField u₀), Function.Surjective ρ.hom →
      ∀ (s' : Spec A' ⟶ Spec (.of Λ))
        (a : Over.mk (Spec.map q ≫ s') ⟶ (algSpec (.of Λ)).obj (op R₀)),
        Spec.map ρ ≫ a.left = (Spec (.of R₀)).fromSpecResidueField u₀ →
      ∀ (yA' : Functor.Fiber F.p (Over.mk s'))
        (yA : Functor.Fiber F.p (Over.mk (Spec.map q ≫ s')))
        (b : yA.val ⟶ yA'.val) (c : yA.val ⟶ x.val),
        F.p.IsHomLift (Over.homMk (U := Over.mk (Spec.map q ≫ s'))
          (V := Over.mk s') (Spec.map q) rfl) b → F.p.IsHomLift a c →
        ∃ (a' : Over.mk s' ⟶ (algSpec (.of Λ)).obj (op R₀)) (d : yA'.val ⟶ x.val),
          F.p.IsHomLift a' d ∧ Spec.map q ≫ a'.left = a.left ∧ b ≫ d = c)) :
    ∃ (R : CommAlgCat.{u} Λ) (p : R ⟶ R₀)
      (j : (algSpec (.of Λ)).obj (op R₀) ⟶ (algSpec (.of Λ)).obj (op R)),
      j = (algSpec (.of Λ)).map p.op ∧ Function.Surjective p.hom ∧
      RingHom.ker p.hom.toRingHom ^ 2 = ⊥ ∧ IsFirstOrderThickening j.left ∧
      (∃ e : RingHom.ker p.hom.toRingHom ≃+ (Spec (.of R₀)).residueField u₀,
        ∀ (r : R) (i : RingHom.ker p.hom.toRingHom),
          e (r • i) =
            (Spec.preimage ((Spec (.of R₀)).fromSpecResidueField u₀)).hom (p.hom r) *
              e i) ∧
      ∃ (y : Functor.Fiber F.p ((algSpec (.of Λ)).obj (op R))) (c : x.val ⟶ y.val),
        F.p.IsHomLift j c ∧
        ∀ (W : (Spec (.of R)).Opens), j.left u₀ ∈ W →
        ∀ (yW : Functor.Fiber F.p
            (Over.mk (W.ι ≫ ((algSpec (.of Λ)).obj (op R)).hom)))
          (aW : yW.val ⟶ y.val), F.p.IsHomLift (Over.homMk
            (V := (algSpec (.of Λ)).obj (op R))
            (U := Over.mk (W.ι ≫ ((algSpec (.of Λ)).obj (op R)).hom)) W.ι rfl) aW →
        ∀ (z : Functor.Fiber F.p (pullback j (Over.homMk
            (V := (algSpec (.of Λ)).obj (op R))
            (U := Over.mk (W.ι ≫ ((algSpec (.of Λ)).obj (op R)).hom)) W.ι rfl)))
          (aU : z.val ⟶ x.val) (aUW : z.val ⟶ yW.val),
          F.p.IsHomLift (pullback.fst j (Over.homMk
            (V := (algSpec (.of Λ)).obj (op R))
            (U := Over.mk (W.ι ≫ ((algSpec (.of Λ)).obj (op R)).hom)) W.ι rfl)) aU →
          F.p.IsHomLift (pullback.snd j (Over.homMk
            (V := (algSpec (.of Λ)).obj (op R))
            (U := Over.mk (W.ι ≫ ((algSpec (.of Λ)).obj (op R)).hom)) W.ι rfl)) aUW →
          aU ≫ c = aUW ≫ aW → ¬ ∃ beta : yW.val ⟶ x.val, aUW ≫ beta = aU := by
  sorry

end AlgebraicGeometry
