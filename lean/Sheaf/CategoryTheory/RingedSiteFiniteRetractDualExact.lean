/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Internal dual and exact Hom of a finite-free retract

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, final finite-free/direct-summand
calculation, expanded in the node into dual-basis and kernel/epimorphism calculations
(blueprint: lem-sfb-ringed-site-finite-retract-dual-exact).

The coefficient universe contains both site universes, without equating them. All maps
below use the existing internal Hom. The bidual isomorphism is specified by evaluation
on every object of every slice, and its inverse by the finite dual-basis formula.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v w}]
  {R : Sheaf J CommRingCat.{max c v w}}

/-- The standard coordinate projection from the existing finite free sheaf.
Source: Stacks 08JJ, coordinate calculation
(blueprint: lem-sfb-ringed-site-finite-retract-dual-exact). -/
def finiteRetractCoordinate (n : ℕ) (j : ULift.{max c v w} (Fin n)) :
    free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R)
      (ULift.{max c v w} (Fin n)) ⟶
      unit ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R) :=
  Sigma.desc (fun k : ULift.{max c v w} (Fin n) ↦ if k = j then 𝟙 _ else 0)

/-- The section `t_j = p(u_j)`, evaluated on any object of the site.
Source: Stacks 08JJ, dual-basis calculation
(blueprint: lem-sfb-ringed-site-finite-retract-dual-exact). -/
def finiteRetractVector {n : ℕ}
    {T : ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
      RingCat.{max c v w})).obj R)}
    (p : free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R)
      (ULift.{max c v w} (Fin n)) ⟶ T)
    (j : ULift.{max c v w} (Fin n)) (U : Cᵒᵖ) : T.val.obj U :=
  (ιFree j ≫ p).val.app U (1 : R.obj.obj U)

/-- The section `λ_j = u_j^* i` of the existing internal dual, as a map on the slice.
Source: Stacks 08JJ, dual-basis calculation
(blueprint: lem-sfb-ringed-site-finite-retract-dual-exact). -/
def finiteRetractCovector {n : ℕ}
    {T : ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
      RingCat.{max c v w})).obj R)}
    (i : T ⟶ free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
      R) (ULift.{max c v w} (Fin n)))
    (j : ULift.{max c v w} (Fin n)) (U : Cᵒᵖ) :
    (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂ CommRingCat.{max
      c v w} RingCat.{max c v
      w})).obj R))).val.obj U :=
  (PresheafOfModules.restrictOver R.obj U.unop).map
    (i ≫ finiteRetractCoordinate (R := R) n j).val

/-- Internal duality, dual bases, biduality, and exact internal Hom for a finite-free retract.

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, final two paragraphs;
sites-modules.tex, Tags 03EM and 03DA supply internal Hom and the abelian category
(blueprint: lem-sfb-ringed-site-finite-retract-dual-exact).

Proof: (1) Coordinate inclusions and projections identify the finite product of copies
of the coefficient sheaf with its coproduct. On each slice, evaluation on the standard
vectors identifies Hom from this free sheaf to F with the finite power of F. Its inverse
sends a tuple to the linear map given by its finite linear combination. These formulas
commute with restriction and postcomposition. (2) Precompose with p and i; their composite
is the identity because i followed by p is the identity. Specializing the coordinate
identification to F = R exhibits the dual as a finite-free retract. (3) Expand i(t) in
coordinates and apply p to get the dual-basis identity. Apply an arbitrary local linear
functional to this identity to expand that functional in the covectors λ_j. (4) Evaluation
is a sheaf map. The displayed sum defines its inverse: one composite is the dual-basis
identity, and the other follows from the functional expansion and commutativity of R.
(5) Associativity of composition makes the precomposition splittings natural in F.
(6) Finite powers preserve kernels coordinatewise and preserve epimorphisms by the
coordinate inclusions and projections; this uses categorical epimorphisms, not
surjectivity on sections. (7) The natural splitting transports the kernel property to
Hom(T,-): insert the inclusion, factor through the finite-power kernel, and apply the
retraction. Monicity gives uniqueness. (8) For epimorphy, a map killing Hom(T,b), after
precomposition with the retraction, kills the finite-power epimorphism, and hence is zero;
compose with the splitting inclusion to recover the original map. (9) Every operation is
restriction, evaluation, composition, a finite sum or scalar multiplication. The formulas
therefore commute with passing to every localized site and with relocalization. For n=0
the splitting forces T=0, and the same proof uses empty sums. -/
theorem ringedSite_finite_retract_dual_exact
    (n : ℕ)
    (T : ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
      RingCat.{max c v w})).obj R))
    (i : T ⟶ free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
      R) (ULift.{max c v w} (Fin n)))
    (p : free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R)
      (ULift.{max c v w} (Fin n)) ⟶ T)
    (hip : i ≫ p = 𝟙 T) :
    (∀ F : ringedSiteModules.{max c v w}
        ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R),
      homObjMap.{max c v w, v, c, max c v w} (R := R) p (𝟙 F) ≫ homObjMap.{max c v w, v, c, max c v
        w} (R := R) i (𝟙 F) =
        𝟙 (homObj.{max c v w, v, c, max c v w} (R := R) T F)) ∧
    (∃ e : ∀ F : ringedSiteModules.{max c v w}
        ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R),
        homObj.{max c v w, v, c, max c v w} (R := R) (free (R := (sheafCompose J (forget₂
          CommRingCat.{max c v w} RingCat.{max c
          v w})).obj R) (ULift.{max c v w} (Fin n))) F ≅
          ∐ (fun _ : ULift.{max c v w} (Fin n) ↦ F),
      (∀ (F : ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
        RingCat.{max c v w})).obj R))
        (U : Cᵒᵖ)
        (φ : (homObj.{max c v w, v, c, max c v w} (R := R)
          (free (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R)
            (ULift.{max c v w} (Fin n))) F).val.obj U)
        (j : ULift.{max c v w} (Fin n)),
        ((e F).hom ≫ Sigma.desc (fun k : ULift.{max c v w} (Fin n) ↦ if k = j then 𝟙 F else
          0)).val.app U φ =
          φ.app (op (Over.mk (𝟙 U.unop)))
            ((ιFree (R := (sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
              R) j).val.app U
              (1 : R.obj.obj U))) ∧
      (∀ (F G : ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
        RingCat.{max c v w})).obj R))
        (f : F ⟶ G),
        homObjMap.{max c v w, v, c, max c v w} (R := R) (𝟙 _) f ≫ (e G).hom =
          (e F).hom ≫ Limits.Sigma.map (fun _ : ULift.{max c v w} (Fin n) ↦ f)) ∧
      (homObjMap.{max c v w, v, c, max c v w} (R := R) p (𝟙 (unit ((sheafCompose J (forget₂
        CommRingCat.{max c v w} RingCat.{max
        c v w})).obj R))) ≫
          (e (unit ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
            R))).hom) ≫
        ((e (unit ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
          R))).inv ≫
          homObjMap.{max c v w, v, c, max c v w} (R := R) i (𝟙 _)) = 𝟙 _ ) ∧
    (∀ (U : Cᵒᵖ) (t : T.val.obj U),
      ∑ j : ULift.{max c v w} (Fin n),
        (@id (R.obj.obj U)
          ((finiteRetractCovector (R := R) (T := T) (n := n) i j U).app (op (Over.mk (𝟙 U.unop)))
            t)) •
          finiteRetractVector (R := R) (T := T) (n := n) p j U = t) ∧
    (∀ (U : Cᵒᵖ)
      (φ : (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂
        CommRingCat.{max c v w} RingCat.{max c
        v w})).obj R))).val.obj U),
      φ = ∑ j : ULift.{max c v w} (Fin n),
        (@id (R.obj.obj U)
          (φ.app (op (Over.mk (𝟙 U.unop))) (finiteRetractVector (R := R) (T := T) (n := n) p j U)))
            •
          finiteRetractCovector (R := R) (T := T) (n := n) i j U) ∧
    (∃ d : T ≅ homObj.{max c v w, v, c, max c v w} (R := R)
        (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂
          CommRingCat.{max c v w} RingCat.{max c v
          w})).obj R)))
        (unit ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj R)),
      (∀ (U : Cᵒᵖ) (t : T.val.obj U) (W : (Over U.unop)ᵒᵖ)
        (φ : (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂
          CommRingCat.{max c v w} RingCat.{max
          c v w})).obj R))).val.obj
          (op W.unop.left)),
        ((d.hom.val.app U t).app W) φ =
          φ.app (op (Over.mk (𝟙 W.unop.left))) (T.val.map W.unop.hom.op t)) ∧
      (∀ (U : Cᵒᵖ)
        (α : (homObj.{max c v w, v, c, max c v w} (R := R)
          (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂
            CommRingCat.{max c v w} RingCat.{max c
            v w})).obj R)))
          (unit ((sheafCompose J (forget₂ CommRingCat.{max c v w} RingCat.{max c v w})).obj
            R))).val.obj U),
        d.inv.val.app U α = ∑ j : ULift.{max c v w} (Fin n),
          (@id (R.obj.obj U)
            (α.app (op (Over.mk (𝟙 U.unop))) (finiteRetractCovector (R := R) (T := T) (n := n) i j
              U))) •
            finiteRetractVector (R := R) (T := T) (n := n) p j U)) ∧
    (∀ S : ShortComplex
        (ringedSiteModules.{max c v w} ((sheafCompose J (forget₂ CommRingCat.{max c v w}
          RingCat.{max c v w})).obj R)),
      S.ShortExact → ∃ hzero : homObjMap.{max c v w, v, c, max c v w} (R := R) (𝟙 T) S.f ≫
        homObjMap.{max c v w, v, c, max c v w} (R := R) (𝟙 T) S.g = 0,
        (ShortComplex.mk (homObjMap.{max c v w, v, c, max c v w} (R := R) (𝟙 T) S.f) (homObjMap.{max
          c v w, v, c, max c v w} (R := R) (𝟙 T) S.g)
          hzero).ShortExact) ∧
    (∀ (U V : Cᵒᵖ) (a : U ⟶ V) (j : ULift.{max c v w} (Fin n)),
      T.val.map a (finiteRetractVector (R := R) (T := T) (n := n) p j U) = finiteRetractVector (R :=
        R) (T := T) (n := n) p j V ∧
      (homObj.{max c v w, v, c, max c v w} (R := R) T (unit ((sheafCompose J (forget₂
        CommRingCat.{max c v w} RingCat.{max c v
        w})).obj R))).val.map a
        (finiteRetractCovector (R := R) (T := T) (n := n) i j U) = finiteRetractCovector (R := R) (T
          := T) (n := n) i j V) := by
  sorry

end SheafOfModules
