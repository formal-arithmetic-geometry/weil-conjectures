/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-! # Bounded ordinary evaluation on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 08JJ and 0A8X.
(blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly)

## Main statements

- `assembly`: the canonical finite diagonal evaluation and its inverse chain map.
- `IsModuleEvaluation`: the section formula for the termwise comparison.

All tensor and Hom objects below are the recorded sheaf constructions. The
section formulas specify the actual comparison, including its normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.RingedSiteBoundedEvaluation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  (R : Sheaf J CommRingCat.{max u v w})

/-- The recorded module category, in a universe containing the site.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
abbrev Modules := ringedSiteModules.{max u v w, max u v w, v, u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- The structure sheaf placed in degree zero.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def unitComplex : CochainComplex (Modules.{u, v, w} R) ℤ :=
  (HomologicalComplex.single (Modules.{u, v, w} R) (.up ℤ) 0).obj (𝟙_ (Modules.{u, v, w} R))

/-- The ordinary Hom dual, with its recorded signed differential.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def dual (E : CochainComplex (Modules.{u, v, w} R) ℤ) : CochainComplex (Modules.{u, v, w} R) ℤ :=
  homComplex E (unitComplex.{u, v, w} R)

/-- The small coproducts used by total complexes exist by module sheafification.
Source: Stacks 03EK (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
instance smallColimits : HasColimitsOfSize.{0, 0} (Modules.{u, v, w} R) := inferInstance

/-- Supply the total-complex coproducts directly, avoiding a search through special totals.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
instance hasTotal (E F : CochainComplex (Modules.{u, v, w} R) ℤ) :
    F.HasMapBifunctor (dual.{u, v, w} R E) (curriedTensor (Modules.{u, v, w} R)) := fun _ ↦
      inferInstance

/-- The existing direct-sum total tensor complex, with sign on the second differential.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def total (E F : CochainComplex (Modules.{u, v, w} R) ℤ) : CochainComplex (Modules.{u, v, w} R) ℤ :=
  letI := hasTotal.{u, v, w} R E F
  CochainComplex.mapBifunctor F (dual.{u, v, w} R E) (curriedTensor (Modules.{u, v, w} R))

/-- The actual coproduct inclusion into the total tensor, with its codomain fixed.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def inclusion (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (p q n : ℤ) (h : p + q = n) :
    F.X p ⊗ (dual.{u, v, w} R E).X q ⟶ (total.{u, v, w} R E F).X n :=
  letI := hasTotal.{u, v, w} R E F
  CochainComplex.ιMapBifunctor F (dual.{u, v, w} R E) (curriedTensor (Modules.{u, v, w} R)) p q n h

/-- Local pure tensors enter the tensor sheaf through its sheafification unit.
Source: Stacks 03EK (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def pureTensor (A B : Modules.{u, v, w} R) (U : Cᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) : (A ⊗ B).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{max u v w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
      (A.val ⊗ B.val) ≫ (SheafOfModules.tensorObjIsoSheafification.{v, u, max u v w}
        (R := R) A B).inv.val).app U).hom
        (x ⊗ₜ[R.obj.obj U] y)

/-- Projection from the ordinary dual to its unique possibly nonzero Hom factor.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def dualProjection (E : CochainComplex (Modules.{u, v, w} R) ℤ) (q i : ℤ) (h : i + q = 0) :
    (dual.{u, v, w} R E).X q ⟶ SheafOfModules.homObj (E.X i) (𝟙_ (Modules.{u, v, w} R)) :=
  homComplexπ E (unitComplex.{u, v, w} R) q i 0 h ≫
    SheafOfModules.homObjMap (𝟙 (E.X i))
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules.{u, v, w} R))).hom

/-- The canonical module comparison is specified on every slice and every pure tensor.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def IsModuleEvaluation (A B : Modules.{u, v, w} R)
    (θ : B ⊗ SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R)) ⟶ SheafOfModules.homObj A B) :
    Prop :=
  ∀ (U : Cᵒᵖ) (y : B.val.obj U)
    (φ : (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R))).val.obj U)
    (V : (Over U.unop)ᵒᵖ) (x : A.val.obj (op V.unop.left)),
    ((((θ.val.app U).hom
      (pureTensor.{u, v, w} R B (SheafOfModules.homObj A (𝟙_ (Modules.{u, v, w} R))) U y φ)).app
        V).hom x) =
        ((φ.app V).hom x) • B.val.map V.unop.hom.op y

/-- The source finite-sum family, indexed by the complete closed interval, possibly empty.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def sourceFamily (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (a b n : ℤ)
    (i : ↥(Finset.Icc a b)) : Modules.{u, v, w} R :=
  F.X (i.val + n) ⊗ SheafOfModules.homObj (E.X i.val) (𝟙_ (Modules.{u, v, w} R))

/-- The target finite-sum family, using the same indexing and degree convention.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
def targetFamily (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (a b n : ℤ)
    (i : ↥(Finset.Icc a b)) : Modules.{u, v, w} R :=
  SheafOfModules.homObj (E.X i.val) (F.X (i.val + n))

/-- Finite biproducts from the existing sectionwise finite products; no new objects chosen.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly). -/
instance finiteBiproducts : HasFiniteBiproducts (Modules.{u, v, w} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Finite-support assembly of the actual ordinary tensor-Hom evaluation.
Source: Stacks 08JJ, last three displays of `lemma-dual-perfect-complex`, and
0A8X, the Hom and total tensor differentials.
(blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly).

Proof: (1) Project the dual onto Hom(E^i,R) in degree -i; all other factors
vanish. This is the projection identification of
lem-sfb-ringed-site-bounded-dual-components; its bidual clause is not used.
(2) Discard zero tensor summands outside the finite interval and reindex by
(p,q)=(i+n,-i). The coproduct universal property gives the source identification.
Zero tensor factors follow sectionwise and then by module sheafification.
(3) Discard zero Hom factors outside that interval. The remaining finite product
is the biproduct: its inclusions have identity diagonal and zero off-diagonal,
and the sum of inclusion-projection composites is the identity.
(4) The slice formula y tensor phi maps to (x maps to phi(x) times y) is balanced
and compatible with restriction. Sheafification and the coproduct universal
property give the degree maps. The analogous construction defines theta.
(5) On a pure tensor in degrees p,q, the tensor differential gives d_F y tensor
phi + (-1)^(p+q+1) y tensor (phi d_E). The Hom differential gives d_F f -
(-1)^(p+q) f d_E. Both have the same two components, at -q and -q-1, and zero
elsewhere, so the maps form a chain map without an additional sign.
(6) Under the specified identifications its matrix is diagonal with blocks theta.
(7) The finite diagonal of the inverses of theta is an inverse in each degree;
this includes the empty interval and requires no bound on F.
(8) Invert the chain-map equation to show that these degreewise inverses form
an inverse chain map. These eight steps are the node's complete proof plan.

The first existential constructs the canonical module comparisons and pins their
values on all slices. The implication then imposes precisely their invertibility,
so no additional existence assumption about those comparisons is needed. -/
theorem assembly (E F : CochainComplex (Modules.{u, v, w} R) ℤ) (a b : ℤ)
    (hbounded : ∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i)) :
    ∃ θ : ∀ (i : ℤ) (M : Modules.{u, v, w} R),
      M ⊗ SheafOfModules.homObj (E.X i) (𝟙_ (Modules.{u, v, w} R)) ⟶
        SheafOfModules.homObj (E.X i) M,
    (∀ (i : ℤ) (M : Modules.{u, v, w} R), IsModuleEvaluation.{u, v, w} R (E.X i) M (θ i M)) ∧
    ((∀ (i : ℤ) (M : Modules.{u, v, w} R), IsIso (θ i M)) →
      ∃ ε : total.{u, v, w} R E F ≅ homComplex E F,
      ∃ δ : ∀ i : ℤ,
        (dual.{u, v, w} R E).X (-i) ≅ SheafOfModules.homObj (E.X i) (𝟙_ (Modules.{u, v, w} R)),
      (∀ i : ℤ, (δ i).hom = dualProjection.{u, v, w} R E (-i) i (by omega)) ∧
      (∀ (p q n r : ℤ) (hpq : p + q = n) (hrq : r + q = 0)
        (hrn : r + n = p) (U : Cᵒᵖ) (y : (F.X p).val.obj U)
        (φ : ((dual.{u, v, w} R E).X q).val.obj U)
        (V : (Over U.unop)ᵒᵖ) (x : (E.X r).val.obj (op V.unop.left)),
        ((((homComplexπ E F n r p hrn).val.app U).hom
          (((inclusion.{u, v, w} R E F p q n hpq ≫ ε.hom.f n).val.app U).hom
            (pureTensor.{u, v, w} R (F.X p) ((dual.{u, v, w} R E).X q) U y φ))).app V).hom x =
          ((((dualProjection.{u, v, w} R E q r hrq).val.app U).hom φ).app V).hom x •
            (F.X p).val.map V.unop.hom.op y) ∧
      (∀ (p q n r t : ℤ) (hpq : p + q = n) (hrt : r + n = t) (_hrq : r + q ≠ 0),
        inclusion.{u, v, w} R E F p q n hpq ≫ ε.hom.f n ≫
          homComplexπ E F n r t hrt = 0) ∧
      (∀ n : ℤ,
        ∃ s : biproduct (sourceFamily.{u, v, w} R E F a b n) ≅ (total.{u, v, w} R E F).X n,
        ∃ t : (homComplex E F).X n ≅ biproduct (targetFamily.{u, v, w} R E F a b n),
        (∀ i : ↥(Finset.Icc a b),
          biproduct.ι (sourceFamily.{u, v, w} R E F a b n) i ≫ s.hom =
            F.X (i.val + n) ◁ (δ i.val).inv ≫
              inclusion.{u, v, w} R E F
                (i.val + n) (-i.val) n (by omega)) ∧
        (∀ i : ↥(Finset.Icc a b),
          t.hom ≫ biproduct.π (targetFamily.{u, v, w} R E F a b n) i =
            homComplexπ E F n i.val (i.val + n) rfl) ∧
        s.hom ≫ ε.hom.f n ≫ t.hom =
          biproduct.map (fun i : ↥(Finset.Icc a b) ↦ θ i.val (F.X (i.val + n)))) ∧
      (∀ (p q r : ℤ),
        inclusion.{u, v, w} R E F
            p q (p + q) rfl ≫
          (total.{u, v, w} R E F).d (p + q) (p + q + 1) ≫ ε.hom.f (p + q + 1) ≫
          homComplexπ E F (p + q + 1) r (r + (p + q + 1)) rfl =
        inclusion.{u, v, w} R E F
            p q (p + q) rfl ≫ ε.hom.f (p + q) ≫
          (homComplexπ E F (p + q) r (r + (p + q)) rfl ≫
            SheafOfModules.homObjMap (𝟙 (E.X r))
              (F.d (r + (p + q)) (r + (p + q + 1))) -
            (p + q).negOnePow •
              (homComplexπ E F (p + q) (r + 1) (r + (p + q + 1)) (by omega) ≫
                SheafOfModules.homObjMap (E.d r (r + 1)) (𝟙 _)))) ∧
      (∀ n : ℤ, IsIso (ε.hom.f n)) ∧
      (∀ n : ℤ, ε.inv.f n ≫ ε.hom.f n = 𝟙 _ ∧ ε.hom.f n ≫ ε.inv.f n = 𝟙 _)) := by
  sorry

end CategoryTheory.RingedSiteBoundedEvaluation
