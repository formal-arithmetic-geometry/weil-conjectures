module

public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Actual coefficient transitions of compact support

Source: blueprint latest, sk-prop-sp-integral-adjunction-direct-image.proof.md,
paragraph (1), the reduction maps are b followed by Rf_! of the input reduction
(blueprint: lem-sp-shriek-normalized-transition-comparison).

All systems and evaluations are the published ordinary derived sequence-site model.
Index n denotes the positive exponent n+1. Scalar coordinates below are fixed by
adjunction uniqueness, rather than a choice of maps between evaluated objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpShriekTransition

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual composite quotient homomorphism, including equal indices.
Source: blueprint coefficient convention
(blueprint: lem-sp-shriek-normalized-transition-comparison). -/
def quotientMap {m n : ℕ} (h : m ≤ n) : SpTowerShriek.R l E n →+* SpTowerShriek.R l E m :=
  ((Functor.ofOpSequence
    (X := fun a : ℕ ↦ CommRingCat.of (SpTowerShriek.R l E a))
    (fun a ↦ CommRingCat.ofHom
      (Ideal.Quotient.factorPowSucc (spEllIdeal l E) (a + 1)))).map (homOfLE h).op).hom

/-- The sequence-site coefficient map is the constant sheaf of the actual quotient map.
Source: blueprint paragraph (1), coefficient transitions
(blueprint: lem-sp-shriek-normalized-transition-comparison).
Proof: induction on the length of the index interval reduces to the adjacent quotient
map. Constant sheafification preserves its identity and composite, and ULift preserves
composition of ring homomorphisms. Thus both sides are the same quotient map. -/
theorem coefficientMap_eq (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SemilinearSections.coefficientMap (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h =
      proEtaleConstantRingMap (T := T) (quotientMap l E h) := by
  let : HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
    WeilConjectures.integralCoefficientRingSheafify.{u, u} T
  let L : CommRingCat.{u} ⥤ CommRingCat.{u + 1} :=
    { obj := fun A ↦ CommRingCat.of (ULift.{u + 1} A)
      map := fun f ↦ CommRingCat.ofHom (RingHom.ulift f.hom) }
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u} := Functor.ofOpSequence
    (X := fun a : ℕ ↦ CommRingCat.of (SpTowerShriek.R l E a))
    (fun a ↦ CommRingCat.ofHom
      (Ideal.Quotient.factorPowSucc (spEllIdeal l E) (a + 1)))
  let G : CommRingCat.{u} ⥤ Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
    L ⋙ constantSheaf.{u, u + 1, u + 1, u + 2} (ProEt.topology T) CommRingCat.{u + 1}
  let t : SemilinearSections.rings.{u + 1, u, u + 1} (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) ⟶ Q ⋙ G := by
    refine NatTrans.ofOpSequence (fun n ↦ 𝟙 _) ?_
    intro n
    simp only [SemilinearSections.rings, Functor.ofOpSequence_map_homOfLE_succ,
      Functor.comp_map]
    simp only [Category.comp_id, Category.id_comp]
    dsimp only [G, L, Functor.comp_map]
    unfold SpTowerShriek.tau spCoefficientCommRings Q
    simp only [Functor.ofOpSequence_map_homOfLE_succ]
    rfl
  exact (Category.comp_id _).symm.trans
    ((t.naturality (homOfLE h).op).trans (Category.id_comp _))

/-- The unique left-adjoint comparison from the generic normalized scalar model to
constant-ring scalar extension. Its right-adjoint comparison is equality transport
of the actual quotient map. Source: blueprint paragraph (1), scalar-adjoint convention
(blueprint: lem-sp-shriek-normalized-transition-comparison). -/
def scalarCoordinates (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {m n : ℕ} (h : m ≤ n) :
    ((b.calculus T).scalar h).T ≅ scalarExtensionFunctor (quotientMap l E h) T :=
  ((b.calculus T).scalar h).adjunction.leftAdjointUniq
    ((proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) (quotientMap l E h))).ofNatIsoRight
        (eqToIso (congrArg
          (fun a ↦ SemilinearSections.resD a) (coefficientMap_eq l E T h))).symm)

/-- The scalar-adjoint of the actual strict transition in constant-ring coordinates.
Source: blueprint paragraph (1); the derived system model's reduction construction
(blueprint: lem-sp-shriek-normalized-transition-comparison). -/
def rho (b : SpTowerShriek.Base l E) (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (C : SpTowerShriek.D l E T) :
    (scalarExtensionFunctor (quotientMap l E h) T).obj ((SpTowerShriek.Ev l E T n).obj C) ⟶
      (SpTowerShriek.Ev l E T m).obj C :=
  (scalarCoordinates l E b T h).inv.app _ ≫
    SemilinearSections.reduction (ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) h ((b.calculus T).scalar h) C

/-- Canonical scalar reassociation transported from the normalized system calculus.
Source: blueprint paragraph (1), the canonical scalar associators
(blueprint: lem-sp-shriek-normalized-transition-comparison). -/
def alpha (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {r m n : ℕ} (h : r ≤ m) (k : m ≤ n) :
    scalarExtensionFunctor (quotientMap l E k) T ⋙
        scalarExtensionFunctor (quotientMap l E h) T ≅
      scalarExtensionFunctor (quotientMap l E (h.trans k)) T :=
  Functor.isoWhiskerRight (scalarCoordinates l E b T k).symm _ ≪≫
    Functor.isoWhiskerLeft _ (scalarCoordinates l E b T h).symm ≪≫
    (b.calculus T).scalarComposition h k ≪≫ scalarCoordinates l E b T (h.trans k)

variable (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The specified b followed by finite compact support of the input reduction.
The b in this definition is literally the proper counit mate followed by the open
scalar comparison, as fixed by reductionDirectImageComparison.
Source: blueprint paragraph (1), the displayed composite
(blueprint: lem-sp-shriek-normalized-transition-comparison). -/
def word {m n : ℕ} (h : m ≤ n) (C : SpTowerShriek.D l E X) :
    (scalarExtensionFunctor (quotientMap l E h) Y).obj
        ((SpTowerShriek.finiteF l E b c n).obj ((SpTowerShriek.Ev l E X n).obj C)) ⟶
      (SpTowerShriek.finiteF l E b c m).obj ((SpTowerShriek.Ev l E X m).obj C) :=
  letI := b.finite n
  letI := b.finite m
  (reductionDirectImageComparison (quotientMap l E h) c.i c.g).app
      ((SpTowerShriek.Ev l E X n).obj C) ≫
    (SpTowerShriek.finiteF l E b c m).map (rho l E b X h C)

/-- The actual output reduction, conjugated by the canonical compact-support evaluations.
Source: blueprint paragraph (1); det-sp-tower-shriek-levels evaluation identifications
(blueprint: lem-sp-shriek-normalized-transition-comparison). -/
def actual {m n : ℕ} (h : m ≤ n) (C : SpTowerShriek.D l E X) :
    (scalarExtensionFunctor (quotientMap l E h) Y).obj
        ((SpTowerShriek.finiteF l E b c n).obj ((SpTowerShriek.Ev l E X n).obj C)) ⟶
      (SpTowerShriek.finiteF l E b c m).obj ((SpTowerShriek.Ev l E X m).obj C) :=
  (scalarExtensionFunctor (quotientMap l E h) Y).map
      ((SpTowerShriek.Fcomparison l E b o c n).inv.app C) ≫
    rho l E b Y h ((SpTowerShriek.F l E b o c).obj C) ≫
    (SpTowerShriek.Fcomparison l E b o c m).hom.app C

/-- The actual compact-support transition is precisely the specified coefficient word,
naturally in the bounded-below input, and its successive words satisfy the scalar cocycle.
Source: blueprint latest, sk-prop-sp-integral-adjunction-direct-image.proof.md,
paragraph (1) (blueprint: lem-sp-shriek-normalized-transition-comparison).

Proof:
1. Use def-sp-reduction-direct-image-comparison to write b as gamma followed by Rp_*(e).
   Gamma is the transpose of the scalar-extended proper counit, and e is the normalized
   comparison of the composite open/scalar left adjoints. These exist on ambient D.
2. Exact extension by zero and scalar restriction commute. The open scalar-adjoint is
   j_!(rho) after e: restrict to the open, use lem-sf-open-tensor-normalization to identify
   its unit and tensor map with the identity, and use full faithfulness to identify the
   maps. This is done on the strict derived system model, before level evaluation.
3. Apply lem-coef-semilinear-derived-sections to p and j_!C. Its actual direct-image
   transition is Rp_*(the open transition) after gamma, preserving the same counit.
   Substitute step 2 and use det-sp-tower-shriek-levels' canonical Fcomparison to obtain
   actual = word. The scalarCoordinates comparisons merely change normalized adjunction
   coordinates; evaluations are never used as a faithfulness test.
4. Naturality of rho and of b gives the displayed naturality square for every input map.
5. Paste successive words using b's naturality at rho. The input reduction cocycle
   replaces the two rho maps by direct reduction after alpha_X. The coefficient cocycle
   det-sp-reduction-direct-image replaces the two b maps by direct b after alpha_Y.
   Thus the result is alpha_Y followed by the direct word. Equal indices use the scalar
   unit and the original transition. No coefficient flatness or projective dimension
   is assumed, and input transitions need not be invertible. -/
theorem shriek_normalized_transition_comparison
    (pchar : ℕ) (hp : 0 < pchar) (hpl : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))] [QuasiCompact (c.Z ↘ Spec (.of k))]
    [IsSeparated (c.Z ↘ Spec (.of k))]
    (C : DerivedCategory.Plus (SpTowerShriek.S l E X))
    (hC : ∀ n : ℕ, SpTowerShriek.GoodLevel l E b X n C.obj) :
    (∀ {m n : ℕ} (h : m ≤ n), actual l E b o c h C.obj = word l E b c h C.obj) ∧
    (∀ (C' : DerivedCategory.Plus (SpTowerShriek.S l E X))
      (_hC' : ∀ n : ℕ, SpTowerShriek.GoodLevel l E b X n C'.obj)
      (v : C.obj ⟶ C'.obj) {m n : ℕ} (h : m ≤ n),
      (scalarExtensionFunctor (quotientMap l E h) Y).map
          ((SpTowerShriek.finiteF l E b c n).map ((SpTowerShriek.Ev l E X n).map v)) ≫
          word l E b c h C'.obj =
        word l E b c h C.obj ≫
          (SpTowerShriek.finiteF l E b c m).map ((SpTowerShriek.Ev l E X m).map v)) ∧
    (∀ {r m n : ℕ} (h : r ≤ m) (k : m ≤ n),
      (scalarExtensionFunctor (quotientMap l E h) Y).map (word l E b c k C.obj) ≫
          word l E b c h C.obj =
        (alpha l E b Y h k).hom.app
            ((SpTowerShriek.finiteF l E b c n).obj ((SpTowerShriek.Ev l E X n).obj C.obj)) ≫
          word l E b c (h.trans k) C.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.SpShriekTransition
