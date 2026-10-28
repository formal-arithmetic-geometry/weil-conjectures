module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.VerdierDual
public import Sheaf.Paper.DerivedWeilOperations
public import Sheaf.Paper.NativeCompactProjectionFormula
import Sheaf.Paper.NativeDerivedWeilTensorConstructible
import Sheaf.Paper.NativeWeilClosedForgetful
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Native Weil dualizing Hom transposition

Source: blueprint, fix-lem-tensor-adjunction.proof.md, Step 1, and
fix-cor-verdier-exchange.proof.md, Steps 1--2
(blueprint: lem-sf-weil-dualizing-hom-transposition).

The structure adjunction is supplied explicitly. All Weil complexes and their
morphisms belong to the actual bounded constructible full subcategories of the
native derived categories. The ambient internal Hom is exactly derivedHom.
-/

@[expose] public noncomputable section

set_option autoImplicit false


universe u

open CategoryTheory Opposite
open scoped MonoidalCategory

-- Use the canonical identity structure on the base point while elaborating.
attribute [-instance] AlgebraicGeometry.specOverSpec

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma closed_uncurry_naturality
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : WeilConjectures.CoefficientClosedStructure H)
    {K K' L L' W : D} (f : K' ⟶ K) (g : L' ⟶ L)
    (v : L ⟶ H.obj (op K, W)) :
    (S.transpose L' K' W).symm (g ≫ v ≫ H.map (Prod.mkHom f.op (𝟙 W))) =
      S.tensor.map (Prod.mkHom g f) ≫ (S.transpose L K W).symm v := by
  let := S.monoidal
  change (MonoidalCategory.tensorRight K').map
      (g ≫ v ≫ H.map (Prod.mkHom f.op (𝟙 W))) ≫ (S.adjunction K').counit.app W =
    S.tensor.map (Prod.mkHom g f) ≫
      (MonoidalCategory.tensorRight K).map v ≫ (S.adjunction K).counit.app W
  simp only [Functor.map_comp, Category.assoc]
  rw [S.evaluation_naturality K K' W f]
  change (g ▷ K') ≫ (v ▷ K') ≫ (H.obj (op K, W) ◁ f) ≫
      (S.adjunction K).counit.app W =
    (g ⊗ₘ f) ≫ (v ▷ K) ≫ (S.adjunction K).counit.app W
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]

namespace AlgebraicGeometry.WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

variable (J : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X)

/-- The dualizing object for the supplied right adjoint, evaluated at the actual
rank-one coefficient Weil sheaf in degree zero on the point.
Source: fix-cor-verdier-exchange, Step 1
(blueprint: lem-sf-weil-dualizing-hom-transposition). -/
def nativeStructureDualizing : WeilComplex k₀ l X :=
  J.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))

/-- Ambient internal-Hom duality for this chosen dualizing object.
Source: fix-cor-verdier-exchange, Step 2; native DerivedHom.lean
(blueprint: lem-sf-weil-dualizing-hom-transposition). -/
def nativeStructureDual : (DerivedCategory (ProEtaleWeilSheaf k₀ l X))ᵒᵖ ⥤
    DerivedCategory (ProEtaleWeilSheaf k₀ l X) :=
  ProEtaleWeilSheaf.derivedHom k₀ l X (nativeStructureDualizing k₀ l X J).obj

/-- Restriction of that exact ambient Hom functor when its values are constructible.
Source: fix-cor-verdier-exchange, Step 2; dual-preservation lemma
(blueprint: lem-sf-weil-dualizing-hom-transposition). -/
def nativeStructureDualOfPreserves
    (h : ∀ K : WeilComplex k₀ l X, objectProperty k₀ l X
      ((nativeStructureDual k₀ l X J).obj (op K.obj))) :
    (WeilComplex k₀ l X)ᵒᵖ ⥤ WeilComplex k₀ l X :=
  ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙ nativeStructureDual k₀ l X J)
    (fun K ↦ h K.unop)

/-- Native uncurrying into the supplied dualizing object. The closed structure uses
right tensoring, so symmetry changes K tensor L to L tensor K before evaluation.
The nativeModel inverse identifies its internal Hom with exactly derivedHom.
Source: fix-lem-tensor-adjunction, Step 1, tensor--Hom transposition
(blueprint: lem-sf-weil-dualizing-hom-transposition). -/
def nativeDualizingUncurry (K L : WeilComplex k₀ l X)
    (v : L.obj ⟶ (nativeStructureDual k₀ l X J).obj (op K.obj)) :
    ((nativeConstructibleTensor k₀ l X).obj (K, L)).obj ⟶
      (nativeStructureDualizing k₀ l X J).obj :=
  ((ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X).weilSymmetry.braiding
      K.obj L.obj).hom ≫
    ((ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X).weilClosed.transpose
      L.obj K.obj (nativeStructureDualizing k₀ l X J).obj).symm
        (v ≫ ((ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X).homModels.nativeModel
          (nativeStructureDualizing k₀ l X J).obj).inv.app (op K.obj))

attribute [local irreducible] ProEtaleWeilSheaf.nativeDerivedClosedComparison

/-- The two native Hom transpositions and all six contravariant naturality squares.
The equivalences are fixed by native uncurrying and the supplied adjunction;
full-subcategory morphisms carry exactly the ambient derived morphisms.
Source: fix-lem-tensor-adjunction.proof.md, Step 1, and
fix-cor-verdier-exchange.proof.md, Steps 1--2
(blueprint: lem-sf-weil-dualizing-hom-transposition).

Proof plan (the node's five steps):
1. Reconcile coefficients by lem-sf-locally-finite-coefficient-ring-realization
and lem-sf-weil-verdier-module-constructibility-comparison. Their natural action
transport respects Frobenius, complexes, and bounded constructibility. The native
closed structure therefore uses exactly the stated coefficients and derivedHom.
2. Apply lem-sf-derived-weil-tensor-hom-adjunction for tensor constructibility.
The chosen J takes the coefficient unit into Weil complexes. For dual preservation,
apply lem-sf-weil-verdier-dual-preserves-weil-complexes to the library right adjoint;
transport along Adjunction.rightAdjointUniq from that adjoint to J. Internal Hom
preserves this target isomorphism, and the object property is isomorphism invariant.
Thus nativeStructureDualOfPreserves restricts the actual ambient Hom functor.
Fullness identifies each Hom set with its ambient derived Hom set.
3. Use lem-sf-weil-native-closed-forgetful: inverse native currying followed by
symmetry is nativeDualizingUncurry. The nativeModel comparison makes its internal
Hom exactly derivedHom. The two inverse identities are the closed adjunction's.
4. Set t to the inverse Hom equivalence of alpha at the coefficient unit. Its
formula is A(v) followed by the chosen counit, and its inverse is alpha itself.
5. For f : K' --> K and g : L' --> L, closed-adjunction naturality gives the c
square and alpha naturality gives the t square, with tensor map f tensor g.
Compose these equalities for the composite square. Apply each inverse bijection
to obtain the three inverse squares. Identity f or g gives separate naturality
in either argument. No biduality or equivalence with fixed derived pairs is used.
-/
theorem native_dualizing_hom_transposition
    (α : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ J) :
    (∀ K L : WeilComplex k₀ l X, objectProperty k₀ l X
      ((ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X).obj (K.obj, L.obj))) ∧
    ∃ hD : ∀ K : WeilComplex k₀ l X, objectProperty k₀ l X
      ((nativeStructureDual k₀ l X J).obj (op K.obj)),
    ∃ c : ∀ K L : WeilComplex k₀ l X,
      (L ⟶ (nativeStructureDualOfPreserves k₀ l X J hD).obj (op K)) ≃
        ((nativeConstructibleTensor k₀ l X).obj (K, L) ⟶ nativeStructureDualizing k₀ l X J),
    ∃ t : ∀ K L : WeilComplex k₀ l X,
      ((nativeConstructibleTensor k₀ l X).obj (K, L) ⟶ nativeStructureDualizing k₀ l X J) ≃
        ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
          ((nativeConstructibleTensor k₀ l X).obj (K, L)) ⟶
            WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))),
    (∀ (K L : WeilComplex k₀ l X)
      (v : L ⟶ (nativeStructureDualOfPreserves k₀ l X J hD).obj (op K)),
      (c K L v).hom = nativeDualizingUncurry k₀ l X J K L v.hom) ∧
    (∀ (K L : WeilComplex k₀ l X)
      (v : (nativeConstructibleTensor k₀ l X).obj (K, L) ⟶ nativeStructureDualizing k₀ l X J),
      t K L v = (α.homEquiv ((nativeConstructibleTensor k₀ l X).obj (K, L))
        (WeilSheaf.toComplex.obj
          (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))).symm v) ∧
    (∀ (K K' L L' : WeilComplex k₀ l X) (f : K' ⟶ K) (g : L' ⟶ L)
      (v : L ⟶ (nativeStructureDualOfPreserves k₀ l X J hD).obj (op K)),
      c K' L' (g ≫ v ≫ (nativeStructureDualOfPreserves k₀ l X J hD).map f.op) =
        (nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g) ≫ c K L v) ∧
    (∀ (K K' L L' : WeilComplex k₀ l X) (f : K' ⟶ K) (g : L' ⟶ L)
      (v : (nativeConstructibleTensor k₀ l X).obj (K, L) ⟶ nativeStructureDualizing k₀ l X J),
      t K' L' ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g) ≫ v) =
        (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map
          ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g)) ≫ t K L v) ∧
    (∀ (K K' L L' : WeilComplex k₀ l X) (f : K' ⟶ K) (g : L' ⟶ L)
      (v : L ⟶ (nativeStructureDualOfPreserves k₀ l X J hD).obj (op K)),
      ((c K' L').trans (t K' L'))
          (g ≫ v ≫ (nativeStructureDualOfPreserves k₀ l X J hD).map f.op) =
        (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map
          ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g)) ≫ ((c K L).trans (t K L)) v) ∧
    (∀ (K K' L L' : WeilComplex k₀ l X) (f : K' ⟶ K) (g : L' ⟶ L)
      (v : (nativeConstructibleTensor k₀ l X).obj (K, L) ⟶ nativeStructureDualizing k₀ l X J),
      (c K' L').symm ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g) ≫ v) =
        g ≫ (c K L).symm v ≫ (nativeStructureDualOfPreserves k₀ l X J hD).map f.op) ∧
    (∀ (K K' L L' : WeilComplex k₀ l X) (f : K' ⟶ K) (g : L' ⟶ L)
      (v : (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
        ((nativeConstructibleTensor k₀ l X).obj (K, L)) ⟶
          WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))),
      (t K' L').symm ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map
          ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g)) ≫ v) =
        (nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g) ≫ (t K L).symm v) ∧
    (∀ (K K' L L' : WeilComplex k₀ l X) (f : K' ⟶ K) (g : L' ⟶ L)
      (v : (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
        ((nativeConstructibleTensor k₀ l X).obj (K, L)) ⟶
          WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))),
      ((c K' L').trans (t K' L')).symm
          ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map
            ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g)) ≫ v) =
        g ≫ ((c K L).trans (t K L)).symm v ≫
          (nativeStructureDualOfPreserves k₀ l X J hD).map f.op) := by
  classical
  let C := ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X
  have : HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) := α.isLeftAdjoint
  let w : dualizingComplex k₀ l X ≅ nativeStructureDualizing k₀ l X J :=
    (Adjunction.rightAdjointUniq
      (derivedLowerShriekUpperShriekAdjunction (X ↘ Spec (CommRingCat.of k₀)))) α |>.app _
  have hD : ∀ K : WeilComplex k₀ l X, objectProperty k₀ l X
      ((nativeStructureDual k₀ l X J).obj (op K.obj)) := by
    intro K
    let e := ((C.homModels.nativeModel (dualizingComplex k₀ l X).obj).app (op K.obj)).symm ≪≫
      C.homModels.weilHom.mapIso
        (Iso.prod (Iso.refl (op K.obj)) ((objectProperty k₀ l X).ι.mapIso w)) ≪≫
      (C.homModels.nativeModel (nativeStructureDualizing k₀ l X J).obj).app (op K.obj)
    exact (objectProperty k₀ l X).prop_of_iso e
      (objectProperty_derivedHom_dualizingComplex k₀ l K)
  let c := fun K L : WeilComplex k₀ l X ↦
    ((objectProperty k₀ l X).fullyFaithfulι.homEquiv (X := L)
      (Y := (nativeStructureDualOfPreserves k₀ l X J hD).obj (op K))).trans
    ((((C.homModels.nativeModel (nativeStructureDualizing k₀ l X J).obj).app
      (op K.obj)).symm.homToEquiv).trans
    ((C.weilClosed.transpose L.obj K.obj (nativeStructureDualizing k₀ l X J).obj).symm.trans
    (((C.weilSymmetry.braiding K.obj L.obj).symm.homFromEquiv).trans
    ((objectProperty k₀ l X).fullyFaithfulι.homEquiv
      (X := (nativeConstructibleTensor k₀ l X).obj (K, L))
      (Y := nativeStructureDualizing k₀ l X J)).symm)))
  let t := fun K L : WeilComplex k₀ l X ↦
    (α.homEquiv ((nativeConstructibleTensor k₀ l X).obj (K, L))
      (WeilSheaf.toComplex.obj
        (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))).symm
  have hc : ∀ (K L : WeilComplex k₀ l X)
      (v : L ⟶ (nativeStructureDualOfPreserves k₀ l X J hD).obj (op K)),
      (c K L v).hom = nativeDualizingUncurry k₀ l X J K L v.hom := by
    intros
    rfl
  have cn : ∀ (K K' L L' : WeilComplex k₀ l X) (f : K' ⟶ K) (g : L' ⟶ L)
      (v : L ⟶ (nativeStructureDualOfPreserves k₀ l X J hD).obj (op K)),
      c K' L' (g ≫ v ≫ (nativeStructureDualOfPreserves k₀ l X J hD).map f.op) =
        (nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g) ≫ c K L v := by
    intro K K' L L' f g v
    apply ObjectProperty.hom_ext
    rw [hc]
    change nativeDualizingUncurry k₀ l X J K' L'
      (g.hom ≫ v.hom ≫ (nativeStructureDual k₀ l X J).map f.hom.op) =
        (ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X).map (Prod.mkHom f.hom g.hom) ≫
          (c K L v).hom
    rw [hc]
    let m := C.homModels.nativeModel (nativeStructureDualizing k₀ l X J).obj
    have hm : (nativeStructureDual k₀ l X J).map f.hom.op ≫ m.inv.app (op K'.obj) =
        m.inv.app (op K.obj) ≫ C.homModels.weilHom.map
          (Prod.mkHom f.hom.op (𝟙 (nativeStructureDualizing k₀ l X J).obj)) :=
      m.inv.naturality f.hom.op
    change (C.weilSymmetry.braiding K'.obj L'.obj).hom ≫
      (C.weilClosed.transpose L'.obj K'.obj (nativeStructureDualizing k₀ l X J).obj).symm
        ((g.hom ≫ v.hom ≫ (nativeStructureDual k₀ l X J).map f.hom.op) ≫
          m.inv.app (op K'.obj)) =
      C.weilClosed.tensor.map (Prod.mkHom f.hom g.hom) ≫
        (C.weilSymmetry.braiding K.obj L.obj).hom ≫
          (C.weilClosed.transpose L.obj K.obj (nativeStructureDualizing k₀ l X J).obj).symm
            (v.hom ≫ m.inv.app (op K.obj))
    simp only [Category.assoc]
    rw [hm]
    have hu := closed_uncurry_naturality C.weilClosed f.hom g.hom
      (v.hom ≫ m.inv.app (op K.obj))
    simp only [Category.assoc] at hu
    let := C.weilClosed.monoidal
    let := C.weilSymmetry
    have hb := BraidedCategory.braiding_naturality f.hom g.hom
    let z := (C.weilClosed.transpose L.obj K.obj
      (nativeStructureDualizing k₀ l X J).obj).symm (v.hom ≫ m.inv.app (op K.obj))
    calc
      _ = (C.weilSymmetry.braiding K'.obj L'.obj).hom ≫
          (C.weilClosed.tensor.map (Prod.mkHom g.hom f.hom) ≫ z) :=
        congrArg (fun q ↦ (C.weilSymmetry.braiding K'.obj L'.obj).hom ≫ q) hu
      _ = ((C.weilSymmetry.braiding K'.obj L'.obj).hom ≫
          C.weilClosed.tensor.map (Prod.mkHom g.hom f.hom)) ≫ z :=
        (Category.assoc _ _ _).symm
      _ = _ := (congrArg (fun q ↦ q ≫ z) hb).symm.trans (Category.assoc _ _ _)
  have tn : ∀ (K K' L L' : WeilComplex k₀ l X) (f : K' ⟶ K) (g : L' ⟶ L)
      (v : (nativeConstructibleTensor k₀ l X).obj (K, L) ⟶
        nativeStructureDualizing k₀ l X J),
      t K' L' ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g) ≫ v) =
        (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map
          ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g)) ≫ t K L v := by
    intro K K' L L' f g v
    exact α.homEquiv_naturality_left_symm _ _
  refine ⟨?_, hD, c, t, hc, ?_, cn, tn, ?_, ?_, ?_, ?_⟩
  · intro K L
    exact nativeDerivedTensor_mem_weilComplex k₀ l X L K
  · intros
    rfl
  · intro K K' L L' f g v
    change t K' L' (c K' L' _) = _
    rw [cn, tn]
    rfl
  · intro K K' L L' f g v
    apply (c K' L').injective
    simp only [Equiv.apply_symm_apply, cn]
  · intro K K' L L' f g v
    exact α.homEquiv_naturality_left _ _
  · intro K K' L L' f g v
    change (c K' L').symm ((t K' L').symm _) =
      g ≫ (c K L).symm ((t K L).symm v) ≫
        (nativeStructureDualOfPreserves k₀ l X J hD).map f.op
    have ht := congrArg (t K' L').symm (tn K K' L L' f g ((t K L).symm v))
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at ht
    have hi : (c K' L').symm
        ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom f g) ≫ (t K L).symm v) =
        g ≫ (c K L).symm ((t K L).symm v) ≫
          (nativeStructureDualOfPreserves k₀ l X J hD).map f.op := by
      apply (c K' L').injective
      simp only [Equiv.apply_symm_apply, cn]
    exact (congrArg (c K' L').symm ht.symm).trans hi

end AlgebraicGeometry.WeilComplex

attribute [instance] AlgebraicGeometry.specOverSpec
