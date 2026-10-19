# cohomologyLinearEquivOfGeometricFiberIso and its Frobenius compatibility

## Reason

The source library already contains the exact theorem and a canonical construction of
its equivalence, with identical public names and signatures. Retire the duplicate
Sheaf modules and point their DAG attachments to these upstream implementations,
following tools/README.md's upstream-overlap policy and the brief's withdrawal rule.
PoincareDuality already imports the upstream module in the current shared tree.
No external consumer imports either duplicate. No consumer source changes are needed.

The old equivalence composes the derived forgetful comparison, the exact
sections/homology comparison and the right-derived composition comparison. The upstream
construction uses the canonical comparison for the combined forgetful/sections functor,
characterized by the right-derived unit equation, and the same constant-unit transport.
This consolidates the implementation of the same canonical construction. It does not
claim definitional equality of the old/new terms. The independent definition review
should check this canonical-comparison identification. No arbitrary witness is chosen.
No target statement uses the replaced equivalence in its signature. The theorem retains
all hypotheses and degrees, including r=0 and unrelated finite base fields.

## Old

`lean/Sheaf/WeilSheaf/CohomologyGeometricConjugacy.lean`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.WeilSheaf.CohomologyGeometricEquivalence
import Sheaf.Paper.CommonStageCompactWeilCohomology
import Sheaf.Paper.ConstantWeilStructure
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.SixFunctors.FrobeniusCohomologyTransport
import Sheaf.Paper.GlobalGeometricFrobenius

/-!
# Cohomology and conjugate geometric Frobenius automorphisms

Source: the transport-of-structure part of the base-change clause of
`sec-poincare-duality/sk-thm-poincare-duality/thm-weil-poincare-duality.md`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

/-- An isomorphism of geometric fibers conjugating one geometric Frobenius to a power
of the other makes the explicit cohomology equivalence intertwine those operators.

Source: literature/blueprint/master/blueprint/sec-poincare-duality/
sk-thm-poincare-duality/thm-weil-poincare-duality.md, base-change clause,
with the transport convention of `def-weil-global-geometric-frobenius`.
(blueprint: lem-pod-cohomology-geometric-conjugacy)

Proof: Pushforward along e is an exact equivalence of the categories of modules over the
continuous coefficient sheaves. Its canonical isomorphism on constant sheaves identifies
the constant object on Ybar with that on Xbar. The canonical isomorphism on global sections
identifies their derived global-section complexes, since an exact equivalence preserves
injective resolutions. The equation he identifies the natural transport by the Frobenius
of Ybar with transport by the r-th power on Xbar: apply composition of pushforwards to
he, and use the composition law for the constant-sheaf and global-section isomorphisms.
The former is `adicConstantSheafToLowerStar_comp`, after forgetting module linearity;
the latter is `globalSectionsLowerStarIso_comp`, together with naturality.
The definition of Weil cohomology as global sections of the homology sheaf of the derived
pushforward to the geometric point agrees with homology of derived global sections:
global sections at an algebraically closed point are exact.
The linear equivalence is the construction
`cohomologyLinearEquivOfGeometricFiberIso`. Naturality of homology carries the transport
identity through its composition isomorphisms to the asserted identity. More explicitly,
the comparison maps are characterized by their equations with the units of right derived
functors. To prove their compatibility, apply `Functor.rightDerived_ext` and these unit
equations, reducing to the preceding identity of maps on complexes. The
r-fold composite of the cohomological Frobenius is its r-th power as a linear endomorphism.
No choice of an embedding between the two base fields is needed for this transport step. -/
theorem cohomologyLinearEquivOfGeometricFiberIso_map_frobenius
    (k k' : Type u) [Field k] [Finite k] [Field k'] [Finite k']
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] [Fact (ringChar k' ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k'))] [QuasiSeparated (Y ↘ Spec (.of k'))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k'))]
    (r : ℕ) (e : (Y ↘ Spec (.of k')).geometricFiber ≅ (X ↘ Spec (.of k)).geometricFiber)
    (he : (Y ↘ Spec (.of k')).geometricGaloisFrobenius.hom ≫ e.hom =
      e.hom ≫ ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ r).hom) (i : ℤ)
    (x : ((adicConstant k' l Y).cohomology i).carrier) :
    cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i
        (((adicConstant k' l Y).cohomology i).frobenius x) =
      (((adicConstant k l X).cohomology i).frobeniusEnd ^ r)
        (cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i x) := by
  sorry

end AlgebraicGeometry.WeilSheaf
```

`lean/Sheaf/WeilSheaf/CohomologyGeometricEquivalence.lean`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import WeilConjectures.WeilSheaf.CohomologyExact

/-!
# The equivalence on constant-sheaf cohomology induced by a geometric isomorphism

Source: the isomorphism-invariance part of the base-change clause of
`sec-poincare-duality/sk-thm-poincare-duality/thm-weil-poincare-duality.md`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

/-- The linear equivalence induced by an isomorphism of geometric fibers.

Source: literature/blueprint/master/blueprint/sec-poincare-duality/
sk-thm-poincare-duality/thm-weil-poincare-duality.md, base-change clause.
(blueprint: def-pod-cohomology-geometric-equivalence)

Construction: identify Weil cohomology, after forgetting Frobenius, with homology of
derived global sections of the constant adic sheaf. The forgetful functor from Weil
sheaves preserves injective resolutions, and global sections at the geometric point
are exact, giving the first identification. Pushforward along e is an exact equivalence;
its composition with global sections is global sections on the source, and it carries
the constant adic sheaf to the constant adic sheaf. Derive this identity, apply homology,
and compose with the two identifications. All comparison isomorphisms are constructed
from the library's composition and exact-functor isomorphisms. -/
noncomputable def cohomologyLinearEquivOfGeometricFiberIso
    (k k' : Type u) [Field k] [Finite k] [Field k'] [Finite k']
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] [Fact (ringChar k' ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k'))] [QuasiSeparated (Y ↘ Spec (.of k'))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k'))]
    (e : (Y ↘ Spec (.of k')).geometricFiber ≅ (X ↘ Spec (.of k)).geometricFiber) (i : ℤ) :
    ((WeilSheaf.adicConstant k' l Y).cohomology i).carrier ≃ₗ[PadicAlgCl l]
      ((WeilSheaf.adicConstant k l X).cohomology i).carrier := by
  let adicΓ (l : ℕ) [Fact l.Prime] (Z : Scheme.{u}) :
      ProEtale.AdicSheaf l Z ⥤ WeilCoefficients.{u} l :=
    ProEtale.AdicSheaf.forget Z ⋙ Sheaf.Γ _ _
  let adicLowerStarΓIso (l : ℕ) [Fact l.Prime]
      {Z W : Scheme.{u}} (g : Z ⟶ W) :
      ProEtale.adicLowerStar l g ⋙ adicΓ l W ≅ adicΓ l Z :=
    Functor.isoWhiskerLeft (ProEtale.AdicSheaf.forget Z)
      (ProEtale.globalSectionsLowerStarIso (WeilCoefficients.{u} l) g)
  let cohomologyCarrierIso (k : Type u) [Field k] [Finite k]
      (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
      (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))] (i : ℤ) :
      ((adicΓ l (X ↘ Spec (.of k)).geometricFiber).rightDerivedFunctor ⋙
        _root_.DerivedCategory.homologyFunctor _ i).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (ProEtale.AdicSheaf.unit l (X ↘ Spec (.of k)).geometricFiber)) ≅
        (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
          ((WeilComplex.homologySheaf i).obj ((WeilComplex.derivedLowerStar
            (X ↘ Spec (.of k))).obj
              (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k l X)))).obj.carrier.X := by
    let a := X ↘ Spec (.of k)
    let f := Scheme.Hom.geometricFiberMap a (comp_over a (Spec (.of k)))
    let G := adicΓ l (Spec (.of k) ↘ Spec (.of k)).geometricFiber
    let F := adicΓ l a.geometricFiber
    let W := ProEtaleWeilSheaf.lowerStar k l a
    let M := (_root_.DerivedCategory.singleFunctor _ 0).obj (WeilSheaf.adicConstant k l X).obj
    let K := W.rightDerivedFunctor.obj M
    have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
      (ProEtale.AdicSheaf l a.geometricFiber) ℤ
    have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
      (ProEtale.AdicSheaf l a.geometricFiber) ℤ
    let e : (IsoAlgebra.forget _).mapDerivedCategory.obj K ≅
        (ProEtale.adicLowerStar l f).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (ProEtale.AdicSheaf.unit l a.geometricFiber)) :=
      (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _).app _ ≪≫
        Functor.mapIso _ (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app
          (WeilSheaf.adicConstant k l X).obj)
    have : G.Additive := by dsimp [G, adicΓ]; infer_instance
    have : PreservesFiniteLimits G := by dsimp [G, adicΓ]; infer_instance
    have : G.PreservesEpimorphisms := by dsimp [G, adicΓ]; infer_instance
    have : G.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels G
    have : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G
    let e₀ := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (ProEtale.adicLowerStar l f) G).symm ≪≫
        Functor.rightDerivedFunctorNatIso (adicLowerStarΓIso l f)
    let e₁ := ((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso i).app K
    let e₂ := (G.mapDerivedCategoryHomologyFunctorIso i).app
      ((IsoAlgebra.forget _).mapDerivedCategory.obj K)
    exact ((G.mapIso e₁) ≪≫ e₂ ≪≫
      (_root_.DerivedCategory.homologyFunctor _ i).mapIso
        (G.mapDerivedCategory.mapIso e ≪≫ e₀.app _)).symm
  let FX := adicΓ l (X ↘ Spec (.of k)).geometricFiber
  let L := ProEtale.adicLowerStar l e.hom
  let U := ProEtale.AdicSheaf.unit l (Y ↘ Spec (.of k')).geometricFiber
  let M := (_root_.DerivedCategory.singleFunctor _ 0).obj U
  let eΓ := (Functor.rightDerivedFunctorCompIso' L FX (adicLowerStarΓIso l e.hom)).app M
  let eU := (L.singleFunctorCompRightDerivedFunctorIso).app U ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso (ProEtale.adicLowerStarUnitIso l e)
  let eD := eΓ.symm ≪≫ FX.rightDerivedFunctor.mapIso eU
  exact WeilCoefficients.linearEquivOfIso
    ((cohomologyCarrierIso k' l Y i).symm ≪≫
      (_root_.DerivedCategory.homologyFunctor _ i).mapIso eD ≪≫
        cohomologyCarrierIso k l X i)

end AlgebraicGeometry.WeilSheaf
```

## New

Both Sheaf modules are withdrawn through deleted.txt and land as empty modules.
Their existing nodes attach to the following source implementations, which are reused
unchanged (including their existing helper lemmas and proofs):

`lean/WeilConjectures/WeilSheaf/CohomologyGeometricConjugacy.lean`:

```lean
/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence

/-!
# Cohomology and conjugate geometric Frobenius automorphisms

An isomorphism `e : Ȳ ≅ X̄` of geometric fibers which conjugates the geometric Frobenius of `Ȳ` to
the `r`-th power of that of `X̄` makes the induced equivalence
`Hⁱ(Y ⊗ k̄', ℚ̄_ℓ) ≃ Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` intertwine the Frobenius of the source with the `r`-th power
of the Frobenius of the target
(`AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso_map_frobenius`). This is
the transport-of-structure part of the base-change clause of `thm-weil-poincare-duality`.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry.WeilSheaf

variable (k : Type u) [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- Under `Hⁱ(X ⊗ k̄, ℚ̄_ℓ) ≅ Hⁱ RΓ(X̄, ℚ̄_ℓ)`, the `n`-th power of the Frobenius is induced by the
transport of `RΓ(X̄, ℚ̄_ℓ)` along the inverse of the `n`-th power of the geometric Frobenius. -/
lemma cohomologyCarrierIso_inv_derivedGlobalSectionsUnitIso_pow (i : ℤ) (n : ℕ)
    (z : (DerivedCategory.homologyFunctor (WeilCoefficients.{u} l) i).obj
      (ProEtale.derivedGlobalSectionsUnit l (X ↘ Spec (.of k)).geometricFiber)) :
    (cohomologyCarrierIso k l X i).inv.hom (((DerivedCategory.homologyFunctor _ i).map
        (ProEtale.derivedGlobalSectionsUnitIso l
          ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).symm).hom).hom z) =
      (((adicConstant k l X).cohomology i).frobeniusEnd ^ n)
        ((cohomologyCarrierIso k l X i).inv.hom z) := by
  have hF : (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
        (X ↘ Spec (.of k)).geometricGaloisFrobenius.symm).hom ≫
        (cohomologyCarrierIso k l X i).inv =
      (cohomologyCarrierIso k l X i).inv ≫
        (IsoAlgebra.forgetCompIsoOfIso (ProEtale.adicLowerStarCompGlobalSectionsIso l
          (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.inv)).hom.app
          ((DerivedCategory.homologyFunctor _ i).obj (derivedLowerStarAdicConstant k l X)) := by
    rw [Iso.comp_inv_eq, Category.assoc, cohomologyCarrierIso_hom_frobenius,
      Iso.inv_hom_id_assoc]
  have hF' : ∀ w, (cohomologyCarrierIso k l X i).inv.hom
      (((DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
        (X ↘ Spec (.of k)).geometricGaloisFrobenius.symm).hom).hom w) =
      ((adicConstant k l X).cohomology i).frobenius
        ((cohomologyCarrierIso k l X i).inv.hom w) := by
    intro w
    rw [cohomology_adicConstant_frobenius]
    exact congrArg (fun f ↦ f.hom w) hF
  induction n generalizing z with
  | zero =>
    rw [pow_zero, pow_zero,
      show (1 : Aut (X ↘ Spec (.of k)).geometricFiber) = Iso.refl _ from rfl,
      Iso.refl_symm, ProEtale.derivedGlobalSectionsUnitIso_refl, Iso.refl_hom,
      CategoryTheory.Functor.map_id]
    rfl
  | succ n ih =>
    have hσ : ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ (n + 1)).symm =
        ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).symm ≪≫
          (X ↘ Spec (.of k)).geometricGaloisFrobenius.symm := by
      rw [pow_succ, Aut.Aut_mul_def, Iso.trans_symm]
    have hD : ProEtale.derivedGlobalSectionsUnitIso l
        ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ (n + 1)).symm =
        ProEtale.derivedGlobalSectionsUnitIso l
          ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).symm ≪≫
        ProEtale.derivedGlobalSectionsUnitIso l
          (X ↘ Spec (.of k)).geometricGaloisFrobenius.symm := by
      rw [hσ, ProEtale.derivedGlobalSectionsUnitIso_trans]
    have hmor : (DerivedCategory.homologyFunctor (WeilCoefficients.{u} l) i).map
        (ProEtale.derivedGlobalSectionsUnitIso l
          ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ (n + 1)).symm).hom =
        (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
          ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).symm).hom ≫
        (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
          (X ↘ Spec (.of k)).geometricGaloisFrobenius.symm).hom := by
      rw [hD, Iso.trans_hom, Functor.map_comp]
    calc _ = (cohomologyCarrierIso k l X i).inv.hom
          (((DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
            (X ↘ Spec (.of k)).geometricGaloisFrobenius.symm).hom).hom
          (((DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
            ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).symm).hom).hom z)) :=
          congrArg (fun f ↦ (cohomologyCarrierIso k l X i).inv.hom (f.hom z)) hmor
      _ = ((adicConstant k l X).cohomology i).frobenius
          ((cohomologyCarrierIso k l X i).inv.hom
            (((DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
              ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).symm).hom).hom z)) := hF' _
      _ = ((adicConstant k l X).cohomology i).frobenius
          ((((adicConstant k l X).cohomology i).frobeniusEnd ^ n)
            ((cohomologyCarrierIso k l X i).inv.hom z)) :=
          congrArg (fun w : ((adicConstant k l X).cohomology i).carrier ↦
            ((adicConstant k l X).cohomology i).frobenius w) (ih z)
      _ = (((adicConstant k l X).cohomology i).frobeniusEnd *
            ((adicConstant k l X).cohomology i).frobeniusEnd ^ n)
            ((cohomologyCarrierIso k l X i).inv.hom z) :=
          rfl
      _ = _ := congrArg
          (fun f : Module.End (PadicAlgCl l) ((adicConstant k l X).cohomology i).carrier ↦
            f ((cohomologyCarrierIso k l X i).inv.hom z))
            (pow_succ' ((adicConstant k l X).cohomology i).frobeniusEnd n).symm

/-- An isomorphism of geometric fibers conjugating one geometric Frobenius to a power of the other
makes the cohomology equivalence
`AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso` intertwine those
operators. This is an ingredient of the base-change clause of `thm-weil-poincare-duality`, with
the transport convention of `def-weil-global-geometric-frobenius`.

Proof: under the identification of the carriers with `Hⁱ RΓ(-, ℚ̄_ℓ)`, the Frobenius is the
transport along the inverse of the geometric Frobenius
(`AlgebraicGeometry.WeilSheaf.cohomologyCarrierIso_hom_frobenius`), and the equivalence is the
transport along `e`. Transport is compatible with composition
(`AlgebraicGeometry.ProEtale.derivedGlobalSectionsUnitIso_trans`), and `he` says
`Fr_Y⁻¹ ≫ e = e ≫ Fr_X⁻ʳ`. -/
theorem cohomologyLinearEquivOfGeometricFiberIso_map_frobenius
    (k k' : Type u) [Field k] [Finite k] [Field k'] [Finite k']
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] [Fact (ringChar k' ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k'))] [QuasiSeparated (Y ↘ Spec (.of k'))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k'))]
    (r : ℕ) (e : (Y ↘ Spec (.of k')).geometricFiber ≅ (X ↘ Spec (.of k)).geometricFiber)
    (he : (Y ↘ Spec (.of k')).geometricGaloisFrobenius.hom ≫ e.hom =
      e.hom ≫ ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ r).hom) (i : ℤ)
    (x : ((adicConstant k' l Y).cohomology i).carrier) :
    cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i
        (((adicConstant k' l Y).cohomology i).frobenius x) =
      (((adicConstant k l X).cohomology i).frobeniusEnd ^ r)
        (cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i x) := by
  have he' : (Y ↘ Spec (.of k')).geometricGaloisFrobenius.symm ≪≫ e =
      e ≪≫ ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ r).symm := by
    refine Iso.ext ?_
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [Iso.inv_comp_eq, ← Category.assoc]
    erw [he]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hD : (DerivedCategory.homologyFunctor (WeilCoefficients.{u} l) i).map
        (ProEtale.derivedGlobalSectionsUnitIso l
          (Y ↘ Spec (.of k')).geometricGaloisFrobenius.symm).hom ≫
        (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l e).hom =
      (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l e).hom ≫
        (DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
          ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ r).symm).hom := by
    have := congrArg (fun φ ↦ (DerivedCategory.homologyFunctor (WeilCoefficients.{u} l) i).map
      (ProEtale.derivedGlobalSectionsUnitIso l φ).hom) he'
    simpa only [ProEtale.derivedGlobalSectionsUnitIso_trans, Iso.trans_hom,
      Functor.map_comp] using this
  have hY : ∀ y, (cohomologyCarrierIso k' l Y i).hom.hom
      (((adicConstant k' l Y).cohomology i).frobenius y) =
      ((DerivedCategory.homologyFunctor _ i).map (ProEtale.derivedGlobalSectionsUnitIso l
        (Y ↘ Spec (.of k')).geometricGaloisFrobenius.symm).hom).hom
        ((cohomologyCarrierIso k' l Y i).hom.hom y) := fun y ↦ by
    rw [cohomology_adicConstant_frobenius]
    exact congrArg (fun f ↦ f.hom y) (cohomologyCarrierIso_hom_frobenius k' l Y i)
  have hT : ∀ y, cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i y =
      (cohomologyCarrierIso k l X i).inv.hom
        (((DerivedCategory.homologyFunctor _ i).map
          (ProEtale.derivedGlobalSectionsUnitIso l e).hom).hom
            ((cohomologyCarrierIso k' l Y i).hom.hom y)) := fun _ ↦ rfl
  rw [hT, hT, hY, ← cohomologyCarrierIso_inv_derivedGlobalSectionsUnitIso_pow]
  exact congrArg (fun f ↦ (cohomologyCarrierIso k l X i).inv.hom
    (f.hom ((cohomologyCarrierIso k' l Y i).hom.hom x))) hD

end AlgebraicGeometry.WeilSheaf
```

`lean/WeilConjectures/WeilSheaf/CohomologyGeometricEquivalence.lean`:

```lean
/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraFrobenius
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedGlobalSectionsTransport
public import WeilConjectures.WeilSheaf.CohomologyExact

/-!
# The equivalence on constant-sheaf cohomology induced by a geometric isomorphism

The cohomology `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` of the constant Weil sheaf is, after forgetting its Frobenius,
the cohomology of the derived global sections `RΓ(X̄, ℚ̄_ℓ)` of the constant `ℓ`-adic sheaf on the
geometric fiber (`AlgebraicGeometry.WeilSheaf.cohomologyCarrierIso`): forgetting the Weil
structure commutes with right derivation, and global sections over `Spec k̄` are exact. Under this
identification the Frobenius is the transport of `RΓ(X̄, ℚ̄_ℓ)` along the inverse of the geometric
Frobenius of `X̄` (`AlgebraicGeometry.WeilSheaf.cohomologyCarrierIso_hom_frobenius`).

An isomorphism `e : Ȳ ≅ X̄` of geometric fibers, over possibly different finite fields, therefore
induces a linear equivalence `Hⁱ(Y ⊗ k̄', ℚ̄_ℓ) ≃ Hⁱ(X ⊗ k̄, ℚ̄_ℓ)`
(`AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso`), the transport of
`RΓ(-, ℚ̄_ℓ)` along `e`. This is the isomorphism-invariance part of the base-change clause of
`thm-weil-poincare-duality`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

section

variable (k : Type u) [Field k] [Finite k] (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  [X.Over (Spec (.of k))]

instance : (IsoAlgebra.forget (frobeniusPullback k l X)).PreservesKInjectiveComplexes := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (.of k)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (.of k)).geometricFiber) ℤ
  infer_instance

instance : PreservesFiniteLimits
    (ProEtale.adicGlobalSections l (Spec (.of k) ↘ Spec (.of k)).geometricFiber) := by
  unfold ProEtale.adicGlobalSections
  infer_instance

instance : PreservesFiniteColimits
    (ProEtale.adicGlobalSections l (Spec (.of k) ↘ Spec (.of k)).geometricFiber) := by
  have : (ProEtale.adicGlobalSections l
      (Spec (.of k) ↘ Spec (.of k)).geometricFiber).PreservesEpimorphisms := by
    unfold ProEtale.adicGlobalSections
    infer_instance
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (ProEtale.adicGlobalSections l (Spec (.of k) ↘ Spec (.of k)).geometricFiber)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end

variable (k : Type u) [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- The derived pushforward `Ra_* ℚ̄_ℓ` of the constant Weil sheaf along the structure morphism,
in the derived category of pro-étale Weil sheaves on `Spec k₀`. -/
noncomputable abbrev derivedLowerStarAdicConstant :
    DerivedCategory (ProEtaleWeilSheaf k l (Spec (.of k))) :=
  (ProEtaleWeilSheaf.lowerStar k l (X ↘ Spec (.of k))).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor _ 0).obj (ProEtaleWeilSheaf.adicConstant k l X))

/-- **The carrier of constant-sheaf cohomology.** Forgetting its Frobenius, the cohomology
`Hⁱ(X ⊗ k̄, ℚ̄_ℓ) = Γ(Spec k̄, 𝓗ⁱ(Ra_* ℚ̄_ℓ))` is `Hⁱ RΓ(X̄, ℚ̄_ℓ)`: global sections over `Spec k̄`
are exact, and `Γ(Spec k̄, -) ∘ Ra_* ≅ RΓ(X̄, -)` after forgetting the Weil structures. -/
noncomputable def cohomologyCarrierIso (i : ℤ) :
    (IsoAlgebra.forget _ ⋙
        ProEtale.adicGlobalSections l (Spec (.of k) ↘ Spec (.of k)).geometricFiber).obj
        ((DerivedCategory.homologyFunctor _ i).obj (derivedLowerStarAdicConstant k l X)) ≅
      (DerivedCategory.homologyFunctor _ i).obj
        (ProEtale.derivedGlobalSectionsUnit l (X ↘ Spec (.of k)).geometricFiber) :=
  ((IsoAlgebra.forget _ ⋙ ProEtale.adicGlobalSections l
      (Spec (.of k) ↘ Spec (.of k)).geometricFiber).mapDerivedCategoryHomologyFunctorIso i).app _ ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      ((IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetCompIso
          (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l (X ↘ Spec (.of k))
            (comp_over (X ↘ Spec (.of k)) (Spec (.of k))))
          (ProEtale.adicLowerStarCompGlobalSectionsIso l
            (Scheme.Hom.geometricFiberMap (X ↘ Spec (.of k))
              (comp_over (X ↘ Spec (.of k)) (Spec (.of k)))))).app _ ≪≫
        (ProEtale.adicGlobalSections l (X ↘ Spec (.of k)).geometricFiber).rightDerivedFunctor.mapIso
          (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app _))

/-- The Frobenius of `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` is the automorphism of global sections over `Spec k̄`
induced by the Weil structure of the cohomology sheaf `𝓗ⁱ(Ra_* ℚ̄_ℓ)`. -/
lemma cohomology_adicConstant_frobenius (i : ℤ) :
    ((adicConstant k l X).cohomology i).frobenius = WeilCoefficients.linearEquivOfIso
      ((IsoAlgebra.forgetCompIsoOfIso (ProEtale.adicLowerStarCompGlobalSectionsIso l
        (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.inv)).app
          ((DerivedCategory.homologyFunctor _ i).obj (derivedLowerStarAdicConstant k l X))) :=
  rfl

omit [Fact (ringChar k ≠ l)] [QuasiCompact (X ↘ Spec (.of k))]
  [QuasiSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
/-- **The Frobenius of constant-sheaf cohomology is the transport along the geometric Frobenius.**
Under `Hⁱ(X ⊗ k̄, ℚ̄_ℓ) ≅ Hⁱ RΓ(X̄, ℚ̄_ℓ)`, the Frobenius is induced by the transport of
`RΓ(X̄, ℚ̄_ℓ)` along the inverse of the geometric Frobenius of `X̄`. -/
lemma cohomologyCarrierIso_hom_frobenius (i : ℤ) :
    (IsoAlgebra.forgetCompIsoOfIso (ProEtale.adicLowerStarCompGlobalSectionsIso l
        (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.inv)).hom.app
          ((DerivedCategory.homologyFunctor _ i).obj (derivedLowerStarAdicConstant k l X)) ≫
        (cohomologyCarrierIso k l X i).hom =
      (cohomologyCarrierIso k l X i).hom ≫ (DerivedCategory.homologyFunctor _ i).map
        (ProEtale.derivedGlobalSectionsUnitIso l
          (X ↘ Spec (.of k)).geometricGaloisFrobenius.symm).hom := by
  have hG := Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_naturality
    (IsoAlgebra.forgetCompIsoOfIso (ProEtale.adicLowerStarCompGlobalSectionsIso l
      (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.inv)) i
    (derivedLowerStarAdicConstant k l X)
  have hB := IsoAlgebra.mapDerivedCategoryNatIso_forgetCompIsoOfIso_hom_app_rightDerivedFunctor_obj
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l (X ↘ Spec (.of k))
      (comp_over (X ↘ Spec (.of k)) (Spec (.of k))))
    (ProEtale.adicLowerStarCompGlobalSectionsIso l
      (Scheme.Hom.geometricFiberMap (X ↘ Spec (.of k))
        (comp_over (X ↘ Spec (.of k)) (Spec (.of k)))))
    (ProEtale.adicLowerStarCompGlobalSectionsIso l
      (Spec (.of k) ↘ Spec (.of k)).geometricGaloisFrobenius.inv)
    (ProEtale.adicLowerStarCompGlobalSectionsIso l
      (X ↘ Spec (.of k)).geometricGaloisFrobenius.inv)
    (fun M ↦ ProEtale.adicLowerStarCompGlobalSectionsIso_inv_app_comm l _ _ _ _ _ M)
    ((DerivedCategory.singleFunctor _ 0).obj (ProEtaleWeilSheaf.adicConstant k l X))
  simp only [cohomologyCarrierIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [reassoc_of% hG]
  simp only [Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  simp only [← Functor.map_comp]
  refine congrArg (DerivedCategory.homologyFunctor _ i).map ?_
  erw [reassoc_of% hB]
  simp only [Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  have h₁ := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor
    (IsoAlgebra.forget (frobeniusPullback k l X)) (frobeniusPullback k l X)
    (ProEtaleWeilSheaf.adicConstant k l X)
  have h₂ := Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor
    (IsoAlgebra.strNatIso (frobeniusPullback k l X)) (ProEtaleWeilSheaf.adicConstant k l X)
  simp only [ProEtale.derivedGlobalSectionsUnitIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  have hn := (Functor.rightDerivedFunctorIsoMapDerivedCategoryComp
    (ProEtale.adicLowerStarCompGlobalSectionsIso l
      (X ↘ Spec (.of k)).geometricGaloisFrobenius.inv)).hom.naturality
    (((IsoAlgebra.forget (frobeniusPullback k l X)).mapDerivedCategorySingleFunctor 0).hom.app
      (ProEtaleWeilSheaf.adicConstant k l X))
  erw [reassoc_of% hn]
  refine congrArg (_ ≫ ·) ?_
  simp only [← Functor.map_comp]
  refine congrArg _ ?_
  rw [Category.assoc, h₂, ← h₁]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

/-- The linear equivalence induced by an isomorphism of geometric fibers: the transport of
`RΓ(Ȳ, ℚ̄_ℓ) ≅ RΓ(X̄, ℚ̄_ℓ)` along `e`, through the identifications
`AlgebraicGeometry.WeilSheaf.cohomologyCarrierIso` of the carriers of the cohomology of the
constant Weil sheaves. This is an ingredient of the base-change clause of
`thm-weil-poincare-duality`. -/
noncomputable def cohomologyLinearEquivOfGeometricFiberIso
    (k k' : Type u) [Field k] [Finite k] [Field k'] [Finite k']
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] [Fact (ringChar k' ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k'))] [QuasiSeparated (Y ↘ Spec (.of k'))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k'))]
    (e : (Y ↘ Spec (.of k')).geometricFiber ≅ (X ↘ Spec (.of k)).geometricFiber) (i : ℤ) :
    ((WeilSheaf.adicConstant k' l Y).cohomology i).carrier ≃ₗ[PadicAlgCl l]
      ((WeilSheaf.adicConstant k l X).cohomology i).carrier :=
  WeilCoefficients.linearEquivOfIso
    (cohomologyCarrierIso k' l Y i ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (ProEtale.derivedGlobalSectionsUnitIso l e) ≪≫
        (cohomologyCarrierIso k l X i).symm)

end AlgebraicGeometry.WeilSheaf
```

## Users

Current tools/downstream.py results and repository-wide import search:
conjugacy has zero downstream modules; equivalence has only the conjugacy duplicate.
The --uses searches find only these same duplicate modules. PoincareDuality already
imports WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy.

| module | group holding it | effect |
|---|---|---|
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | H1 | Withdraw unused duplicate; reattach node. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Withdraw duplicate with its sole importer; reattach node. |

## Status

landed 20261019T231208-L-560105 2026-10-19 (merge of deliver/H1/Sheaf.WeilSheaf.CohomologyGeometricConjugacy)
