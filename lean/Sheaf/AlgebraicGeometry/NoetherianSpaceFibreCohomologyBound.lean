/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Coherent higher-image vanishing above geometric fibre dimension

Source: Stacks Project, Cohomology of Spaces, Tag 0A4T,
lemma-higher-direct-images-zero-above-dimension-fibre, applied at every geometric point
(blueprint: lem-sfb-noetherian-space-fibre-cohomology-bound).

The scheme target is its representable algebraic space over itself. Fibre dimension is
bounded on all affine etale scheme charts. Coherence is quasi-coherence together with
finite generation on one jointly surjective Noetherian affine etale cover. The conclusion
uses the canonical derived module direct image on the equivalent small affine model.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper algebraic space over a locally Noetherian scheme has no coherent higher
module direct images above the common geometric fibre-dimension bound. There is no
flatness assumption on the morphism or the module.
Source: Stacks Project, Cohomology of Spaces, Tag 0A4T,
lemma-higher-direct-images-zero-above-dimension-fibre
(blueprint: lem-sfb-noetherian-space-fibre-cohomology-bound).

Proof:
1. Fix a degree above d and a geometric point of Y. Formal functions identifies the
completed higher-image stalk with the inverse limit of cohomology on the infinitesimal
neighbourhoods of its fibre. Finite type of F can be tested on the given affine etale
cover, by lem-sfb-space-qcoh-affine-chart-calculus. Thus the coherent proper-image theorem
lem-sfb-space-proper-coherent-higher-images shows that this stalk is a finite module over
the Noetherian etale local ring A.
2. Properness is preserved under base change by lem-sfb-space-flat-proper-fp-locality.
The closed fibre and its infinitesimal neighbourhoods are therefore qcqs. An algebraic
closure of the residue field gives a geometric fibre covered by the hypothesis. Apply
lem-sfb-space-etale-atlas-topological-dimension and lem-sfb-space-field-extension-dimension
to conclude that the closed fibre has topological dimension at most d.
3. By lem-sfb-space-thickening-base-change the closed fibre and each infinitesimal
neighbourhood have homeomorphic point spaces, so each has dimension at most d, including
when they are empty.
4. Tensor pullback preserves quasi-coherence by lem-sfb-space-module-pullback-quasicoherent.
Apply lem-sfb-space-qcoh-vanishing-above-dimension to each infinitesimal neighbourhood:
its cohomology in the chosen degree is zero. No flatness is needed.
5. Every coordinate of the inverse limit is zero. The formal-functions comparison
lem-sfb-space-formal-functions-geometric-stalk therefore makes the completed stalk zero.
6. Successive quotient maps of the finite stalk modulo powers of the maximal ideal
are surjective. Recursively lifting gives surjectivity from its completion onto its
residue-field quotient. That quotient is zero, so Nakayama,
lem-weil-pbc-nakayama-jacobson, makes the stalk zero.
7. All geometric stalks vanish. Apply lemma-weil-pbc-geometric-stalk-conservative to the
map from the zero underlying abelian sheaf. Its module sheaf is zero as well. The exact
small-model equivalence preserves injective resolutions and homology; applying the
canonical derived direct image to F in degree zero gives these same higher images.
-/
theorem higherDirectImage_isZero_above_geometricFibreDimension
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] (Z : AlgebraicSpace Y)
    (p : Z ⟶ schemeSpace (Over.mk (𝟙 Y))) (hp : MapIsProper p) (d : ℕ)
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (CommRingCat.of Ω) ⟶ Y) (U : Over Y)
      (a : yoneda.obj U ⟶ Limits.pullback p.hom.hom
        (yoneda.map (Over.homMk y : Over.mk y ⟶ Over.mk (𝟙 Y)))),
      IsEtale a → IsAffine U.left → topologicalKrullDim U.left ≤ (d : WithBot ℕ∞))
    (F : Z.Modules) [F.IsQuasicoherent]
    (hcoh : ∃ (ι : Type w) (T : ι → Z.EtaleSite),
      IsJointlySurjective (fun k : ι ↦ (T k).obj.hom) ∧
      ∀ k : ι, IsAffine (Z.etaleForget.obj (T k)) ∧
        IsNoetherianRing Γ(Z.etaleForget.obj (T k), ⊤) ∧
        Module.Finite Γ(Z.etaleForget.obj (T k), ⊤) (F.val.obj (op (T k))))
    [HasDerivedCategory.{v} Z.SmallModules]
    [HasDerivedCategory.{v} (schemeSpace (Over.mk (𝟙 Y))).SmallModules]
    (q : ℤ) (hq : (d : ℤ) < q) :
    IsZero ((DerivedCategory.homologyFunctor
      (schemeSpace (Over.mk (𝟙 Y))).SmallModules q).obj
        ((derivedDirectImage p).obj
          ((DerivedCategory.singleFunctor Z.SmallModules 0).obj
            (Z.smallModuleRestriction.obj F)))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
