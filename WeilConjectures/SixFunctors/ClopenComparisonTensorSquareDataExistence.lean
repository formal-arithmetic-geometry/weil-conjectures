/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ClopenComparisonTensorSquareData
public import WeilConjectures.SixFunctors.OpenTensorNormalization
import WeilConjectures.SixFunctors.CanonicalPullTensor
import WeilConjectures.SixFunctors.ClopenOpenTensorDataExistence
import WeilConjectures.SixFunctors.ClopenDeltaKDataExistence

/-!
# Existence of normalized clopen tensor comparison data

Source: Stacks Project, sites-cohomology.tex, Tags 07A4
(lemma-pullback-tensor-product) and 0GL1 (lemma-j-shriek-and-tensor), and the
clopen tensor refinement of Tag 0F7B, original steps 1–7
(blueprint: lem-sf-clopen-comparison-tensor-data-existence).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.ClopenComparisonTensorSquare

/-- Normalized comparison data exist for the canonical lift of a proper/open square.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4
(lemma-pullback-tensor-product) and 0GL1 (lemma-j-shriek-and-tensor), and the
clopen tensor refinement of Tag 0F7B, original steps 1–7
(blueprint: lem-sf-clopen-comparison-tensor-data-existence).

Proof:
1. The proper/open calculus makes the canonical square lift `s` clopen
   (lem-cbc-strict-tower-proper-open-calculus).
2. The canonical tensor pullback comparisons for p and for the Cartesian projection q
   give the two PullTensor records tensorP and tensorQ (lem-sf-canonical-pull-tensor).
3. The open tensor records on j' and on s, the exact extension along s and the reverse
   clopen adjunction with its counit normalization exist
   (lem-sf-clopen-open-tensor-data-existence: restriction preserves pure tensors and flat
   K-flat representatives, the localized open projection formula gives the deltas, and
   clopen gluing makes extension also right adjoint to restriction).
4. Composing the two open projection formulas gives deltaK with the prescribed inverse
   transpose (lem-sf-clopen-delta-k-data-existence).
5. These fields assemble to Data. No Equations assertion is made here. -/
theorem data_nonempty (m : Mode) {A B C D : Scheme.{u}}
    (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (R : Sheaf (topology m D) CommRingCat.{u + 1})
    (S : Sheaf (topology m B) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m p).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m D) (topology m B)).obj S)
    (t : SiteSquare (input m p i R S c))
    (o : Operations (input m p i R S c) t) (_a : Assertion o) :
    Nonempty (Data o (AlgebraicGeometry.ProEtale.StrictTower.squareLift k r p i h)) := by
  let d := input m p i R S c
  let s := AlgebraicGeometry.ProEtale.StrictTower.squareLift k r p i h
  let _ : IsOpenImmersion s :=
    AlgebraicGeometry.ProEtale.StrictTower.squareLift_open k r p i h
  let _ : IsClosedImmersion s :=
    AlgebraicGeometry.ProEtale.StrictTower.squareLift_closed k r p i h
  obtain ⟨hp⟩ := canonical_pull_tensor m p R S c o.gPull o.tensorX o.tensorX'
  obtain ⟨hq⟩ := canonical_pull_tensor m d.gU
    (restrictRing m d.j d.R) (restrictRing m d.j' d.S)
    (cornerCoefficient t) o.gUPull o.tensorU o.tensorU'
  obtain ⟨b⟩ := open_tensor_data_nonempty o s
  obtain ⟨z⟩ := deltaK_data_nonempty b
  exact ⟨{
    tensorP := hp
    tensorQ := hq
    tensorB := b.tensorB
    extensionS := b.extensionS
    tensorA := b.tensorA
    tensorS := b.tensorS
    rightAdjunction := b.rightAdjunction
    counit_normalization := b.counit_normalization
    deltaK := z.deltaK
    inverse_transposeK := z.inverse_transposeK }⟩

end SheafOfModules.ClopenComparisonTensorSquare
