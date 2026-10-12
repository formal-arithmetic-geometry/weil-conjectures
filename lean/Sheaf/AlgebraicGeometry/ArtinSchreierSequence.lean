/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent
import Sheaf.RingTheory.LocalRing.ArtinSchreierKernel
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.ArtinSchreierData
import Sheaf.AlgebraicGeometry.ArtinSchreierExact

/-!
# The Artin–Schreier sequence

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/lem-sc-as-sequence.md,
node `lem-sc-as-sequence` (blueprint: lem-sc-as-sequence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false

/-- The Artin–Schreier sequence, with its sectionwise maps specified.
Source: Stacks Project, Étale Cohomology, Section 0A3J, and blueprint
`lem-sc-as-sequence` (blueprint: lem-sc-as-sequence).

The isomorphism identifies `G` with the universe lift of the recorded étale
structure-module sheaf. The natural additive equivalences `a` identify its
sections with global functions, including their restriction maps. The equation
on the sheafification unit specifies the unique extension of `c ↦ c • 1`.

Proof:
1. In characteristic p, Frobenius minus the identity is additive and natural.
   The constant-presheaf map factors uniquely through sheafification
   (def-weil-pbc-sheafification, def-sc-constant-sheaves), using quasi-coherent
   descent (lem-sc-etale-qcoherent-descent). Fermat gives the zero composite.
2. Locally adjoin a root of `T^p-T-f`. Its derivative is -1, so the resulting
   cover is étale (lem-weil-pbc-standard-etale-monic-derivative), and its
   geometric fibres are nonempty (lem-weil-pbc-surjective-nonempty-fibres).
   Local surjectivity gives epimorphy (lem-weil-pbc-abelian-sheaf-epi-locally-surjective).
3. Exact geometric stalks (prop-weil-pbc-geometric-stalks-exact) identify the
   kernel with the elements satisfying `x^p=x`. In a local ring these are
   precisely the prime-field constants (lem-sc-local-ring-artin-schreier-kernel).
   The constant sheaf has stalk `ZMod p` (lem-weil-pbc-constant-sheaf-geometric-stalk);
   constants inject since the pointed neighbourhood rings are nonzero.
4. Conservativity (lemma-weil-pbc-geometric-stalk-conservative) identifies the
   kernel sheaf with the constant sheaf. With epimorphy and the zero composite,
   this is short exact (def-weil-pbc-exact-sequence). -/
theorem artinSchreier_shortExact
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (p : ℕ) [CharP k p] (hp : 0 < p) :
    ∃ (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
      (_ : G ≅ (sheafCompose C.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C)))
      (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
      (wp : G ⟶ G) (iota : C.constantZMod p ⟶ G) (hzero : iota ≫ wp = 0),
      (∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
        a V (G.obj.map g x) = g.unop.left.appTop (a U x)) ∧
      (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a U (wp.hom.app U x) = (a U x) ^ p - a U x) ∧
      (∀ (U : C.Etaleᵒᵖ) (c : ZMod p),
        a U (iota.hom.app U
          ((toSheafify C.smallEtaleTopology
            ((Functor.const C.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
          (c.val : Γ(U.unop.left, ⊤))) ∧
      ShortComplex.ShortExact (ShortComplex.mk iota wp hzero) := by
  obtain ⟨G, hG, a, wp, iota, hzero, hrestr, hwp, hiota⟩ :=
    artinSchreier_data f p hp
  refine ⟨G, hG, a, wp, iota, hzero, hrestr, hwp, hiota, ?_⟩
  exact artinSchreier_data_shortExact f p hp G hG a wp iota hzero hrestr hwp hiota

end AlgebraicGeometry
