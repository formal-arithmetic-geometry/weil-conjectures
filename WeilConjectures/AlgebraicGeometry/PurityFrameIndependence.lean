/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FrameProductOnSupport
import WeilConjectures.AlgebraicGeometry.FrameProductElementary
import WeilConjectures.AlgebraicGeometry.FrameProductPullback
import WeilConjectures.AlgebraicGeometry.FrameHomZariskiSeparated
import WeilConjectures.AlgebraicGeometry.GeneratingTupleSpreading

/-!
# Independence of the concrete frame class

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-frame-independence (blueprint: lem-pur-frame-independence).

The frame class is transported from its presentation of the zero subscheme to
`Z ×_V U` using the canonical isomorphism of pullback squares. Two tuples on the
same etale neighbourhood can then be compared in literally the same Hom group.
For different neighbourhoods, apply the statement to their restricted tuples on
their fibre product, using naturality of the Kummer boundaries and supported cup.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- Read the concrete class of a frame in cohomology supported on the fixed
scheme-theoretic pullback `Z ×_V U`. The isomorphism is the canonical comparison
of the frame's pullback square with the chosen pullback, and the coefficient
isomorphism is the one already used by the frame-class construction. Only the
source of the supported Hom representative is transported; its degree and twist
are unchanged. This does not choose a class or a trivialization of the twist.
Source: blueprint main-20261015, lem-pur-frame-independence, equality of classes
for the same pair (blueprint: lem-pur-frame-independence). -/
def frameClassOnPullback (P : PurityFiniteSetting.{u}) {B V Z : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension P.level v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)] (c : ℕ)
    (hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞)) (F : i.EtaleFrame c) :
    cupSupportedHom P (pullback.snd i F.e)
      ((cupSingle P F.U).obj (P.frameTwist F.U c)) (2 * (c : ℤ)) :=
  let _codimension := hcodim
  P.frameProductOnSupport (pullback.snd i F.e) (F.e ≫ v ≫ b) c F.f
    F.isPullback.isoPullback F.isPullback.isoPullback_hom_snd

set_option allowUnsafeReducibility true in
attribute [local irreducible] frameProductOnSupport frameBoundaryProduct
  functorialCupPullback frameClosedCoefficientIso

-- STATEMENT-DISPUTED: the former codimension convention allowed infinite ambient
-- stalk dimensions. The returned E2 repair adds hfinite before using that convention.
/-- The concrete class depends only on the closed pair, not its ordered tuple
of equations. Both tuples present the same scheme-theoretic pullback of `Z` on
an arbitrary common etale neighbourhood `U`. In particular, no equality of
lists, equality of their ranges, or chosen invertible change-of-generators
matrix is assumed. For frames on different neighbourhoods, use their common
etale fibre product and the restrictions of their functions in this statement.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-frame-independence (blueprint: lem-pur-frame-independence).

The ambient stalks along Z are assumed finite-dimensional so the Krull-dimension
codimension convention can be used in bottom-degree descent.

Proof (the seven steps of the DAG node):
1. Compare two length-c frames on the same etale neighbourhood; different
   neighbourhoods are compared on their etale fibre product
   (def-weil-pbc-etale-site). At c=0 both classes are the supported unit.
2. By lem-pur-relative-support-bottom-descent equality can be tested on a
   Zariski cover. At each stalk, lem-pur-local-generating-tuples transforms one
   generating tuple into the other by finitely many permutations, unit scalings
   and shears. Spread the finitely many coefficients, unit inverses and equations
   to an affine open neighbourhood. Lem-pur-supported-cup-functoriality identifies
   the restricted classes with their defining boundary products. No strict
   henselization is asserted to be an etale neighbourhood.
3. A unit scaling adds a Kummer class extending over U. Its individual support
   boundary vanishes by thm-pur-with-support-exactness, so its factor is unchanged.
4. Adjacent factors have degree two, giving the graded sign (-1)^(2*2)=1.
   The twists are rank-one lines, so their symmetry preserves the canonical
   product identification. Adjacent swaps generate all permutations.
5. For a shear replace f_i by f_i+t*a*f_j on the affine line over U. This tuple
   cuts out the constant pullback of Z_U. Its individual Kummer boundaries and
   ordered supported product define a class whose zero and unit section
   restrictions are the original and sheared classes. The interpolation scheme
   need not be etale over V; only the boundary/product construction is used there.
6. Lem-pur-supported-affine-line-homotopy identifies that class with a pullback
   from U. Both section pullbacks are inverse to the projection pullback, hence
   equal; this proves shear invariance.
7. Compose these invariances locally and descend by the bottom-degree equality
   test. The same argument on the common etale fibre product compares the
   restricted classes of frames on different neighbourhoods. The canonical
   support identifications are precisely those in frameClassOnPullback. -/
theorem frameClass_independent (P : PurityFiniteSetting.{u}) {B V Z : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension P.level v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)] (c : ℕ)
    (hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (hfinite : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) ≠ ⊤)
    (U : Scheme.{u}) (e : U ⟶ V) [Etale e] (f g : Fin c → Γ(U, ⊤))
    (tf : U.zeroLocusSubscheme (Set.range f) ⟶ Z)
    (tg : U.zeroLocusSubscheme (Set.range g) ⟶ Z)
    (hf : IsPullback tf (U.zeroLocusSubschemeι (Set.range f)) i e)
    (hg : IsPullback tg (U.zeroLocusSubschemeι (Set.range g)) i e) :
    P.frameClassOnPullback b v i c hcodim
      { U := U, e := e, etale := inferInstance, f := f, toZ := tf, isPullback := hf } =
    P.frameClassOnPullback b v i c hcodim
      { U := U, e := e, etale := inferInstance, f := g, toZ := tg, isPullback := hg } := by
  classical
  change P.frameProductOnSupport (pullback.snd i e) (e ≫ v ≫ b) c f
      hf.isoPullback hf.isoPullback_hom_snd =
    P.frameProductOnSupport (pullback.snd i e) (e ≫ v ≫ b) c g
      hg.isoPullback hg.isoPullback_hom_snd
  apply P.frameHom_zariski_separated b v i c hcodim hfinite U e f tf hf
  have hid := (Scheme.Hom.ker_of_isPullback i e hf).trans
    (Scheme.Hom.ker_of_isPullback i e hg).symm
  rw [Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι] at hid
  intro x
  obtain ⟨W, hxW, hc⟩ := generatingTupleChain_of_idealSheaf_eq U c f g hid x
  refine ⟨W, hxW, ?_⟩
  intro sq
  have hpf := framePresentationPullback (pullback.snd i e) W.ι c f
    hf.isoPullback hf.isoPullback_hom_snd
  have hpg := framePresentationPullback (pullback.snd i e) W.ι c g
    hg.isoPullback hg.isoPullback_hom_snd
  have hp := P.frameProductOnSupport_pullback _ _ W.ι _ sq (e ≫ v ≫ b) c f
    hf.isoPullback hf.isoPullback_hom_snd
    hpf.isoPullback hpf.isoPullback_hom_snd
  have hq := P.frameProductOnSupport_pullback _ _ W.ι _ sq (e ≫ v ≫ b) c g
    hg.isoPullback hg.isoPullback_hom_snd
    hpg.isoPullback hpg.isoPullback_hom_snd
  have hm := P.frameProductOnSupport_elementary _ (W.ι ≫ (e ≫ v ≫ b)) c _ _
    hpf.isoPullback hpf.isoPullback_hom_snd hpg.isoPullback
    hpg.isoPullback_hom_snd hc
  have hpm := hp.trans hm
  exact hpm.trans hq.symm

end WeilConjectures.PurityFiniteSetting
