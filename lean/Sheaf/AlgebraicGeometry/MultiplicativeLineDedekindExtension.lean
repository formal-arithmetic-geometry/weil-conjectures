/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.CoherentMultiplicativeLine
public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.RigidifiedLineBigOpenExtension
import Sheaf.AlgebraicGeometry.NormalGroupVerticalCartierDescent
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Extending coherent multiplicative lines over a Dedekind base

Source: BLR, Neron Models, 10.1 Proposition 7, printed p.292 (PDF p.298),
primitive-line extension to the identity component, in the coherent rigidified form
and with the frame-product geometry spelled out in the DAG
(blueprint: lem-sfb-multiplicative-line-dedekind-extension).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.MultiplicativeLine

open Scheme.Modules SplitTorusFrames

/-- The j-th coordinate on the actual recursively constructed split torus over a ring.
Source: BLR 10.1 Proposition 7, p.292; Laurent coordinates
(blueprint: lem-sfb-multiplicative-line-dedekind-extension). -/
def ringCoordinate (D : Type u) [CommRing D] :
    (r : ℕ) → Fin r → ((RingGroupSchemes.splitTorus D r).X ⟶
      (RingGroupSchemes.multiplicative D).X)
  | 0, j => Fin.elim0 j
  | n + 1, j => Fin.cases
      (fst (RingGroupSchemes.multiplicative D).X (RingGroupSchemes.splitTorus D n).X)
      (fun i ↦ snd (RingGroupSchemes.multiplicative D).X
        (RingGroupSchemes.splitTorus D n).X ≫ ringCoordinate D n i) j

/-- The Laurent coordinate of a torus point as a regular unit-valued scalar.
Source: BLR 10.1 Proposition 7, p.292; Stacks Tag 022U
(blueprint: lem-sfb-multiplicative-line-dedekind-extension). -/
def ringScalar {D : Type u} [CommRing D] {r : ℕ} {U : Over (Spec (.of D))}
    (t : U ⟶ (RingGroupSchemes.splitTorus D r).X) (j : Fin r) : Γ(U.left, ⊤) :=
  (t ≫ ringCoordinate D r j).left.appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial D))).inv (LaurentPolynomial.T 1))

/-- Evaluate a represented frame using a specified universal frame.
Source: Stacks Tag 01M2; canonical pullback of frames
(blueprint: lem-sfb-multiplicative-line-dedekind-extension). -/
def atFrame {S : Scheme.{u}} {G : CommGrp (Over S)} {B : CommGrp (Over S)}
    (q : B.X ⟶ G.X) (A : Coherent G)
    (f : unit B.X.left ≅ (tensorPullback q.left).obj A.line)
    {U : Over S} (x : U ⟶ B.X) : Point A.toRaw U :=
  ⟨x ≫ q, pullFrame A.line q.left f x.left⟩

/-- The geometric conclusion for a finite family, with all schemes, frames and operations
specified. The kernel isomorphism is normalized by scalar multiplication of identity frames.
Fppf exactness is the objectwise kernel identification and local surjectivity of Yoneda.
Source: BLR 10.1 Proposition 7, p.292; Stacks Tags 01M2, 0499 and 049A
(blueprint: lem-sfb-multiplicative-line-dedekind-extension). -/
structure FrameExtension {D : Type u} [CommRing D]
    (G : CommGrp (Over (Spec (.of D)))) (r : ℕ) (A : Fin r → Coherent G) where
  group : CommGrp (Over (Spec (.of D)))
  quotient : group.X ⟶ G.X
  homomorphism : IsMonHom quotient
  frames (j : Fin r) : FrameModel (A j).line
  productIso : Over.mk quotient.left ≅ ∏ᶜ fun j : Fin r ↦ (frames j).space
  universalFrame (j : Fin r) :
    unit group.X.left ≅ (tensorPullback quotient.left).obj (A j).line
  product_frame (j : Fin r) : universalFrame j =
    (frames j).at (productIso.hom ≫ Pi.π (fun i : Fin r ↦ (frames i).space) j)
  multiplication (U : Over (Spec (.of D))) (x y : U ⟶ group.X) (j : Fin r) :
    atFrame quotient (A j) (universalFrame j) (x * y) =
      mul (A j).toRaw (atFrame quotient (A j) (universalFrame j) x)
        (atFrame quotient (A j) (universalFrame j) y)
  identity (U : Over (Spec (.of D))) (j : Fin r) :
    atFrame quotient (A j) (universalFrame j) (1 : U ⟶ group.X) = one (A j).toRaw U
  smooth : Smooth group.X.hom
  separated : IsClosedImmersion (pullback.diagonal group.X.hom)
  finiteType : LocallyOfFiniteType group.X.hom ∧ QuasiCompact group.X.hom
  connectedFibres : GeometricallyConnected group.X.hom
  kernelIso : RingGroupSchemes.splitTorus D r ≅ Grp.mk (GrpObj.ker quotient)
  kernel_scalar (U : Over (Spec (.of D)))
      (t : U ⟶ (RingGroupSchemes.splitTorus D r).X) (j : Fin r) :
    HEq (((atFrame quotient (A j) (universalFrame j)
      (t ≫ kernelIso.hom.hom.hom ≫ GrpObj.kerι quotient)).2.hom).app ⊤
        (unitSectionsEquiv (X := U.left) ⊤ 1))
      (ringScalar t j •
        ((one (A j).toRaw U).2.hom).app ⊤ (unitSectionsEquiv (X := U.left) ⊤ 1))
  quotient_locallySurjective : Presheaf.IsLocallySurjective
    (Scheme.fppfTopology.over (Spec (.of D))) (yoneda.map quotient)
  group_sheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of D)))
    (yoneda.obj group.X)
  quotient_sheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of D)))
    (yoneda.obj G.X)
  rank_zero : r = 0 → IsIso quotient

/-- Spec of the fraction-field embedding.
Source: BLR 10.1 Proposition 7, p.292
(blueprint: lem-sfb-multiplicative-line-dedekind-extension). -/
def genericMap (D K : Type u) [CommRing D] [Field K] [Algebra D K] :
    Spec (.of K) ⟶ Spec (.of D) :=
  Spec.map (CommRingCat.ofHom (algebraMap D K))

/-- The prescribed coherent generic line extends, and every finite family has the stated
smooth separated connected frame-group extension, including the empty family.

Source: BLR, Neron Models, 10.1 Proposition 7, printed p.292 (PDF p.298),
agent-extracted coherent rigidified form and frame-product geometry
(blueprint: lem-sfb-multiplicative-line-dedekind-extension).

Proof:
1. The affine base is normal integral Noetherian and has local dimension at most one.
   Finite type makes Q Noetherian, quasi-separated and finitely presented. The affine
   neighbourhoods of the generic point have limit Spec K; their base changes have limit Q_K
   (lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods, lem-weil-pbc-scheme-over-limit).
2. Descend the generic line and its specified identity frame after shrinking the base
   (lem-trf-invertible-affine-limit-descent, lem-trf-fp-module-limit-isomorphism-descent).
   The rigidified big-open extension lemma extends it to all of S, since every point has
   local dimension at most one (lem-sfb-rigidified-line-big-open-extension).
3. Each Q^n is smooth separated finite type with connected geometric fibres. Apply
   lem-sfb-normal-group-vertical-cartier-descent to obtain normality and integrality.
   Smooth flatness makes localization into the generic fibre injective on local functions;
   hence maps of lines agreeing generically agree globally (lem-pc-smooth-flat).
4. Regard the specified multiplication as a rational section of the Hom line on Q^2.
   Its divisor is vertical and becomes zero off finitely many closed base points. By
   lem-sfb-normal-group-vertical-cartier-descent it is pulled back from the identity section.
   In a local frame compatible with the rigidification write the section as h times a
   regular unit v. The generic unit axiom gives h times e*v = 1, so h is a local unit.
   Its Cartier divisor is therefore zero and the section extends invertibly everywhere.
5. Associativity on Q^3, symmetry on Q^2 and the identity-axis laws agree generically.
   Step 3 proves equality globally, with the canonical tensor/pullback comparisons
   (lem-weil-pbc-invertible-pullback-tensor).
6. Trivialize the finitely many extended lines simultaneously. Glue products with G_m^r
   by inverse transition units (lem-weil-pbc-glue-schemes). These represent simultaneous
   frames, naturally on every test scheme by fpqc descent of morphisms. The product
   universal property gives productIso; for r=0 it identifies the product with Q.
7. Multiply frames using the extended multiplication. Yoneda gives the group law and
   identity. The perfect pairing with the inverse-pulled-back line gives the inverse;
   in local coordinates it sends z to c inverse times z inverse. Coherence gives all
   group identities (lem-pc-yoneda, lem-pc-tensor-dual-invertible).
8. Representables are fppf sheaves by fpqc descent. Frames above the identity are uniquely
   scalar multiples of the identity frames. Bilinearity gives the scalar kernel group
   G_m^r. Local frames give Zariski, hence fppf local surjectivity. The generic line
   identification recovers the original identity and multiplication.
9. Frame-product charts are Spec R[z_j^{±1}] by lem-sfb-frame-product-laurent-algebra.
   They are opens in affine spaces, hence smooth. Their finite-type presentations and
   affine diagonals prove finite type and separatedness, then composition proves the
   properties over S (sbc-lem-affine-space-smooth, lem-trf-smooth-composition).
10. On any geometric fibre the frame projection is open surjective with connected torus
   fibres. A clopen decomposition would give a clopen decomposition of the connected
   base fibre, so one part is empty. This proves geometric connectedness, including r=0.
-/
theorem exists_multiplicative_line_dedekind_extension
    (D K : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D]
    (_hdim : ringKrullDim D = 1) [Field K] [Algebra D K] [IsFractionRing D K]
    (G : CommGrp (Over (Spec (.of D))))
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [GeometricallyConnected G.X.hom] :
    (∀ A : Coherent (changeBase G (genericMap D K)),
      ∃ E : Coherent G, Nonempty (Identification (genericMap D K) E A)) ∧
    (∀ (r : ℕ) (A : Fin r → Coherent (changeBase G (genericMap D K))),
      ∃ E : Fin r → Coherent G,
        (∀ j : Fin r, Nonempty (Identification (genericMap D K) (E j) (A j))) ∧
          Nonempty (FrameExtension G r E)) := by
  sorry

end AlgebraicGeometry.MultiplicativeLine
