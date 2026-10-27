/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-! # Étale base change of an infinitesimal pushout of algebraic spaces

Source: Stacks Project, spaces-pushouts.tex, Tag 07W3, final flat counit assertion
and part (5) (blueprint: lem-sfb-space-pushout-etale-base-change).

The base-changed square uses the actual sheaf fibre products. Its pushout property
is the bijection between maps out of the étale scheme and compatible pairs of maps
out of the two restrictions, for every algebraic-space target over the base scheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The induced map on the two sheaf fibre products in the base-changed pushout square.
It sends a compatible pair `(t, z)` to `(t, f(z))`; no map or isomorphism is chosen.
Source: Stacks, Tag 07W3, restriction of the pushout triple along an étale scheme
(blueprint: lem-sfb-space-pushout-etale-base-change). -/
def pushoutEtaleBaseChangeMap {B : Scheme.{u}} {E X Y Q : AlgebraicSpace B}
    (e : E ⟶ Q) (x : X ⟶ Q) (y : Y ⟶ Q) (f : X ⟶ Y) (h : f ≫ y = x) :
    enlargedFibreProduct e x ⟶ enlargedFibreProduct e y :=
  ObjectProperty.homMk
    (Limits.pullback.map e.hom x.hom e.hom y.hom (𝟙 E.obj) f.hom (𝟙 Q.obj)
      (by simp) (by simpa using congrArg (fun k : X ⟶ Q ↦ k.hom) h.symm))

/-- An étale scheme base change of an affine-thickening pushout is again a pushout
in algebraic spaces over the same base. `IsPushout` expresses exactly the universal
bijection against every algebraic-space target, with the two displayed projections.
Source: Stacks, Tag 07W3, part (5) and final flat counit assertion
(blueprint: lem-sfb-space-pushout-etale-base-change).

Proof: (1) The existence and recovery lemma lem-sfb-space-affine-thickening-pushout
identifies Q with the constructed pushout, so C to Q is a thickening. By
lem-sfb-space-thickening-base-change, its restriction C_E to E is a thickening,
as is A_E to A_E+. The map A_E to C_E is affine by its scheme base changes.
Associativity of the sheaf fibre products identifies the common overlap.
(2) Form Z = C_E amalg_{A_E} A_E+ by the same pushout existence lemma. Its
universal property gives f : Z to E. Recovery identifies its restrictions over C
and A+ with C_E and A_E+. These maps are base changes of e, hence étale by
lem-trf-space-chartwise-etale-permanence. The criterion
lem-sfb-space-pushout-etale-morphism-criterion makes Z to Q chartwise étale.
(3) Both Z and E are étale over Q, so f is chartwise étale by permanence.
Recovery identifies its base change to the thickening C_E in E with the identity
of C_E, using the original coprojection. Thus f is an isomorphism by
lem-sfb-space-etale-thickening-detects-iso.
(4) For compatible maps from C_E and A_E+ to any H, the pushout Z supplies a
unique map h : Z to H. Compose h with the inverse of f to obtain the required
map from E. Equality is tested on the two pieces after composition with f,
giving uniqueness. No finite-order, flatness or finite-presentation bound on
the original spaces or thickening is used. -/
theorem affineThickeningPushout_etaleBaseChange {B : Scheme.{u}}
    (A A' C Q : AlgebraicSpace B) (i : A ⟶ A') (a : A ⟶ C)
    (j : C ⟶ Q) (b : A' ⟶ Q)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hiTop : IsHomeomorph (mapPoint i.hom.hom))
    (ha : IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) a.hom.hom)
    (hp : IsPushout a i j b) (E : Over B) (e : schemeSpace E ⟶ Q)
    (he : IsEtale e.hom.hom) :
    IsPushout
      (pushoutEtaleBaseChangeMap e (a ≫ j) j a rfl)
      (pushoutEtaleBaseChangeMap e (a ≫ j) b i hp.w.symm)
      (enlargedFibreProductFst e j) (enlargedFibreProductFst e b) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
