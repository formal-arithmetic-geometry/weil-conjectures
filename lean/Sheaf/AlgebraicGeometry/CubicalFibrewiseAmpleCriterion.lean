/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Sheaf.AlgebraicGeometry.CubicalRigidifiedLine
public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.AlgebraicGeometry.StrictHenselianFibrewiseSectionDensity
import Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAmpleLocal
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.StrictHenselizationNoetherian

/-! # Fibrewise ampleness of cubical lines on semiabelian schemes

Source: Agent-formulated supporting criterion for the relative Picard input in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/_section.md`.
Motivated by Raynaud, Faisceaux amples sur les schemas en groupes et les espaces homogenes,
LNM 119, XI; the original is locally WANTED, so no numbered Raynaud result is asserted.
(blueprint: lem-sfb-cubical-fibrewise-ample-criterion)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A cubical rigidified line that is ample on every residue-field fibre of a smooth
separated commutative group scheme of finite presentation with semiabelian geometric
fibres is ample over the inverse image of every affine open of its normal locally
Noetherian base. Finite presentation is encoded by smoothness (hence local finite
presentation), quasi-compactness, and separatedness (hence quasi-separatedness).

Source: Agent-formulated supporting criterion, motivated by Raynaud, Faisceaux amples,
LNM 119, XI (original locally WANTED); blueprint six-functors-basics, relative Picard input.
(blueprint: lem-sfb-cubical-fibrewise-ample-criterion)

Proof (the accepted agent-written split):
1. For t in an affine open V of T, put A = O_{T,t}. Normality makes A an integrally
   closed domain, and a Noetherian affine chart plus localization makes it Noetherian
   (`lem-weil-pbc-localization-noetherian`). Pull back the group and cubical line to
   Spec A; smoothness, separatedness and finite presentation persist by
   `lem-pc-proper-base-change`, `lem-weil-pbc-separated-base-change` and
   `lem-weil-pbc-qcqs-morphism-permanence`. Its residue fibres are original fibres
   at generalizations of t, hence remain ample. Choose a separable closure of kappa(t)
   and form R = A^sh, X = H_R, L = B_R. The triples and Noetherian strict-henselization
   lemmas give a Noetherian strictly henselian local R.
2. Apply `lem-sfb-cubical-strict-local-affine-seed` to the A-family, obtaining n > 0
   and a section s of L^n with affine nonvanishing open U containing the closed identity.
   The rigidification identifies its value along the identity with an element of R
   outside the maximal ideal. That element is a unit, so the whole identity section
   lies in U. Finite presentation over affine Spec R makes X quasi-compact and
   quasi-separated (`lem-weil-pbc-qcqs-morphism-permanence`).
3. Each geometric fibre is connected: its torus kernel and abelian quotient are
   connected; a clopen decomposition is constant on torus cosets and descends along
   the fppf quotient, hence is constant. The smooth-section component lemma
   (`lem-sbc-smooth-section-component-geometrically-irreducible`) now makes every
   residue fibre geometrically irreducible. Apply
   `lem-sfb-strict-henselian-fibrewise-section-density`: values of X(R) meet every
   nonempty open of every geometric fibre. Smoothness, separatedness, finite
   presentation, the identity section and the Noetherian strictly henselian base
   supply exactly its hypotheses.
4. For a in X(R), pull back the trivialized cube along x |-> (x,a,-a). Cancelling
   identity factors with the rigidification gives
   t_a^*L tensor t_{-a}^*L = L^2 tensor p_R^*(a^*L tensor (-a)^*L), up to the canonical
   line isomorphism. Every invertible module on local Spec R is trivial, so trivialize
   the base factor. Tensor the isomorphism n times and transport
   t_a^*s tensor t_{-a}^*s to a section q_a of L^{2n}. Pullback and tensor fibre formulas
   (`lem-weil-pbc-invertible-pullback-tensor`) identify its nonvanishing open with
   t_a^{-1}(U) intersect t_{-a}^{-1}(U).
5. Translation makes the first open affine; `lem-sc-affine-cap-section-open` makes
   its intersection with the other section's nonvanishing locus affine. For any
   geometric point x, the open (U-x) intersect (x-U) is nonempty by geometric
   irreducibility. Section density supplies a in X(R) in this open, so x is in X_{q_a}.
   Every scheme point has a geometric lift, hence these affine nonvanishing opens
   cover X. Quasi-compactness and positive-power sections give ampleness of L.
6. Spec R is the limit of the small category of affine pointed etale neighbourhoods
   of t in V (`def-weil-pbc-strict-henselization-limit` and
   `lem-exc-affine-strict-local-ring-comparison`, respecting the structural map).
   Pulling back H gives qcqs terms, affine transitions and limit X. Reindex by a
   nonempty directed set (`lem-weil-pbc-cofiltered-limit-directed-reindex`) and use
   `lem-trf-ample-affine-limit-descent` to obtain an affine pointed etale neighbourhood
   W_t of t over which B is ample.
7. Every affine open W' of affine W_t maps affinely to W_t. After base change, the
   affine pullback theorem (`lem-weil-pbc-pullback-ample-invertible`) gives ampleness
   over W'. The W_t form a jointly surjective etale family, so the scheme case of
   `lem-trf-algebraic-space-ample-local` gives ampleness over V. For empty V the
   ample definition applies directly. V was arbitrary. -/
theorem CubicalRigidifiedLine.isAmple_over_affine_of_fibrewise
    {T : Scheme.{u}} [IsLocallyNoetherian T]
    (hnormal : ∀ t : T, IsDomain (T.presheaf.stalk t) ∧
      IsIntegrallyClosed (T.presheaf.stalk t))
    (H : Grp (Over T)) [IsCommMonObj H.X]
    [Smooth H.X.hom] [IsSeparated H.X.hom] [QuasiCompact H.X.hom]
    (B : CubicalRigidifiedLine H.X)
    (hample : ∀ t : T,
      ∃ hBt : ((Scheme.Modules.tensorPullback (H.X.hom.fiberι t)).obj B.line).IsInvertible,
        @Scheme.Modules.IsAmple (H.X.hom.fiber t)
          ((Scheme.Modules.tensorPullback (H.X.hom.fiberι t)).obj B.line) hBt)
    (hsemi : HasSemiabelianGeometricFibres H) :
    ∀ V : T.Opens, IsAffineOpen V →
      ∃ hBV : ((Scheme.Modules.tensorPullback (H.X.hom ⁻¹ᵁ V).ι).obj B.line).IsInvertible,
        @Scheme.Modules.IsAmple (H.X.hom ⁻¹ᵁ V).toScheme
          ((Scheme.Modules.tensorPullback (H.X.hom ⁻¹ᵁ V).ι).obj B.line) hBV := by
  sorry

end AlgebraicGeometry
