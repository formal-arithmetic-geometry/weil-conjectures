## Worker report

States `lem-sfb-topological-homogeneous-cochain-coordinates` in
`Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates`.
There are three declarations, all belonging to this node's own notions:
`ContinuousCohomology.JointContinuousCochainCoordinates`,
`ContinuousCohomology.exists_jointContinuousCochainCoordinates`, and
`ContinuousCohomology.jointContinuousCochainCoordinates_naturality`.
The two theorems have `sorry` proofs. The structure has actual complex, evaluation,
isomorphism, and derived-isomorphism data and the full characterizing equations;
there is no definition choosing data from an unproved existence theorem.

The main theorem asserts existence of the two integer-indexed complexes and all
of the coordinate/derived data in the structure. The evaluation maps are injective
linear maps with exactly specified images. Thus the underlying spaces are identified
with precisely the function spaces in the node, with their pointwise E-vector-space
structures. This permits an ambient universe lift without replacing continuous
functions by iterated maps or changing the mathematical objects. These interfaces
are completely characterized, rather than arbitrary comparison maps: `phi`, `psi`,
`derived_hom`, and `derived_inv` prescribe the actual representatives. Image exactness
and injectivity identify each realization uniquely up to evaluation-preserving linear
isomorphism; the two differential equations determine the differentials.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Topological field E: `(E : Type u) [Field E] [TopologicalSpace E]
  [IsTopologicalDivisionRing E]`. `Field` is the declaration of `def-weil-field`.
- Topological group J: `(J : Type v) [Group J] [TopologicalSpace J]
  [IsTopologicalGroup J]`.
- Topological E-vector space V: `(V : Type w) [AddCommGroup V] [Module E V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul E V]`.
- E-linear group action: `ρ : J →* V ≃ₗ[E] V`. The group laws give invertibility
  of every linear action operator, exactly as for a linear group action.
- Joint continuity: `hρ : Continuous (fun p : J × V ↦ ρ p.1 p.2)`.
- Homogeneous cochains in degree n: `bEval n`, `bInjective n`, and `bRange n F`.
  The last says the image consists exactly of jointly continuous F on
  `Fin (n+1) → J` satisfying `F (fun i ↦ a * x i) = ρ a (F x)` for every a,x.
  The evaluation map is E-linear, so operations correspond to pointwise operations.
- Inhomogeneous cochains: `cEval n`, `cInjective n`, and `cRange n f` specify
  exactly the continuous functions on `Fin n → J`, with their pointwise operations.
  At n=0, `Fin 0 → J` is a singleton, and evaluation at its unique empty tuple
  identifies this space canonically with V; all such constant functions are continuous.
- Homogeneous alternating omission differential: `delta` evaluates the actual
  complex differential as the sum over `i : Fin (n+2)` of `(-1:E)^i.val` times
  evaluation after `i.succAbove`. This omits precisely coordinate i, in order.
- Inhomogeneous differential: `differential` gives the first action term and the
  sum over `i : Fin (n+1)` with sign `(-1:E)^(i.val+1)`. For i<n,
  `Fin.contractNth i (· * ·)` merges consecutive coordinates i and i+1, which
  is the node's term indexed i+1. For i=n, every surviving index is less than i,
  so this drops the final coordinate. This is precisely the node's final term,
  with sign `(-1)^(n+1)`.
- Degree zero differential: set n=0 in `differential`. The first term is
  `ρ (g 0) v`; the sum has its sole index 0, sign -1, and empty contracted tuple.
  Hence it is exactly `g v - v`, with no exception for n=0.
- These are ordinary E-vector-space complexes: `B C : CochainComplex
  (ModuleCat E) ℤ`. The complex laws include differential-squared-zero.
  No topology on these category objects is used.
- Extension by zero in negative degrees: `bNegative` and `cNegative` give
  `IsZero (B.X i)` and `IsZero (C.X i)` for every integer i<0. Thus maps incident
  to the negative terms are the unique zero maps, including the degree -1 boundary.
- Actual E-linear cochain isomorphism Phi with inverse Psi: `iso : B ≅ C`.
  Both maps are genuine morphisms in the category of integer-indexed complexes;
  the inverse identities and the two differential-commutation equations are
  part of this isomorphism's type.
- Phi formula: `phi` states evaluation after `iso.hom.f n` equals homogeneous
  evaluation at `Fin.partialProd g`. Its documented definition is
  `(1,g₁,g₁g₂,...,g₁...gₙ)` in precisely that order, with no commutativity used.
- Psi formula: `psi` states evaluation after `iso.inv.f n` equals
  `ρ (x 0)` applied to evaluation at `(x i.castSucc)⁻¹ * x i.succ`.
  These are the successive ratios in the node.
- Degree-zero Phi/Psi: `Fin.partialProd` of the empty tuple is the singleton
  tuple 1, so `phi` gives F(1). The ratio tuple in `psi` is empty, so `psi`
  gives x₀v. These are the node's displayed degree-zero formulas.
- Derived isomorphism: `derived : DerivedCategory.Q.obj B ≅
  DerivedCategory.Q.obj C`; `derived_hom` and `derived_inv` identify its two
  arrows with Q of the actual cochain arrows. This is an isomorphism in the
  abstract derived category, rather than just a family of cohomology isomorphisms.
- Both naturalities: the second theorem simultaneously takes a continuous
  homomorphism `h : H →* J` and a continuous E-linear map `u : V →ₗ[E] W`,
  with `heq : ∀ a v, u (ρ (h a) v) = σ a (u v)`. Its `bMap` and `cMap`
  are chain maps characterized by postcomposition with u and coordinatewise
  precomposition with h. It states both actual-cochain naturality squares and
  both squares for the specified derived arrows. Taking H=J,h=id gives exactly
  coefficient naturality. Taking W=V,u=id and σ=ρ composed with h gives exactly
  restriction along arbitrary continuous group homomorphisms. Conversely these
  two naturalities compose to give the simultaneous form stated here.
- No compactness, discreteness, completeness, separation, dimension, or local
  compactness hypothesis is added. The localized category's
  `[HasDerivedCategory.{r} (ModuleCat E)]` parameter implements the chosen
  morphism-size universe of `def-weil-abstract-derived-category`.
- E,J,V,H,W have separately bound universes u,v,w,v',w'. The complexes have
  a separate ambient carrier universe t. The main theorem uses `max v w t`,
  allowing arbitrary enlargement. For the naturality theorem, choose the common
  ambient universe to dominate v,w,v',w'; no equality between any of these
  carrier universes is required. No variable or universe is auto-bound.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs (the `def-weil-field` Mathlib match),
  read with its full signature and docstring.
- `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.Q`,
  Mathlib.Algebra.Homology.DerivedCategory.Basic, the recorded dependency interface.
  This is the derived category of the abelian category ModuleCat E with its
  integer-indexed cochain localization.
- Mathlib's `CochainComplex`, `ModuleCat`, `LinearMap`, `LinearEquiv`,
  `IsZero`, `Fin.partialProd`, `Fin.contractNth`, and `Fin.succAbove`.
  In particular, the full definitions of partialProd and contractNth were read
  to check cumulative-product order and the sign/index of the final face.

Source read: `literature/stacks-project/etale-cohomology.tex`, lines 9007--9045,
Tag 0DVG. It gives arbitrary topological abelian coefficients and exactly the
inhomogeneous differential, including gv-v in degree zero. The homogeneous
coordinate conversion and naturality are the agent-written calculations already
explicitly designated as such in the node, not attributed as a verbatim Stacks theorem.
The module docstrings carry all twelve proof steps, including cancellation,
continuity, telescoping, signs, both naturalities and localization.

Edge cases checked before and after writing: n=0 (empty tuple, first/last faces,
F(1), x₀v and gv-v); n=1 (first action term, internal negative product term,
positive last term); trivial J (alternating zero/identity differentials agree);
zero V (both spaces and all maps are zero); negative degrees and the boundary
from -1; arbitrary characteristic, including characteristic 2 (the signs are
field scalars, so cancellation still applies); nondiscrete coefficients and
non-locally-compact groups (only finite-product continuity is used). No assertion
about an exponential law or derived category of topological vector spaces occurs.

Searches for existing statements and notions:

- msearch.py leanfinder: “Jointly continuous equivariant homogeneous cochains of
  topological representations are naturally isomorphic to inhomogeneous continuous
  cochains by partial products”. Eight hits, including the old-index
  `ContinuousCohomology.homogeneousCochains` and ordinary algebraic cochain isomorphisms;
  none states the unrestricted jointly continuous result.
- msearch.py loogle: `TopRep.homogeneousCochains`. Twelve hits, including
  `TopRep.homogeneousCochains` and `ContinuousCohomology.cochainsMap`. Read the actual
  Mathlib source: its homogeneous cochains use iterated continuous maps and actions
  continuous separately on the coefficient variable. The module explicitly says
  identification with jointly continuous maps requires a further comparison.
  It does not supply the node's spaces or the unrestricted coordinate theorem.
- msearch.py grep: `homogeneousCochains|inhomogeneousCochainsIso` in
  RepresentationTheory. Hits include the iterated-continuous API and
  `groupCohomology.inhomogeneousCochainsIso`. Read the latter: it concerns all
  functions in Rep, not precisely continuous functions.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id, homogeneous,
  inhomogeneous, jointly continuous, and the new declaration names. The existing
  `Rep.exists_homogeneousCochains_inhomogeneous_coordinates` was read in full:
  it requires compact Hausdorff totally disconnected groups, discrete coefficients
  and open stabilizers, uses iterated maps and locally constant coordinates, and
  does not supply the present unrestricted E-linear derived/naturality statement.
- rg in `dag/lean_names_upstream.json`, Mathlib, WeilConjectures and Sheaf for
  `JointContinuousCochainCoordinates`, `jointContinuousCochainCoordinates`, and
  `exists_jointContinuousCochainCoordinates`: no existing declarations.

No new independent notion or dependency repair is needed: the structure packages
exactly the complexes, coordinate maps, and derived representatives already
introduced by this node itself. The node is changed only in `lean`. There is no
statement correction and no disputed statement.

Validation: the prescribed scompile.py compiled the sandbox file and its library
module against the live published build. Both passed in approximately six seconds;
there were no errors or non-sorry warnings. No global build or direct repository edit
was run. The earlier refusal concerned an unchanged stage-1 packet; this delivery
adds the actual stage-2 module and Lean record.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
