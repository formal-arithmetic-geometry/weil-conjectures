## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianDenseOpenSpreading` states
`AlgebraicGeometry.exists_abelianScheme_denseOpen`, with its sole proof `sorry`.
There are no new definitions or helper theorems. The existing group-object and
base-change constructions supply all data. The node changes only in `lean`.

Hypotheses and clauses, checked against the unchanged node:

- D is a Dedekind domain in the node's explicitly dimension-one convention:
  `(D : Type u) [CommRing D] [IsDedekindDomain D] (_hD : ringKrullDim D = 1)`.
  Mathlib's class supplies Noetherianity, integral closedness, and the domain
  condition, but only dimension at most one; `_hD` imposes exactly one.
- E is its fraction field: `(E : Type u) [Field E] [Algebra D E]
  [IsFractionRing D E]`. No choice of a particular representation is imposed.
- S is Spec D: `Spec (CommRingCat.of D)` is written directly throughout.
- A/E is an abelian variety: `(A : Over (Spec (CommRingCat.of E)))
  [GrpObj A] [IsAbelianVariety A]`. The recorded definition intentionally keeps
  the group structure separate from properness, smoothness and connectedness.
- The open subscheme is `U : (Spec (CommRingCat.of D)).Opens`, with associated
  scheme `U.toScheme` and canonical open inclusion `U.ι`.
- Nonemptiness is `(U : Set (Spec (CommRingCat.of D))).Nonempty`.
- Containing the generic point is `genericPoint (Spec (CommRingCat.of D)) ∈ U`.
  The domain makes Spec D irreducible, so this also makes U dense.
- The generic point map factors through U by the existential `j`, constrained
  by `j ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap D E))`. This is the
  canonical factorization, unique since an open immersion is a monomorphism;
  it is not an unconstrained extra map or a new hypothesis.
- The U-group scheme is `B : Grp (Over U.toScheme)`. The existing `GrpObj`
  data includes multiplication, inverse, unit, associativity, and both unit
  and inverse diagrams, in the category of U-schemes.
- Smooth and proper mean `Smooth B.X.hom ∧ IsProper B.X.hom`.
- Commutative means `IsCommMonObj B.X`, whose defining equality is
  `(β_ B.X B.X).hom ≫ μ = μ`: multiplication is invariant under interchange.
- Connected fibres means `∀ s : U.toScheme, ConnectedSpace (B.X.hom.fiber s)`.
  These are scheme-theoretic fibres over residue fields, not geometric point
  sets. Geometric connectedness is not imposed as an extra conclusion.
- The generic-fibre isomorphism of E-group schemes is
  `Nonempty (((Over.pullback j).mapGrp.obj B) ≅ Grp.mk A)`.
  `mapGrp` transports group operations by the canonical product-preserving
  pullback functor. An isomorphism in `Grp (Over (Spec (.of E)))` has maps over
  Spec E preserving the group operations in both directions.
- The node's phrase “abelian scheme” names exactly the smooth proper
  commutative group scheme with connected fibres just listed. No second
  predicate is introduced. Its explanation of separatedness is the existing
  `IsSeparated.isClosedImmersion_diagonal`, inherited from `IsProper`.

Dependency declarations read and used:

- `def-pc-scheme`, `def-weil-affine-spectrum`:
  `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `def-pc-base-change`:
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, whose module
  docstring explicitly identifies scheme base change with `Over.pullback`,
  object `pullback` and projections `pullback.fst`/`pullback.snd`. Its
  `Scheme.Hom.geometricFiberAt` and module-pullback helpers are unnecessary
  for the ordinary scheme-theoretic fibres used here.
- `def-sbc-smooth-morphisms`:
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, used through properness/separatedness.
- `def-sc-abelian-variety`:
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety` (proper, smooth, connected).
- `def-weil-proper-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  with the existing separatedness and universal-closedness interfaces.
- Existing constructions: `Scheme.Opens.toScheme`, `Scheme.Opens.ι`,
  `Scheme.Hom.fiber`; `CategoryTheory.Grp`, `GrpObj`, `IsCommMonObj`,
  `CategoryTheory.Functor.mapGrp` and `Over.pullback`. The relevant
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` module provides the
  product-preserving pullback functor and its group base change.

All recorded, stated proof-dependency modules are imported privately:
`WeilConjectures.RingTheory.LocalizationColimitPrincipalLocalizations`,
`WeilConjectures.AlgebraicGeometry.LimitAffineTransition`,
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
`Mathlib.RingTheory.FiniteStability`,
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic`,
`WeilConjectures.AlgebraicGeometry.GenericGeometricallyConnectedSpread`,
`Sheaf.AlgebraicGeometry.DescendSmoothQcqs`, and
`WeilConjectures.AlgebraicGeometry.EventuallyProper`.
The scheme-conventions node fixes conventions only and has no module of its own.
The complete seven-step DAG proof is included in the theorem docstring.

Source checked directly: BLR §1.4, printed pp.19–20 (PDF pp.25–26), the paragraph
before Theorem 3 and its proof, in the primary-source scan named by the node:
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf
The paragraph states extension over a dense open and explains descent by limit
arguments; the proof spreads a smooth proper model. No statement correction is
needed. No disputed statement or dependency fault was found.

Edge cases checked before writing: the zero-dimensional abelian variety
(trivial group) is allowed; no dimension or characteristic restriction is
imposed on A or E. The empty open is explicitly excluded; Spec D is nonempty
because D is a domain. Fields as D are excluded exactly as the node demands
by the dimension-one equality, not merely by Mathlib's Dedekind class. U may
be all of S, allowing everywhere good reduction. Every residue-field fibre
is tested, including the generic fibre. Group morphisms, rather than bare
scheme isomorphisms, preserve the specified original group structure.
All universes and variables are explicit and `autoImplicit` is false.

Searches made (all via the prescribed msearch wrapper unless stated):

- LeanFinder: “An abelian variety over a fraction field spreads to a smooth
  proper commutative group scheme with connected fibres on a dense open
  subset of a Dedekind scheme”. Eight hits concern Weierstrass integral
  models/good reduction; none states this result.
- Loogle: `IsAbelianVariety, IsDedekindDomain`. No hits; remote service reports
  unknown identifier `IsAbelianVariety`.
- Mathlib grep: `AbelianScheme|abelian.*spreading|IsDedekindDomain` in
  `AlgebraicGeometry`. Three hits are imports/open commands in elliptic-curve
  files, no matching general spreading result.
- LeanSearch: “abelian variety extends to abelian scheme over dense open”.
  Eight hits concern rational maps and dense open restrictions, no match.
- Direct rg in project `lean/WeilConjectures` and `lean/Sheaf`:
  `IsAbelianScheme|abelian.*[Ss]pread|exists.*abelian.*open|` followed by
  the item id; and `abelian.*spread|spreading.*abelian|dense.open.*abelian`.
  Only the unrelated finite abelian-group etale torsor spreading comment
  matches. Direct grep for the exact item id in WeilConjectures finds none.
- Direct source inspection finds the existing `Grp`, `GrpObj`, `mapGrp`,
  `Over.pullback`, and commutativity interfaces, so none is copied.

Validation: scompile.py compiled the module both as a sandbox module and at
its library module path, cleanly. The final delivery is also validated by
scompile.py and the prescribed deliver2.py dry run.

## Second reading by Q97

A separate self-review pass reopened the node and the Lean signature; no
other agent was started, as required by the dispatcher. The maintainer's
independent review remains the independent reading of this delivery.
The comparison above covers every hypothesis and conclusion clause.
Particular checks: `IsAbelianVariety` is paired with `GrpObj`; dimension one
is explicit; the canonical map j has its required composite; group base change
uses the existing `mapGrp`, and the final isomorphism belongs to the category
of group objects over E. Properness includes the required closed diagonal.
Ordinary connected fibres match the node without silently strengthening it
to geometric connectedness. No mismatch or additional node was needed.
