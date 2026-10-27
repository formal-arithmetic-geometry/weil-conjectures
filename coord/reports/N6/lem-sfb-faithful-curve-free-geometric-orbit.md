## Worker report

The module `Sheaf.AlgebraicGeometry.FaithfulCurveFreeGeometricOrbit` states
`AlgebraicGeometry.faithful_curve_free_geometric_orbit` with one postponed theorem.
Its proof is `sorry`; its docstring records all seven DAG proof steps, their
prerequisite nodes, the fixed-scheme construction, the irreducibility induction,
and the distinction between fixed morphisms and fixed underlying points.
The three helper abbreviations have real, fully specified data: the canonical
`Over.pullback` object, the induced `Functor.mapAut` homomorphism composed with
the given action, and `Scheme.Modules.tensorPullback` along `pullback.fst`.
No independent new definition, dependency repair, or statement correction is needed.
The item's statement, source, proof and proof dependencies are unchanged.
The existing landed node `def-sc-finite-locally-free-sheaf` is added to statement
dependencies because the conclusion explicitly uses its variable-rank notion.

Hypotheses and clauses, with the node and module read together:

- Field F: `{F : Type u} [Field F]`. The specified structure morphism
  `f : C ⟶ Spec (.of F)` is appropriate here because the result involves base change
  and automorphisms over that same base.
- Smooth, projective, geometrically integral finite-type curve:
  `[Smooth f] [IsHProjective f] [GeometricallyIntegral f]`,
  `[LocallyOfFiniteType f] [QuasiCompact f]`, and
  `hdim : topologicalKrullDim C = 1`. Geometric integrality includes integrality
  over F itself. Projectivity uses the recorded finite projective-space embedding
  convention, rather than an alternative projective convention.
- A finite group acting by F-automorphisms:
  `{G : Type v} [Group G] [Finite G] (ρ : G →* Aut (Over.mk f))`.
  An automorphism in the over category is exactly an F-automorphism, including
  compatibility with the structure map. Faithfulness is `Function.Injective ρ`.
- Ample invertible module: `(L : C.Modules) [L.IsInvertible]` and
  `hL : Scheme.Modules.IsAmple C L`. This is the recorded Scheme.Modules
  invertibility predicate, not the similarly named general sheaf predicate.
- Every extension E/F: `∀ (E : Type u) [Field E] [Algebra F E]`.
  The first helper is definitionally `pullback f (Spec.map (algebraMap F E))`
  with its second projection to Spec E. The module helper is exactly tensor
  pullback along its first projection, so it denotes L_E.
- Base-changed curve: the first five conjuncts are `Smooth`, `IsProper`,
  `GeometricallyIntegral`, `IsNoetherian`, and `topologicalKrullDim ... = 1`.
  Mathlib's `IsNoetherian` extends `IsLocallyNoetherian` and `CompactSpace`:
  the quasi-compact scheme covered by Noetherian affine spectra in the node.
- Base-changed line bundle: `∃ hInv : (...).IsInvertible, @IsAmple ... hInv`.
  The existential asserts invertibility rather than assuming it, and supplies
  the proof parameter required to type the existing IsAmple definition.
- Every finite locally free module V is coherent:
  `∀ V, V.IsFiniteLocallyFree → RingedSpace.IsCoherent ... V`.
  The recorded `SheafOfModules.IsFiniteLocallyFree` permits locally varying finite
  ranks, including rank zero; it is not restricted to a specified constant rank.
- Every coherent ideal tensored with such V is coherent:
  `∀ I : ...IdealSheafData, IsCoherent ... I.toModules → ∀ V,
  V.IsFiniteLocallyFree → IsCoherent ... (I.toModules ⊗ V)`.
  The actual ideal module `I.toModules` is the canonical kernel of the restriction
  from the structure module to the closed subscheme, not an arbitrary monomorphism.
  On the Noetherian scheme a coherent ideal is quasi-coherent, so the recorded
  IdealSheafData convention represents every ideal the node quantifies over.
- Every algebraic closure Ω/F:
  `∀ (Ω : Type u) [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]`.
  The induced action is exactly `(Over.pullback ...).mapAut ... |>.comp ρ`.
  Its faithfulness is asserted as `Function.Injective` of that homomorphism.
- Nonempty open: `∃ U : ...Opens, Set.Nonempty (U : Set ...) ∧ ...`.
  For every algebraically closed K and `y : Spec K ⟶ D` whose underlying point
  lies in U, `∀ g, g ≠ 1 → y ≫ (ρ_Ω g).hom.left ≠ y`.
  This compares actual scheme morphisms, including their residue maps. It covers
  every geometric point of D in the project's universe convention, without
  assuming it to be Ω-rational or passing only to underlying fixed points.
- Rational closed point in U: `∃ x : Spec Ω ⟶ D`, together with
  `x ≫ D.hom = 𝟙 (Spec Ω)`, membership of its `SpecToEquivOfField` point in U,
  and membership in `closedPoints D`.
- All orbit points distinct: `Function.Injective (fun g ↦ (ρ_Ω g).hom.left point)`.
  This is injectivity of underlying points, rather than merely of point morphisms.
- Trivial group and arbitrary characteristic: no nontriviality or characteristic
  hypotheses occur. The free-open condition is vacuous when G is trivial.

Dependency declarations read and used (module / declaration):

- `Mathlib.Algebra.Field.Defs` / `Field`, and `Mathlib.Algebra.Algebra.Defs` /
  `Algebra`, `algebraMap` (field and extension nodes).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth` / `Smooth`;
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective` / `IsHProjective`;
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` / `GeometricallyIntegral`;
  `Mathlib.AlgebraicGeometry.Properties` / `IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` / `QuasiCompact`;
  `Mathlib.Topology.KrullDimension` / `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible` /
  `Scheme.Modules.IsInvertible`;
  `WeilConjectures.AlgebraicGeometry.Ample` / `Scheme.Modules.IsAmple`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` / its recorded
  `Over.pullback`/`Limits.pullback` convention and first/second projections;
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` / its public
  `Scheme.Modules.tensorPullback`, used for the actual module pullback.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` / its public
  `RingedSpace.IsCoherent` from `WeilConjectures.AlgebraicGeometry.Coherent`.
  This is finite type plus the finite-type-kernel condition, not just the
  similarly named quasi-coherent finite-type conjunction.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` / `AlgebraicClosure`, and
  `Mathlib.FieldTheory.IsAlgClosed.Basic` / `IsAlgClosure`, `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField` / `Scheme.SpecToEquivOfField`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `IsProper`;
  `Mathlib.Topology.JacobsonSpace` / `closedPoints`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree` /
  `SheafOfModules.IsFiniteLocallyFree` (added existing statement dependency).
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` /
  `Scheme.IdealSheafData.toModules` for the canonical ideal module.

All stated proof-dependency modules are imported, with proof-only imports not
marked public. These include ProjectiveImpliesProper,
CurveBaseChangeRelativeDimensionOne, SchemeRelativeAmpleBaseChange,
CoherentFiniteTypeLocallyNoetherian, FieldExtensionFpqcCover,
FpqcMorphismsDescend, DensePoints, and the Mathlib properness, Noetherian,
closed-immersion, separatedness and irreducibility interfaces.

Edge cases checked: the trivial group gives the whole curve as its permissible
free open; rank-zero V and the zero ideal give zero tensor modules; E=F and
all algebraic closures are included; no assumption that the group order is
invertible or that characteristic is zero; the empty scheme is excluded by
geometric integrality and dimension one, exactly as in the node. Universes u
and v are explicitly bound and autoImplicit is false. Field extensions and
geometric test fields use Type u, matching Scheme.{u}, its pullbacks and the
recorded geometric-integrality and SpecToEquivOfField APIs. The declaration is
polymorphic in u and imposes no countability or cardinal bound on the field.

Searches made before writing:

- msearch.py leanfinder: “A faithful finite group action on a smooth projective
  geometrically integral curve has a free geometric orbit”: OK, eight hits in
  Galois category actions and field Galois groups; none states this scheme theorem.
- msearch.py loogle: `AlgebraicGeometry.Scheme, MulAction.stabilizer`: OK, zero hits.
- msearch.py grep: `faithful.*orbit|free.*orbit` in AlgebraicGeometry: OK, zero hits.
- msearch.py leansearch: “A finite group acting faithfully on an integral curve
  has a geometric point with trivial stabilizer”: UNAVAILABLE, curl service error;
  no mathematical verdict inferred from that unavailable service.
- rg in WeilConjectures and Sheaf for faithful/free geometric orbit terminology
  and the node id found only unrelated group-action prose and the parent
  SeparatingPairOpen proof outline; no exact declaration.
- rg of declaration names in dag/lean_names_upstream.json, Mathlib, WeilConjectures,
  and Sheaf found no existing names for the four delivered declarations.
- DAG title/Lean-record search located the already stated variable-rank
  `def-sc-finite-locally-free-sheaf`; reused its declaration rather than
  introducing a second notion. Ideal sheaf and coherence searches located the
  existing IdealSheafData/toModules and RingedSpace.IsCoherent definitions.

Source verification used the local Stacks source: curves.tex
`theorem-curves-rational-maps`, schemes.tex `lemma-where-are-they-equal`,
morphisms.tex `lemma-ample-base-change`, coherent.tex `lemma-coherent-Noetherian`,
and varieties.tex `lemma-smooth-separable-closed-points-dense`.
The node's proof is an agent-assembled consequence of these sources, not a
claim that Tag 0BY1 alone states all these conclusions. No node fault or
STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled the sandbox and library module cleanly,
with no errors and no warnings (7.5 s and 6.2 s). The first compile's ambient
tensor-category and open-set inference issues were repaired with explicit
ambient module and set types before this clean compile.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
