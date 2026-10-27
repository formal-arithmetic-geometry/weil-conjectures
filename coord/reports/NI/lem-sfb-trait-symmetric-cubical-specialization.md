## Worker report

The module `Sheaf.AlgebraicGeometry.TraitSymmetricCubicalSpecialization` states
`AlgebraicGeometry.trait_symmetric_cubical_specialization`, with its sole proof
`sorry`. The node's natural-language statement and all its other fields are
unchanged. No new notions, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- The DVR is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. The Mathlib class means a local principal ideal
  domain that is not a field; this is the dependency's exact convention.
- The arbitrary fraction field is `(K : Type u) [Field K] [Algebra R K]
  [IsFractionRing R K]`. Its canonical inclusion is `algebraMap R K`.
  `Spec (.of R)` is T. The special field is the actual quotient
  `IsLocalRing.ResidueField R`, reached by `IsLocalRing.residue R`.
- `H : Grp (Over (Spec (.of R)))` supplies the scheme, its structure morphism
  `H.X.hom`, and its multiplication, inverse and identity as morphisms over T
  satisfying the group identities. `[IsCommMonObj H.X]` supplies commutativity.
- `[Smooth H.X.hom]` is smoothness; `[IsSeparated H.X.hom]` means the diagonal
  is a closed immersion. `[LocallyOfFinitePresentation H.X.hom]` and
  `[QuasiCompact H.X.hom]` express finite presentation. Quasi-separatedness
  follows already from separatedness, so no additional hypothesis is needed.
- `hH : HasSemiabelianGeometricFibres H` is the dependency's exact fppf extension
  condition on all geometric fibres, including split-torus rank zero.
- `B : CubicalRigidifiedLine H.X` supplies the invertible module `B.line`, its
  proof `B.invertible`, identity rigidification, nowhere-vanishing cube section,
  and the permutation, identity-slice normalization and cube cocycle laws.
  These data are not replaced by an arbitrary line or an unconstrained map.
- `B.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))` is the given
  cubical line restricted to H_K. The dependency constructs the underlying
  group using `Over.pullback`, whose scheme is the actual fibre product.
  Its line is the tensor inverse image along the first projection. `hample`
  applies the existing `Scheme.Modules.IsAmple` to this line, explicitly passing
  its existing `.invertible` proof rather than adding an invertibility assumption.
- `hsymmetric` is `Nonempty` of an isomorphism from the tensor pullback of this
  generic line along the generic group's `GrpObj.inv` (its underlying scheme
  morphism `.left`) to the same line. Thus it means exactly iota_K^*B_K ≅ B_K.
  It does not demand that this isomorphism preserve cubical rigidifications,
  extend over T, or be supplied as distinguished data.
- The conclusion is the existing `Scheme.Modules.IsAmple` on the line of
  `B.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))`.
  This is B_k on H_k, again using the existing base-change invertibility proof.
- There are no completeness, henselianity, excellence, algebraic-closedness,
  residue-characteristic, or generic-properness hypotheses. Rings, fields and
  schemes share the ambient size universe, as in the dependency interfaces;
  it is arbitrary and can be enlarged simultaneously. No test-scheme universe
  has been independently shrunk.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`:
  `AlgebraicGeometry.HasSemiabelianGeometricFibres`.
- `Sheaf.AlgebraicGeometry.CubicalRigidifiedLine`:
  `AlgebraicGeometry.CubicalRigidifiedLine`, `CubicalRigidifiedLine.baseChange`,
  and `CubicalLine.baseChangedGroup` with its actual pulled-back group structure.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  the recorded section-normalized tensor-pullback interface, and
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` from its upstream public import
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. Its object is explicitly
  O_X tensor over inverse-image O_Y with inverse-image M, followed by sheafification.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, the quasi-compact positive-power
  affine-section-neighbourhood criterion.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`
  (the dependency is a Mathlib leaf and correctly has no `lean` record).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`, used by
  the dependency's `Over.pullback` construction.
- The existing Mathlib `GrpObj.inv` is used on the induced generic group, and
  `IsSeparated` is the existing diagonal-closed-immersion predicate.

Plain imports include every recorded proof-dependency module, and the Mathlib
modules of the matching leaves (DVR dimension, qcqs permanence, separatedness,
proper/smooth base change, affine spectra, and generating sections). The currently
unstated proof nodes `lem-sfb-regular-scheme-affine-line-section-cover`,
`lem-sfb-trait-primitive-section-specialization`, and
`lem-sfb-semiabelian-effective-square-generation` have no module to import yet.
The declaration docstring carries all seven accepted proof steps with the
corresponding dependencies, and accurately identifies the original supporting
lemma as agent-formulated; it does not pretend the WANTED originals were read.

Edge cases checked before stating:

- A field is excluded precisely by the DVR dependency's non-field axiom.
- Rank-zero tori, trivial groups and zero-dimensional fibres remain allowed.
  The identity section precludes an empty fibre over either field.
- Arbitrary residue characteristic and non-algebraically-closed K and k are
  retained. No properness condition excludes toric or other nonproper fibres.
- The actual residue quotient is used; no algebraic closure, completion or
  strict henselization replaces it. The generic symmetry is only an existence
  of a line isomorphism, exactly as stated.
- No positive tensor exponent is fixed in this theorem: the existing ample
  predicate quantifies over positive powers individually at each point.

Searches made using the prescribed launcher wrapper:

- `leanfinder`: "A symmetric cubical line on a smooth semiabelian group over a
  discrete valuation ring with ample generic fibre has ample special fibre".
  Eight hits concerned Weierstrass good reduction/minimality, Proj valuative
  existence, affine space or valuative-square domain/field data; none states
  ampleness specialization of a cubical line.
- `loogle`: `"IsAmple", "special"`; zero hits.
- `leansearch`: "Symmetric cubical invertible sheaf generically ample on a
  semiabelian scheme over a DVR is ample on the closed fibre". Eight hits give
  scheme module/sheaf/stalk infrastructure and no specialization theorem.
- `grep`: `ample.*special|cubical.*ample|trait.*ample` in Mathlib's
  `AlgebraicGeometry`; zero hits.
- Direct `rg` with `trait.*(ample|cubical)|symmetric_cubical|cubical.*special` in
  both `lean/WeilConjectures` and `lean/Sheaf` found no match. Direct `grep -rn`
  for this node id in `lean/WeilConjectures` also found none. The dependency
  records and full relevant source signatures/docstrings were read directly.

Validation: the delivered file compiled in both sandbox and library module modes
through `scompile.py NI lem-sfb-trait-symmetric-cubical-specialization`, cleanly
in 3.1 and 3.2 seconds. Auto-implicit and relaxed auto-implicit binding are both
explicitly disabled. No definitions or additional postponed theorems are introduced.
No statement dispute or node fault was found.

## Second reading by NI

Independent second reading (maintainer cc review service, 2026-10-24) of the delivery at
7aae9dcf. The first worker's own re-check (self-audit) has been replaced by this reading.

Node clauses and their Lean rendering:

1. R is a DVR with fraction field K and residue field k = R/m_R: `(R : Type u) [CommRing R]
   [IsDomain R] [IsDiscreteValuationRing R]` (the Mathlib leaf of def-sc-discrete-valuation-ring),
   `(K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]`. k is the actual
   `IsLocalRing.ResidueField R`, reached through `IsLocalRing.residue R`. Exact.
2. T = Spec R: `Spec (.of R)`. Exact.
3. p : H → T is a commutative group scheme over T: `H : Grp (Over (Spec (.of R)))` with
   `[IsCommMonObj H.X]`. Addition, inverse and identity are Over-morphisms and the group laws hold. Exact.
4. Smooth, separated (diagonal closed immersion) and of finite presentation: `[Smooth H.X.hom]`,
   `[IsSeparated H.X.hom]`, `[LocallyOfFinitePresentation H.X.hom]`, `[QuasiCompact H.X.hom]`.
   Quasi-separatedness follows from separatedness, so nothing stronger is assumed. Exact.
5. Semiabelian geometric fibres: `HasSemiabelianGeometricFibres H` (def-sfb-semiabelian-geometric-fibres;
   it quantifies over all algebraically closed k : Type u and all s. The torus has rank r ∈ ℕ and r = 0 is
   allowed). Exact.
6. (B, r, τ) is a cubical rigidified line: `B : CubicalRigidifiedLine H.X` (def-sfb-cubical-rigidified-line).
   Its fields are line, invertible, rigidification, sectionIso and compatible. The CommGrpObj instance comes
   from H.grp and IsCommMonObj. Exact.
7. B_K and B_k are tensor inverse images on H ×_T Spec K and H ×_T Spec k:
   `B.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))` and the same with
   `IsLocalRing.residue R`. In the dependency, `baseChange` = `pullbackOver` along the Over.pullback counit,
   and its line is `(tensorPullback h.left).obj B.line`. The group is
   `CubicalLine.baseChangedGroup g H.X = (Over.pullback g).obj H.X`, the actual fibre product (def-pc-fibre-product).
   Exact.
8. B_K is ample: `@Scheme.Modules.IsAmple _ B_K.line B_K.invertible`. This uses the IsInvertible proof the
   dependency itself supplies and adds no invertibility hypothesis. IsAmple (def-weil-pbc-ample-invertible-module)
   is CompactSpace ∧ ∀ x ∃ n > 0 with an affine nonvanishing neighbourhood. Exact.
9. Symmetric, ι_K^*B_K ≃ B_K: `Nonempty ((tensorPullback (GrpObj.inv (X := baseChangedGroup …)).left).obj
   B_K.line ≅ B_K.line)`. The inverse is the induced generic group inverse (instance
   `baseChangedGroup_grpObj` = Over.pullback mapGrp). The node asks for a bare isomorphism of lines,
   with no compatibility with the rigidification, so `Nonempty` is the right strength. Exact.
10. Conclusion, B_k ample on H_k: `@Scheme.Modules.IsAmple _ B_k.line B_k.invertible`. Exact.
11. No completeness, henselianity, excellence, algebraic closedness or properness is assumed:
    the signature has none of these. Exact.

Edge cases: K may be any fraction field. k may have any characteristic and need not be perfect or
algebraically closed. Torus rank 0 (abelian fibres) and the trivial group are allowed, and a nonproper
generic fibre is allowed. A field is excluded only by the DVR's maximalIdeal ≠ ⊥, as the node requires.
Universe: one ambient u for R, K and the schemes, the same convention as the dependencies. The residue field
is in Type u. No universe is shrunk.

Records: the item node in the snapshot differs from the live node only in its new `lean` record. The
record's `lean.statement` is the file's signature verbatim, without ` := by`. Each stmt_dep resolves to the
declaration used: Mathlib leaves for scheme, smooth, LFP, fibre product and DVR; recorded modules for
HasSemiabelianGeometricFibres, CubicalRigidifiedLine, tensorPullback, IsInvertible and IsAmple. All
imported proof-dependency modules exist.

Duplicate search: rg `trait_symmetric_cubical|lem-sfb-trait-symmetric-cubical-specialization` in the live
and side-live lean trees found no hits. The worker's leanfinder, loogle, leansearch and grep searches found
no Mathlib statement.

Gates: one theorem, proved only by `sorry`. The module and declaration docstrings carry the source place
and `(blueprint: …)`, and the declaration docstring has all seven proof steps. autoImplicit is off, there are
no new definitions, and there is no pro-étale substitute. No mismatch was found in the Lean, so the Lean is
unchanged.
