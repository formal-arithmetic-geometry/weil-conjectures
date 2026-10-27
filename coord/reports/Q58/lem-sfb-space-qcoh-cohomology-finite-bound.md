## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceQCohCohomologyFiniteBound` states
`AlgebraicGeometry.AlgebraicSpace.exists_qcoh_cohomology_finite_bound`, with its sole
proof `sorry`. Source: Stacks Project, spaces-cohomology.tex, Tag 072C,
`lemma-vanishing-quasi-separated` (read statement and proof). The module docstring
contains all five steps of the node's proof. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
and its direct-images proof were read; this is a supporting ordinary-sheaf input,
not a change to the unit statement or route.

Clause-by-clause correspondence:

- The size convention is explicit `universe u`, `Scheme.{u}`, the original module
  section universe `u`, and the existing `SmallEtaleModel` of the small étale site.
  `set_option autoImplicit false` forbids implicit undeclared variables.
- A scheme S and an algebraic space X over S are `{S : Scheme.{u}} (X : AlgebraicSpace S)`.
- Quasi-compactness of |X| is `[CompactSpace (Point X.obj.obj)]`, with the existing
  final/atlas topology from `AlgebraicSpacePointTopology`.
- Absolute quasi-separatedness is `(hqs : X.IsAbsolutelyQuasiSeparated)`. This is
  the recorded affine-test criterion equivalent to the absolute diagonal being
  quasi-compact (Stacks 0AHR); no quasi-separatedness assumption is imposed on S.
- One integer C at least 1 is `∃ C : ℤ, 1 ≤ C ∧ ...`. This precedes the quantifiers
  over M and q, so C depends only on X, not on M or its presentation.
- Every quasi-coherent O_X-module is `(M : X.QCoh)`, the existing full subcategory
  for Mathlib `SheafOfModules.IsQuasicoherent`. This includes arbitrary coproduct
  presentations and imposes no finite generation.
- All integer degrees q at least C are `(q : ℤ), C ≤ q → ...`. Since C ≥ 1,
  q is nonnegative and `q.toNat` is exactly that degree, without discarding any case.
- The underlying abelian sheaf is obtained by `SheafOfModules.toSheaf` after
  `X.smallModuleRestriction.obj M.obj`. This is restriction of the given module
  to the existing affine basis, with its actual regular-function rings and no lift.
- H^q is `((Sheaf.Γ X.smallEtaleModelTopology AddCommGrpCat.{u}).rightDerived
  q.toNat).obj ...`, precisely Mathlib's injective-resolution right derived functor
  from the recorded def-sp-left-exact-additive dependency. Vanishing is `IsZero`
  on this abelian-group object.
- Global sections are the right adjoint to the constant sheaf functor (`Sheaf.Γ`),
  canonically the compatible-family limit (`Sheaf.isLimitConeΓ`); no terminal
  object of the site is required or assumed. Computing on the existing affine
  basis is the size-convention presentation of the same étale topos. Restriction
  preserves sheaf sections, injectives and their resolutions, so this is the
  cohomology of M_ab on X_et, not a module-cohomology substitute.
- There is no Noetherian, dimension, finite-type or finite-generation binder.

Dependency declarations used and read with their signatures/docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `etaleTopology`, `structureSheaf`, `Modules` and the representability
  predicates, using the fppf sheaf and actual étale scheme charts.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`; this is used through `Modules` and QCoh.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh` and the existing slice instances;
  Mathlib `SheafOfModules.IsQuasicoherent` is the local presentation predicate.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `CategoryTheory.Functor.rightDerived`;
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj` identifies it with the
  homology after applying the functor to any injective resolution.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `CategoryTheory.Injective`, `CategoryTheory.InjectiveResolution` (the N-indexed
  injective cochain complex and its degree-zero quasi-isomorphism).
- Added existing landed definition dependency `def-sfb-space-small-ringed-model`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`, with
  `SmallEtaleModel`, `smallEtaleModelTopology`, `smallStructureRings`,
  `smallModuleRestriction`, `smallModuleEquivalence`. This supplies the existing
  equivalent small-site presentation, rather than any new definition or size binder.
- Added existing landed definition dependency `def-sfb-space-absolute-quasi-separated`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`,
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`.
- Proof dependencies with recorded interfaces are already public through the
  above imports (`def-a1-space-point-topology`, quasi-coherent modules), or imported
  plainly (`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`). The atlas, fibre-bound, distinct-tuples,
  alternating-spectral-sequence, separated-quotient and separated-space-bound
  theorem nodes currently have no Lean records and hence no modules to import.
  They are not needed to type the statement and are retained unchanged in proof_deps.

Edge cases checked before writing: the empty space permits C=1 and every cohomology
object is zero; the zero module is included; affine spaces permit C=1, so degree
zero is correctly excluded; q=C is included; negative q cannot satisfy C≤q with
C≥1; arbitrary and infinitely generated modules are included. The base S is
arbitrary, including non-quasi-separated bases. There is no characteristic
restriction or bound on Krull dimension. The chosen small affine model retains
module carriers in universe u and has a genuinely small index category, so its
sheafification, compatible-family global sections, Grothendieck abelianness and
enough injectives are inferred without added hypotheses.

Searches performed (2026-10-24):

- `msearch.py ... leansearch "Quasi coherent sheaves on a quasi compact quasi separated
  algebraic space have uniformly bounded higher cohomology"`: eight hits for the
  quasi-coherent local-presentation structures, no uniform vanishing theorem.
- `msearch.py ... leanfinder` with the same query: eight hits, including
  `exists_of_res_zero_of_qcqs_of_top`, section restriction and quasi-coherent
  presentation results; none states this cohomological bound.
- `msearch.py ... loogle '"cohomology", "QuasiCompact"'`: zero hits.
- `msearch.py ... grep 'AlgebraicSpace|quasi.?coherent.*(vanish|bound)|cohomolog.*dimension'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` over `lean/WeilConjectures` for the item id and the candidate declaration:
  no matching theorem. Searches for finite cohomology gave unrelated finiteness
  and Poincare-duality results, not this ordinary quasi-coherent vanishing bound.
- `rg` over `lean/Sheaf` for algebraic-space cohomology/global-sections and qcqs
  declarations found the existing `AlgebraicSpaceGlobalSectionsAmplitude` (an
  unbounded derived amplitude consequence citing this item), H1 affine-base-change
  statements (different), and the small ringed model and absolute qs definitions
  reused here. No declaration states this item's ordinary-sheaf theorem.

No statement correction, new node, dependency repair or disputed statement.
Only the item's lean record and its two added landed definition dependencies change.
Server scompile.py validated both sandbox and library module modes in about three
seconds each, with no errors or warnings beyond permitted sorry handling.

## Second reading by Q58

Self-audit of the node against the final file: the bound precedes M, absolute qs is
used rather than relative qs, every integer q≥C is included via q.toNat, and the
coefficient is the underlying abelian sheaf of the actual restricted module.
The small affine basis is the existing recorded topos model, not an extra
hypothesis; `rightDerived` uses injectives in abelian sheaves, not module sheaves.
No mismatch was found. No independent worker was started, in accordance with the
dispatcher brief; the maintainer's independent review remains the independent reading.
