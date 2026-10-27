## Worker report

The new module `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineSchubertCurveDegree`
states `AlgebraicGeometry.homogeneousLine_schubertCurve_degree`, with one `sorry`
and no definitions or additional theorem declarations. The original node statement,
statement dependencies, proof, and proof dependencies are unchanged.

The statement is uniform in the simple root and then in the character. In particular,
the same rank-one map and first-column isomorphism work for every character, rather
than choosing unrelated curve parametrizations for different characters.

Clause-by-clause reading:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  All schemes, group schemes and commutative test algebras have universe `u`.
- `G T B : Grp (Over (Spec (.of F)))` are actual group schemes over F.
  `hG : IsSemisimpleGroupScheme G.X` expands to smooth, connected, affine,
  locally finite type and quasi-compact, with every smooth connected solvable
  normal closed subgroup terminal. Solvability is the scheme-theoretic derived series.
- `hsc` says every map from a semisimple group scheme that is surjective and has
  finite central kernel is an isomorphism. Centrality is tested on every
  commutative F-algebra, including nonreduced algebras, with the actual kernel inclusion.
- `iT`, `hT`, `hsplit`, `iB`, `hB`, `j`, `hj` give precisely the split maximal
  torus, Borel, and containment T -> B -> G. The Borel predicate includes closedness,
  smoothness, connectedness, solvability and maximality.
- The instances `IsCommMonObj` supply the commutative character and cocharacter
  lattices. The actions `aG`, `aB` are explicitly pinned to conjugation by `haG`,
  `haB`. `Φ`, `D`, `base`, `hred`, `hroot`, `hpair`, `hΦ`, `hpos` are the
  reduced root datum and positive simple-root base from the Borel-pair dependency:
  the lattices are actual additive Hom groups, the integer pairing is composition
  with power maps, roots are exactly nonzero character weights, and positivity is
  exactly occurrence in Lie(B). These are not differential weights.
- `p : B ⟶ T` and `hp : j ≫ p = 𝟙 T` use the Borel projection. This property
  suffices to characterize that projection: a map B -> T kills the unipotent radical,
  since a unipotent group has no nontrivial torus characters, and B=U⋊T. Thus this
  binder does not choose an arbitrary extension of a character or add a hypothesis
  beyond the supplied canonical projection. There is no second definition of p.
- `Q`, `π`, `hQ`, `hπflat`, `hπsurj`, `hπinv`, `hπtorsor` specify exactly the
  proper finite-type flag quotient and faithfully flat right B-torsor, including its
  scheme-theoretic kernel-pair square `(g,b) ↦ (g,gb)`.
- `RankOneRoots.Weyl iT` is the actual rational normalizer quotient, where normalizing
  is tested after every scalar extension. `act` and `hact` pin its conjugation action;
  `s` and `hs` specify the coroot reflection on every character; `n` and `hn` are
  representatives. The longest cell and w0 are setup in the node, and impose no
  further conditions on this local calculation; they are supplied by the imported
  Bruhat theorem for the same quotient, rather than added as unused binders.
- `∀ α : base.support` is precisely indexing by the simple roots. For each α,
  the conclusion produces `v : RankOneRoots.SL2Hom G`, an actual natural group
  homomorphism on determinant-one matrices over every F-algebra.
- `R`, `iR`, `IsClosedImmersion iR.left`, `IsReduced R.left`, and the exact equality
  of `Set.range iR.left` with the closure of the image of `b ↦ b n_s B` specify
  the reduced scheme-theoretic Schubert curve. A reduced closed immersion with this
  topological image uniquely specifies the reduced closure. This is not just an
  assertion about rational points or an arbitrary abstract curve.
- The first universal matrix clause sends `diag(t,t⁻¹)` to the coroot composed
  with `iT`. Laurent coordinates use the dependency's `multiplicativeValue`,
  including evaluation at the inverse multiplicative-group point.
- The next clause sends all matrices with lower-left entry zero into the actual
  B-subgroup on every algebra. This is exactly v(B2) ⊆ B scheme-theoretically.
- `e : (ProjectiveLine (Spec (.of F))).asOver (Spec (.of F)) ≅ R` is over F.
  The following clause identifies its composite with `iR` and `π v` on every
  matrix over every commutative F-algebra, using `ProjectiveSpace.homOfSections`
  with sections `g[k,0]`. Thus it is the map induced by v under the first-column
  identification SL2/B2 = P1, rather than an unspecified P1 parametrization.
  The existential `h` is the proof required by `homOfSections` that this first
  column generates the unit ideal; determinant one provides it (ad-bc=1).
  No helper proof is silently assumed and no definition contains `sorry`.
- `∀ (lam : RankOneRoots.Character T) (χ : RankOneRoots.Character B),
  χ.hom.hom = (p ≫ lam).hom.hom⁻¹ → ...` is exactly χ=-λp, so the existing
  `AssociatedCharacterLineBundle.Presentation ... χ` has quotient action
  `(g,z)b=(gb,λp(b)z)`. Quantification over every presentation means the result
  applies to the line bundle supplied by the homogeneous-sections dependency and
  is independent of its chosen presentation; that dependency supplies existence.
- The first final conjunct is `Nonempty` of the actual sheaf isomorphism from
  `e^*(iR^* P.L)` to `ProjectiveSpace.twist ... m`, with
  `m = D.toLinearMap (Additive.ofMul lam) (D.coroot α.val)`.
  The coordinate type is `ULift (Fin 2)`, exactly the upstream projective line;
  its twist is the recorded twist, with the dual-tautological sign convention.
- The second final conjunct is the existing `Scheme.Modules.degree` of the
  restricted sheaf on R with the explicit F-structure `⟨R.hom⟩`, equal to the same
  integer pairing. The degree is not moved to an unrelated curve.
- There is no dominance, nonnegativity or characteristic assumption on lam or F.

Dependency declarations read and reused:

- Mathlib `Field` (`Mathlib.Algebra.Field.Defs`) and `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`), as recorded in the two Mathlib leaves.
- `CategoryTheory.GrpObj`/`Grp` from `Mathlib.CategoryTheory.Monoidal.Grp`, with
  their specialization and kernel conventions documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` (the group-scheme node).
- `AlgebraicGeometry.reductive_borel_pair_structure` and
  `semisimpleGroupScheme_isReductive`, module
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`: the exact
  root lattices, Borel predicate, quotient and canonical radical projection.
- `AlgebraicGeometry.bruhat_longest_cell_charts`, module
  `Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts`: actual normalizer
  quotient, representatives and the right quotient conventions.
- `AlgebraicGeometry.RankOneRoots.reductive_rankOne_reflections`, module
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections`, together
  with its publicly imported `RankOneRootInterfaces`: `SL2Hom`, `Weyl`,
  `pointImage`, `Character`, `multiplicativeValue`; no private copies.
- `AlgebraicGeometry.exists_homogeneousLineBundle_sections`, module
  `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections`, and its
  publicly imported `AssociatedCharacterLineBundle.Presentation`: actual quotient
  relation and sheaf of sections, with the correct inverse-character convention.
- `AlgebraicGeometry.Scheme.Modules.degree`, module
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: Euler-characteristic
  difference with the structural map explicitly supplied.
- `AlgebraicGeometry.ProjectiveSpace.twist`, module
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`, and
  `ProjectiveSpace.homOfSections`, module
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections`, give the existing
  projective-line twist and the actual first-column projective map.

The module imports the recorded proof-dependency modules with plain `import`:
StandardParabolicLeviCharts, AffineHomomorphismFlatImage,
CentralIsogenyBorelRootCompatibility, HomogeneousOrbitQuotientGeometry,
BorelRootProductCoordinates, Mathlib's ZariskisMainTheorem, and upstream Cohomology.Serre.
The already public statement imports also supply proof dependencies. The nodes
split-rank-one-classification, regular-cocharacter-borel-description,
split-torus-subgroups-diagonalizable, and multiplicative-isogeny-borel-comparison
had no recorded Lean module at reading time; no invented import was added.

Edge cases checked before drafting and during rereading:

- Empty simple-root support: the outer universal quantifier is vacuous; no
  `Nonempty` instance for that support is required.
- Zero character: χ is trivial, m=0, and both final clauses say O(0) and degree 0.
- m=1: with a0(t) and a1(t⁻¹), the overlap is [[t⁻¹,-1],[0,t]], and the quotient
  gives e0=t⁻¹e1. Dual tautological frames have exactly this transition.
- m=-1 and m≤-2: integer exponents and the existing negative twists retain both
  cases; χ(O(-1))=0 and χ(O(m))=m+1 give degree m. No positivity is inserted.
- Characteristic two: central kernels and subgroup membership are tested on
  nonreduced algebras too; no division by 2 or use of Lie differentials replaces
  character data. Signs in matrix identities remain valid in characteristic two.
- Test algebras need not be fields or reduced. Their determinant-one first columns
  generate the unit ideal, even where neither entry is a global unit.
- R is a proper reduced curve by its F-isomorphism with P1; its F-structure is
  retained by `e`. The existence conclusion rules out an empty replacement curve.

Searches performed with the prescribed msearch.py wrapper:

- LeanFinder: `homogeneous line bundle degree on a simple Schubert curve equals
  character coroot pairing` returned eight root-system/Lie-algebra hits, including
  RootPairing.Base.height and LieAlgebra.IsKilling.apply_coroot_eq_cast; no exact
  statement and no algebraic-group line-bundle construction.
- Loogle: `AlgebraicGeometry.Scheme.Modules.degree, ProjectiveSpectrum,
  SpecialLinearGroup` returned zero hits and an unknown identifier for the
  project-local degree definition. Its recorded upstream source was read directly.
- Mathlib grep: `Schubert|schubert|homogeneous.*[Dd]egree` returned 25 unrelated
  homogeneous-polynomial and Proj hits, no Schubert statement.
- LeanSearch: `degree of homogeneous line bundles on Schubert curves` returned
  eight graded-polynomial/localization hits, no match.
- `rg` of both project libraries for `Schubert|schubert|firstColumn|first.column|
  projectiveLine|SL2Hom|IsSimplyConnected` found the existing SL2 matrix interface,
  semisimplicity and gallery statement; none states this coroot-degree result.
  The node-id search in WeilConjectures returned no match. The final declaration
  name was searched in both libraries and was absent.
- `tools/blueprint_refs.py search 'Schubert curve'` and direct latest-blueprint
  searches found no independent duplicate of this statement. No new notion or
  definition node is needed.

Source reading: opened the primary author-hosted Brion--Kumar PDF,
https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf, Section 2.1 (printed
pp.62--63, equation (7)) and 2.2, plus local Milne Theorem 21.11 and paragraph
21.24 (pdftotext). The current blueprint direct-image proof (3) was read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.
It is the ancestor route, not a replacement definition for the rank-one calculation.
The theorem docstring carries all nine proof steps and the dependency ids.

No statement correction, dependency repair, new node, or statement dispute.
The server scompile.py check passed for both its sandbox and library module modes;
only the expected postponed theorem is present. Every variable and universe is
explicitly bound, `autoImplicit false` is set, and all Lean lines are at most 100 characters.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
