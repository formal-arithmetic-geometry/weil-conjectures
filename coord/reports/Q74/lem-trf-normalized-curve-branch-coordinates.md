## Worker report

The delivery states `AlgebraicGeometry.Scheme.normalized_curve_branch_coordinates` in
`Sheaf.AlgebraicGeometry.NormalizedCurveBranchCoordinates`. The node's natural-language
statement, dependencies, proof, and proof dependencies are unchanged. The theorem has
one `sorry`; the five auxiliary abbreviations/definitions have real data and no proofs
are postponed inside them. No new definition node or dependency repair is needed.

I read the node, every statement dependency's statement and recorded Lean interface
(including the Mathlib matches for the field and algebraic-closure nodes), the actual
normalization and pure-dimension source declarations, the Mathlib definitions, and the
existing normalization-stalk and structural-coefficient constructions. I also checked
the interfaces of recorded proof dependencies. Four proof-only prerequisites have no
Lean record yet: curve-delta-completion-data, normalization-affine-stalk-closure,
nagata-normalization-dvr-branches, and finite-dvr-branch-completion. They are not notions
needed to type this statement. The module imports the recorded proof dependencies
that already have modules, plus the Mathlib modules supplying the remaining recorded
Mathlib proof matches.

Source passages read: `literature/stacks-project/varieties.tex`,
`lemma-prepare-delta-invariant` (Tag 0C1R), especially (3), (6)--(8), and
`lemma-normalization-same-after-completion` (Tag 0C3V); `algebra.tex`,
`lemma-completion-finite-extension` (Tag 07N9), and
`lemma-regular-complete-containing-coefficient-field` (Tag 0C0S), clause (2) and
its proof with prescribed parameters. These give the actual local factors,
completion maps, and the prescribed coefficient field. The final diagonal calculation
is the first-projection calculation in step 7 of the accepted DAG proof.

Hypotheses, clause by clause:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  The k-scheme is `X : Scheme.{u}` with its specified structure map `p`.
- Reducedness is `[IsReduced X]`. Finite type is exactly
  `[LocallyOfFiniteType p] [QuasiCompact p]`, the conjunction specified by the
  finite-type dependency's Lean note. Pure dimension one is `X.IsPureDimension 1`.
  The point is `x : X` with `IsClosed ({x} : Set X)`.
- The normalization and map are the recorded `X.reducedNormalization` and
  `X.fromReducedNormalization`; no abstract replacement is quantified.
- The index type is the actual fibre
  `{y : X.reducedNormalization // X.fromReducedNormalization y = x}`.
  `Finite` and `Nonempty` state precisely that it admits an enumeration by `Fin b`
  with `1 ≤ b < ∞`. Indexing directly by these distinct points avoids choosing or
  changing that enumeration. An enumeration transports the same product equivalence.
- A is literally `X.presheaf.stalk x`. B is the existing
  `normalizationPushforwardStalk X x`, the stalk of the actual pushforward of the
  normalization structure presheaf. Its existing algebra instance is the stalk map
  of the actual structure-sheaf morphism. H and C are the existing
  `normalizationBaseCompletion X x` and `normalizationStalkCompletion X x`.
  The latter uses `normalizationCompletionIdeal X x = m_A.map (algebraMap A B)`;
  its powers are `m_A^n B`, so its completion is exactly the stated inverse limit.
- `normalizedCurveBranchLocalRing X x y` abbreviates the actual stalk at `y.val`;
  `normalizedCurveBranchCompletion X x y` is its maximal-ideal completion Ri.
  These abbreviations reuse Mathlib's stalk and `AdicCompletion`; they are not new
  ring constructions or replacements for existing normalization/completion notions.
- For each Li the conclusion is `IsDomain Li ∧ IsPrincipalIdealRing Li ∧ ¬ IsField Li`.
  The local-ring instance already comes from the actual scheme stalk. For Ri the
  theorem supplies its local-ring structure `hlocal y`, and the same three clauses.
  This spells out exactly the node's definition of DVR (local PID, not a field),
  without requiring any DVR hypotheses on the input curve.
- `IsAdicComplete (maximalIdeal Ri) Ri` gives completeness for the *own* maximal ideal
  of Ri. Explicit `@IsLocalRing.maximalIdeal ... (hlocal y)` terms use the concluded
  local structures and do not add assumptions. Bijectivity of the composite of
  `normalizedCurveBranchCoefficient p x y` with the quotient map Ri → Ri/m_Ri
  identifies the residue field with k by the structural map.
- The coefficient map is the completion algebra map composed with the existing
  `Orgogozo.localScalar (ν ≫ p) y.val`. It uses the structural k-map, not a selected
  abstract isomorphism of residue fields.
- `g : H →+* C` is specified at *every* quotient level by completion of the existing
  A → B map. The ring equivalence `e : C ≃+* ∏ y, Ri` is specified at *every*
  quotient level by `normalizedCurveBranchStalkMap X x y : B →+* Li`.
  This latter map is constructed from Mathlib's stalk equality isomorphism along
  the fibre equation and its `stalkPushforward`; it restricts an actual section germ
  to the actual branch. The formulas uniquely characterize the completed maps,
  since equality in `AdicCompletion` is equality in all quotients. Consequently e
  is exactly the canonical product map, with the H-algebra structures induced by
  these completed local maps; no arbitrary ring map or equivalence is substituted.
- The residue isomorphism `r : A/m_A ≃+* k` is normalized by
  `r (mk _ (Orgogozo.localScalar p x a)) = a` for every a. The theorem supplies
  `hH : IsLocalRing H` and identifies its maximal ideal with the kernel of
  `r ∘ AdicCompletion.evalOneₐ m_A`. Thus the residue expression used below is
  literally the stipulated structural identification `H/m_H = k`.
- The coordinate clause quantifies over *every* family `t y : Ri` with
  `Ideal.span {t y} = maximalIdeal Ri`. It supplies ring equivalences
  `E y : PowerSeries k ≃+* Ri`, maps every constant to the structural coefficient,
  and sends `PowerSeries.X` to `t y`. The ideal-comap equation for every power
  specifies their adic continuity and that of their inverses. Thus these are the
  prescribed evaluation k-algebra isomorphisms, not arbitrary abstract ring
  equivalences. One-variable `PowerSeries k` is the dependency's prescribed
  one-variable convention, equivalent to `MvPowerSeries (Fin 1) k`.
- `normalizedCurveBranchProductCoordinates e E` is constructed explicitly as
  `e.trans (RingEquiv.piCongrRight (fun y ↦ (E y).symm))`. This is the asserted
  identification `C ≃ ∏ y, k[[T_y]]` using those maps.
- For every h and every actual fibre point y, the displayed `PowerSeries.constantCoeff`
  equality gives exactly `r (evalOneₐ m_A h)`, its structural residue. The final
  `Set.range` equality says precisely that the image of H in k to the power of
  the fibre is the range of `a ↦ fun _ ↦ a`, the diagonal copy of k. It includes
  surjectivity onto every diagonal tuple, as well as equality of all coordinates.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (as supplied by the algebraic-closure node's Mathlib match).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension`;
  `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization` and
  `Scheme.fromReducedNormalization`. These are publicly available through the imported
  owning modules, not copied definitions.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `IsAdicComplete`, `AdicCompletion.evalₐ`, `AdicCompletion.evalOneₐ`, and its algebra map.
- `Mathlib.RingTheory.PowerSeries.Basic`: `PowerSeries`, `PowerSeries.C`,
  `PowerSeries.X`, `PowerSeries.constantCoeff`, the existing single-variable interface
  to `Mathlib.RingTheory.MvPowerSeries.Basic`.
- `Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper`: the existing
  `Scheme.normalizationPushforwardStalk`, its structural algebra instance,
  `Scheme.normalizationBaseCompletion`, `Scheme.normalizationCompletionIdeal`,
  and `Scheme.normalizationStalkCompletion` (all source/docstrings read).
- `Sheaf.Paper.OrgogozoInductionData`: `AlgebraicGeometry.Orgogozo.localScalar`,
  the canonical scalar map from the global structural sections and stalk germ.
- `Mathlib.Topology.Sheaves.Stalks`: `TopCat.Presheaf.stalkCongr` and
  `TopCat.Presheaf.stalkPushforward`; `Mathlib.Algebra.Ring.Equiv`:
  `RingEquiv.piCongrRight`, whose explicit pointwise data constructs the product map.

Edge cases checked: an empty curve has no input point x; it is not excluded by an
extra nonempty-scheme assumption. A smooth point has one branch, C = H, and the
constant-coefficient map is onto k. A node has two actual branches with identical
constant coefficients from H. A cusp has one branch but H need not equal C: the
statement asserts a product presentation of C, not smoothness or a presentation of H.
No singularity, separatedness, characteristic-zero, or nodality hypothesis was added.
All finite branch counts are allowed; the nonempty fibre assertion is a conclusion.
The arbitrary choice of each generator is retained, with its structural coefficients.
Every variable and universe is explicit; no `let`, hidden `show`, local notation,
private declaration, axiom, or data-valued `sorry` is used.

Searches actually run for this item, through `msearch.py Q74 <item>`:

- LeanFinder: "The completed normalization of a reduced curve is a product of completed
  local branches with power series coordinates and diagonal residue". Eight hits,
  principally Weierstrass reduction/preparation results; no matching statement.
- Loogle: `AdicCompletion, PowerSeries`. Successful search, zero hits.
- Mathlib grep: `completion.*[Pp]rod|[Pp]rod.*completion|powerSeries.*[Ee]quiv` in
  `RingTheory`. Twenty-five hits including Laurent series, power-series evaluation,
  restricted products and multivariate-power-series renaming. These do not give the
  actual normalized scheme branches or the canonical product with diagonal residues.
- LeanSearch: "The normalization of a reduced finite type algebraic curve has complete
  discrete valuation local branches isomorphic to power series rings, with diagonal
  constant terms". Eight hits: scheme normalization constructors and
  `PowerSeries.instIsDiscreteValuationRing`. These construct normalization or prove the
  *source* series ring is a DVR; they do not state the theorem about the actual branches.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf` (including the trace-formula and algebraic
  geometry directories) for the node id, `normalizedCurveBranch`, branch/completion,
  and normalization completion names. No existing matching declaration. This found
  the normalization-stalk aliases reused above and the previously stated ordinary-point
  delta theorem, which gives a different inequality/equality criterion. It also found
  the prescribed-coordinate theorem reused as a proof import, which applies to a
  general complete regular local ring and does not assemble actual curve branches.
- Checked `dag/lean_names_upstream.json` and both source roots for every new declaration
  name: no collision. The mathematical route's existing general coordinate theorem is
  `IsLocalRing.exists_ringEquiv_regular_complete_coefficients`; its complete signature
  and docstring were read. It is imported, not restated as another general theorem.

Validation: the complete module passed `scompile.py` as both a sandbox module and its
final library module, without errors or warnings. The node's `lean.statement` is copied
verbatim from the final signature. The module/theorem docstrings retain all seven
accepted proof steps. There is no statement dispute or source correction.

## Second reading by Q74

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
