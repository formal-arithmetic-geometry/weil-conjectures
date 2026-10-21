## Worker report

Recorded existing upstream declarations in `WeilConjectures.Compactification.ValuativeCriterion`:

- `AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion_of_isDominant` (lines 590–593).
- `AlgebraicGeometry.IsSeparated.of_valuativeCriterion_of_isDominant` (lines 601–604).
- `AlgebraicGeometry.IsProper.of_valuativeCriterion_of_isDominant` (lines 646–648).

The local source and the current server source returned by
`scompile.py --source WeilConjectures.Compactification.ValuativeCriterion` agree on these
signatures and on `ValuativeCriterion.RelativeTo`. The node's `lean.statement` is the first
signature verbatim. The `lean.declarations` list includes every conclusion of the node.
No module is added: these are the exact existing results, not ordinary valuative criteria
requiring every generic point of W to factor through D. The blueprint unit was read at
`literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/sk-lem-nagata-sketch-dense-valuative/_section.md`;
it states these three conclusions and cites Stacks 0894.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

1. The node's D, W, S are `{U X S : Scheme.{u}}`, respectively, with arbitrary universe `u`;
   its f and h are `(f : X ⟶ S)` and `(h : U ⟶ X)`. No scheme is required to be reduced,
   affine, Noetherian, nonempty, or quasi-compact.
2. Quasi-compact h is exactly `[QuasiCompact h]` in each declaration.
3. Dense topological image is `[IsDominant h]`: the class has precisely the field
   `denseRange : DenseRange h` in Mathlib's `Morphisms.UnderlyingMap`.
4. The entire lifting assumption is `(H : ValuativeCriterion.RelativeTo f h)`.
   Its definition quantifies over `(sq : ValuativeCommSq f)` and
   `(ηU : Spec (CommRingCat.of sq.K) ⟶ U)` with `ηU ≫ h = sq.i₁`.
   The square packages an arbitrary valuation domain `sq.R`, its fraction field `sq.K`,
   the generic leg `sq.i₁`, the base leg `sq.i₂`, and their commutativity over S.
   Specifically it has `[CommRing sq.R] [IsDomain sq.R] [ValuationRing sq.R]`,
   `[Field sq.K] [Algebra sq.R sq.K] [IsFractionRing sq.R sq.K]`.
   Mathlib's `ValuationRing` says divisibility is total, equivalent for a domain to
   the node's fraction-field membership condition (see `ValuationRing.isFractionRing_iff`).
   Thus putting `sq.i₁ = ηU ≫ h` is exactly the node's arbitrary u and a with fhu=a|K.
5. The conclusion `Nonempty (Unique sq.commSq.LiftStruct)` in `RelativeTo` expresses
   existence and uniqueness of the lift b. `CommSq.LiftStruct` contains exactly a morphism
   `l : Spec (CommRingCat.of sq.R) ⟶ X` with
   `Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁`
   and `l ≫ f = sq.i₂`. These are exactly b|K=hu and fb=a; equality of proof fields
   introduces no extra data. The same module's `RelativeTo.existsUnique` and
   `RelativeTo.of_existsUnique` display both directions of this equivalence explicitly.
6. First conclusion: `[QuasiCompact f]` gives `UniversallyClosed f` by the first
   recorded theorem. It imposes no quasi-separatedness or finite-type hypothesis on f.
7. Second conclusion: `[QuasiSeparated f]` gives `IsSeparated f` by the second theorem.
   Crucially this theorem does not assume `[QuasiCompact f]`.
8. Third conclusion: `[QuasiCompact f] [LocallyOfFiniteType f] [QuasiSeparated f]`
   gives `IsProper f` by the third theorem. The first two assumptions together are
   precisely finite type in the dependency's recorded interface. Universal closedness
   itself implies quasi-compactness, so Mathlib's properness definition agrees with
   the node's separated, finite-type, universally-closed definition.
9. A dense quasi-compact open immersion is included by taking h to be its inclusion:
   the three declarations accept every quasi-compact dominant morphism, hence this
   special case with no extra condition. The node's last sentence introduces no further
   conclusion or additional hypothesis on the general h.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  its morphisms `Scheme.Hom`.
- `def-weil-affine-spectrum`: the same module, `AlgebraicGeometry.Spec` and `Spec.map`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, together with `QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`; finite type is their conjunction.
- `def-weil-quasi-separated-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated`, meaning the diagonal is quasi-compact.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, with `IsSeparated` from `Morphisms.Separated`
  and `UniversallyClosed` from `Morphisms.UniversallyClosed`.

Edge cases checked before recording: empty W forces empty D and gives the usual proper
empty morphism; empty D cannot be dense in nonempty W. Identity h is admitted. A field
as its own valuation ring is admitted. The zero ring is excluded precisely because a
valuation ring in the node is a domain. Nonreduced schemes are admitted. No finite-rank
or discrete valuation restriction occurs. The separatedness clause retains the case of
non-quasi-compact f. All schemes, valuation rings, and fraction fields use the same
arbitrary universe u, matching Mathlib's valuative criterion and allowing residue-field
and valuation probes at that size; there is no independently smaller testing universe.
A quasi-compact open immersion need not have globally quasi-compact domain, and no such
condition is imposed here.

Searches performed on 2026-10-21:

- `msearch.py ... leanfinder "A quasi compact morphism tested on valuation diagrams with
  generic point through a quasi compact dense source is universally closed, and if quasi
  separated it is separated and finite type implies proper"`: eight hits, including the
  ordinary Mathlib universal-closedness and properness criteria; these alone are not the
  dense-source result.
- `msearch.py ... leansearch "Dense source valuative criterion: a quasi compact dominant
  source suffices to test universal closedness, separatedness, and properness"`: eight
  hits, including ordinary valuative criteria and `dominant_eq_topologically`.
- `msearch.py ... loogle "AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion,
  AlgebraicGeometry.IsSeparated.of_valuativeCriterion"`: successful search, zero hits.
- `msearch.py ... grep "of_valuativeCriterion|RelativeTo" AlgebraicGeometry`: five hits
  in Mathlib's `AlgebraicGeometry.ValuativeCriterion`, all ordinary criteria.
- `rg -n "of_valuativeCriterion_of_isDominant|dense.*[Vv]aluative|[Vv]aluative.*[Dd]ense"`
  over `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib: exact matches in upstream
  `Compactification/ValuativeCriterion.lean`, including all three recorded theorems.
  Sheaf references are consumers of the node, not duplicate statements.
- `rg -n "sk-lem-nagata-sketch-dense-valuative" lean/WeilConjectures`: the properness
  theorem's docstring explicitly names this node (line 642).
- Opened the full signatures and docstrings of all five statement dependencies, the
  three matching upstream theorems, `RelativeTo`, `ValuativeCommSq`, `LiftStruct`,
  `IsDominant`, and `ValuationRing` to check their semantics rather than their names.

No new nodes, dependency repairs, statement correction, or statement dispute is needed.
No new proof or sorry is introduced. Existing upstream proofs are reused unchanged.
The prescribed dry run performs a server-side #check of all three recorded declarations
through scompile.py, then the maintainer's preflight. Validation results are recorded below.

Validation: `deliver2.py NQ sk-lem-nagata-sketch-dense-valuative --no-push` returned
`OK (dry run): commit 80c2f030d47 passes the preflight and compiles; nothing pushed`.
The server checked all three existing declarations without errors or warnings.
Preflight requires the historical branch label `slopmaster2` for every WeilConjectures
module; the record uses that label, with live-server source confirmation described above.

## Second reading by NQ

No second reading by a worker: this dispatcher-started worker delivers directly, and the
maintainer's independent review is the only independent review, as specified by the brief.
