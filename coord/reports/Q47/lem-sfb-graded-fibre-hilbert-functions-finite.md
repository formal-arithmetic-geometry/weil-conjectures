## Worker report

States `AlgebraicGeometry.graded_fibre_hilbert_functions_finite` in
`Sheaf.AlgebraicGeometry.GradedFibreHilbertFunctionsFinite`. Its only postponed
proof is the theorem, with all seven DAG proof steps in its docstring. The real
helper definition `gradedFibreHilbertFunction` computes the complete function from
the canonical module stalk, the canonical residue map, and `Module.finrank`.
There are no new axioms, choices of unspecified objects, or postponed definition
data. Stage 2 proves nothing.

The prior worker's stale-assignment diagnosis confused stage 1 with stage 2.
The Q60 delivery reviewed on 2026-10-22 split the proof and did not attach a Lean
statement; the current item has no `lean` record. This delivery leaves that
reviewed seven-step split and the natural-language statement unchanged.

Clause-by-clause correspondence:

- Noetherian scheme S: `(S : Scheme.{u}) [IsNoetherian S]`. Mathlib's class
  extends exactly `IsLocallyNoetherian S` and `CompactSpace S`, as required by
  the node and the project's convention; it assumes no separatedness or
  nonemptiness.
- Nonnegatively graded algebra and module: `(B L : ℕ → S.Modules)`,
  `(A : GradedSheafAlgebra B)` and `(M : GradedSheafModule A L)` use the
  recorded restriction-compatible unital, commutative, bilinear algebra
  structure and its associative unital module action.
- Quasi-coherent graded algebra: `hB` asserts quasi-coherence of every
  homogeneous piece. This is the homogeneous-family presentation of a
  quasi-coherent direct sum: each piece is a direct summand, and conversely
  sums of quasi-coherent modules on a scheme are quasi-coherent. This is also
  the presentation in the existing consumer `exists_gradedTailRankStratum`.
- Degree zero is the structure sheaf: `hzero : IsIso A.unit`. The given
  structural unit is the canonical identification, not an unrelated isomorphism.
- Coherent degree-one part: `hone : RingedSpace.IsCoherent S.toRingedSpace (B 1)`.
  This is the Stacks kernel/finite-type definition recorded upstream for
  `pqf-def-coherent`, not a new coherence predicate.
- Generated in degree one: `hgen : A.IsGeneratedInDegreeOne`, the published
  local sheaf span of degree-one times degree-n sections. With `hzero` this
  is exactly generation by degree one.
- Quasi-coherent module pieces: `hL` is `∀ d, SheafOfModules.IsQuasicoherent (L d)`.
- Local finite homogeneous generation: `hM : M.IsLocallyFinitelyGenerated`.
  The existing definition chooses finitely many degrees `d : Fin t → ℕ`
  and sections in those degrees near each point. It permits arbitrary shifts,
  local lifting on smaller opens, and an empty family, exactly as required.
- Every piece is coherent: the first conjunct is
  `∀ d, RingedSpace.IsCoherent S.toRingedSpace (L d)`.
- Residue fields and stalk fibres: `gradedFibreHilbertFunction L s d` is
  `Module.finrank (S.residueField s)` of
  `κ(s) ⊗[S.presheaf.stalk s] ((RingedSpace.moduleStalkFunctor
  S.toRingedSpace s).obj (L d))`. The scalar algebra comes literally from
  `(S.residue s).hom.toAlgebra`. The tensor is in extension-of-scalars order;
  the tensor commutor identifies it with the node's `L_d,s ⊗ κ(s)` without
  altering dimensions. Coherence on the locally Noetherian scheme makes
  each stalk finite and hence each fibre finite-dimensional, so `finrank`
  is the ordinary natural dimension here (its infinite-dimensional default
  is never used in this theorem).
- Simultaneous finiteness: `∃ H : Set (ℕ → ℕ), H.Finite ∧ ...` and
  `∀ s, gradedFibreHilbertFunction L s ∈ H`. Thus H consists of whole
  functions and one H works in every degree. It does not merely bound each
  degree separately and does not assert equality of functions or flatness.
- Empty scheme: the final clause `IsEmpty S → H = ∅` explicitly supplies
  the allowed empty set when there are no points; there is no nonempty
  hypothesis on S or on H.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` and
  `IsNoetherian` (the latter bundles the two hypotheses).
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (via `IsNoetherian`).
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`:
  `AlgebraicGeometry.GradedSheafAlgebra`, `GradedSheafModule`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType` is the currently recorded
  interface of `pqf-def-coherent`; its module is imported. The separate
  three notions listed by that node already exist: Mathlib's
  `SheafOfModules.IsQuasicoherent` and `IsFiniteType`, and
  `WeilConjectures.AlgebraicGeometry.Coherent`'s
  `AlgebraicGeometry.RingedSpace.IsCoherent`. We use the exact latter
  definition for coherent pieces, as required by STATE's coherence convention.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.residue`, whose definitions use the quotient of the actual stalk
  by its maximal ideal.
- `Sheaf.AlgebraicGeometry.GradedSheafGeneration`:
  `GradedSheafAlgebra.IsGeneratedInDegreeOne` and
  `GradedSheafModule.IsLocallyFinitelyGenerated`.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`.

The last two definition nodes were already published and reviewed. Their IDs
`def-sfb-graded-sheaf-generation` and `def-pc-module-stalk-functor` are added to
`stmt_deps` under brief-stage2 §5 (existing landed nodes). No dependency node is
changed. All stated proof dependencies are imported non-publicly, including
coherence on locally Noetherian schemes, affine free evaluation and germ
localization, Noetherian ACC and minimal primes, generic freeness, projectivity,
and the finite-projective locally constant rank theorem.

Edge cases checked before writing:

- Empty S: all pointwise generation hypotheses are vacuous, every sheaf on it
  is zero/coherent, and the empty H covers all zero points.
- Zero L / empty module generating family: every fibre function is zero;
  for nonempty S the singleton containing the zero function works.
- `B_1 = 0`: degree-one generation forces all positive algebra pieces zero;
  finite homogeneous generators can still occur in positive degrees, and
  the theorem does not exclude them.
- Generators above d contribute no monomials in degree d; degree zero is included.
- Over S=Spec k[t] the module `(k[t]/t)[x]` has distinct functions at t=0
  and away from t=0. The statement allows both and assumes no base flatness.
- Over a field, positive shifts such as B(-2) give zero dimensions in
  degrees 0 and 1 and the usual dimensions thereafter, so replacing finite
  homogeneous generation by degree-zero generation would lose valid cases.
- Nonreduced bases are allowed; the local ring and residue map retain their
  actual scheme meanings. No characteristic restriction is imposed.

Searches actually run with msearch.py (recorded in searches.jsonl):

- leanfinder: "A finite graded sheaf module over a standard graded algebra on
  a Noetherian scheme has finitely many fibre Hilbert functions". Eight hits,
  including ordinary sheaf generators, Rees finite type, and finite irreducible
  components. None states simultaneous finiteness of all graded fibre functions.
- loogle: "Module.finrank, Set.Finite". Nine hits on dimensions of spans and
  affine spans; none is this theorem.
- grep: "hilbertFunction|HilbertFunction|IsLocallyGenerated" in Mathlib.
  Zero hits from the wrapper. This is recorded as the wrapper's actual result.
- leansearch: "There are finitely many entire Hilbert functions among fibres of
  a finite graded module over a Noetherian base". Eight hits including
  Polynomial.hilbertPoly and finite/Noetherian modules, none matching the claim.
- Direct rg of WeilConjectures and Sheaf for IsLocallyGenerated,
  GeneratedInDegreeOne, graded finite, hilbertFunction/HilbertFunction found
  the existing generation definitions and the graded-tail consumer. The upstream
  `Scheme.Hom.hilbertFunction` is an Euler characteristic of powers of one line
  bundle, a different notion; no duplicate is introduced here.
- Direct rg of WeilConjectures for the item ID found no existing declaration.
  Searching both source trees for the two new declaration names found no clash.
- Read Stacks more-morphisms.tex, lemma-generic-flatness-stratification (0ASY),
  and algebra.tex, lemma-graded-module-fg (00K0), including their proofs.

No statement correction, dependency repair, new node, or disputed statement.
Validation: server single-file compile and required delivery preflight are run
through scompile.py and deliver2.py only; their final outcome is recorded below.

Validation completed: scompile.py passed both sandbox and library checks
(15.0 s and 15.7 s), with no errors or non-sorry warnings. The deliver2.py
--no-push dry run passed server preflight and compilation. Local record inspection
confirmed that only lean and the two added stmt_deps change, that the recorded
signature is verbatim, that no Lean line exceeds 100 characters, and that the
only sorry is the main theorem's proof.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
