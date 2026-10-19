## Worker report

The module `Sheaf.AlgebraicTopology.NormalizedHornDisk` states
`AlgebraicTopology.NormalizedSimplex.normalized_horn_disk`, with its sole proof `sorry`.
The five construction helpers have real data. There is no statement correction, new node,
or dependency repair.

The previous attempt confused Q79's reviewed stage-1 split with a stage-2 statement.
The current node has no Lean record. Q79's split, statement, proof and review are preserved;
this delivery adds only the Lean record and its new statement module.

Hypotheses and clauses, matched individually:

- The arbitrary commutative coefficient ring is `(Λ : Type u) [CommRing Λ]`; no nontriviality,
  characteristic or field hypothesis is imposed.
- Every dimension at least one is represented uniquely by `(n : ℕ)` with actual dimension
  `n + 1`; `(k : Fin (n + 2))` covers precisely `0 ≤ k ≤ n + 1`, including outer horns.
- `d : DiagonalData Λ` names the string model furnished by the already stated dependency
  `exists_diagonalData`. The theorem is uniform over all such realizations; no special
  choice of model, normalization or extra existence assumption is required.
- The degreewise free simplicial module is postcomposition by `ModuleCat.free Λ` using
  `Functor.whiskeringRight`; `normalizedFreeChains` then applies `normalizedMooreComplex`.
  Thus both objects and all simplicial operators are the actual free constructions.
- `hornChains Λ n k` is `K`, using `(SSet.horn (n + 1) k).toSSet`;
  `simplexChains Λ n` is `B`, using `SSet.stdSimplex.obj ⦋n + 1⦌`.
  `hornInclusion` applies that functor to the actual horn subset inclusion `.ι`.
- `hornDisk Λ n` uses Mathlib's `HomologicalComplex.double` on the identity of
  `ModuleCat.of Λ Λ`, in degrees `n + 1` and `n`, zero elsewhere. This is the specified
  identity-differential disk, with no arbitrary-map input or data choice.
- The existential comparison `e : simplexChains Λ n ≅ d.P.obj ⦋n + 1⦌` is pinned down by
  its formula on every degree and normalized element. The ambient normalized subobject
  arrow yields the finite combination of simplex strings; `.sum` discards noninjective
  strings and retains each injective string with its original coefficient. This is exactly
  the dependency's natural quotient-normalization comparison in the actual free-module
  presentation, including Mathlib's `ULift` presentation of standard simplices.
- `IsSplitMono (hornInclusion Λ n k)` states the split monomorphism of complexes.
- `∃ φ : hornChains Λ n k ⊞ hornDisk Λ n ≅ simplexChains Λ n, biprod.inl ≫ φ.hom = ...`
  gives the required direct-sum isomorphism with the specified restriction on `K`.
- In each degree the range of `(hornInclusion Λ n k) ≫ e.hom` equals the span of the
  `d.basisP` vectors indexed by strict strings omitting some vertex `j ≠ k`.
  By the explicit Stacks horn description these are exactly all strict strings except
  the top string and the omitted face. The equality is degreewise for a chain map,
  so it identifies the whole subcomplex, not just an abstract isomorphic module.
- `cokernel (hornInclusion Λ n k)` is the chain quotient `B/iK`.
  Its top-degree basis `bTop : Module.Basis Unit Λ ...` is normalized by the image of
  `d.basisP ... (OrderIso.refl _).toOrderEmbedding` through `e.inv` and the actual cokernel projection.
  Its bottom-degree basis `bFace` is normalized in the same way by
  `Fin.succAboveOrderEmb k`, the strict string deleting vertex `k`.
  These equations specify the actual two classes as free generators.
- `∀ r, r ≠ n + 1 → r ≠ n → IsZero ...` makes all remaining quotient terms zero.
  The displayed equation for the quotient differential on `bTop ()` is
  `((-1 : Λ) ^ k.val) • bFace ()`. Since both relevant terms have these bases and all
  other terms vanish, it specifies the entire quotient differential with its original sign.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.NormalizedSimplexChainDiagonal`:
  `AlgebraicTopology.NormalizedSimplex.String`, `DiagonalData`, its `P` and `basisP`,
  and `exists_diagonalData`. Read the full structure, comparison formula, naturality,
  theorem and proof docstring.
- `Mathlib.AlgebraicTopology.DoldKan.Equivalence`:
  `CategoryTheory.Abelian.DoldKan.equivalence` (the dependency's `mathlib_match`), whose
  functor is `normalizedMooreComplex`. Read `N`, `Γ`, the equivalence and inverse theorem,
  and `NormalizedMooreComplex.objX`, `objD`, `obj` and `map` in MooreComplex.lean.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: its module documentation explicitly
  uses Mathlib's `SSet`, `stdSimplex` and `horn`; the only notions from this dependency
  required here are precisely those Mathlib primitives. Read the recorded `coneCategory`
  declaration and surrounding construction, while importing its module as required.
- Mathlib's `ModuleCat.free` and `HomologicalComplex.double` implement the free module
  and identity disk directly. `HomologicalComplexAbelian` supplies actual chain cokernels.

Edge cases checked before drafting: dimension one (`n = 0`) for both `k = 0, 1` has
one retained vertex, one omitted vertex and the edge; the sign is respectively `+1,-1`.
The omitted face has degree zero and zero outgoing differential. In dimension two all
three choices of `k` remove just the top triangle and the specified edge. Arbitrary
zero divisors and characteristic two cause no change: the splitting uses only
`((-1)^k)^2 = 1`, not a field hypothesis. The zero ring is included: rank-one free modules
and their singleton bases are still legitimate over the zero ring, with all elements zero.
The `n+1` indexing excludes exactly dimension zero, which the node excludes. Coefficients
and simplicial sets share the arbitrary universe `u`; no finite-type or nonempty condition
is imposed on simplicial sets in the free functor.

Searches for an existing declaration:

- `msearch.py`, LeanFinder: “Normalized free module chains of a simplicial horn split off a
  two term disk complex from simplex chains” returned eight horn-definition/inclusion hits,
  including `SSet.horn`, `SSet.horn.ι`, `SSet.horn.face` and horn multicoequalizer data.
  None states the normalized free-chain splitting or its signed quotient description.
- `msearch.py`, Loogle: `"horn", "chain"` returned zero hits.
- `msearch.py`, Mathlib grep under AlgebraicTopology:
  `horn.*(normal|disk)|(normal|disk).*horn` returned zero hits.
- `rg` of the project and upstream source for `NormalizedHorn`, `normalizedHorn`,
  `horn.*disk`, `horn.*Disk`, and the exact item id found no existing declaration;
  the project hits concerning geometric disk pairs have different objects.
- Source inspection of Horn.lean established the exact omitted-vertex predicate;
  inspection of MooreComplex.lean and DoldKan/Equivalence.lean established the kernel
  normalization convention. Searches for disk constructions found Mathlib's Double.lean,
  which is reused rather than reimplemented.

No STATEMENT-DISPUTED issue remains. All postponed mathematical content is the one named
theorem, with the complete five-step DAG argument in its docstring.

Validation: `scompile.py Q07 lem-cbc-normalized-horn-disk` compiled the delivered file
cleanly, both as the sandbox module and under its final library module name; no warnings.
The final-name compile took 10.1 seconds within the per-file 60-second limit.

## Second reading by Q07

Independent maintainer second reading, 2026-10-17, of immutable delivery
`1a872e760f25f61c1a3dbaea199055290ec392e1`. The reader did not author this
delivery or its earlier readings. This section records the maintainer reading
under the required group heading; it does not attribute that reading to the worker.

I read the packet, item JSON and five proof steps, every statement dependency,
the delivered module and all six declarations, their docstrings, and this report.
I followed check-brief2.md, coord/brief-stage2.md and delivery-errors.md section H.
The mathematical statement passes clause by clause:

- Coefficients: `(Λ : Type u) [CommRing Λ]` is exactly an arbitrary commutative
  ring. No field, nontriviality, characteristic, finiteness or projectivity
  hypothesis is added.
- Dimension and horn: `(n : ℕ) (k : Fin (n + 2))` represents every positive
  dimension as `n + 1`, with every inner and outer horn index. The underlying
  simplicial set and horn are Mathlib's actual standard simplex and subcomplex.
- Free modules and normalization: `normalizedFreeChains` postcomposes by
  `ModuleCat.free Λ`, then applies `normalizedMooreComplex`. `hornChains`,
  `simplexChains` and `hornInclusion` therefore give exactly the node's K, B and
  induced inclusion, including the operators. No arbitrary map is substituted.
- Disk: `hornDisk` is `HomologicalComplex.double` of the identity on Λ, in
  degrees `n + 1` and `n`. Its other terms and differentials vanish. The `rfl`
  only supplies the definitional chain-shape relation; it proves no local lemma.
- Model: `d : DiagonalData Λ` uses the recorded simplex dependency. I read all
  its fields, especially `basisP`, `boundary`, `operatorsF`, `mapF`, `q` and
  `quotient_formula`, and `exists_diagonalData`. Existence is already the cited
  theorem's conclusion. Uniformity in the presentation is legitimate: its
  bases and operator equations canonically identify F with the actual free
  module presentation. The formula for e transports the dependency comparison
  through that identification, including the standard simplex's ULift.
- Splitting: `IsSplitMono (hornInclusion Λ n k)` asserts a retraction in the
  category of complexes. The existential biproduct isomorphism φ and equation
  `biprod.inl ≫ φ.hom = hornInclusion Λ n k` assert precisely the stipulated
  direct-sum decomposition with its restriction.
- Horn span: the degreewise range equality uses the strict-string basis and
  `∃ j, j ≠ k ∧ j ∉ Set.range σ`. A strict string violates this condition
  precisely when it is the top string or the face omitting k. Since the map is
  a chain map, these equalities identify the subcomplex, not just its ranks.
- Quotient: the cokernel is the chain quotient. Singleton module bases in the
  two degrees, with equations specifying the images of the identity string
  and `Fin.succAboveOrderEmb k` through e.inv and the actual cokernel projection,
  give precisely the two named classes. `IsZero` applies to ModuleCat objects
  in all other degrees. The last equation gives the differential coefficient
  `(-1 : Λ)^k.val`, with no rescaling of the specified classes.

Source and dependency checks: in the read-only Q07 clone, simplicial.tex
5674–5685 describes the horn as containing all nondegenerate simplices except
these two; 2028–2057 gives the abelian normalized splitting; 3899–3915 describes
the degenerate subcomplex; 4045 onward states Dold–Kan. The tag table identifies
08NU, 017V, 0FKI and 019G with those labels. Stacks uses the opposite-end kernel
convention; Mathlib MooreComplex.lean:64–83,116–140,156–158 and
DoldKan/Equivalence.lean:142–171 confirm the explicitly recorded positive-face,
d_0 convention actually used here. In NormalizedSimplexChainDiagonal.lean I
read String, delete, front, back, the full DiagonalData and its existence
statement and proof docstring. EnhancedDiagramsCones.lean explicitly reuses
Mathlib's SSet/stdSimplex/horn; I also inspected its recorded coneCategory and
comma construction. Mathlib Horn.lean:27–64, StdSimplex.lean:39,67,142,
ModuleCat/Adjunctions.lean:40–42, Homology/Double.lean:35–83 and
HomologicalComplexAbelian.lean confirm the exact constructions used.

Edge cases: for simplex dimension one (Lean n = 0), k = 0 retains vertex 0,
the missing face is vertex 1 and the quotient differential is +1; k = 1
retains vertex 1, the missing face is vertex 0 and the coefficient is -1.
The bottom degree is zero, with zero outgoing differential. In dimension two,
each of the three choices removes exactly the triangle and the designated edge.
Degrees above the simplex dimension have no strict strings. Characteristic two,
zero divisors and the zero ring are allowed: the inverse splitting needs only
((-1)^k)^2 = 1, and singleton bases over the zero ring are valid. Universe u is
arbitrary; the relevant finite simplex and horn can be lifted into it. There
is no equality between independent site/coefficient universes and no site
hypothesis. Dimension zero is excluded exactly as in the node.

I independently searched Mathlib/AlgebraicTopology, upstream WeilConjectures
and Q07 lean/Sheaf for normalized horn, horn chains/disks/splittings and the
helper names. No existing theorem duplicates the complete statement. I read
Mathlib SimplicialSet/Homology/Basic.lean and Nondegenerate.lean: the former
uses the unnormalized alternating complex, the latter the nondegenerate
coproduct model. Neither is the positive-face-kernel functor constructed here
by composition of existing free and normalization functors. The worker also
records semantic, Loogle and grep searches. No primitive is reimplemented.

The module has source/blueprint docstrings for every declaration and all five
DAG proof steps in the theorem docstring. All definitions contain real data;
the sole theorem proof is `sorry`. Both implicit-variable options are false,
the sole universe u is bound, and no line exceeds 100 characters. I extracted
the complete theorem signature and checked literal equality with lean.statement.
No new nodes, dependency repair, statement correction or citer audit is needed.
There is no pro-etale substitute or unrecorded independent prerequisite.

Compiler reproduction: ran only
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q07 lem-cbc-normalized-horn-disk snapshot/lean/Sheaf/AlgebraicTopology/NormalizedHornDisk.lean`
from the immutable review directory. Exit code 0; sandbox
Sheaf/Stage2/Sandbox0.lean passed in 1.8 s and final library module
Sheaf/AlgebraicTopology/NormalizedHornDisk.lean passed in 2.1 s, with no
warnings or errors. The wrapper currently delegates to the server private side
overlay and returns its compiler output. I made no direct SSH call and ran no
lake build, global build, delivery, merge, Git mutation or live Lean write.
The worker's historical 10.1 s timing is a report claim; the successful runs
above are the independently reproduced evidence.

Finding and repair: the original second-reading section only said no worker
second reading occurred. That is not a real reading (H11 and the substantive
report requirement in H1). I preserved the Worker report verbatim and replaced
that placeholder with this independent reading. No Lean or JSON changes were
necessary. This complete report is supplied as
`fixes/lem-cbc-normalized-horn-disk.report.md`, the report-replacement form
accepted by merge_delivery.py --stage 2. Verdict: FIX, report only.
