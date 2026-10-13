## What changed

Repaired E2 of reviewer X-3eef1 using the proposed Lean replacements.
`determinant_split_comparison_restriction` now takes a natural linear family d₀
and pointwise equality d=d₀, and is proved by substituting that equality into hn.
The false arbitrary-tuple generator hypothesis and disputed comment are removed.
The local construction remains reduced to the two separate linear construction
and local bijectivity theorems, with its original signature unchanged.

Forced adaptation of `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison`:
retain hn from `determinant_split_linear_maps_exists`, obtain the chart from
`determinant_split_linear_maps_locally_bijective`, and convert the same maps to
linear equivalences. Their wedge formula is unchanged by definitional equality;
the corrected restriction theorem transfers their retained naturality.
The caller's existing signature, visibility, docstring and public imports stay
identical. Added only the two proof-only imports required by this construction.
Updated both the restriction node and the caller's proof route to match the Lean.
All four delivered modules compile without errors or warnings through lcompile.py.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_local`
(node `new-determinant-split-local`): one original hole closed by decomposition
into the two strictly separate obligations below. Its combining proof is complete.

`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction`
(node `new-determinant-split-restriction`): the false original interface is corrected;
the replacement is proved outright by substitution and has no sorry. This is a
statement correction, not a proof of the old false statement.

`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_exists`
(node `lem-sc-determinant-split-comparison`): forced adapted proof is complete;
it retains exactly the original statement and adds no hole.

Exactly two remaining holes, both introduced by the original decomposition:
`AlgebraicGeometry.Scheme.Modules.determinant_split_linear_maps_exists`
(node `lem-sc-split-determinant-linear-maps`) and
`AlgebraicGeometry.Scheme.Modules.determinant_split_linear_maps_locally_bijective`
(node `lem-sc-split-determinant-linear-bijective`). Their statements and proofs in
words are unchanged by this repair. No new hole is added during the repair.
The item's module contains no sorry; neither does the adapted caller.
No data definition or arbitrary witness construction is introduced: the natural
linear family is uniquely determined. Do not count removal of the false statement
as a proof of it; the local determinant result remains a decomposition.

## No longer needed

No imports or modules removed. All original public imports support the statements.
The item's two new proof-only imports are used in its local construction.
The forced caller retains the existing imports to restrict the adaptation to the
forced lines. Its route no longer uses `new-determinant-split-local`: it needs to
retain naturality before conversion, which that theorem's conclusion discards.
Its proof_deps now lists the two linear-family nodes and the restriction node.
The local node is retained as the item's first declaration, not imported elsewhere
for its proof by the adapted caller. No unit route is bypassed:
`sk-thm-picard-rr.realized` has empty statement and step lists.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery left a false sorry merely marked disputed. That did not meet
the requirement that every remaining sorry be true. The old restriction theorem
allowed arbitrary c without lift or restriction compatibility. On Spec(Q[t])
with V=X, A=0, B=C=O_X, f=0, g=id and ranks (0,1,1), let d_X=id,
d_W=2 id for every proper subopen, and c_W(b)=d_W(b). Its wedge formula holds,
but restriction to D(t) maps d_X(1) to 1 while d_D(t)(1)=2. The repair replaces
that false interface by the exact natural-family transfer lemma the caller needs.
This replacement is valid for all ranks, empty opens, zero rings, and regardless
of supplied nonlinear lifts: its proof uses only pointwise equality and naturality.
The caller's former proof discarded the naturality supplied by the linear
construction; the adapted proof retains it. No target or definition is altered.

## New nodes

No new nodes during this repair. The two previously added nodes remain:
`lem-sc-split-determinant-linear-maps`, unique natural linear wedge maps on a split
open without invertibility or a quotient-rank hypothesis; and
`lem-sc-split-determinant-linear-bijective`, local bijectivity of given maps with
the wedge formula. They are strictly separate parts of the determinant argument.
Each has its own module, source, complete proof in words, and recorded searches.
Change record: `coord/changes/determinant_split_comparison_restriction.md`.

## Statement corrected

`new-determinant-split-restriction`: replace arbitrary c and its generator equation
by a natural linear family d₀ and pointwise equality d=d₀. The statement_change
records the counterexample and the original statement/proof. Its only DAG citer,
`lem-sc-determinant-split-comparison`, keeps its statement unchanged; its proof is
adapted to retain hn, and its node now records the actual three-step route.

## Forced adaptations

`Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison` is unclaimed in the
current snapshot. Original against corrected dependencies fails as follows:

```
DeterminantSplitComparison.lean:93:4: error: Application type mismatch: The argument
  fun W hW b j ↦ l W ⋯ ?m.420
has type
  (W : X.Opens) → (hW : W ≤ V) → (b : ?m.421 W hW) → ?m.422 W hW b → ↑(S.X₂.val.obj (op W))
but is expected to have type
  (W : X.Opens) →
    W ≤ V →
      ↑((S.X₁.exteriorSheaf r₁ ⊗ S.X₃.exteriorSheaf r₃).val.obj (op W)) →ₗ[↑(X.presheaf.obj (op W))]
        ↑((S.X₂.exteriorSheaf r₂).val.obj (op W))
in the application
  determinant_split_comparison_restriction S r₁ r₂ r₃ hr V d fun W hW b j ↦ l W (LE.le.trans hW hVU) ?m.420
DeterminantSplitComparison.lean:93:40: error: Function expected at
  b
but this term has type
  ?m.421 W hW

Note: Expected a function because this term is being applied to the argument
  j
DeterminantSplitComparison.lean:95:13: error: Application type mismatch: The argument
  hW
has type
  X.Opens
of sort `Type v` but is expected to have type
  W ≤ V
of sort `Prop` in the application
  hd W hW

(with the modules compiled into /home/ubuntu/weil-sandbox/V1/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal/scratchpad/counterfactual/.lbuild) [4.1 s]
[exit code 1: NOT compiled]

```

The adapted module compiles without warnings. Proof-only import lines 14–15 make
the construction and bijectivity declarations available. Proof lines 90–105
replace the old call using a tuple family by construction from d₀, retaining hn,
converting its bijective restrictions, then supplying hn and rfl to the corrected
restriction theorem. The old local result cannot supply these new hypotheses:
it discards naturality. This replacement is necessary to preserve the caller's
unchanged wedge formula and restriction conclusion. No extra caller edits occur.

## Second reading by V1

1. Compared both existing modules with the repository using diff and the declaration
   signature parser. The local construction's entire signature is byte-for-byte
   unchanged; the caller's signature, visibility, docstring and existing imports
   are unchanged. The only changed existing signature is the restriction theorem,
   explicitly covered by the change record and statement_change. Rechecked its
   counterexample: ranks (0,1,1), identity quotient on Spec(Q[t]), identity on X
   and multiplication by 2 on D(t); the arbitrary c absorbs the change in the
   wedge formula but restriction of 1 disagrees. The new hn and hd transfer lemma
   is true by substitution. No target or definition changes. Verdict: pass with
   the recorded statement correction, not a proof of the false old statement.

2. Independently compiled all four modules in import order with lcompile.py;
   no errors or warnings. Searched all delivered Lean for sorry and forbidden
   declarations: exactly the two reported named theorems have `:= by sorry`,
   and no data definitions or prohibited declarations are added. Appended
   #print axioms for all five declarations in scratch copies and compiled them:
   restriction uses only propext, Classical.choice, Quot.sound; local construction,
   caller, and both split lemmas additionally use sorryAx. No other axiom appears.
   The selected natural family is specified uniquely, and no public definition
   chooses an arbitrary witness. Verdict: complete combining proofs, two open
   obligations; no claim of a sorry-free determinant result.

3. Read both split statements and their complete docstring arguments. The linear
   construction assumes rank only on A and produces a unique natural family,
   without invertibility. The other lemma takes existing maps with a wedge
   formula, assumes rank also on C, and proves local bijectivity without assuming
   naturality. These are separate obligations, not the original equivalence
   statement under another name. For lift independence, hf and hg identify the
   difference with a first-summand image; expanding the wedge gives r+1 such
   entries, precisely the cited rank-wedge-zero assertion. For uniqueness one
   must use local representatives and separatedness, not global generation on
   arbitrary opens. For bijectivity, shrink to a common free chart; all its
   subopens inherit bases and the sheafification units are bijective there.
   Checked r=0, s=0, both zero, empty U, empty subopens and zero scalar rings:
   empty wedges are the degree-zero units and no nonzero-ring argument is used.
   Independently searched LeanFinder for canonical natural exterior multiplication
   on direct sums of sheaves, Loogle for exteriorPower/prod, and grep for
   exterior/biproduct/direct-sum and determinant/naturality/bijectivity, plus
   rg in lean/Sheaf, lean/WeilConjectures and the upstream WeilConjectures tree.
   Results were module exterior functors and the known sectionwise topDirectSum;
   none supplies either asserted sheaf-level result. Verdict: true and strictly
   separate decomposition; neither hole has a short existing replacement.

4. Read the proofs top down: construction produces hd and hn; bijectivity supplies
   hbij on V; ofBijective preserves the forward function; hd is reused verbatim;
   the caller retains hn and uses the corrected transfer lemma with rfl.
   This is the shortest available combining route. The two new imports are
   proof-only and both are used. Existing public imports support signature
   notions. The caller's old proof-only top-direct-sum import is retained because
   pruning it would exceed the forced adaptation. The old caller proof dependency
   new-determinant-split-local is explicitly reported as no longer used; the
   item's own old proof_deps were empty. No delivered module is pruned.
   Opened sk-thm-picard-rr.json: realized.statement is empty and realized.steps
   is [[]]; no realized unit step is bypassed. Verdict: pass.

5. Compared node fields against the repository and Lean. Local proof_deps are the
   construction and bijectivity nodes; restriction has no proof dependencies;
   the caller has those two plus restriction, matching its actual applications.
   Existing changes are limited to proof metadata and the recorded restriction
   interface correction. New nodes have source, chapter/unit, creation record,
   blueprint ancestry, search records, Lean module/file/declaration and verbatim
   signature, status split and complete proof plans. Read the cited wedge-map,
   local-free-comparison, restriction-isomorphism, rank-wedge-zero and
   topDirectSum statements: none is itself either new lemma. The restriction
   isomorphism alone does not assert a section formula; the construction's
   docstring correctly calls for the canonical sheafified identifications,
   whose compatibility must be proved in closing that hole, not inferred from
   an arbitrary witness of the isomorphism theorem. The cited blueprint markdown
   is not present in this machine's read-only literature directory, so I checked
   the available node statements, unit record and Lean docstrings rather than
   claiming to have reopened that missing source. Verdict: nodes match the
   delivery; the two lower proofs remain to be formalized.

Second reading changed only this report: added independent signature, mathematical,
search, compilation and axiom evidence, and clarified the canonical restriction
comparison obligation. No Lean proof or signature needed further repair. The local
hole is closed by a two-hole decomposition; the old restriction hole is retired by
correction and is not counted as a proof of its old statement. There is no net
hole-reduction claim and no module-pruning claim.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison
Original against changed dependencies failed:
```
/tmp/forced-adaptation-m_5lfjkg/lean/Sheaf/AlgebraicGeometry/Modules/DeterminantSplitComparison.lean:93:4: error: Application type mismatch: The argument
  fun W hW b j ↦ l W ⋯ ?m.420
has type
  (W : X.Opens) → (hW : W ≤ V) → (b : ?m.421 W hW) → ?m.422 W hW b → ↑(S.X₂.val.obj (op W))
but is expected to have type
  (W : X.Opens) →
    W ≤ V →
      ↑((S.X₁.exteriorSheaf r₁ ⊗ S.X₃.exteriorSheaf r₃).val.obj (op W)) →ₗ[↑(X.presheaf.obj (op W))]
        ↑((S.X₂.exteriorSheaf r₂).val.obj (op W))
in the application
  determinant_split_comparison_restriction S r₁ r₂ r₃ hr V d fun W hW b j ↦ l W (LE.le.trans hW hVU) ?m.420
/tmp/forced-adaptation-m_5lfjkg/lean/Sheaf/AlgebraicGeometry/Modules/DeterminantSplitComparison.lean:93:40: error: Function expected at
  b
but this term has type
  ?m.421 W hW

Note: Expected a function because this term is being applied to the argument
  j
/tmp/forced-adaptation-m_5lfjkg/lean/Sheaf/AlgebraicGeometry/Modules/DeterminantSplitComparison.lean:95:13: error: Application type mismatch: The argument
  hW
has type
  X.Opens
of sort `Type v` but is expected to have type
  W ≤ V
of sort `Prop` in the application
  hd W hW

(with the modules compiled into /tmp/forced-adaptation-m_5lfjkg/.lbuild) [3.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
