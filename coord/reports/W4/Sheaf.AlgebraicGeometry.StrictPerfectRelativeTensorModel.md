## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorModel
with a compiling construction and reduction. T is explicitly the scalar restriction
of Tot(L tensor G|_U), defined in StrictPerfectRelativeTensorComplex without any
unproved data choice. The private helper relativeTensorComplex_bound proves its
[a+c,b+d] support bound by the total coproduct universal property, tensor zero
preservation and integer arithmetic. The existing bounded-above flat K-flat theorem
supplies K-flatness. Two independent named statements supply relative term flatness
and the roof comparison. No existing statement or target signature changed.

The public import of OpenKFlatTensorHomologyComparison was replaced by the existing
proved zero-map restriction theorem in RhomIntoKInjectiveLocal, registered locally.
The former homology comparison is a later calculation and is not used to construct
this model. Change record: coord/changes/strictPerfectRelativeTensorModel-imports.md.
The sole direct caller separately imports the removed module and needs no adaptation.

## Proved and sorry left

Closed AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_model
(lem-pc-strict-perfect-relative-tensor-model), by decomposition, not a complete
axiom-free proof of the mathematical result. One upper hole closed and two lower
holes added: net -1. No sorry remains in the item or the explicit construction.

The two new holes, each the whole proof of a public named theorem, are:

- AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_terms_flat
  (lem-pc-strict-perfect-relative-tensor-terms-flat), in
  Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorTermsFlat.
- AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_roof
  (lem-pc-strict-perfect-relative-tensor-roof), in
  Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorRoof.

The flatness statement has no derived category data or model-comparison conclusion.
The roof statement has no relative flatness hypotheses, prescribed degree interval,
or base-ring K-flatness conclusion. Both concern the fixed constructed tensor,
so neither is a renamed existence-of-bounded-model statement. The real combining
proof establishes support, supplies the upper bound to the existing K-flat result,
and assembles the independent roof witnesses.

## No longer needed

Removed import: Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison;
lem-pc-open-kflat-tensor-homology-comparison is not needed by this model theorem.
It remains needed and separately imported by StrictPerfectTensorRelativeTorBound;
no global pruning of that module is claimed.

The direct caller separately imports OpenKFlatTensorHomologyComparison; no caller
source edit is proposed. The second reading checks its unchanged source imports.

The original aggregate lem-pc-kflat-closure / KFlatTelescopeClosure is replaced by
its needed bounded-above flat-complex part,
lem-pc-bounded-above-flat-kflat-site / BoundedAboveFlatSheafKFlat. Its mapping-cone,
countable-coproduct, telescope and flat-coproduct conclusions are not needed here.
The filtered-colimit argument is needed inside the new flatness step through the
existing lem-pc-relative-flat-module-stalk; no pruning of that argument is claimed.
Derived open restriction and K-flat derived tensor comparison remain needed by the
new roof step, rather than being directly imported into the item. Definitions used
by the unchanged signature remain public dependencies; no unit route is bypassed.

All old direct proof dependencies absent from the new direct list are:

- def-pc-derived-category
- def-pc-flat-sheaf-modules
- def-pc-perfect-complex
- def-pc-quasi-iso-modules
- def-pc-scheme-module-flat-over
- lem-pc-derived-tensor-open-restriction-universes
- lem-pc-kflat-closure
- lem-pc-kflat-derived-tensor-comparison
- lem-weil-pbc-filtered-colimit-flat-modules

The definitions remain signature dependencies where needed. The roof and flatness
steps retain the relevant mathematics indirectly; this list records direct DAG
pruning, not removal from the targets import closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement was found. The original docstring
cites 08CG near the roof step, but that tag defines Tor amplitude. The new roof
statement cites 05RT (saturated quasi-isomorphism multiplicative system) instead.
The flatness criterion is 05NE; 06YB is the K-flat stalk criterion. Checked sources:
[0DJQ](https://stacks.math.columbia.edu/tag/0DJQ),
[08CI](https://stacks.math.columbia.edu/tag/08CI),
[05NE](https://stacks.math.columbia.edu/tag/05NE), and
[05RT](https://stacks.math.columbia.edu/tag/05RT).

The existing relative
stalk-flatness theorem covers the affine-basis colimit and localization step, with
no quasi-coherence hypothesis. The original planned lemmas do not themselves
supply the fixed local scalar tensor's term-flatness or its chain-map roof.
These missing interfaces are now stated separately with complete proof descriptions.

The initial compile exposed an unavailable cached olean for the original
OpenKFlatTensorHomologyComparison import. The eventual import change is a pruning
of an unused homology theorem, using an existing proved restriction theorem; no
copy or replacement of the missing homology comparison was made.

Edge cases checked: empty U and zero G or L give zero terms; reversed prescribed
intervals force the corresponding factor to vanish in every degree. The omega
argument does not assume either pair of endpoints is ordered. Finite-free rank
zero is allowed, and term-flatness imposes no coherence or compactness assumptions.
The roof is existential only and does not define an arbitrary unproved witness.

Mathlib searches: LeanFinder found flat tensor exactness criteria, Loogle located
Functor.map_isZero, and grep found the total bifunctor API. LeanSearch was unavailable
and this is recorded in searches.jsonl. No existing complete relative model theorem
or theorem with either new interface was found.

## New nodes

- def-pc-strict-perfect-relative-tensor-complex: the real local scalar-restricted
  total tensor construction, Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorComplex.
- lem-pc-strict-perfect-relative-tensor-terms-flat: original step 3, relative
  flatness of every term of that fixed construction.
- lem-pc-strict-perfect-relative-tensor-roof: original steps 1 and 4, the
  comparison roof for that fixed construction, independently of relative flatness.

Change record: coord/changes/strictPerfectRelativeTensorModel-imports.md.

## Second reading by W4

1. Compared the existing module with the repository using diff and compared its
   strictPerfect_relativeTensor_model signature verbatim: every hypothesis, universe,
   let-bound base ring, interval conclusion, K-flatness conclusion and roof endpoint
   is unchanged. The only existing API change is the declared public-import replacement.
   StrictPerfectTensorRelativeTorBound directly imports both this module and the
   removed homology comparison, so its source loses no declaration. No target changed.
2. Read all four delivered modules. The construction uses restriction, mapBifunctor
   totalization and restriction of scalars, with no choice from a mere existence theorem.
   The support helper proves zero identity using mapBifunctor.hom_ext: p+q=n and
   neither factor outside its interval contradict n outside the sum interval by omega.
   The main proof uses that bound, the flatness theorem, the existing bounded-above
   K-flat theorem, and the roof theorem. Compiled the modules in import order; the
   only two sorries are the reported public named theorems. No axiom, unsafe, opaque,
   extern or implemented_by declaration appears. Axiom probes are checked below.
3. Read Stacks 0DJQ (local finite sums of G terms), 08CI (flat bounded complexes
   compute tensor), 05NE (stalkwise flatness) and 05RT (saturated quasi-isomorphisms).
   Flatness: relative_flat_module_stalk applies without coherence; a finite-free
   retract of L gives a retract of a finite sum of base-flat stalks after tensoring.
   Totalization gives sums, and stalkwise exactness gives sheaf flatness. Roof:
   strict perfection supplies structure-ring K-flatness independently of hGflat;
   exact monoidal restriction and K-flat comparison identify the ordinary tensor,
   then exact scalar restriction carries the isomorphism to the stated endpoints.
   A right fraction has a quasi-isomorphic left leg, and its right leg is also
   quasi-isomorphic because localization inverts it. Actual chain representatives
   exist. Empty opens, zero factors, rank-zero free terms and reversed intervals
   are allowed. Neither new lemma contains the other lemma's conclusion or the
   combined model existence. Repeated LeanFinder, Loogle and grep searches with
   different queries; read Mathlib DerivedCategory.right_fac and stalk tensor and
   flat coproduct APIs. They provide ingredients, not either complete new statement.
   Neither remaining proof can be closed in a few minutes with these interfaces.
4. The combining proof follows the original four local calculation steps: construct
   tensor, prove support, obtain relative flatness and K-flatness, assemble roof.
   The unit sk-thm-picard-semicon has empty realized lists in the repository; no
   unit realization or unit-level route is deleted or bypassed. Completed the
   report's list of every removed old direct proof dependency, distinguishing
   retained indirect mathematics from globally pruned modules. Removed the redundant
   RhomIntoKInjectiveLocal import from the roof module; its public construction
   dependency already provides the needed signature instance. The model's same
   import must remain public: changing it to plain import fails synthesis in the
   unchanged statement at overFunctor A U, before elaborating the proof.
5. Read all four JSON nodes against the declarations and proof. The original node
   retains its statement and statement dependencies; its four proof steps and
   dependency union match the actual proof. New definition and two theorem nodes
   have source, blueprint origin, searches, created metadata, matching chapter/unit
   and Lean records. The two named holes have complete natural-language docstrings.
   Verdict: valid decomposition, one upper hole closed, two lower holes added,
   net -1; not a complete axiom-free proof of the model theorem.

Changed: removed the redundant public RhomIntoKInjectiveLocal import from the new
roof module, put its signature colon on the preceding line, and completed the
pruning report. No theorem statement or mathematical proof was rewritten.

Axiom probe results: strictPerfectRelativeTensorComplex and the private support
helper relativeTensorComplex_bound use exactly propext, Classical.choice and
Quot.sound. The two split statements and strictPerfect_relativeTensor_model use
those three plus sorryAx, as expected. All probe copies compiled through lcompile.py.
Dry run: deliver3.py --no-push returned OK and CODEX (new nodes/modules and the
recorded public-import replacement); no preflight failure remains.
