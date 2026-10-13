## What changed

Replaced the sorry in `CochainComplex.acyclic_homComplex_of_bounded_exact_columns`
by a concrete opposite Hom bicomplex, proofs of its bounds and exact columns,
and the existing proved bounded-above columnwise total comparison. The signature
and public imports are unchanged. Retained proof imports for filtered additive-group colimits, the source
comparison, and the new short-complex comparison module. The second reader
removed five redundant added imports, all reached publicly through retained modules.

The opposite bicomplex is a proved private construction. Its data are not chosen
from an existence theorem. The zero bicomplex uses the categorical zero object,
whose universal property determines it up to isomorphism.

## Proved and sorry left

Closed the original hole in
`CochainComplex.acyclic_homComplex_of_bounded_exact_columns`
(node `lem-sc-bounded-hom-exact-columns`). Its bounds, column exactness, and
acyclicity of the opposite total are fully proved from existing declarations.

Added one hole:
`CochainComplex.homComplex_sc_iso_dual_total`
(node `lem-sc-hom-complex-dual-total-comparison`). It identifies short complexes
by the product universal property and an explicit sign change. It has no
exact-column or boundedness hypothesis, and asserts an isomorphism rather than
acyclicity. This is a decomposition, not a net reduction in holes: one closed,
one added. No sorry remains in the item's module or any definition.

## No longer needed

None of the original public imports can be removed: they supply the unchanged
statement and its notions. All four original proof dependencies remain needed.
The manual local descending-lift proof route is replaced by the existing closed
bounded-above bicomplex comparison; no separate local-lift lemmas are imported
or created. No previously imported module or node is pruned. Removed these redundant
imports added by the first worker: `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`,
`Mathlib.CategoryTheory.Sites.LeftExact`, `Mathlib.CategoryTheory.Sites.Equivalence`,
`Mathlib.CategoryTheory.Abelian.Opposite`, and `Mathlib.Algebra.Homology.Opposite`.
They remain available transitively, so this is import cleanup rather than pruning
modules from the target closure.

## Where the brief, the DAG or earlier work was wrong

The original proof plan cites definitions but no theorem implementing its finite
local descent. The existing source bicomplex theorem supplies that argument once
both bounds are upper bounds. Passing to the opposite category and negating the
second index achieves this without strengthening any hypothesis. The unit's
statement and steps are preserved.

Automatic sheafification for the output universe requires resizing the filtered
covering category before transporting preservation of its colimits. This is
proved locally from Mathlib; no additional sheafification assumption was added.

The remaining comparison was checked for negative indices, zero complexes, and
unbounded complexes with products. Its sign is
`(-1)^(p*n+p*(p+1)/2)`, with adjacent sign ratios `(-1)^p` and `(-1)^(n+1)`.

## New nodes

`lem-sc-hom-complex-dual-total-comparison`, in
`Sheaf.Algebra.Homology.HomComplexDualTotalComparison`, isolates the product
identification and signed differential compatibility. Its source and full
coordinate proof are recorded both in its docstring and node. The syntactic command changes are documented in
`coord/changes/bounded-hom-exact-columns-proof-scope.md`; no existing signature,
visibility, or definition is changed.


## Second reading by V3

1. Compared the delivered item with the repository using `diff` and an exact
   text comparison of its theorem header. The sole existing public declaration,
   `CochainComplex.acyclic_homComplex_of_bounded_exact_columns`, has precisely
   its original signature and visibility. Restored one extra whitespace character
   before `:=` to make the header byte-for-byte identical. The three original
   public imports remain unchanged. No target statement or existing definition
   was changed; no forced adaptations are delivered. Verdict: pass.

2. Compiled both delivered modules in import order with `lcompile.py --all`.
   Inspected every definition and proof: no forbidden declaration or attribute,
   no data chosen from an unproved arbitrary-existence theorem, and exactly one
   `sorry`, in the reported named comparison theorem. The private bicomplex is
   a concrete graded-object construction with proved identities. The categorical
   zero object is determined up to unique isomorphism. Scratch `#print axioms`
   checks for the original theorem and comparison show only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`; the Hom existence theorem
   and bounded-above total comparison use only the three permitted axioms.
   Verdict: valid reduction with the explicitly reported remaining hole.

3. Read the new comparison theorem, its complete coordinate proof, and its node.
   Unop of the diagonal coproduct is the required product, indexed by the
   bijection `(p,q) ↔ p` with `q=-p-n`. Checked Mathlib's actual total signs:
   horizontal coefficient 1, vertical coefficient `(-1)^p`. Writing
   `a(p,n)=p*n+p*(p+1)/2`, the identities
   `a(p,n+1)-a(p,n)=p` and
   `a(p+1,n)-a(p,n+1)=n+1` establish both needed sign ratios for every integer;
   also checked indices -30 through 30 directly. Zero complexes, vanishing
   diagonals, and unbounded products satisfy the same universal property.
   The new statement assumes no exactness or bounds and identifies short
   complexes; it is strictly the identification step of the argument, not a
   restatement of acyclicity. Searched again with independently phrased
   LeanFinder, Loogle, and grep queries via `msearch.py`, and searched both
   repository roots. Generic bifunctor totalization and Hom complexes of
   morphism groups do not provide this internal-sheaf-Hom comparison.
   Formalizing that product/sign construction is substantial, so its named
   hole remains. Verdict: true, useful split with no duplicate found.

4. Read the proof from its conclusion backwards: exactness transports through
   the short-complex isomorphism and unop, while the opposite total is acyclic
   by the existing proved columnwise comparison from zero. Both upper bounds
   and column exactness are proved, not passed to a new acyclicity placeholder.
   All four old proof dependencies remain used. Removed five redundant added
   proof imports and recompiled successfully. Read
   `dag/units/sk-thm-picard-duality.json`: its `realized.statement` and sole
   realized step are empty; this reduction does not bypass any realized unit
   declaration or change the unit route. Verdict: pass; no closure module pruned.

5. Compared both node proofs and dependency lists with the Lean reduction.
   Each `proof_deps` is exactly the union of its proof steps' `uses`.
   The original node retains all old dependencies and adds totalization,
   the existing comparison theorem, and the new signed comparison. Its
   `proof_origin` describes the actual route. The new node has the required
   source, complete proof, search records, creation metadata, blueprint origin,
   chapter/unit, and verbatim Lean statement. The theorem's docstring and node
   agree. Verdict: pass.

Changes by this reader: removed the five redundant proof imports above,
restored original signature whitespace, clarified the report's import accounting,
and recorded the independent compilation, axiom, sign, search, and DAG checks.
One original hole is closed and one identification hole is added: this remains
a decomposition with zero net holes removed, not a completed acyclicity proof.
