# Q56 repair: lem-sfb-polynomial-derived-bar-comparison

## Worker report

### Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-derived-bar-comparison.json`: existing statement, split; its statement and statement dependencies are unchanged. The seven-step, 5031-character proof is replaced by a five-step assembly of 1920 characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-polynomial-augmented-resolution.json`: new statement, unsplit; no Mathlib match. Construction, equivariance, differential identities, contraction, and the equivariant derived augmentation isomorphism.
- `dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-polynomial-invariant-coordinates.json`: new statement, unsplit; no Mathlib match. Simultaneous translation coordinates, full internal invariant submodule, and the specified isomorphism of the invariant polynomial complex with its additive-bar form, including its derived image.
- `dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-polynomial-bar-evaluation.json`: new statement, unsplit; no Mathlib match. Parameterwise homogeneous evaluation as an equivariant augmentation-preserving cochain map and its exact inhomogeneous normalization.
- `report.md`, `citations.json`, `searches.jsonl`, search-result captures, and repair/report scripts, all in the authorized sandbox. `former-proof.json` preserves the former seven steps verbatim.

### Attachments

None. The read clone's `WeilConjectures/` has no declaration tagged with this item and no matching polynomial internal-bar comparison under the concept searches. `lean/Sheaf/CategoryTheory/PolynomialDerivedBarComparison.lean` was read: its declaration `Profinite.CondensedAction.PolynomialBar.polynomial_derived_bar_comparison` ends in `sorry`. Its helpers specify the polynomial model and evaluation; they prove none of the three new statements. The corresponding translation-acyclicity module is also a separate obligation, not evidence that this item is proved. No Lean file was written or compiled.

### WANTED

WANTED: an exact literature reference for the internal homogeneous polynomial resolution, its invariant-complex coordinate identification, and its parameterwise augmentation-preserving evaluation, for the three new nodes. The explicit algebraic arguments below are agent-written; paragraph (3) of the blueprint delegates the analytic calculation and does not contain these lemmas.

WANTED (retained from the earlier split): an exact all-continuous, noncomplete-coefficient reference for `lem-sfb-polynomial-translation-acyclic`, and an internal-bar arrow-normalization reference for `lem-sfb-equivariant-resolution-bar-normalization`. These existing nodes are reused, not recreated.

### Issues and limits

The returned long proof is a genuine distribution-of-work issue. No statement dispute was found and no statement, coefficient topology, hypothesis or conclusion was changed. The parent retains all continuous maps into the norm-topological noncomplete algebraic closure, ordinary internal derived modules, and the specified evaluation arrow. The analytic acyclicity statement remains an independent unfinished dependency. No SGA route is used.

The assigned sandbox was empty at start: there was no retained item, report or search log to dry-run. I copied the current repository item and read the existing Q06 stage-1 report and NA ownership-repair report. The current item contains the returned seven steps verbatim, together with later definition-ownership metadata. I preserved that metadata and all old Mathlib entries, and append the original Q06 report below as historical material rather than replacing it with an unrecorded new proof. The only parent fields changed are proof, proof_deps, proof_origin and split_report. No repository or launcher file was edited, no git command was run there, and no agent was started.

## Repair of the return

The single batch5 return requires at least two comparable statement-only nodes, a parent proof of at most 3000 characters, and preservation of every old argument. This packet adds three nodes of 1936, 2591 and 2857 statement characters (the repeated self-contained hypotheses account for part of each length), all `status: unsplit`, empty `proof` and `proof_deps`, with source and five actual searches each. They distribute distinct arguments rather than moving the full comparison to one child:

1. Former steps 1 and 2 are the augmented-resolution node: finite substitution and action laws, paired-deletion differential-square identity, exactness detection after forgetting, and the inserted-zero homotopy with its augmented degree-zero identity. Its conclusion is an equivariant resolution, not the parent comparison with a derived bar.
2. Former steps 3 and 4 are the coordinate node: inverse polynomial substitutions, translated and spectator variables, unit-translation leading coefficients, local finite polynomial sections and gluing, and the endpoint/interior face formulas. The parent applies the already existing translation-acyclicity theorem to its module identification. This child asserts no derived-invariant vanishing.
3. The polynomial part of former step 6 is the evaluation node: continuous generalized evaluation, equivariance, deletion compatibility, constant augmentation and the prefix-sum calculation giving the precise inhomogeneous evaluation. It asserts no derived-bar isomorphism. The already existing normalization node supplies the equality of derived arrows in the parent's assembly.
4. Former step 5 and the final formal inference of former step 6 remain the short assembly: apply the existing bounded-below acyclicity theorem, invert the derived augmentation, and use the normalization equation and the bar isomorphism. Creating another node for this direct composition would add an elementary wrapper to existing results.
5. Former step 7 is included in the conclusions of all three children and checked in the final assembly. No variable, sign convention, zero-rank case, augmentation normalization, or noncomplete-coefficient restriction was dropped.

The full former arguments, with no shortening, are reproduced in the appendix below for the workers who will split the new nodes. The new node statements specify the conclusions and formulas those arguments must establish; they contain no proof sketches. This is the requested one-level re-split, with work below it intentionally left available for parallel workers.

## Sources and searches

I read `GOAL.md`, the three levels in SETUP.md, the stage-1 brief and stage document, delivery-errors B through E in full, the chapter and unit records, and main-20261015 `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially paragraph (3). The latter gives the compactification/open-coefficient route but no exact polynomial theorem. All three new sources say explicitly that they are agent-formulated refinements of this input, with an exact reference WANTED. I also read Stacks Tag 015E, `derived.tex`, `lemma-leray-acyclicity`, whose canonical comparison for a bounded-below complex of acyclic objects is exactly the formal input to assembly step 3. No Stacks tag is presented as proving the new polynomial statements.

Whole-DAG and whole-blueprint searches were made for homogeneous polynomial, inserted-zero/insertion of zero, polynomial resolution, translation invariants, consecutive differences, homogeneous evaluation and polynomial evaluation. The blueprint searches of the combined regular expressions had no equivalent node. A statement scan for the exact polynomial phrases and source searches locate the parent and the distinct existing contraction/translation/bar lemmas, not a separate statement of any proposed child. The three proposed ids were checked absent before writing. `blueprint_refs.py ancestor` returns None for this inherited created-node chain, so the existing null ancestor is preserved, with the parent prepended to its full via chain and a precise paragraph/argument place on every child. The item is not the unit key theorem and no unit realization fields are changed.

Each child has five real msearch calls: LeanFinder in two different phrasings, Loogle, Mathlib grep, and LeanSearch. All services returned actual results, with no unavailable service in this run. Exact query texts and result digests are copied from the log into the appropriate node and full output is retained in `search-results/`. There is no invented or unexecuted search record. Existing parent searches were retained, as its statement/search question is unchanged.

For the resolution, hits were abstract `Rep.standardComplex` free chain resolutions, extra degeneracies/Dold-Kan splitting, and generic homotopy constructors. I read the beginning of Mathlib's Homological/Resolution source: its terms are free modules on arbitrary group tuples, not the internal polynomial direct sums here. None specializes in one line to construction, parameter-dependent translation and the displayed contraction.

For coordinates, the first phrasing found abstract Rep bar faces and the second found scalar polynomial shifts/denominator clearing; LeanSearch found forward differences. The grep hits were fixed subfields and symmetric polynomials (read in `FieldTheory/Fixed.lean` and `MvPolynomial/Symmetric/Defs.lean`), invariance under permutations rather than additive translations. They do not state the sheaf invariant-submodule and cochain identification.

For evaluation, Loogle found `MvPolynomial.continuous_eval` and the uniform continuity of evaluation into power series. I read `Topology/Algebra/MvPolynomial.lean`: it proves continuity for one polynomial, which is an ingredient, not the entire internal cochain comparison. Other hits were polynomial scalar evaluation/finSucc identities, homogenization and ordinary group cochain definitions. They do not assert the generalized internal map, its augmentation/translation compatibility and the normalized prefix-sum equation together. No new node is a Mathlib leaf.

## Not duplicates

lem-sfb-homogeneous-polynomial-augmented-resolution vs lem-sfb-polynomial-derived-bar-comparison: the child constructs a nontrivial equivariant resolution and its underlying contraction; it asserts no invariant-acyclicity or comparison with the derived bar.

lem-sfb-homogeneous-polynomial-augmented-resolution vs lem-sfb-rational-polynomial-bar-contraction: the existing node contracts the invariant additive-bar complex to an exterior complex; the child contracts the augmented homogeneous polynomial complex before invariants, to constants after forgetting the action.

lem-sfb-homogeneous-polynomial-invariant-coordinates vs lem-sfb-polynomial-translation-acyclic: the existing node supplies higher derived-invariant vanishing for a translation representation; the child supplies explicit polynomial coordinates and identifies the entire invariant complex and its differential, without any vanishing conclusion.

lem-sfb-homogeneous-polynomial-invariant-coordinates vs lem-sfb-rational-polynomial-bar-contraction: the existing node computes an already-defined additive-bar complex's exterior homotopy type; the child identifies that bar differential from simultaneous-translation invariants of a different equivariant complex.

lem-sfb-homogeneous-polynomial-invariant-coordinates vs lem-sfb-ind-unipotent-procyclic-difference: the existing node identifies derived invariants of an ind-unipotent procyclic system with a two-term difference complex; the child uses finite polynomial substitutions to identify underived invariant modules and all deletion faces for arbitrary finite lattice rank.

lem-sfb-homogeneous-polynomial-bar-evaluation vs lem-sfb-equivariant-resolution-bar-normalization: the existing node assumes an augmentation-preserving equivariant cochain map e and proves a derived-unit normalization equation; the child constructs the polynomial e and checks that its normalized invariant map is polynomial evaluation. It proves no derived-unit equation.

lem-sfb-homogeneous-polynomial-bar-evaluation vs lem-sfb-condensed-derived-invariant-bar: the existing node computes derived invariants by a derived internal Hom total; the child constructs a map into the underived homogeneous bar, without asserting any column acyclicity or derived total comparison.

lem-sfb-homogeneous-polynomial-bar-evaluation vs lem-sfb-internal-bar-ordered-cup: the existing node compares products of additive-character cocycles with ordered derived cup products; the child constructs evaluation for every homogeneous polynomial and fixes its cochain and augmentation compatibility, without a cup-product assertion.

lem-sfb-homogeneous-polynomial-bar-evaluation vs lem-sfb-finite-index-rectangle-primitive-operator: the existing node constructs a primitive operator for continuous cocycles vanishing on a rectangle; the child constructs polynomial evaluation, with no rectangle, finite-index subgroup or primitive operator.

All three new nodes vs one another: the resolution asserts an augmented quasi-isomorphism before invariants; coordinates asserts an invariant complex isomorphism but no augmentation quasi-isomorphism; evaluation asserts a specific cochain map but no invertibility. Their hypotheses and explicit formulas are repeated for self-containment, not to repeat any of these conclusions.

The new sources carry no Stacks tag shared with other nodes. Tag 015E is used only through the already existing `sk-thm-acyclicity`, not copied into a new lemma.

## Review by Q56

I read the three actual new statements and all cited existing statements with delivery-errors B–E open. The source for each new node is the agent expansion of the blueprint paragraph (3) identified above; no absent literature proof is claimed. Every object is introduced: prime, both fields and topology, ring on every profinite parameter, nonnegative rank, polynomial coproduct, action, cochain degrees, augmentation and ambient categories. The first two statements include the specified derived-category isomorphism, not merely degreewise cohomology groups. All three retain locally finite sheaf sections and all continuous coefficients. The new nodes are unsplit and have no proof/proof-dependency content; their arguments are preserved only in this report for the next workers. Their non-elementary internal constructions/comparisons were explicitly requested to be separated by this return, rather than again labelled elementary in the parent's proof.

Assembly step 1 cites only `lem-sfb-homogeneous-polynomial-augmented-resolution`. Its statement explicitly constructs the augmented action complex, gives the internal contracting maps and identities, and asserts that a is a quasi-isomorphism in the equivariant category. This is precisely the input used; no equivariance of the contraction is inferred. The identity in degree zero is written as a h^0+h^1 delta^0=1, not incorrectly as an unaugmented formula.

Assembly step 2 cites `lem-sfb-homogeneous-polynomial-invariant-coordinates` for both its invertible translation/spectator substitutions and its specified cochain isomorphism phi. It cites `lem-sfb-polynomial-translation-acyclic` for R^q Gamma(T_(r,m))=0 for q>0. I checked the exact latter statement: m is any nonnegative integer and the full internal polynomial direct sum with spectator variables is permitted. The substitutions match its action y maps to y-g, with m=nr, not a finite-degree truncation; F is exactly E or the noncomplete norm-topological Omega. No commutation of derived invariants with a filtered colimit is taken from it.

Assembly step 3 cites `lem-sfb-condensed-derived-restriction-calculus` for the Grothendieck action category, exactness detection, the exact trivial-inflation/invariant adjunction and ordinary triangulated right derived functor. Its right-adjoint invariants are left exact additive. I read the bounded-below derived-object clause of `sk-thm-acyclicity` and the corresponding Stacks lemma: K is zero in negative degrees and its terms are invariant-acyclic by step 2; the action categories have enough injectives. Thus its canonical u_K is an isomorphism. The quasi-isomorphism a from step 1 and phi from step 2 give exactly the displayed c in D(Mod_A). This is direct composition/inversion of the specified isomorphisms, with no hidden new comparison theorem. The existing off-unit tool declaration is retained in split_report.tool_uses because this is generic homological algebra, not a replacement for the unit's analytic route.

Assembly step 4 cites `lem-sfb-homogeneous-polynomial-bar-evaluation` for e, ea=b, equivariance, cochain compatibility, all generalized parameters and the exact polynomial formula for the invariant map after phi. I checked `lem-sfb-equivariant-resolution-bar-normalization`: it requires N with trivial action, an equivariant quasi-isomorphism a:N[0] to K and an equivariant augmentation-preserving cochain map to R_N. We have N=A and all these requirements from steps 1 and 4. Its statement gives j Q(rho)=epsilon (R Gamma(Qa))^(-1) u_K as an equality of derived arrows. After Q(phi), its left side is the eta in the parent statement, not a chosen arbitrary isomorphism. The final citation `lem-sfb-condensed-derived-invariant-bar` expressly supplies the normalized epsilon isomorphism for compatible nonnegative resolutions. No underived-Hom column is asserted acyclic.

Assembly step 5 cites all three children for their r=0 clauses, rather than pretending a generic group simplification proves the whole analytic statement. In the first child K^n=A and delta alternates zero/identity with the contraction h the identity in each degree; in the second phi is the identity; in the third the empty product is one, so coefficients and the augmentation are unchanged. Both field choices remain quantified throughout. This step only reads those specializations and is elementary relative to its cited statements.

I tested the new statements on r=0, n=0,1, and small monomials for r=1,2. For the contraction, h^0 a=1 and a h^0+h^1 delta^0=1 at n=0; deleting the inserted zero has sign +1, and the other terms occur with opposite signs. For invariants, a unit translation in a z coordinate sends the degree d leading coefficient to d times that coefficient in degree d-1 of the difference. Every positive integer is invertible in C(S,F), even though this section ring may have zero divisors. No integral-domain hypothesis on the section ring is needed. The argument is local on polynomial direct-sum sections and glues. The z-free polynomials are invariant under every varying translation, not just constant units. The coordinate inverse is y_a=z+x_1+...+x_a; dropping the first y drops x_1, dropping an interior y merges adjacent x blocks, and dropping the last y drops the last x. At n=0 the two invariant faces cancel. For evaluation, the first tuple entry is zero and successive prefix-sum differences are exactly g_a, so a monomial in consecutive differences evaluates to the stated monomial in g_a. Continuity uses only finite sums/products of continuous coordinates; it needs neither completeness nor an infinite sum. Empty profinite parameters are harmless since the formulas restrict naturally; zero coefficients evaluate to zero.

As an additional finite algebra check, exact integer arithmetic verified 396 monomial/tuple cases for the inserted-zero homotopy and delta squared (r=0,1,2, degrees n=0..3, monomials of total degree at most two, three deterministic sample tuples), plus 28 deletion/consecutive-difference face cases. These checks are not a proof of the analytic acyclicity input. No compiler or Lake tool was invoked.

C1/C4 were checked against every cited node's statement, not its proof. `citations.json` has a verbatim quote for every step/node pair. The proof_deps list is exactly the union of the uses. No new node cites the parent or an ancestor, so the split introduces no cycle. The child statements do not assert all or a clause of the parent's conclusion: each provides a separately usable smaller argument. All five parent steps are below the 2000-character long-step threshold and together below 3000. The old full argument is retained below rather than blurred or replaced with a short proof sketch. The server review_split check passed; the combined delivery preflight follows this report.

## Unfinished below this split

The three new obligations are statement-only, ready for future workers. The existing translation acyclicity and bar-normalization obligations remain separate. This delivery is a stage-1 decomposition, not a claim that these downstream results are proved.

## Preserved former proof (verbatim)

### Former step 1

Put $A=A_F$. Construct an equivariant complex $K^n$ as the internal polynomial direct sum in $(n+1)r$ variables $y_0,\ldots,y_n$, where each $y_a$ is an $r$-tuple. Let $g$ act by substituting $y_a-g$ for every $y_a$, and set $\delta f=\sum_{i=0}^{n+1}(-1)^i f(y_0,\ldots,\widehat y_i,\ldots,y_{n+1})$. The augmentation $a:A[0]\to K$ is inclusion of constants. Each substitution sends a monomial to a finite sum, hence defines an internal $A$-linear map, including for a parameter-dependent $g$. Pairing the two orders of deleting any two coordinates proves $\delta^2=0$; substitution commutes with deletion, so these differentials are equivariant. Forgetting actions detects exactness by [lem-sfb-condensed-derived-restriction-calculus].

Cited nodes: lem-sfb-condensed-derived-restriction-calculus.

### Former step 2

The augmented underlying complex is split exact. Define $h^n:K^n\to K^{n-1}$ by $(h^nf)(y_0,\ldots,y_{n-1})=f(0,y_0,\ldots,y_{n-1})$ for $n>0$, and $h^0:K^0\to A$ by evaluation at zero. In $\delta h+h\delta$, terms retaining the inserted zero occur twice with opposite signs; deleting that zero contributes exactly $f$. Thus $\delta h+h\delta=1$ on the augmented complex, and $h^0a=1$. These identities are finite polynomial identities, so hold on internal direct sums and after every restriction of parameters. The contracting maps need not be equivariant. Exactness after forgetting suffices by step 1, hence $a$ is an equivariant quasi-isomorphism.

Cited nodes: (none; elementary in the former split).

### Former step 3

Change polynomial coordinates to $z=y_0$ and $x_a=y_a-y_{a-1}$ for $1\leq a\leq n$. The inverse is $y_a=z+x_1+\cdots+x_a$. These inverse substitutions identify $K^n$ with the translation module $T_{r,nr}$ of [lem-sfb-polynomial-translation-acyclic], where $z$ is translated and all $x_a$ are fixed. Its hypotheses are exactly $F=E$ or the norm-topological $\Omega$, $L=\mathbf Z_\ell^r$, and nonnegative $r,nr$. Consequently every $K^n$ is $\Gamma_L$-acyclic as an internal module. The assertion used is for the polynomial direct sum itself; it does not infer acyclicity by commuting a derived functor with a filtered colimit.

Cited nodes: lem-sfb-polynomial-translation-acyclic.

### Former step 4

The same coordinates identify $(K^n)^L$ with the polynomial direct sum in $x_1,\ldots,x_n$. To check this internally, invariance implies invariance under each constant integer unit translation in a coordinate of $z$. If a polynomial has positive degree $d$ in that coordinate, the coefficient of degree $d-1$ in $f(z+1)-f(z)$ is $d$ times its leading coefficient. Since $d$ is invertible in every $A(S)$, that coefficient must be zero, a contradiction; induction removes that coordinate. Apply this to each coordinate of $z$. Sections of the direct sum are locally finite polynomials, so this calculation applies locally and glues; conversely a polynomial independent of $z$ is fixed under every parameter-dependent translation. Deleting $y_0$ drops $x_1$; deleting an interior $y_a$ replaces $(x_a,x_{a+1})$ by $x_a+x_{a+1}$; deleting $y_{n+1}$ drops $x_{n+1}$. Thus $K^L$ is exactly $P_{A,r}$, including its stated differential.

Cited nodes: (none; elementary in the former split).

### Former step 5

The action category is Grothendieck abelian with left exact additive invariants by [lem-sfb-condensed-derived-restriction-calculus]. Apply the bounded-below complex clause of [sk-thm-acyclicity] to $K$, using step 3. It makes the canonical unit $u_K:Q(K^L)\to R\Gamma_L(QK)$ an isomorphism of derived objects. Step 2 makes $R\Gamma_L(Qa)$ an isomorphism as well. Therefore $c=(R\Gamma_L(Qa))^{-1}u_K:P_{A,r}\to R\Gamma_L(A[0])$ is an isomorphism. This uses the derived-object clause of acyclicity, rather than just its per-degree cohomology conclusion.

Cited nodes: lem-sfb-condensed-derived-restriction-calculus, sk-thm-acyclicity.

### Former step 6

Evaluate a homogeneous polynomial $f\in K^n$ on $(g_0,\ldots,g_n)\in L^{n+1}$ to define $e:K\to R_A^\bullet$ of [lem-sfb-equivariant-resolution-bar-normalization]. A coefficient $c\in A(S)$ evaluates to $c(s)$; multiplication by the coordinates of $g_a$ is continuous in $(s,g_0,\ldots,g_n)$, so this defines internal morphisms. Translation and deletion commute with evaluation, and constants evaluate to constants. Thus $e$ is equivariant, is a cochain map, and preserves the augmentation. The homogeneous-to-inhomogeneous substitution in that node is $(0,g_1,g_1+g_2,\ldots,g_1+\cdots+g_n)$ in additive notation. By step 4 its consecutive differences are exactly $g_1,\ldots,g_n$. Hence its map $\rho:K^L=P_{A,r}\to U_A^\bullet(L)$ is precisely the polynomial evaluation in the item. The normalization node now gives $\eta_{F,r}=\epsilon c$ as an equality of specified derived arrows. The bar node [lem-sfb-condensed-derived-invariant-bar] makes $\epsilon$ an isomorphism, so $\eta_{F,r}$ is an isomorphism.

Cited nodes: lem-sfb-equivariant-resolution-bar-normalization, lem-sfb-condensed-derived-invariant-bar.

### Former step 7

When $r=0$ there is no translation variable and $L=1$. Invariants are the identity. The inserted-zero contraction of step 2 is the contraction of the augmented constant cosimplicial complex. Evaluation on the unique tuple is the identity on its term $A$ in every degree, so the comparison has the same degree-zero augmentation. Both permitted fields have been retained throughout. No step replaces all continuous $\Omega$-valued functions by finite-subextension-valued functions or invokes convergence of a series in $\Omega$.

Cited nodes: (none; elementary in the former split).

## Historical Q06 report retained verbatim

The following is the earlier stage-1 report read from the current repository. Its two new nodes were already landed before Q56; the present delivery adds the three nodes listed above. Its historical validation refers to the old delivery only.

# Q06: lem-sfb-polynomial-derived-bar-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-derived-bar-comparison.json`: item, statement, now split into seven steps; statement and statement dependencies unchanged. Existing Mathlib searches retained and five fresh searches added.
- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-translation-acyclic.json`: new statement-only analytic lemma; unsplit, no Mathlib match. Polynomial direct sums with simultaneous lattice translation and arbitrary finitely many spectator variables are acyclic for internal derived invariants.
- `dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-resolution-bar-normalization.json`: new statement-only formal lemma; unsplit, no Mathlib match. An augmentation-preserving map from an equivariant resolution into the homogeneous bar gives the normalized derived-invariants arrow, even without acyclicity of the bar terms.
- `citations.json`: exact statement quotations for all six step/node pairs.
- `searches.jsonl`: fifteen actual msearch records; retained without alteration. The JSON search entries copy these actual records and their query strings.

No Lean source, repository file, launcher file, unit record or chapter record was written. Mathematical formula checks are in the sandbox's `check_formulas.py`; they use integer polynomial substitutions, not Lean or a compiler. No earlier split/report/search log existed in this sandbox.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for polynomial/bar, lattice and translation-resolution notions. No project declaration states the item or the new lemmas. Mathlib's `Rep.standardComplex` is an abstract group representation resolution, not this internal condensed comparison. Upstream sorry declarations were not treated as proofs.

## WANTED

WANTED: an exact reference for internal derived-invariant acyclicity of the polynomial translation direct sum over all-continuous norm-topological E and noncomplete Omega, for `lem-sfb-polynomial-translation-acyclic`. The complete-coefficient Mahler theorem alone does not supply it.

WANTED: an exact reference for the homogeneous internal bar/derived-unit normalization equation in `lem-sfb-equivariant-resolution-bar-normalization`. Its formal ingredients are the existing internal bar comparison and derived-unit naturality; the blueprint does not supply this equation.

## Source, route and issues found

Read the current main-20261015 direct-images proof paragraph (3) named in the item's source, the chapter record `sec-six-functors-basics`, the unit record `sk-thm-sf-ctf-stability`, and the parent split `lem-sfb-trivial-ladic-derived-exterior`. Paragraph (3) delegates the open-coefficient calculation; it does not prove a polynomial comparison. The item already labels the exact analytic reference WANTED. Accordingly this split is honestly agent-written; it claims neither a sourced proof of the analytic lemma nor a finished analytic result.

For the homological input I read Stacks Tag 015E, `derived.tex`, `lemma-leray-acyclicity` (including the bounded-below proof), and Tag 0156, `section-right-derived-functor`, especially `lemma-injective-acyclic`. Only the existing `sk-thm-acyclicity` is used for Leray's lemma. No Stacks tag is represented as proving the analytic assertion. I also converted the local Scholze Six-Functor Formalisms PDF to text and inspected its coefficient discussion; it does not provide the exact noncomplete polynomial-translation assertion. No SGA source is cited.

The generic acyclic-resolution lemma `sk-thm-acyclicity` is declared as a tool use in `split_report.tool_uses`: it supplies formal homological algebra, not a replacement route. The two new lemmas remain inside the item's unit. `blueprint_refs.py ancestor` returns None, which is inherited from this created-node chain; the existing null ancestor was retained, with the full via chain and precise paragraph places. The item is not the unit key theorem, so no unit realization fields were changed.

No statement dispute was found in this item. In particular no completeness hypothesis, finite-subextension-valued replacement, underived-column acyclicity assertion or conclusion about cohomology only was added. The analytic content was isolated rather than justified by a completeness assumption that Omega lacks.

## Not duplicates

Whole-DAG keyword searches and `blueprint_refs.py search` were made for polynomial, polynomial cochain, polynomial translation, derived bar, homogeneous, acyclic resolution, translation and resolution comparison. The searches found no existing statement of either new fact. Search hits and actual verdicts were read, including Mahler's `CompleteSpace` hypothesis and the abstract module coefficients in `Rep.standardComplex`.

- lem-sfb-polynomial-translation-acyclic vs lem-sfb-polynomial-derived-bar-comparison: the new lemma is about higher invariants of a nontrivial polynomial translation representation, with spectator variables; it states no polynomial-to-bar comparison, no exterior cohomology and no claim about trivial-coefficient derived objects. The item now constructs the resolution, proves its exactness, computes its invariants and identifies the actual arrow.
- lem-sfb-polynomial-translation-acyclic vs lem-sfb-rational-polynomial-bar-contraction: the latter is an algebraic contraction of the invariant additive polynomial bar over any Q-algebra; the new lemma concerns acyclicity before taking invariants in an internal lattice action category. Neither supplies the other by a one-line specialization.
- lem-sfb-polynomial-translation-acyclic vs lem-sfb-dense-lattice-derived-invariants-comparison: the latter concerns finite-dimensional continuous representations and its proof depends on the parent of this item. Our polynomial direct sum is unbounded in degree and is not finite dimensional. Citing that ancestor would create a cycle.
- lem-sfb-equivariant-resolution-bar-normalization vs lem-sfb-condensed-derived-invariant-bar: the bar node gives a normalized isomorphism from derived invariants of a module, but does not state the equation for an arbitrary equivariant resolution K mapping to the underived homogeneous bar. The new lemma gives this arrow equality, without asserting that it is an isomorphism.
- lem-sfb-equivariant-resolution-bar-normalization vs lem-sfb-resolution-inflation-comparison: the latter is for projective resolutions of integral abstract group modules and only per-degree inflation maps. It does not cover internal A-modules, arbitrary equivariant cochain resolutions or the derived internal bar equation.
- lem-sfb-equivariant-resolution-bar-normalization vs lem-sfb-internal-bar-ordered-cup: the latter treats the cocycle made from an ordered list of additive characters and compares cup products; the new lemma concerns arbitrary resolutions and augmentation-preserving evaluation, with no cup assertion.
- lem-sfb-equivariant-resolution-bar-normalization vs lem-sp-derived-injective-resolution-naturality: the latter assumes specified injective resolutions and gives naturality between their derived-object computations; the new lemma identifies the map from a possibly noninjective equivariant resolution into an internal homogeneous bar.

Neither new source carries a Stacks tag shared by existing nodes: both are explicitly agent-formulated sub-obligations under paragraph (3), with exact references WANTED. The existing generic Stacks result is reused, not duplicated.

## Review by Q06

I reviewed delivery-errors B through E, both copies, against the actual JSON and the sources. Every new node introduces its ring, group, variables, action, topology and universes, and cites the definitions it uses. Both are statement-only with empty proof and proof dependencies. Neither is an elementary fact or a clause of the item's trivial-coefficient comparison. In particular the nontrivial translation representation is a smaller effacing object, and the normalization lemma supplies a formal arrow identity rather than the item's isomorphism. I wrote out the elementary polynomial arguments instead of making more nodes.

Step 1 cites the statement of `lem-sfb-condensed-derived-restriction-calculus` only for exactness detection after forgetting actions. That statement explicitly says kernels/cokernels are underlying ones and forgetting is exact and detects exactness. The finite substitutions, action law and cancellation for delta squared are written out in the step; polynomial and action definitions are already statement dependencies.

Step 2 has no non-elementary citation: insertion of zero contracts the augmented underlying complex. I checked the signs: deleting the inserted zero has sign +1, and all other terms cancel in pairs; in degree zero the remaining augmentation term is evaluation at zero. The contraction need not preserve actions, and the proof uses only exactness detection from step 1 to obtain the equivariant quasi-isomorphism. No projectivity of represented free modules is assumed.

Step 3 uses exactly the vanishing statement of `lem-sfb-polynomial-translation-acyclic`. The invertible polynomial coordinate change is explicit, and its r translation variables and nr spectator variables match that node. All required indices are nonnegative; F has exactly the permitted norm topology. The new node asserts acyclicity of the full direct sum, so there is no silent assertion that derived invariants commute with an unbounded filtered union. This is the analytic input still to be split below this delivery, and it was not replaced with the complete-field Mahler theorem.

Step 4 is a polynomial calculation. I checked the leading-coefficient argument over A(S), which can have zero divisors: multiplication by a positive integer remains invertible since F contains Q, so the conclusion does not require A(S) to be an integral domain. Invariance under the whole group implies invariance under the integer unit translations used; independence of the translated variables conversely gives invariance under all parameter-dependent translations. Internal direct-sum sections are locally finite polynomials; the argument is local and glues, so it does not assume every sheaf colimit is a naive sectionwise colimit. Consecutive differences give exactly the first, interior and last bar faces, including n=0 where the two terms cancel.

Step 5 cites `lem-sfb-condensed-derived-restriction-calculus` for the Grothendieck action category, left exact invariants and derived-functor properties, and the exact derived-object clause of `sk-thm-acyclicity` for the canonical comparison on a bounded-below acyclic complex. K is zero in negative degrees; step 3 verifies termwise acyclicity. Step 2 supplies a quasi-isomorphism in the correct action category. These hypotheses make both factors defining c invertible. I did not use a bare list of cohomology isomorphisms to identify a derived arrow.

Step 6 cites the full equality of `lem-sfb-equivariant-resolution-bar-normalization`, after checking N=A with trivial action, the equivariant quasi-isomorphism a and the evaluation map e. I checked continuity with a varying profinite parameter, equivariance, deletion compatibility, and preservation of the constant augmentation. The specified homogeneous tuple in additive notation has consecutive differences g_1,...,g_n, so rho is the precise evaluation map in the item, without an arbitrary choice of an isomorphism. `lem-sfb-condensed-derived-invariant-bar` is used for epsilon being an isomorphism, which its statement supplies. The new normalization lemma carries the formal comparison theorem explicitly instead of hiding it in the word 'canonical'.

Step 7 checks the trivial group r=0 explicitly. Then all variables disappear, the polynomial terms are A, invariants are the identity and the constant cosimplicial contraction is the same inserted-zero calculation. Empty parameter sets, zero coefficients and zero spectator variables introduce no exception. Rank one and two were checked with the formulas below. No step exceeds 2000 characters.

For the analytic new lemma I checked r=0 (invariants identity), m=0, and r=1 where polynomial antidifferences are finite rational polynomials; the latter is a plausibility check, not a claimed proof of internal derived acyclicity. I did not infer internal vanishing merely from ordinary cohomology on the one-point parameter. For the formal new lemma I checked G=1, N=0 and K=N[0] when G=1: its equation reduces to naturality of the derived unit with the constant augmentation. The underlying homogeneous complex is contracted by insertion of the identity. A route for its later proof is evaluation into the homogeneous bar of one equivariant injective resolution: forgetting preserves injectives by the flat represented-free-module induction adjunction already exposed in the bar node, and homogeneous coinduction preserves injectives as the right adjoint of exact forgetting. This gives the equivariantly injective total resolution on which the equation is derived-unit naturality. This proof plan is in the report, not in the new statement.

Exact integer-coefficient checks in `check_formulas.py` passed 132 monomials for the inserted-zero homotopy (r=0..2, cochain degree 0..3, total polynomial degree at most 2), including the augmented degree-zero identity. Separate symbolic linear-coordinate checks passed every deletion/addition face for r=1..2, n=1..3. These checks verify the finite algebra only; they do not certify the analytic new lemma. An initial optional SymPy invocation found that package unavailable; I replaced it with a dependency-free integer polynomial check, without installing anything.

The citations file contains verbatim statements, with each use justified above. The proof dependency list is exactly their union. I checked no new node depends on the item or its parent and that no cyclic ancestor comparison was cited. I preserved all imported metadata, the item statement and its statement dependencies. All new searches have actual msearch records; none was invented, and none of the services used was unavailable.

## Unfinished below this one-level split

The two new statement-only obligations remain unsplit, as required. In particular this delivery does not certify the analytic incomplete-coefficient theorem. The complete proof of the item is conditional on those named DAG lemmas, with all remaining non-elementary inputs exposed.

## Validation

The required server `review_split` check passed before this report was written. The final combined delivery dry run is run after this report; its result is recorded below when it exits.

Combined dry run exited successfully: `OK (not pushed) deliver/Q06/lem-sfb-polynomial-derived-bar-comparison at 26ae30de9fe: preflight passed`. The push command performs preflight again with this validation note included.

## Q56 validation

Server review_split before the report: PASS. Required combined dry run and push are recorded after they finish.

The first combined dry run rejected one citation excerpt as shorter than 40 characters. I expanded the translation-acyclicity quote to include the full vanishing assertion and its coefficient/direct-sum qualifications, verbatim from the existing node. No mathematical step changed.

The repaired combined dry run exited 0: `OK (not pushed) deliver/Q56/lem-sfb-polynomial-derived-bar-comparison at 885662a651c: preflight passed`. It saved a durable receipt. The push command reruns the preflight with this validation note included.


## Repair of landing refusal (returned head 06f3d872b97)

The 2026-10-22 06:35 UTC return in coord/returns/Q56.md approved the mathematics but refused landing because the side completion had not been promoted to the live DAG. I retained the delivered sandbox and its three child statements, full former proof, original reports, citations and search logs. The required first dry run on this repair exited 0 at ea3b9ae4bbb against the current server DAG. The delivery tool constructs the rebased commit in its own worktree; no git operation was run in the shared read clone.

I compared all four sandbox node files with the current read clone. The three child ids are still absent there. For the parent, only proof, proof_deps, proof_origin and split_report differ: the live node has the former seven-step argument, whereas this delivery has the five-step assembly required by the still-released stage-1 repair note. Statement, statement dependencies, blueprint and ownership metadata and Lean record already agree with the current DAG. Thus there is no stale statement or metadata to overwrite. The updated split_report now records this landing-return repair explicitly rather than presenting an unchanged re-push.

I re-read every current proof dependency, not only the ones for which a change could be identified. Step 1 takes the equivariant quasi-isomorphism and underlying contraction from the augmented-resolution child. Step 2 takes the invariant-complex coordinate isomorphism from the coordinate child and applies the existing translation-acyclicity statement to T_(r,nr); that statement still quantifies over both permitted fields, arbitrary spectator rank, and the full internal polynomial direct sum. Step 3 uses the current restriction-calculus statement for the Grothendieck action category, exact forgetting and ordinary derived invariants, and the bounded-below derived-object clause of sk-thm-acyclicity. Step 4 uses the evaluation child for the actual augmentation-preserving map and its prefix-sum formula; the current normalization statement gives the equality j Q(rho) = epsilon (R Gamma(Qa))^(-1) u_K, and the current derived-bar statement supplies the normalized epsilon isomorphism with compatible nonnegative resolutions. Step 5 reads the explicit zero-rank clauses in all three children. None of these current statements invalidates a step or requires a mathematical change.

I also re-read the current statement definitions, the chapter and unit records, blueprint main-20261015 direct-images proof paragraph (3), and Stacks Tag 015E, derived.tex lemma-leray-acyclicity. The blueprint delegates the analytic input, so the WANTED references and agent provenance remain explicit. The current action definition requires invariance after all profinite base changes, which the coordinate and evaluation children explicitly retain. The bundled scalar definition retains all continuous maps; no completeness or finite-subextension restriction is introduced. The project's current Sheaf polynomial comparison theorem still ends in sorry, and no exact finished declaration was found in WeilConjectures.

For the B–E recheck, the children remain statement-only, self-contained and distinct from the parent comparison and from each other. I re-read all fifteen saved search-result captures and the corresponding searches.jsonl entries; the statements and search questions have not changed, so no queries were repeated or invented. The saved results give ordinary representation resolutions, polynomial continuity and scalar identities, not these internal sheaf constructions. The prior Not duplicates analysis still applies. The r=0, degree-zero augmentation, characteristic-zero unit-translation argument, noncomplete Omega coefficients, and signs in consecutive differences all remain as checked in Review by Q56. Every one of the eleven step/node citation quotes is still a verbatim part of the current statement; citation coverage is exact. Proof lengths are 273, 445, 364, 501 and 337 characters, totaling 1920, so no long step hides another obligation. This review repairs the landing-return bookkeeping and revalidates the accepted split on the current DAG without changing its mathematics.
