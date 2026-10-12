## What changed

Proved `Algebra.exists_jacobian_minor_of_smooth_fibre_localizedPresentation` in
`Sheaf.RingTheory.SmoothFibreLocalizedPresentationJacobian`, with its signature and all
existing public imports unchanged. Added proof imports of
`Mathlib.RingTheory.Localization.BaseChange`,
`Sheaf.Paper.RelativeGlobalCompleteIntersectionBaseChange`, and
`Sheaf.RingTheory.RelativeGlobalCompleteIntersectionSmoothJacobian`.

The existing base-change theorem supplies the reduced presentation, its equivalence with
the fibre, and its complete-intersection condition. Two proved private helpers transport
smoothness through a principal localization and an algebra equivalence. The main proof
constructs the corresponding fibre prime, applies the existing Jacobian criterion, proves
the quotient/coefficient compatibility by algebra-homomorphism extensionality, and identifies
the contracted prime using injectivity of localization contraction. Finally `pderiv_map`
and `RingHom.map_det` pull the minor back. Updated the item's proof and dependencies accordingly.

Sources read: Stacks `algebra.tex`, proofs of `lemma-flat-fibre-smooth` (00TF),
`lemma-relative-global-complete-intersection-smooth` (00TE), and
`lemma-base-change-relative-global-complete-intersection` (00SS (1)), from the available
local copy at `/home/ubuntu/work-bp/sheaf/literature/stacks-project/algebra.tex`.

## Proved and sorry left

Closed the sole hole:
`Algebra.exists_jacobian_minor_of_smooth_fibre_localizedPresentation`
(node `lem-weil-pbc-smooth-fibre-localized-presentation-jacobian`).
No `sorry` remains in the item's module; no hole is added or split off elsewhere.
Both private helper theorems are proved. This proves the item from existing stated
nodes, rather than completing all their dependencies: the imported existing declarations
`Algebra.relativeGlobalCompleteIntersection_baseChange` and
`Algebra.isSmoothAtPrime_iff_exists_jacobian_minor` still contain `sorry` in their own
modules, which this delivery does not modify.

Single-file compilation passes without warnings. Edge cases use the same proof:
`c = 0` has determinant one; `c > n` is excluded by the existing criterion and
complete-intersection hypotheses at the constructed prime. No new statement requires an
edge-case review. The new equivalence is used inside a theorem proof and its generator
formula fixes its action on every polynomial; no definition chooses arbitrary unproved data.

## No longer needed

No original import is removed and no library module is claimed globally pruned.
The direct planned uses of `lem-weil-pbc-polynomial-scalar-extension` and
`lem-weil-pbc-tensor-quotient-base-change` are replaced by the already stated
`lem-weil-pbc-relative-global-complete-intersection-base-change`, whose combined interface
supplies both the quotient equivalence and preservation of the specified presentation.
These two nodes are removed from this item's direct proof dependencies; this makes no
claim about whether other nodes still need them. All remaining planned localization,
smoothness, Jacobian-criterion and derivative dependencies are used.
The item's unit is `sk-thm-p1`; none of its realized statement or proof-step nodes is
bypassed or removed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned separate polynomial/tensor quotient and fibre-dimension
argument can be replaced by the existing specified-presentation base-change theorem.
The original docstring described a residue-field-kernel comparison; the proof instead
identifies the prime by the injectivity of localization contraction and the inverse law
for `PrimeSpectrum.preimageEquivFiber`. The updated docstring and DAG describe this argument.

## Second reading by W3

1. **Interface: pass.** Compared the complete delivered module with the repository using
   `diff -u`, and compared the existing theorem's signature byte for byte with a script.
   The rings, prime `q`, localization element `g`, lifted prime `qg` and contraction
   equality, specified `n`, `c`, equations, complete-intersection hypothesis, algebra
   equivalence, fibre smoothness hypothesis, and increasing-minor conclusion are unchanged.
   There is no definition change or change record. The only new declarations are two
   proved private helpers; all three new imports are plain proof imports.
2. **Proof and axioms: pass, relative to the existing open dependencies.** Compiled the
   delivered file using `lcompile.py`: no errors or warnings (5.7 seconds). Compiled a
   scratch copy with `#print axioms` for both helpers and the main theorem (6.3 seconds).
   Both helpers use only `propext`, `Classical.choice`, and `Quot.sound`; the main theorem
   additionally uses `sorryAx` through the existing base-change and Jacobian-criterion
   theorems identified above. The delivered module has no `sorry`, forbidden axiom or
   execution escape, or data definition. The equivalence extracted from base change is
   constrained on every variable, and the proof extends that formula to all original
   polynomials explicitly in `hpoly`; no arbitrary unproved witness is made into data.
3. **Split statements and shorter routes: pass.** There are no new split statements or
   holes. Read both existing theorem interfaces: base change supplies the specified
   reduced equations, generator-compatible equivalence, and precisely `hciBar`; the
   Jacobian criterion applies to those equations and the constructed prime. Independently
   searched with Loogle `Algebra.Smooth, Localization.Away`, LeanFinder `smooth algebra
   equivalence principal localization smooth at prime transport`, and `rg` through the
   library and Mathlib smoothness files. The results give the localization and composition
   facts already used, or Mathlib's different local-smoothness predicate with finite
   presentation hypotheses; none directly replaces this presentation comparison.
   The similar transport helper in `FlatSmoothFibreSmoothAtPrime` is private and in a
   downstream module importing this item, so cannot be imported here. Checked `c = 0`
   (empty determinant one), `c > n` (incompatible with a nonempty complete-intersection
   fibre), and `g = 0` or a zero ring (no lifted prime). No case is silently discarded.
4. **Route and pruning: pass.** Read Stacks `algebra.tex` at
   `lemma-base-change-relative-global-complete-intersection` (00SS (1), lines 36639ff),
   `lemma-relative-global-complete-intersection-smooth` (00TE, lines 37629ff), and
   `lemma-flat-fibre-smooth` (00TF, lines 37673ff). The proof implements the source's
   reduction to the fibre and comparison of reduced minors. In `smoothAt_away`, the two
   successive localizations are explicitly compared as localizations at the product;
   `smoothAt_comap_equiv` transports the smooth neighbourhood along the inverse
   equivalence. `hQ` and `hqc` establish the contractions, rather than assuming prime
   compatibility; `hmem` and `hdet` then pull back the nonmembership. Each added import
   supplies a theorem used in the body; the original public imports support the signature.
   The No longer needed section lists both omitted old direct proof dependencies, and
   correctly makes no claim of globally pruning their modules. Read
   `dag/units/sk-thm-p1.json`: neither this item nor either omitted dependency is a realized
   statement or step of the unit; its recorded route is preserved.
5. **DAG: pass.** The node diff changes only `proof`, `proof_deps`, and `proof_origin`.
   Its statement and Lean signature record are unchanged. The five proof steps correspond
   to the reduced presentation, fibre localization, smoothness transport, existing
   Jacobian criterion, and polynomial/prime/determinant comparison in Lean. Verified
   programmatically that `proof_deps` equals the union of the steps' `uses`. The new
   base-change dependency replaces the separate scalar-extension and tensor-quotient
   steps exactly as the report says. There are no new nodes requiring schema review.

Second-reading changes: appended this independent review and its compilation, axiom,
source, and search evidence. No repair to the Lean proof or node was needed. Holes closed:
`Algebra.exists_jacobian_minor_of_smooth_fibre_localizedPresentation` (one); holes added:
none; split off: none. This is one local hole closed using existing open dependencies,
not a claim that the target's import closure is sorry-free.
