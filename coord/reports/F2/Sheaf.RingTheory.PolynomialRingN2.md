## What changed

Replaced the sole hole in `Sheaf.RingTheory.PolynomialRingN2.isN2_polynomial`
without changing its signature, definitions, public imports, or existing docstring.
The original node now records the implemented eight-step route.

The complete private lemma `finite_polynomial_extension` proves coefficientwise
finiteness: constant polynomials of finite module generators span all constants,
and their polynomial span contains every monomial and hence every polynomial.
The complete private lemma `isN2_polynomial_normal` splits the characteristic of
the polynomial fraction field. In characteristic zero it applies Mathlib's
`IsIntegralClosure.finite` directly, using perfect-field separability. In prime
characteristic it applies the existing N-2 purely inseparable criterion.

The main proof constructs the normalization as `integralClosure R (FractionRing R)`,
gets its module finiteness directly from `hR`, installs its Noetherianity and
normality, applies the existing N-2 finite-domain-extension ascent theorem,
proves the polynomial extension finite and injective, and applies existing
N-2 finite-extension descent. All data are actual constructions; no definition
was added or changed.

Added `Sheaf.RingTheory.PolynomialPurelyInseparableIntegralClosureFinite` for the
positive-characteristic, normal-base, finite-purely-inseparable-extension part of
Stacks Tag 032O. This is strictly part of the argument: it assumes normality,
prime characteristic, and a purely inseparable finite extension, and concludes
finiteness in that extension, rather than the full N-2 conclusion. Its full
proof in words includes the coefficient-root construction omitted by Stacks.

Added proof imports of the two existing ascent/descent modules, the new module,
`Mathlib.RingTheory.DedekindDomain.IntegralClosure`, and
`Mathlib.RingTheory.Polynomial.IsIntegral`. Kept the existing private import of
`Sheaf.RingTheory.N2CharPPurelyInseparableCriterion`.

## Proved and sorry left

Closed the one original hole: `isN2_polynomial`
(node `lem-weil-pbc-polynomial-ring-n2`). No `sorry` remains in the item's module.
Its two private helpers are completely proved.

Added one hole: `finite_polynomial_purelyInseparable_integralClosure`
(node `lem-weil-pbc-polynomial-purely-inseparable-closure-finite`) in its own new
module. Its proof is exactly `:= by sorry`. This delivery is a decomposition:
one original hole closed, one narrower hole added, net zero direct holes.

The proof also uses existing, still-unproved declarations
`isN2_of_finite_domain_extension`, `isN2_of_finite_extension`, and
`isN2_of_finite_purelyInseparable_integralClosure`; their source modules were not
modified. These are the named dependency statements intended by stage 3.

Local compilation of both modules in dependency order passed without warnings.
The final dry run performs the delivery checks and axiom probes. The item still
depends on `sorryAx` through its stated dependencies; this is a reduction, not a
claim of a fully axiom-free target proof.

## No longer needed

Removed the unused private import `Sheaf.FieldTheory.SeparableExtension`.
The characteristic-zero proof needs algebraic separability, supplied directly
by Mathlib's perfect-field instances, rather than separably generated extensions.
The node no longer uses `def-weil-pbc-separable-field-extension` or
`def-weil-pbc-transcendence-basis`. Their only planned role was that detour.
No unit statement or realized unit step was bypassed.

Direct imports of `Mathlib.FieldTheory.Perfect` and
`Mathlib.RingTheory.Polynomial.Basic` were tested and removed as redundant;
the final required proof imports already expose the needed instances.

The original main node's direct dependencies on
`def-weil-algebraic-closure`, `def-weil-algebraic-element`,
`def-weil-pbc-finite-purely-inseparable-extension`,
`def-weil-rational-function-field`, `def-weil-ring-frobenius`,
`lem-weil-pbc-field-degree-multiplicativity`, and
`lem-weil-pbc-noetherian-submodule-finite` now belong to the new purely
inseparable closure node. They are delegated, not globally pruned.

Direct uses of `lem-weil-pbc-finite-algebra-is-integral`,
`lem-weil-pbc-finite-module-over-finite-algebra`, and
`lem-weil-pbc-integral-transitive` in the original normalization argument
are encapsulated by the existing finite-extension ascent/descent lemmas.
Those nodes remain needed in the proofs of the existing dependencies;
this delivery does not claim that they disappear from the target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original characteristic-zero
route through separably generated extensions and transcendence bases is
unnecessary: finite extensions of a characteristic-zero field are already
algebraic separable in Mathlib.

The source TeX is not present in this machine's read-only literature checkout.
The actual Stacks Tag 032O page was fetched into the sandbox scratchpad and
read; its normalization, characteristic split, and purely inseparable
polynomial argument agree with the parent node. The new node retains the
canonical project source citation. The detailed coefficient-root argument
expands the source's explicit omission.

LeanSearch was attempted and returned an internal server error; it is recorded
as unavailable, not as evidence of absence. LeanFinder, Loogle, direct Mathlib
and source-library searches, and a whole-blueprint search found no existing
lemma giving the new purely inseparable closure conclusion.

Edge cases checked for the new statement: the zero ring is excluded by
`IsDomain`; the finite extension is a field and hence nontrivial; prime
characteristic excludes p=0 and p=1; q=p^e is positive, including q=1;
the trivial extension is permitted; a field base is permitted. The final
submodule finiteness step retains the Noetherian hypothesis.

## New nodes

`lem-weil-pbc-polynomial-purely-inseparable-closure-finite` realizes original
Steps 5 to 8 for a normal Japanese base. Its module is
`lean/Sheaf/RingTheory/PolynomialPurelyInseparableIntegralClosureFinite.lean`.
Its source is Stacks Tag 032O, second assertion, positive-characteristic proof.
It has a complete four-step proof in words, its statement dependencies, the
actual search results, and the exact compiled Lean signature. The parent
node imports and applies it after the characteristic split. No change
record is needed because no existing public interface changed.

## Second reading by F2

1. **Interfaces: pass.** Compared the delivered parent module with the repository
   using `diff -u`. The existing `isN2_polynomial` signature and its docstring
   are byte for byte unchanged. All existing public imports remain unchanged;
   the added imports are private proof imports. No definition or existing
   statement changed, and no change record is needed. The only delivered new
   public statement is the explicitly reported purely inseparable closure lemma.

2. **Proof and axioms: pass as a decomposition.** Both delivered modules compiled
   locally in dependency order without errors or warnings. Scratch copies with
   `#print axioms` checked all four declarations: the coefficientwise finiteness
   helper uses only `propext`, `Classical.choice`, and `Quot.sound`; the normal-base
   helper, original theorem, and split theorem additionally use `sorryAx`.
   The only delivered hole is exactly the named split theorem reported above.
   No forbidden declaration mechanism or hollow definition occurs. Normalization
   is the actual `integralClosure` construction; no arbitrary witness is chosen
   from an unproved existence theorem. The normalization ascent, polynomial
   extension finiteness and injectivity, characteristic split, and descent all
   have the claimed types. This is one original hole closed and one narrower
   hole added, net zero direct holes, with existing dependency holes still open.

3. **Split statement: pass.** Read its full docstring and four node proof steps
   against the saved Stacks Tag 032O text. The common Frobenius exponent, finite
   coefficient-root field, embedding into K′(t), normal closure A[t], and generators
   a_j t^r give a complete mathematical argument. The nonzero denominators and
   transcendence of t are justified. Checked field bases, trivial extensions,
   q=1, and the exclusions of the zero ring and p=0,1; Noetherianity supplies the
   final finite-submodule step. Normality and purely inseparable extensions make
   this strictly part of the original argument, not a restatement of N-2.
   Repeated LeanFinder and Loogle with different queries and searched Mathlib,
   upstream, and Sheaf sources. No existing theorem closes this hole. It requires
   substantial field and polynomial constructions, beyond a few-minute repair.

4. **Route and pruning: pass.** Characteristic zero uses Mathlib directly;
   normalization and characteristic p use the already stated ascent, descent,
   and purely inseparable criterion. The finite polynomial extension helper is
   a direct coefficient-span proof. Each remaining import supplies statements,
   instances, or a theorem used by this route. Compared the full old/new
   `proof_deps`: all twelve removed direct dependencies are accounted for in
   `No longer needed`, including the dependencies delegated to the new node or
   encapsulated by existing ascent/descent. This does not claim those modules
   vanish from the targets' closure. Read `dag/units/sk-thm-p1.json`, including
   `realized`: the polynomial lemma is below its realized statement and steps;
   no realized unit statement or step is removed or bypassed.

5. **DAG: pass.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Its eight steps describe the implemented Lean route, including
   the three existing dependency theorems and new split lemma. Both nodes'
   `proof_deps` exactly equal the union of step `uses`. The new node has the
   required source, blueprint provenance, self-contained statement, searches,
   creation metadata, chapter/unit, and Lean declaration record. Its signature
   agrees with the Lean theorem. Source attribution now explicitly distinguishes
   the source's omitted details from the worker's expansion.

Second reading changed no Lean proof or statement. It clarified the new node's
proof-origin attribution, recorded the independent searches on that node, and
added this review. The proof is accepted as a decomposition, with no claim of
an axiom-free proof of the target.
