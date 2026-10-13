## What changed

Replaced the sole `sorry` in `lean/Sheaf/Paper/CyclicExtensionCocycle.lean`,
`Paper.cyclic_extension_cocycle`, with a complete proof of all three clauses.
The existing signature, docstrings, public imports, and visibility are unchanged.
No other module is changed.

The proof follows the existing node's five-step route. Write
`d = e.constr A f`, `g x = e.constr A x`, and `r x = (g x).prod (-d)`.
Mathlib's `Module.Basis.constr_range` identifies the ranges of `d` and `r x`
with `J` and the relation submodule. The basis extensionality theorem identifies
`μ.comp W.mkQ` with `d`. For admissible `x`, its quotient map `xhat` identifies
`g x` with `xhat.comp W.mkQ`, so `g x` vanishes on the kernel of `d`.

The projection is explicitly constructed by `Submodule.liftQ`. Its kernel is
calculated on representatives using the range of `d`, and injectivity of the
first inclusion uses the preceding vanishing statement. In an arbitrary
extension, exactness supplies each `x i`, with uniqueness from injectivity of
`j`. The basis map `g x` descends through `W`, and injectivity of `j` proves
admissibility. The explicit map `(p,a) ↦ j p + a • lift` has kernel exactly the
relation submodule and is surjective; `LinearEquiv.ofBijective` constructs the
required equivalence from its quotient map. The inverse is chosen from a
proved bijectivity statement, hence is uniquely determined.

For change of lift, use `xhat - (toSpanSingleton m).comp μ` and the explicit
linear equivalence `(p,a) ↦ (p + a • m,a)`, whose inverse subtracts `a • m`.
`Submodule.map_span` checks the image of the relation submodule, and
`Submodule.Quotient.equiv` induces the quotient equivalence. All requested
compatibilities are proved on representatives.

Searches ran through `msearch.py`: LeanFinder for extension classification,
Loogle for `Submodule.span, LinearMap.range`, and grep for quotient/exactness
lemmas. Searches of the project found no existing classification theorem.
Loogle found the basis range lemma used in the proof. Stacks Tags 05ED and
05EE were read online because this clone lacks the cited local `.tex` file.

## Proved and sorry left

Closed: `Paper.cyclic_extension_cocycle`
(node `lem-weil-pbc-cyclic-extension-cocycle`), one of one original holes.
Added holes: none. Remaining holes: none. No new theorem, definition, or
intermediate statement is introduced. The full file compiles with
`lcompile.py` without warnings.

## No longer needed

None of the original imports, nodes, or modules is pruned. The proof uses the
existing free-module, quotient-module, direct-sum, and exactness dependencies
through their Mathlib interfaces. A trial proof import of
`Mathlib.LinearAlgebra.Basis.Basic` was removed: the existing imports already
supply all needed declarations. No proof dependency is added. The existing
node proof and its dependency list still describe the implemented argument;
the blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The cited local file
`literature/stacks-project/more-algebra.tex` is absent on this machine;
the corresponding official Stacks pages were read instead. The hypothesis
`ht : 1 ≤ t` is unnecessary for the argument, but its original binder and the
entire statement are retained unchanged. The proof also covers zero generators,
zero modules, the zero ring, and the unit ideal without additional assumptions.

## Second reading by E2

1. **Interface preservation — pass.** Compared the sole delivered module with
   the repository using `diff -u`. The entire declaration signature, including
   `ht : 1 ≤ t`, the universes, the existential projection, all three clauses,
   and every compatibility equation, is byte for byte unchanged. There are no
   other delivered declarations, definitions, node changes, or change records.
   Only the proof differs. All original public imports are preserved.

2. **Proof and axioms — pass.** Independently compiled the original delivered
   file with `lcompile.py`, without warnings or errors. Compiled a scratch copy
   of the proof with the original imports and
   `#print axioms Paper.cyclic_extension_cocycle`; the output is exactly
   `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, forbidden declaration,
   or hollow definition occurs. The coordinate choice `x` is made from proved
   exactness and is uniquely determined by the injectivity of `j`; `xhat` and
   both quotient maps are actual `liftQ` constructions. The inverse of `theta`
   comes from the proved bijectivity of its explicit forward map.

3. **Split-off statements — pass, none.** No lower hole or new statement was
   introduced. Checked the signs on representatives: adding `r x b` changes
   `(p,a)` to `(p + g x b,0)`, while a kernel pair is `r x (-b)`.
   For `t = 1`, all Koszul relations vanish but admissibility still kills
   `ker d`; for zero generators, admissibility forces every coordinate to
   vanish. If `J` is the unit ideal, the projection is zero and exactness
   identifies the whole quotient with the included `P`. The proof requires
   neither nonzero modules nor a nontrivial ring. No unproved existence is
   used to choose data.

4. **Shortest route, imports, and blueprint — pass.**
   Read Mathlib's `Basis.constr_range`, quotient kernel/lift lemmas, and the
   exactness descent lemmas in `Algebra.Exact.Basic`; the latter require an
   already exact sequence and do not replace the central kernel computation.
   Searched `lean/Sheaf`, `lean/WeilConjectures`, the upstream algebra and
   algebraic-geometry directories, and Mathlib's module presentation and
   injective-module files for cyclic extensions, Koszul cycles, and quotient
   classification. Found no existing theorem giving these three clauses.
   The supplied proof already uses the basis range lemma to avoid explicit
   sums, so I retained it. A scratch compilation showed that quotient Defs
   alone lacks `Ideal.span`; quotient Basic suffices for this file. However,
   narrowing the existing public Operations import changes the downstream
   exported interface, and the dry-run preflight requires an interface change
   record. Restored the original import to preserve that interface; this module
   supplies ideal span and ideal quotient notions appearing in the signature.
   All other retained imports also supply signature notions. There are no new
   proof-only public imports. The four
   original DAG proof dependencies are all used as mathematical notions;
   none is obsolete. Read `dag/units/sk-thm-p1.json`, including `realized`:
   this supporting algebra lemma bypasses no realized unit statement or step.

5. **DAG agreement — pass.** Read the complete node
   `lem-weil-pbc-cyclic-extension-cocycle` and its four dependency nodes.
   Step 1 is implemented by `hd`, `hdr`, `hr`, and `hkill`; step 2 by the
   quotient projection and its injectivity/exactness/surjectivity proofs;
   step 3 by `hfi`, `hcycle`, and `hxadm`; step 4 by `hker`, `hsurj`, and
   `theta`; step 5 by `xhat'`, `shear`, and `hshear`. The free-module,
   quotient-module, direct-sum, and module-exactness notions agree with the
   dependencies' recorded Mathlib interfaces (binary direct sums are products).
   The existing `proof`, `proof_deps`, and `proof_origin` remain accurate.
   Independently read [Stacks 05ED](https://stacks.math.columbia.edu/tag/05ED)
   (naive Koszul presentation) and
   [Stacks 05EE](https://stacks.math.columbia.edu/tag/05EE)
   (extensions through maps from the ideal): the construction implements the
   stated explicit extension interpretation with all original hypotheses.

**Changes made by the second reader:** added this independent review. A trial
 import reduction was reverted after the preflight identified a public-interface
 change; the final Lean file is the first worker's file unchanged. No mathematical
 proof repair was needed; one original hole is closed, zero holes are added,
 and zero holes remain. No DAG node or project module is pruned.
