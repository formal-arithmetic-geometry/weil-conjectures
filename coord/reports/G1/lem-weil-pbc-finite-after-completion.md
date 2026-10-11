## Worker report

The module `lean/Sheaf/Algebra/FiniteAfterCompletion.lean` states the completion finiteness lemma from Stacks Algebra Tag 0394 (blueprint `lem-weil-pbc-finite-after-completion`). It uses Mathlib's `AdicCompletion` and `Module.Finite`. The source rings are explicit commutative rings `R` and `S`, both local, with ideals `m` and `n` identified with their maximal ideals by `hm` and `hn`; `φ` is a local ring homomorphism (`[IsLocalHom φ]`). The finite-generation hypotheses are `hm_fg` and `hn_fg`, and `hlocal` renders `φ(m) ⊆ n`. The special-fibre finite-dimensional hypothesis is rendered by `hfinite : Module.Finite (R ⧸ m) (S ⧸ Ideal.map φ m)` together with the quotient algebra instance.

The conclusion gives an isomorphism `γ : AdicCompletion (Ideal.map φ m) S ≃+* AdicCompletion n S` preserving the canonical maps from `S`, a completion ring map `φhat : AdicCompletion m R →+* AdicCompletion n S` preserving the canonical maps from `R`, and finite generation of the target over the source using `letI := φhat.toAlgebra`.

Dependency declarations used: `AdicCompletion` from `Mathlib.RingTheory.AdicCompletion.Basic` (via `Mathlib.RingTheory.AdicCompletion.Algebra`), and `Module.Finite` from `Mathlib.RingTheory.Finiteness.Defs`; these are the declarations recorded by `def-weil-pbc-adic-completion` and `def-weil-finitely-generated-module`.

Edge cases checked: arbitrary universe levels `u v`; no nonzero-ring, noetherian, or positive-exponent assumptions are added; ideals and local rings are explicit, so zero and residue-field cases remain included.

Searches: LeanSearch query “completion of a local ring with finitely generated maximal ideal is finite over completion of base if fibre S/mS is finite dimensional” (no match); LeanFinder query “local homomorphism of local rings, S/mS finite over residue field, then completion of S is a finite module over completion of R” (no exact match); Loogle query `Module.Finite (AdicCompletion _ _) _` (no results); grep of Mathlib AdicCompletion files and project `WeilConjectures/` (no existing theorem). The dependency notions are Mathlib matches, so no new nodes or dependency modules were needed.

## Earlier second reading (a previous round; superseded)

Reading the node and file clause by clause: local rings and the local map are represented by `[IsLocalRing R]`, `[IsLocalRing S]`, and `[IsLocalHom φ]`; `m,n` are their maximal ideals via `hm, hn`; finite generation is `m.FG`, `n.FG`; the map condition is `Ideal.map φ m ≤ n`; the finite-dimensional fibre is the quotient `Module.Finite`; (1) is the ring isomorphism `γ` preserving canonical completion maps; (2) is the finite module conclusion after installing the algebra induced by `φhat`. No clause of the node is omitted in the Lean statement.


## Second reading by G1

I independently opened the original node, sandbox node and module, both dependency nodes and
Mathlib declaration bodies. The node has no statement correction, new definition node or
dependency module. Its mathematical statement is correct and remains unchanged.
The original worker report describes the earlier signature; this section records the repaired
signature and supersedes that description.

Source reading: this machine has no literature/stacks-project checkout. I read the official
Stacks algebra.tex at https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
label lemma-finite-after-completion (Tag 0394), statement and entire proof, together with the
chapter's Conventions section (commutative rings with 1). The source assumes local rings,
a local map, finitely generated maximal ideals and finite-dimensional special fibre; it adds
no Noetherian, injectivity, finite-type, characteristic or same-universe assumption.

Objects, hypotheses and conclusions, listed independently from the node and matched:

1. Commutative local rings R and S: `(R : Type u) (S : Type v) [CommRing R]
   [CommRing S] [IsLocalRing R] [IsLocalRing S]`. Exact, separate arbitrary universes.
2. Their maximal ideals m and n: `(m : Ideal R) (n : Ideal S)` and equalities `hm`, `hn`
   with `IsLocalRing.maximalIdeal`. Exact; these are not arbitrary nonmaximal ideals.
3. Local homomorphism φ: `(φ : R →+* S) [IsLocalHom φ]`; `hlocal : Ideal.map φ m ≤ n`
   writes the containment stated by the node. This containment is redundant, not stronger.
4. Finitely generated maximal ideals: `hm_fg : m.FG`, `hn_fg : n.FG`. Exact.
5. Extended ideal mS and special fibre: `Ideal.map φ m` and `S ⧸ Ideal.map φ m`.
   `hfinite` installs `(Ideal.quotientMap (Ideal.map φ m) φ Ideal.le_comap_map).toAlgebra`
   before asserting `Module.Finite (R ⧸ m) (S ⧸ Ideal.map φ m)`. Exact induced action.
   R/m is a field mathematically because hm identifies a maximal ideal; no extra field
   instance or axiom is needed to express its finite dimension as Module.Finite.
6. R-completion, n-adic S-completion and mS-adic S-completion: respectively
   `AdicCompletion m R`, `AdicCompletion n S`, `AdicCompletion (Ideal.map φ m) S`.
   The latter is S' because ideal map commutes with powers. Exact dependency notion:
   Basic.lean defines compatible families; Algebra.lean supplies componentwise ring
   operations and `evalₐ I k : AdicCompletion I R →ₐ[R] R ⧸ I ^ k`.
7. Canonical comparison γ is an isomorphism: existential `γ : AdicCompletion
   (Ideal.map φ m) S ≃+* AdicCompletion n S`, with the first universal component clause.
   For every k, x, representative s of x_k, the k-component of γ(x) is s modulo n^k.
   Quotient representatives always exist; this specifies precisely the canonical map,
   not just its values on the image of S. Exact clause (1).
8. Canonical φ-completion map: existential `φhat : AdicCompletion m R →+*
   AdicCompletion n S`, with the second universal component clause. For every k, x
   and representative r of x_k, its k-component is φ(r) modulo n^k. Exact; this fixes
   the map on the whole completion and the order of its component quantifiers.
9. Finiteness of S-completion for that map: `letI := φhat.toAlgebra; Module.Finite
   (AdicCompletion m R) (AdicCompletion n S)`. Exact clause (2), not finiteness over R.
   Finiteness dependency source Finiteness/Defs.lean identifies Module.Finite with
   finite generation of the top submodule, as the dependency node requires.

Mismatches repaired:

- H3: removed the arbitrary special-fibre Algebra instance, which did not connect its
  action with φ. hfinite now installs the canonical quotient ring map's algebra.
- H3: the earlier γ and φhat clauses only specified values on original-ring elements.
  Replaced them by component conditions on arbitrary completion elements, giving the
  actual canonical maps named in the node without any continuity assumption.
- H8: expanded the abbreviated proof docstring to the node's seven steps, naming all
  the proof dependencies in their relevant steps and describing module-action comparison,
  completeness, separation and the finite special-fibre quotient.
- H9: moved the module from Algebra to RingTheory and changed the root camel-case name
  to `AdicCompletion.finite_after_completion`; synchronized lean.file/module/declaration
  and copied the final signature verbatim into lean.statement. No node mathematics changed.

Edge cases: k ranges over all ℕ, including k = 0 (quotients by the unit ideal are zero,
so both component clauses remain valid). Zero maximal ideals and maps of fields are
included; no positive-power or nonzero-module assumption appears. The zero ring is
excluded by the local-ring hypothesis in the source itself (a local ring has a unique
maximal ideal), not by an added hypothesis. Empty index sets and empty schemes are not
objects in this statement; the inverse system is the specified natural-number tower.
Every characteristic and independent universe u, v are allowed. No finite-dimensional
field hypothesis replaces a ring hypothesis on R or S.

Independent duplicate searches used different words from the worker:

- LeanFinder via msearch.py: `finite module between completions of local rings with finite
  residue fibre`, 8 hits, including residue-field finiteness and quasi-finite fibres;
  their signatures concern residue fields or fibres, not completions. No exact match.
- Loogle via msearch.py: `AdicCompletion, Module.Finite`, 10 hits. The tensor-product
  comparison assumes finite generation of the original module (and usually Noetherianity);
  exactness/injectivity results also differ. None states the present local-map theorem.
- grep via msearch.py: `finite_after_completion|finiteAfterCompletion|0394`, zero hits.
  Direct rg also searched Mathlib, WeilConjectures, repository lean/Sheaf and upstream
  names. Broader `completion.*finite|finite.*completion` in project/source found other
  finite-extension, quotient and quasi-finite-prime theorems; their settings differ.
- LeanSearch via msearch.py: `local ring completion finite module finite special fibre`
  returned UNAVAILABLE (Internal Server Error), recorded as unavailable, not a no-match.

No new notion was introduced: quotientMap, Ideal.map, AdicCompletion and Module.Finite
are existing Mathlib constructions. There is no hollow definition and only the named main
theorem's `sorry`; no theorem was proved. All binders and universes are explicit. The final
63-line module compiled with scompile.py without errors or warnings. Required dry-run
and delivery checks follow.

Validation: deliver2.py --no-push printed OK: the delivery compiles and passes the
maintainer's stage-2 preflight (dry-run commit 59974b04b).
