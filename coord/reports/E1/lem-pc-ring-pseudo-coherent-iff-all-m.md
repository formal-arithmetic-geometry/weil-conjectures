## Worker report

The repaired module states the equivalence of conditions (1) and (2) of
[Stacks Tag 064U](https://stacks.math.columbia.edu/tag/064U), with a `sorry` proof.
It introduces no definition and no new node.

Hypotheses and clauses:

- `R : Type w` and `[CommRing R]` give the source's commutative ring (the convention
  throughout More on Algebra).
- `C : CochainComplex (ModuleCat.{w} R) ℤ` is a cochain complex of ring modules.
- `Q.obj C` views that complex in the derived category.
- `IsPseudoCoherent (Q.obj C)` means existence of a strictly bounded-above complex
  with every term finite free, isomorphic to `Q.obj C` in the derived category.
- `∀ m : ℤ, IsMPseudoCoherent m (Q.obj C)` quantifies over every integer. The landed
  predicate supplies a complex bounded below and above, every term finite free, and
  a derived-category map inducing cohomology isomorphisms above `m` and an epi at `m`.
- `↔` states both implications without additional hypotheses.

Dependency declarations read and used: `DerivedCategory.IsPseudoCoherent` in
`Sheaf.RingTheory.RingPseudoCoherent` (node def-pc-ring-pseudo-coherent-complex), and
`DerivedCategory.IsMPseudoCoherent` in `Sheaf.RingTheory.MPseudoCoherent` (node
 def-pc-ring-m-pseudo-coherent). Their ring arguments are implicit; the integer is
first in `IsMPseudoCoherent`. The Mathlib match for def-weil-abstract-derived-category
is `DerivedCategory` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`, with
`DerivedCategory.Q` the localization functor. Its signature and docstring were read.
`HasDerivedCategory.standard` supplies the chosen localization locally.

Edge cases checked: all integer degrees, including negative degrees and zero;
the zero complex and zero ring; no Noetherian, characteristic, boundedness, or
finite-dimensional hypothesis on `C`. The explicitly bound universe `w` is arbitrary.

Searches (original runs retained in searches.jsonl): LeanFinder query
“pseudo-coherent complex of modules iff m-pseudo-coherent for every integer” returned
bounds and K-projectivity results, no equivalence; Loogle query
`PseudoCoherent, DerivedCategory, bounded finite free` returned no hits; Mathlib grep
`pseudo.?coherent|PseudoCoherent` under Algebra/Homology returned no hits. LeanSearch
was unavailable. Repair-time `rg` for `IsPseudoCoherent|IsMPseudoCoherent` across
Mathlib/Algebra/Homology, the source WeilConjectures, and lean/Sheaf confirmed the
landed predicates in RingPseudoCoherent.lean and MPseudoCoherent.lean, and their users;
no existing iff declaration was found. The sole citer remains
lem-pc-ring-pseudo-coherent-localization-glue.

Return repairs:

- H12/H4/H9: removed the duplicate new definition node and PseudoCoherent.lean;
  imported RingPseudoCoherent and MPseudoCoherent and cited their landed nodes.
- H8: expanded the docstring to include the upper cohomology bound from
  0-pseudo-coherence, the descending-induction base, the kernel-killing extension,
  and adjoining `R^r` mapped to cocycles generating the remaining cokernel.
- H11: corrected all predicate argument orders and removed the inaccurate claim
  of two new nodes. The previous second reading was removed because it described
  obsolete files and missed landed declarations; an independent second reader
  must read the repaired module before delivery.

No statement dispute. The existing statement correction is retained below.
Server compilation passed cleanly (exit code 0, 1.4 seconds). The delivery dry run
printed OK: compilation and preflight passed except for the independent second reading,
which the second reader writes. Nothing was pushed.

## Statement corrected

Old statement: the final sentence introduced “a complex of $R$-modules [def-pc-cochain-complex-modules]”.
That dependency node is specifically the sheaf-of-modules complex notion, so it did not match the
ring-level object in Tag 064U. Following Tag 064U, the corrected wording is “a cochain complex
of $R$-modules, viewed as an object of $D(R)$”; the Lean signature already had exactly this
ring-level object. The sole citer `lem-pc-ring-pseudo-coherent-localization-glue` holds: true,
because its use is of the ring-level pseudo-coherence equivalence.

## Second reading by E1

I read the sandbox node and module independently, all three statement-dependency
nodes, and the declarations in RingPseudoCoherent.lean, MPseudoCoherent.lean and
Mathlib/Algebra/Homology/DerivedCategory/Basic.lean. The Stacks checkout is absent
under this clone's literature directory; I read the actual Stacks .tex at
/home/ubuntu/c1-stacks-review/more-algebra.tex, lines 15853–15903 and 16046–16142,
and its tags/tags mapping. Tag 064U is lemma-pseudo-coherent; the definitions are
at definition-pseudo-coherent (064Q). The Stacks conventions.tex line 51 states
that a ring is commutative with 1. Thus CommRing is the source convention,
not an extra Noetherian or characteristic assumption.

Object/hypothesis/conclusion inventory and matching:

1. A ring R: `(R : Type u) [CommRing R]`; exact under the source convention.
2. The abelian category of R-modules and its derived category: `ModuleCat.{v} R`
   and `[HasDerivedCategory.{w} (ModuleCat.{v} R)]`. Reading Basic.lean shows this
   instance chooses a localization at quasi-isomorphisms, with morphisms in w;
   it is the dependency's chosen-universe convention, not a finiteness hypothesis.
3. An arbitrary integer-indexed cochain complex: `(C : CochainComplex
   (ModuleCat.{v} R) ℤ)`; no boundedness assumption on C. `Q.obj C` is its image
   in precisely that localization. Exact.
4. Pseudo-coherence: `IsPseudoCoherent (Q.obj C)`. Its landed definition existentially
   quantifies E and an integer upper bound, requires `E.IsStrictlyLE b`, and requires
   `Module.Free R (E.X j)` and `Module.Finite R (E.X j)` in every degree. The final
   `Nonempty (Q.obj E ≅ Q.obj C)` expresses quasi-isomorphism in D(R), as the node
   states. Finite and free together mean finite free; no alternate local notion.
5. For each integer m, m-pseudo-coherence: `IsMPseudoCoherent m (Q.obj C)`.
   Its definition quantifies E, integer lower/upper bounds a,b, requires strictly
   bounded E and finite free terms, then a morphism `f : Q.obj E ⟶ Q.obj C`.
   `∀ i : ℤ, m < i → IsIso ((homologyFunctor ... i).map f)` gives exactly the
   isomorphisms above m; `Epi ((homologyFunctor ... m).map f)` gives surjectivity
   in degree m in ModuleCat. It neither requires an isomorphism at m nor any
   condition below m. Exact.
6. Both implications, for every m: `IsPseudoCoherent (Q.obj C) ↔
   ∀ m : ℤ, IsMPseudoCoherent m (Q.obj C)`. Witnesses may depend on m, as required.
   Tag 064U has additional equivalent conditions and a sharpened upper bound;
   this node requests only (1) iff (2), and exactly those are stated.

The recorded statement correction was checked against the .tex before matching
Lean: removing the sheaf-complex citation gives the ring-module complex actually
introduced in Tag 064U, without weakening or strengthening anything. A fresh
search of dag/nodes for this item's id finds exactly one external citer,
lem-pc-ring-pseudo-coherent-localization-glue. I read its statement and proof
step 4: it applies the forward direction locally for every integer and the
reverse direction globally. Its holds:true verdict is correct. There is no
second citer to inspect. No new definition nodes or dependency modules remain
in this delivery, and no missing notion requires one.

Edge cases: m ranges over all integers, including zero and negative values.
The zero complex and zero ring are allowed (zero modules are finite free of
rank zero). There is no nontriviality, characteristic, Noetherian, cohomology
finiteness or boundedness assumption on C. Empty schemes and index sets do not
occur in this ring-level statement. Rings, module carriers and localization
morphism universes now have independent explicitly bound u, v and w, matching
the dependency signatures and allowing the chosen localizations of the citer.

Independent searches, recorded by msearch.py in searches.jsonl:
LeanSearch query `finite free bounded above resolution equivalent to finite free
approximations in every cohomological degree` was unavailable (Internal Server
Error). Loogle query `"coherent"` returned unrelated quotient/topological and
quasicoherent-sheaf declarations, no pseudo-coherence equivalence. Mathlib grep
`pseudo.?coher|forall_isMPseudo|finite.free.*approx` returned zero hits.
The same rg over WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
found only prose in upstream DirectImage.lean and the landed predicates and
other ring pseudo-coherence lemmas; none states this equivalence. This avoids
duplicating a Mathlib or upstream notion and uses both recorded dependencies.

Mismatches repaired:
- H3: the old theorem tied ring and module universes to w and selected the standard
  derived category locally. I replaced that specialization by independent u/v/w
  and the explicit chosen-localization instance used by both dependency nodes;
  removed the local standard instance. The original binder list would not
  directly apply to the citer's arbitrary chosen localization.
- H8: the docstring did not state the triangle lemma's stage-n hypothesis.
  I made explicit that the bounded finite-free F is n-pseudo-coherent by its
  identity, while C is (n-1)-pseudo-coherent, so clause one with m=n-1 applies.
  The remaining kernel-killing and cokernel-generating construction matches
  the source's proof and is retained.
- Updated lean.statement verbatim to the repaired signature. The corrected
  natural-language statement and its correction record are unchanged.

No hollow definitions, additional declarations or proofs were added. Both imports
are used, every variable/universe is bound, the only proof remains `by sorry`,
and module/declaration docstrings retain the source and blueprint id. The repaired
single file compiled cleanly on the server (exit code 0, 1.4 s, no warnings).
