## Worker report

The module `Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion` states
`DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology`, with its sole proof
`sorry`. No definitions or auxiliary theorems are introduced. The node is unchanged except
for `lean`. Source read: `literature/stacks-project/more-algebra.tex`, lines 16516–16552,
Tag 066E, `lemma-Noetherian-pseudo-coherent`, clause (2) and its proof.

Hypothesis and clause correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`.
- R is Noetherian: `[IsNoetherianRing R]`, namely every ideal is finitely generated.
- K belongs to D(R): `(K : DerivedCategory (ModuleCat.{max u v} R))`, with the explicit
  localization-size parameter `[HasDerivedCategory.{w} (ModuleCat.{max u v} R)]`.
  The maximum ensures that R itself and finite free modules fit in the module universe;
  u, v, w are explicitly bound. There is no restriction to a particular representative
  complex or to bounded complexes.
- K is pseudo-coherent: the recorded `DerivedCategory.IsPseudoCoherent K`.
- “if and only if”: `↔`, with both conditions on the right joined by `∧`.
- An integer b: `∃ b : ℤ`.
- Vanishing for every i > b: `∀ i : ℤ, b < i →
  IsZero ((homologyFunctor (ModuleCat R) i).obj K)`.
  Here `IsZero` is applied to the module-category object, not its underlying bare type.
- Every H^i(K) is finitely generated over R: `∀ i : ℤ,
  Module.Finite R ((homologyFunctor (ModuleCat R) i).obj K)`.
  Finite generation is required in all degrees, including i = b and negative degrees.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, lines 193–205, including `isNoetherianRing_iff_ideal_fg`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `HasDerivedCategory`, `DerivedCategory`, and `DerivedCategory.Q`, lines 68–98;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`, lines 33–41.
  These are publicly available through the recorded pseudo-coherence module.
- `def-pc-ring-pseudo-coherent-complex`: `Sheaf.RingTheory.RingPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`, full definition and docstring read: a bounded-above
  complex of finite free modules and an isomorphism in the derived category.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite` and `Module.finite_def`, lines 116–130.
- Proof dependency `lem-weil-pbc-noetherian-submodule-finite`:
  `Mathlib.RingTheory.Noetherian.Basic`, `Submodule.FG.of_le`, lines 380–383,
  imported non-publicly.
- Proof dependency `lem-weil-pbc-finite-free-resolution-noetherian`:
  `Sheaf.RingTheory.FiniteFreeResolution`, `Module.exists_finite_free_resolution`,
  full docstring and signature read; imported non-publicly.
- Proof dependency `lem-weil-pbc-pseudocoherent-cohomology-implies-pseudocoherent`
  has no `lean` or `mathlib_match` in this snapshot, so has no import. Its exact node
  statement is the final step of the declaration's proof plan. This missing proof-stage
  interface does not affect typing this statement.

The declaration docstring records all four proof steps: finite-free representative gives
upper vanishing; Noetherian cycles and quotient generators give finite cohomology;
finite-free resolutions make each cohomology module pseudo-coherent in degree zero;
Tag 066B then gives pseudo-coherence of K. No proof is implemented at stage 2.

Edge cases checked against the source and the definitions: the zero ring and zero complex
are included (no nontriviality assumption); a rank-zero free term is permitted. The bound
may be any integer, including negative integers. The assertion at i = b is finite
generation only, with no forced vanishing. Complexes with nonzero cohomology in arbitrarily
negative degrees are included. No lower bound, finite Tor dimension, cohomology freeness,
or uniform bound on the numbers of generators is assumed. Module sizes may be enlarged
arbitrarily through v; the chosen localization universe w is explicit.

Searches actually run, via `msearch.py NE <item>`:

- LeanFinder: “Over a Noetherian commutative ring a derived complex is pseudo coherent if
  and only if its cohomology is bounded above and finitely generated in every degree”.
  Eight hits, headed by `DerivedCategory.isLE_iff`, `isGE_iff` and their Q-object
  variants; all concern cohomology bounds, none the finite-cohomology criterion.
- Loogle: `"Noetherian", "Complex"`: zero hits.
- Mathlib grep: `pseudo.?coherent|noetherian.*cohomology|cohomology.*noetherian`:
  zero hits.
- LeanSearch: “Over a Noetherian ring a complex is pseudo coherent exactly when it is
  bounded above with finitely generated cohomology”: service unavailable, Internal Server
  Error; this is not recorded as a negative mathematical search result.
- `rg` on project `lean/Sheaf/RingTheory` and the upstream `WeilConjectures` tree for
  `noetherian.*[Pp]seudo|[Pp]seudo.*noetherian|isPseudoCoherent_iff` found other
  pseudo-coherence equivalences (nilpotent invariance and all-m-pseudo-coherence), not
  the criterion. A second search for finite-generation/pseudo-coherence combinations
  found upstream perfectness comments and `isPerfect_of_finiteTorAmplitude`.
  Its complete signature was read in `WeilConjectures/CategoryTheory/DerivedCategory/Perfect.lean`:
  it concludes perfectness and assumes finite Tor amplitude, so is not this statement.
- `grep -rn` for this node id in upstream `WeilConjectures` and `rg` in
  `dag/lean_names_upstream.json` returned no match.
- The chosen full declaration name was searched in Mathlib, upstream `WeilConjectures`,
  and project `lean/Sheaf`: no collision.

No node fault, statement correction, new node, dependency replacement, or
STATEMENT-DISPUTED issue was found.

Validation: server-only compilation through `scompile.py`, then `deliver2.py --no-push`;
the single file compiled cleanly in 1.1 s (nice 19, two threads, 60 s limit).
The delivery dry run printed OK: compilation and preflight passed except for the
second-reading section, which the independent second reader supplies. Nothing was pushed.
No local compiler or global build was used.


## Second reading by NE

Independent second reading: opened the sandbox node and Lean file, each of the four
statement-dependency nodes and its actual declaration, and the three proof-dependency
nodes. Read More on Algebra, `lemma-Noetherian-pseudo-coherent`, Tag 066E (2),
lines 16516–16552, including all three clauses and the proof. Read the section's opening
at lines 15854–15908, Definition 064P (2), and the pseudo-coherent clause of
`lemma-cohomology-pseudo-coherent`, Tag 066B, at lines 16252–16281. The section assumes
only a ring; clause 066E adds Noetherianity. There is no implicit field, characteristic,
nontriviality, bounded-below, or finite Tor-dimension hypothesis.

Object/hypothesis/conclusion inventory, matched individually with Lean (H3):

- Object R, a commutative ring: `(R : Type u) [CommRing R]`. Exact.
- Hypothesis R Noetherian: `[IsNoetherianRing R]`. Exact. Opened the recorded
  `IsNoetherianRing` in Mathlib/RingTheory/Noetherian/Defs.lean, lines 193–205:
  Noetherian as an R-module is equivalent to all ideals finitely generated, as the
  dependency node requires.
- Object K in the unbounded derived category D(R):
  `(K : DerivedCategory (ModuleCat.{max u v} R))`, with
  `[HasDerivedCategory.{w} (ModuleCat.{max u v} R)]`. Exact. Opened the recorded
  Mathlib/Algebra/Homology/DerivedCategory/Basic.lean, lines 68–98: localization at
  quasi-isomorphisms of integer-indexed cochain complexes. The instance chooses its
  morphism universe; it is the dependency's size convention, not a mathematical
  finiteness assumption. The maximum permits finite free R-modules in the module
  universe and arbitrary enlargement through v. All u, v, w are explicitly bound.
- Left clause K pseudo-coherent: `IsPseudoCoherent K`. Exact. Read the whole definition
  in Sheaf/RingTheory/RingPseudoCoherent.lean: existence of E and b, strict upper term
  bound, `Module.Free` and `Module.Finite` in every degree, and
  `Nonempty (Q.obj E ≅ K)`. This is exactly Definition 064P (2) and the recorded
  dependency node; neither a local scheme notion nor perfectness is substituted.
- Equivalence: `↔`. Both implications are present, with no extra antecedent. Exact.
- Existence of an integer upper bound: `∃ b : ℤ`. Exact; b depends on K.
- For every integer i above b, H^i(K) vanishes:
  `∀ i : ℤ, b < i → IsZero ((homologyFunctor (ModuleCat R) i).obj K)`.
  Exact. Read Mathlib/Algebra/Homology/DerivedCategory/HomologySequence.lean,
  lines 33–41: this functor factors the cochain homology functor through Q.
  Thus the notation homology here means the source's cohomology. IsZero applies
  to an object of ModuleCat, not to a bare underlying type.
- Every H^i(K) is finitely generated over R:
  `∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat R) i).obj K)`.
  Exact. Read the recorded Module.Finite and finite_def in
  Mathlib/RingTheory/Finiteness/Defs.lean, lines 116–130: the top submodule is FG.
  The quantifier covers all integers, independently of b; `∧` joins this with upper
  vanishing. This matches the node's quantifier order because finiteness does not
  depend on the chosen b.

Proof-interface and documentation reading (H8): step 1 uses the actual finite-free
representative from IsPseudoCoherent; step 2 uses Submodule.FG.of_le (opened
Mathlib/RingTheory/Noetherian/Basic.lean, lines 375–383), then quotients and isomorphisms;
step 3 uses Module.exists_finite_free_resolution (opened the entire existing
Sheaf/RingTheory/FiniteFreeResolution.lean, including its augmentation, differentials,
surjectivity and kernel-image clauses); step 4 uses precisely the general bounded-above
pseudo-coherent-cohomology node. The last node has no Lean declaration in this snapshot,
so there is no available proof-dependency module to import. It is not needed to type
this stage-2 statement. Both available proof interfaces are imported non-publicly.
The four-step docstring faithfully carries the node's proof. No new definition node or
dependency module is delivered, and there is no statement correction or citer verdict
requiring re-review. The only theorem in the delivery has exactly a sorry proof; no data,
private notion, local instance, local notation or auxiliary result was introduced.

Edge cases: the zero ring and zero derived object are included; finite free rank zero
is allowed by the definition. The strict inequality imposes no vanishing at i = b,
although finite generation is still required there. Arbitrarily negative b and nonzero
cohomology in arbitrarily negative degrees are covered. No restriction on characteristic,
finite generation ranks, or Tor amplitude appears. Integer degree zero is included.
There is no external index family or scheme, so empty-index and empty-scheme tests are
inapplicable. The maximum universe places R and its finite free modules in the module
universe; v allows any larger size, and w remains an explicit localization-size choice.

Independent searches actually performed with different wording:

- LeanFinder via msearch.py: “A Noetherian ring has a bounded above finite free
  representative for every derived object with finite cohomology and vanishing cohomology
  in sufficiently high degrees”. Eight hits: projective resolutions, IsKProjective,
  DerivedCategory.isLE_iff/isGE_iff, Ext/injective-dimension and single-complex morphisms.
  None states the criterion. The isLE_iff hit only identifies the vanishing clause.
- Loogle via msearch.py: `"PseudoCoherent"`; zero hits.
- LeanSearch via msearch.py: “Finite cohomology and an upper cohomological bound
  characterize pseudo coherent derived objects over Noetherian rings”. Service returned
  Internal Server Error, recorded as unavailable rather than a negative result.
- Direct rg over Mathlib, upstream WeilConjectures, and the project's lean/Sheaf for
  Noetherian/pseudo-coherent combinations and the chosen full declaration name found no
  ring criterion or name collision. Separate broader searches for pseudo-coherent and
  finite homology found upstream DerivedCategory/Perfect.lean and project scheme results.
  Opened isPerfect_of_finiteTorAmplitude, lines 415–428: it assumes finite Tor amplitude
  and concludes perfectness, so it is not this statement. Opened the full project
  NoetherianBoundedCoherentPseudoCoherent.lean: its main theorem requires two-sided
  bounds on a scheme and coherent sheaves, so it is not the present ring criterion.
- Searched the node id and declaration name in upstream WeilConjectures and
  dag/lean_names_upstream.json: no match. The actual shared ring pseudo-coherent
  definition was found and used; no second definition is appropriate (H4).

Verdict: no mathematical, dependency, documentation, or convention mismatch found.
The Lean module and node signature are unchanged; only this independent review was
appended. Checked the stored lean.statement byte-for-byte against the declaration
signature, line lengths at most 100, and all binders/universes by eye.
Validation: scompile.py compiled the delivered file on the server cleanly in 1.0 s,
nice 19, two threads, 60 seconds per file. No local compiler or library build was run.
