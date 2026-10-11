## Worker report

The module [FlatPermanence.lean] states the Stacks Tag 039V permanence lemma.  It binds
commutative rings `R` and `S`, a ring homomorphism `φ : R →+* S`, and an additive
commutative `S`-module `M`.  The hypothesis `[Module.FaithfullyFlat S M]` renders faithful
flatness over `S`.  The explicit hypothesis
`hM : letI := Module.compHom M φ; Module.Flat R M` renders flatness of `M` over `R`
using the scalar action induced by `φ`; this avoids introducing an unrelated `R`-action.
The conclusion `RingHom.Flat φ` is flatness of the ring map.

The proof is `sorry` as required at stage 2.  Its docstring records the four proof steps:
reduce flatness to injectivity after tensoring, use flatness of `M`, cancel base change,
and reflect exactness using faithful flatness.  The dependency declarations used by the
proof are Mathlib's `RingHom.Flat`, `Module.Flat`, `Module.FaithfullyFlat`, and
`TensorProduct.AlgebraTensorModule.cancelBaseChange` (the latter is cited in the node's
proof, though no proof term is written here).

Edge cases checked: arbitrary universe levels `u`, `v`, `w`; no nontriviality, finite
presentation, or characteristic assumptions; and the induced `R`-module action is tied
to `φ` by `Module.compHom`.

Searches made: the node's recorded LeanSearch, LeanFinder/Loogle, and grep searches found
no combined permanence theorem.  Repository searches (`rg -n "FaithfullyFlat|RingHom.Flat"`
under `lean/Sheaf` and `WeilConjectures`) found only separate flatness APIs.  Mathlib
signatures were read in `RingTheory/RingHom/Flat.lean`,
`RingTheory/Flat/FaithfullyFlat/Basic.lean`, and
`LinearAlgebra/TensorProduct/Tower.lean`; no existing declaration has this statement.

Fresh searches on 2026-10-11:
- LeanFinder: "If an S-module M is flat over R and faithfully flat over S then S is flat
  over R" returned eight related results, including `FaithfullyFlat.trans` and
  `Flat.of_flat_tensorProduct`; neither has this direction or these hypotheses.
- Loogle: `Module.FaithfullyFlat, Module.Flat` returned twelve related results; no match.
- LeanSearch: "An S-module flat over R and faithfully flat over S implies S is flat over R"
  was unavailable (Internal Server Error).
- Mathlib grep: `flat_permanence|039V|flat_of_flat_module` under RingTheory returned no hits.
- Project/upstream-name grep for the item id and proposed declaration found only two
  proof-docstring references to this node, no declaration.

The local literature checkout is absent. Source verified against
https://stacks.math.columbia.edu/tag/039V, whose statement agrees with the node.
No correction, new node, or dependency module is required. The two statement dependencies
are Mathlib leaves: `Mathlib.RingTheory.RingHom.Flat` (`RingHom.Flat`, `Module.Flat`) and
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` (`Module.FaithfullyFlat`). The equivalence
with the exactness formulation is `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`.
Zero rings and zero modules are permitted: faithful flatness of a zero module forces the
base ring to be zero, and that case is retained without a `Nontrivial` binder.

## Second reading by J1

I independently opened the item node, the delivered Lean file, both statement-dependency
nodes, and the Mathlib declarations they record. I read the source statement and proof at
[Stacks Tag 039V](https://stacks.math.columbia.edu/tag/039V), and the raw
[algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex),
labels `lemma-flat-permanence`, `definition-flat`, and `section-conventions`.
The local literature checkout is absent. Current upstream line numbers differ from the
node's recorded checkout; the labels and tag identify the same statement. The chapter
conventions explicitly permit the zero ring and require commutative rings with identity;
the flatness section imposes no further standing hypotheses.

Object/hypothesis/conclusion checklist (node first, then its Lean rendering):

1. Arbitrary rings R and S: `{R : Type u} {S : Type v}` and `[CommRing R]
   `[CommRing S]`. PASS: commutativity and identity are source conventions, not added
   assumptions. Both carriers and all their ring structures are universally quantified.
2. A ring map R to S: `(φ : R →+* S)`. PASS: an arbitrary unital ring map, with no
   injectivity, locality, finiteness, or field hypothesis.
3. An S-module M: `{M : Type w} [AddCommGroup M] [Module S M]`. PASS: arbitrary module
   over the given S; no finite generation or nontriviality constraint.
4. M flat as an R-module through the given map: `hM : letI := Module.compHom M φ;
   Module.Flat R M`. PASS: I opened `Algebra/Module/RingHom.lean:57`; `compHom` acts by
   `r • m = φ r • m`. Thus no unrelated R-module structure is quantified or assumed.
   I opened `RingTheory/Flat/Basic.lean:113` and the injectivity equivalences at lines
   300–319. This is exactly the notion of `def-weil-pbc-flat-ring-map`, whose recorded
   declarations are `Module.Flat` and `RingHom.Flat`.
5. M faithfully flat as an S-module: `[Module.FaithfullyFlat S M]`. PASS: I opened
   `RingTheory/Flat/FaithfullyFlat/Basic.lean:63`, and
   `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact` at line 424. The class is equivalent
   to preservation and reflection of exactness from `def-weil-pbc-faithfully-flat-ring-map`.
   Writing this proposition as an instance does not strengthen it. It is not a hollow
   hypothesis: the zero module over a nonzero ring fails it.
6. Conclusion R to S flat: `RingHom.Flat φ`. PASS: I opened
   `RingTheory/RingHom/Flat.lean:27`; it installs `φ.toAlgebra` and asserts `Module.Flat R S`
   with that action. This is the sole conclusion of both the node and Tag 039V. The
   order of the two hypotheses has no quantifier dependency and changes no meaning.

Edge cases: independent universes `u v w` are all bound; none imposes a size relation.
The equivalence criteria use test modules in `max` universes and do not introduce a
vacuous independent smaller universe. Zero R, zero S and the zero module are retained.
For a zero module faithful flatness forces S to be zero (otherwise a maximal ideal
violates `submodule_ne_top`); the resulting zero target is flat over every R. No
characteristic restriction occurs. Empty index sets, empty schemes and n = 0 are not
parameters of this ring/module statement. No hidden Noetherian, finite presentation,
scalar-tower, or algebra instance is required.

Independent duplicate searches on 2026-10-11:

- LeanFinder: "descent of flatness of the intermediate ring from a faithfully flat
  module over it" returned eight results. `Module.Flat.trans` and
  `Module.FaithfullyFlat.trans` have the opposite direction; `Flat.of_flat_tensorProduct`
  assumes S faithfully flat over R, rather than M faithfully flat over S. I opened its
  signature and proof at Basic.lean:588. None states this node.
- Loogle: `Module.FaithfullyFlat, Module.Flat` returned twelve results, all separate
  criteria or the different base-change descent theorem. No exact match.
- LeanSearch: "A faithfully flat S module which is flat over R implies the ring map R
  to S is flat" returned Internal Server Error; recorded as unavailable, not a negative
  result. The other independent searches completed.
- `rg` for permanence, faithful-flat module hypotheses and flatness descent names in
  Mathlib's `RingTheory/Flat` and `RingTheory/RingHom` found only the different statements
  above and tensor-product injectivity descent. Searches for the declaration, item id,
  `FlatPermanence`, and related phrases in `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no duplicate declaration. The two project
  references to this item are proof-docstring references, not statements.

No missing notion, new node, dependency module, or statement correction is needed.
Both recorded statement dependencies are usable Mathlib notions. The proof dependency
`TensorProduct.AlgebraTensorModule.cancelBaseChange` was also opened in Tower.lean:436;
its equivalence and naturality give exactly docstring step 3. The declaration docstring
contains the source and blueprint id and all four node proof steps: injectivity
criterion and symmetry, flatness of M, tensor cancellation, then reflection of exactness.
There is one named theorem with proof `sorry`, no other theorem proved and no definition
or hollow data. Imports are both used; all lines are at most 100 characters, the
namespace is `RingHom`, and every variable and universe is bound.

Mismatch repaired: H9 topic directory. Moved `lean/Sheaf/Algebra/FlatPermanence.lean` to
`lean/Sheaf/RingTheory/FlatPermanence.lean`, following the Mathlib location of flat ring
maps and faithfully flat modules. Updated only `lean.module` and `lean.file` accordingly.
The correct theorem, signature and docstrings were preserved. The node's `lean.statement`
was checked verbatim against the declaration signature. No mathematical mismatch found.

Additional Loogle query `"Flat", "FaithfullyFlat", "S"` returned twelve results about
faithfully flat tensor products, triviality reflection and free modules, again no match.
Validation: `scompile.py J1 lem-weil-pbc-flat-permanence` compiled the final RingTheory
module on the server in 1.5 seconds, exit code 0, with no warnings or errors.
