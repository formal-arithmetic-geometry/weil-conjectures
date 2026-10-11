## Worker report

The module `Sheaf.RingTheory.LocalRing.ArtinSchreierKernel` states
`IsLocalRing.pow_eq_self_iff_existsUnique_zmod`, with its proof left as `sorry`.
No definitions, additional nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:
- A prime number p: `(p : ℕ) (hp : p.Prime)`.
- An arbitrary commutative local ring R: `{R : Type u} [CommRing R] [IsLocalRing R]`,
  with `universe u` explicitly declared. Mathlib's local-ring predicate includes nontriviality
  and is equivalent to existence of exactly one maximal ideal. Its declaration/docstring
  were read in `Mathlib.RingTheory.LocalRing.Defs`; `of_unique_max_ideal` was inspected in
  `Mathlib.RingTheory.LocalRing.Basic` as well.
- The literal hypothesis p times 1_R = 0: `(hchar : (p : R) = 0)`. Natural-number cast is
  p times the ring identity. No characteristic or algebra instance is assumed separately.
- An element a: `(a : R)`.
- The root condition: `a ^ p = a`.
- Exactly one c in F_p = Z/pZ maps to a: `∃! c : ZMod p, (ZMod.cast c : R) = a`.
  The signature and docstring of `ZMod.cast` in `Mathlib.Data.ZMod.Basic` were read:
  at positive modulus it is the natural cast of the residue's value. Since p is prime
  and its cast vanishes, this is precisely the canonical ring map, independent of residue
  representative, sending c to c times 1_R. It requires no extra algebra structure.
- The equivalent bijection clause is encoded by the biconditional. Its reverse direction
  says that every constant is a root; its forward direction gives existence and uniqueness
  of a preimage for every root. Together these assert bijectivity of the canonical map into
  the root subtype, without choosing subtype proof data or adding a separate notion.

Statement dependencies: `stmt_deps` is empty, so there are no recorded dependency
modules to import. The two imports give precisely `ZMod.cast`/`ZMod` and `IsLocalRing`.
The proof docstring reproduces all three DAG proof steps and names both proof dependencies
(`lem-sc-field-artin-schreier-kernel`, `lem-weil-pbc-local-ring-unit-criterion`);
these are future proof inputs, not statement imports.

Edge cases checked mathematically before writing:
- p = 0 and p = 1 are excluded by the given primality hypothesis; p = 2 works.
- R = F_p and field extensions have exactly the expected p roots.
- Nonreduced rings are allowed: in F_p[ε]/(ε²), for a = c + dε the equation forces d = 0.
  The maximal-ideal/unit argument in the docstring applies without reducedness or Noetherianity.
- The zero ring has no maximal ideal, hence is excluded by exactly the node's local-ring
  hypothesis. Mathlib's `IsLocalRing` likewise entails nontriviality. Without it uniqueness
  would fail, so no omission of this condition is possible.
- Nonlocal F_p × F_p has extra roots and is correctly excluded.
- No field, algebraic-closure, strict Henselianity, finiteness, or dimension hypothesis is added.

Searches (run through `/home/ubuntu/weil-launcher/msearch.py`, recorded in searches.jsonl):
- LeanFinder: “In a local commutative ring of characteristic p, solutions of a^p=a are
  exactly the unique images of ZMod p”. Eight hits: `Subfield.mem_bot_iff_pow_eq_self`,
  `ZMod.pow_card`, perfect-ring/closure and polynomial facts. None covers a general local ring.
- Loogle: `IsLocalRing, ZMod`. Two hits: local homomorphisms to ZMod and locality of ZMod(p^r),
  neither a root/kernel statement.
- Mathlib grep: `artin.?schreier|pow_eq_self|castHom` in `RingTheory/LocalRing`: zero hits.
- LeanSearch: “In a local ring R with p prime and p = 0, a^p=a if and only if a is the
  image of a unique element of ZMod p”. Unavailable (Internal Server Error); no verdict
  is drawn from that unavailable service.
- Direct rg of `pow_eq_self` in `WeilConjectures`: only field facts used in
  `LinearAlgebra/SemilinearFrobenius.lean` and described in the algebraically closed field
  module. Search for this item's exact blueprint id found no declaration.
- Direct rg of Artin–Schreier/kernel names in project `lean/Sheaf` and source ring-theory
  modules: the existing `IsAlgClosed.artinSchreier_surjective_and_kernel` has the stronger
  algebraically closed field hypothesis and additionally asserts surjectivity of x^p-x;
  it is not the present local-ring statement. Its complete docstring/signature were read.
- Exact proposed declaration-name search across Mathlib, WeilConjectures and lean/Sheaf:
  no hit. `dag/lean_names_upstream.json` likewise carries no local-ring kernel declaration.

Source: the local `literature/blueprint` and `literature/stacks-project` texts are absent
on this machine. The node's full source/proof record was read, and the cited Stacks
section was opened at https://stacks.math.columbia.edu/tag/0A3J: its opening states the
Artin–Schreier short exact sequence with constant Z/pZ kernel for characteristic-p schemes.
The source agrees with the node; no statement dispute or node fault was found.

Validation: server single-file compilation and delivery preflight are run for this sandbox.
The independent second-reading section is intentionally left to the designated second reader.

## Second reading by K1

I independently opened the item node and the complete delivered module. No mathematical
or signature mismatch was found; the Lean and node record are retained unchanged. The
only addition is this independent review. There are no new definition nodes, dependency
modules, or statement_change records in this delivery.

Source check: I read the actual Stacks etale-cohomology.tex text at
`section-artin-schreier` (Tag 0A3J), fetched from
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex,
and the corresponding https://stacks.math.columbia.edu/tag/0A3J page. The opening kernel
assertion assumes only a prime p and a scheme in characteristic p; the affine,
quasi-compact, dimension, and algebraically closed hypotheses in subsequent lemmas do
not apply to that assertion. I also read algebra.tex at
`lemma-characterize-local-ring` (Tag 00E9), including its equivalence with a nonzero
ring in which x or 1-x is invertible. The local blueprint text is absent on this machine;
the complete node source record and its parent lem-sc-as-sequence were opened. The
parent uses the result in an ordinary local ring O_(U,u), with no reducedness assumption.

Object/hypothesis/conclusion inventory and Lean correspondence:

- A prime number p: `(p : ℕ) (hp : p.Prime)`. Exact; primality is an explicit
  proposition, not an additional typeclass prerequisite.
- A commutative ring R: `{R : Type u} [CommRing R]`. Exact; `universe u` is bound
  explicitly and arbitrary. No field, domain, Noetherian, finite, reduced, or Henselian
  hypothesis is present.
- Exactly one maximal ideal of R: `[IsLocalRing R]`. Exact in the commutative setting.
  I read the class and docstring in Mathlib.RingTheory.LocalRing.Defs (line 30),
  `IsLocalRing.of_unique_max_ideal` in LocalRing.Basic (line 67), and
  `IsLocalRing.maximal_ideal_unique` in LocalRing.MaximalIdeal.Basic (line 51).
  The implicit nontriviality is forced by the node's existence of a maximal ideal,
  rather than an extra restriction. The ideal m itself is not chosen data in the
  conclusion, so using the predicate introduces no missing quantifier.
- p times 1_R equals zero: `(hchar : (p : R) = 0)`. Exact natural-number cast.
  No stronger characteristic or algebra instance is required to apply the statement.
- The canonical constants F_p = Z/pZ: `ZMod p`. Exact. I read `ZMod.cast` in
  Mathlib.Data.ZMod.Basic (line 170), including its positive-modulus branch
  `fun i => i.val`, and `ZMod.castHom` (line 331), whose toFun is precisely `cast`.
  Since p is prime and vanishes in the nontrivial ring R, the prime-field map exists
  and is injective; changing a representative by a multiple of p changes its natural
  cast by zero. Thus the function in the signature is exactly c maps to c times 1_R,
  without introducing a separately chosen algebra structure.
- An arbitrary element a of R: `(a : R)`, following the ring, prime, and characteristic
  hypotheses. Exact order: the constant c is chosen for each a, not uniformly before a.
- If a^p=a, existence of a constant mapping to a: the forward implication of
  `a ^ p = a ↔ ∃! c : ZMod p, (ZMod.cast c : R) = a`. Exact.
- Exactly one such constant: `∃!` includes both existence and equality of every other
  witness to that witness. Exact; neither mere membership in a range nor existence alone.
- Equivalent bijection F_p to the roots: the same biconditional encodes the root
  correspondence. All constants satisfy c^p=c (and the canonical ring map preserves
  powers), so every constant image is a root; the forward implication then supplies
  the unique preimage of each root. Conversely a bijection gives exactly this
  biconditional. The injection of the canonical map is automatic under the stated
  hypotheses, so the reverse implication does not strengthen the node.

Dependency audit: the node's stmt_deps is empty. The mathematical notions already
exist in the two imported Mathlib modules; no private definition or missing dependency
module is used. The two proof-dependency ids are named in the docstring as future proof
inputs, not assumed as hypotheses. I checked all three docstring proof steps against
all three node proof steps: residue-field reduction and its unique constant; b in m,
Frobenius binomial expansion, p-1 positive, the unit 1-b^(p-1), cancellation; constants
are roots and uniqueness after reduction. Both required dependency names and Stacks
00E9 occur. The module and declaration have source places and the exact blueprint id.
There is one theorem, its body is only `sorry`, and there is no definition, hollow or
otherwise. The two imports are used in the signature. No binder or universe is unbound.
The recorded lean.statement is verbatim the theorem signature before `:=`.

Edge cases: p=0 and p=1 are excluded exactly by primality; p=2 is included. The zero
ring is excluded exactly by existence of a maximal ideal in the node and Nontrivial
in IsLocalRing. a=0 gives the unique constant 0; a=1 gives 1. Fields (including F_p
itself and arbitrary extensions) are included, as are nonreduced local rings such as
F_p[e]/(e^2), where (c+de)^p=c forces d=0. The product F_p x F_p is excluded by locality,
as required. Rings in all universes are covered; fixing the finite constants in Type
introduces no restriction on R. Empty schemes and empty index sets are not objects
of this ring lemma, and no nonempty indexing assumption has been introduced.

Independent searches (queries differ from the author's; service calls are recorded
in searches.jsonl):

- LeanFinder: "Frobenius fixed elements in a commutative local ring are uniquely
  constants from the prime field". Eight hits concerned perfect closures,
  perfection, arithmetic Frobenius, and perfect rings; none states this root result.
- Loogle: `IsLocalRing, (_ ^ _)`. Twelve hits concerned powers of ideals,
  localizations, Krull intersection, and DVRs; none states the root correspondence.
- LeanSearch: "The fixed points of Frobenius in a local ring of prime characteristic
  are the prime field". Service returned Internal Server Error; recorded unavailable,
  with no mathematical verdict attributed to that service.
- Direct rg in Mathlib RingTheory/LocalRing and RingTheory/Frobenius for
  `fixed|eq_self|ZMod|prime.field|schreier`: only unrelated fixed-subring/Frobenius
  facts and local homomorphisms to ZMod; no root/kernel statement.
- Direct rg of `mem_bot_iff_pow_eq_self`, `fieldRange_castHom_eq_bot`, and the
  proposed full declaration name in Mathlib, WeilConjectures, lean/Sheaf, and the
  upstream name table. I read Subfield.mem_bot_iff_pow_eq_self with its section
  binders: it requires Field F, so is not this arbitrary local-ring statement.
- Direct rg of alternative Frobenius/fixed/root terminology in the source ring-theory
  modules and project Lean, followed by opening the complete existing
  `IsAlgClosed.artinSchreier_surjective_and_kernel` signature/docstring and the
  source `IsAlgClosed.surjective_pow_sub_self` declaration. Both require an
  algebraically closed field; neither states the present theorem. General source
  Artin-Schreier polynomial/etale-map results concern other objects.

Verdict: exact statement, no repair needed. Single-file server compilation with
scompile.py completed successfully in 1.0 seconds, with no errors or warnings.
Delivery dry-run and push are performed after adding this review.
