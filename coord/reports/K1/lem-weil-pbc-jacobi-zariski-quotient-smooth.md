## Worker report

The module Sheaf.RingTheory.JacobiZariskiQuotientSmooth states
`Algebra.jacobiZariski_quotient_smooth`, with its sole proof `sorry`.
It asserts the entire five-term exact sequence of the node. No definition,
additional node, dependency module or statement correction is needed.

Hypothesis and clause correspondence:

- Commutative rings A → B: `(A : Type u) (B : Type v) [CommRing A]
  [CommRing B] [Algebra A B]`. An algebra structure encodes any ring homomorphism.
- H₁(L[B/A]) = 0: `[Subsingleton (H1Cotangent A B)]`. This is vanishing of
  a module, since its zero element is then its sole element.
- Ω[B/A] projective: `[Module.Projective B (KaehlerDifferential A B)]`.
  There is no smoothness or finite presentation hypothesis: smoothness in
  the node is an example, not an additional condition.
- Ideal a and C = B/a: `(a : Ideal B)` and `let C := B ⧸ a`.
  Mathlib supplies the quotient A-algebra induced by A → B → C.
- a/a²: `a.Cotangent` is Mathlib's `I ⧸ (I • ⊤ : Submodule B I)`;
  `Ideal.mem_toCotangent_ker` identifies the kernel with elements of a².
- A sequence of C-modules: the three existential maps `i`, `δ`, `w`
  are all `→ₗ[C]`, with precisely the four nonzero modules in the node.
- Exactness at H₁: `Function.Injective i` renders the initial zero.
- Exactness at a/a²: `Function.Exact i δ`.
- Exactness at C ⊗[B] Ω[B/A]: `Function.Exact δ w`.
- Exactness at Ω[C/A]: `Function.Surjective w` renders the terminal zero.
- δ(a mod a²) = 1 ⊗ da: the `∀ x : a` clause uses `a.toCotangent x`
  and `1 ⊗ₜ[B] KaehlerDifferential.D A B x`.
- w(c ⊗ db) = c d(b̄): the final clause quantifies over `c : C` and `b : B`,
  using `Ideal.Quotient.mk a b` for b̄ and scalar multiplication by c.

The first arrow is existential, exactly as the node's assertion that there
is an exact sequence; the node prescribes formulas only for δ and w.
These formulas determine δ and w by their generators.

Dependency declarations read and used:

- def-weil-pbc-smooth-ring-map is a Mathlib leaf. Its match
  `Algebra.Smooth` (Mathlib.RingTheory.Smooth.Basic) includes formal
  smoothness and finite presentation; its stated first homology is
  `Algebra.H1Cotangent` (Mathlib.RingTheory.Extension.Cotangent.Basic).
  This abbreviation is the kernel of the canonical presentation's
  cotangent complex. The present theorem uses this first homology and
  projectivity directly, since the node assumes less than smoothness.
- def-weil-pbc-kahler-differentials is a Mathlib leaf matched by
  `KaehlerDifferential` (Mathlib.RingTheory.Kaehler.Basic), with universal
  derivation `KaehlerDifferential.D` and universal property
  `KaehlerDifferential.linearMapEquivDerivation`.
- `Ideal.Cotangent` and `Ideal.toCotangent` from
  Mathlib.RingTheory.Ideal.Cotangent implement the standard conormal
  module and its quotient map without introducing a private notion.

Edge cases checked before finalizing: a = 0 gives C = B and zero conormal
module, consistent with the assumed H₁ vanishing; a = ⊤ gives the zero
quotient ring and zero C-modules. Zero rings, arbitrary characteristic,
and ideals without finite generation are included. The two ring universes
u and v are independent; C is the literal quotient of B. Projectivity is
not replaced by finite projectivity or flatness of C over B.

Sources checked: the local Stacks source files are absent on this machine,
so the source was read at https://stacks.math.columbia.edu/tag/00S2,
https://stacks.math.columbia.edu/tag/07BP,
https://stacks.math.columbia.edu/tag/00RU and
https://stacks.math.columbia.edu/tag/07M7. Tag 00S2 gives the homology
sequence and its Tor₁/Tor₂ base-change condition; projectivity supplies
both vanishings. Tags 07BP and 00RU supply the conormal identification
and maps. No statement fault was found.

Searches for an existing statement (2026-10-11):

- msearch.py leansearch: "Jacobi Zariski exact sequence quotient ideal
  smooth algebra projective differentials first cotangent homology".
  Service unavailable (Internal Server Error); no verdict from this service.
- msearch.py leanfinder: "H1 cotangent injects into ideal cotangent for
  quotient of formally smooth algebra". Eight hits, including
  Algebra.FormallySmooth.kerCotangentToTensor_injective_iff,
  Algebra.Extension.cotangentComplex_injective_iff and
  Algebra.Extension.h1Cotangentι_injective. These are component results,
  not the entire asserted exact sequence and two map formulas.
- msearch.py loogle: "Algebra.H1Cotangent, Module.Projective". Three hits:
  the finite-H₁ instance, Algebra.FormallySmooth.mk, Algebra.formallySmooth_iff.
  None states the node.
- msearch.py grep in RingTheory: "quotient.*smooth|exact.*[Pp]rojective|cotangent.*[Ii]njective".
  Twenty-five hits, principally cotangent injectivity and base-change results;
  no full matching assertion. The JacobiZariski source was read: its left
  exactness theorem assumes C flat over B, which is not assumed here.
- rg in WeilConjectures and lean/Sheaf for
  "jacobiZariski_quotient_smooth|Jacobi.Zariski|quotient.*smooth|H1Cotangent".
  No matching statement. Project files mention this node as a proof input,
  and other H₁ lemmas concern characteristic or local fields.
- grep -rn for the item id in WeilConjectures: no hit.
- rg for the proposed full declaration name in Mathlib and
  dag/lean_names_upstream.json: no collision.

Validation: scompile.py compiled the statement cleanly on the server.
The only theorem has a sorry proof; nothing is proved in this delivery.
The independent second reading is left to the dispatcher-appointed reader.


## Second reading by K1

Independent reading of the repository node, both statement-dependency nodes,
the delivered module and its node copy, and the Mathlib declarations below.
No mathematical mismatch was found. No Lean or node change was needed; this
section records the second reading. There are no new nodes, dependency modules,
or statement corrections in this delivery.

Source check: the local literature tree does not contain algebra.tex. I fetched
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex into
this item's scratchpad and read the full lemma and proof at
lemma-exact-sequence-NL (00S2), lemma-NL-surjection (07BP), and
lemma-differential-seq (00RU), also checking their published tag pages and 07M7.
00S2 assumes arbitrary composable commutative ring maps and explicitly requires
both Tor_1 and Tor_2 vanishings for its left-term identification. Projectivity
of Omega kills both, so the node's specialization is justified. 07BP requires
surjectivity, supplied by B -> B/a. 00RU takes the same base ring on both sides,
which is A here. There is no ambient Noetherian, field, finite generation,
finite presentation, characteristic, or nonzero-ring assumption to add.
The tensor symmetry takes the source's differential-tensor-quotient convention
to the node's quotient-tensor-differential convention.

Object, hypothesis, and conclusion inventory, with Lean correspondence:

1. Arbitrary commutative rings A and B and a ring map A -> B:
   `(A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]`.
   Verdict: exact. Any commutative-ring homomorphism supplies its toAlgebra;
   this does not impose injectivity, surjectivity, or a field structure.
2. H_1(L[B/A]) = 0: `[Subsingleton (H1Cotangent A B)]`.
   Verdict: exact, since this additive module has zero. I read
   Extension/Cotangent/Basic.lean: `Algebra.Extension.H1Cotangent` is the
   kernel of the conormal differential, and `Algebra.H1Cotangent` uses
   `(Generators.self A B).toExtension`. Generators.lean's `self` has
   `val := id` and `sigma := X`: precisely the canonical polynomial
   presentation with one variable per element of B from the dependency node.
3. Omega[B/A] projective over B:
   `[Module.Projective B (KaehlerDifferential A B)]`.
   Verdict: exact. Smoothness is only an example in the node. I read the
   smooth dependency's recorded Mathlib match `Algebra.Smooth`, its
   `FormallySmooth` fields, and `FinitePresentation` field; the theorem
   correctly assumes only the two hypotheses actually needed.
4. An arbitrary ideal a and C = B/a with induced A-algebra structure:
   `(a : Ideal B)` and `let C := B ⧸ a`. Verdict: exact. There is no
   separately chosen C-algebra structure or incompatible scalar tower.
5. Conormal module a/a^2: `a.Cotangent`. Verdict: exact. I read
   Ideal/Cotangent.lean: quotient of a by `a • top`, its derived
   `Module (B ⧸ a)` instance, and `mem_toCotangent_ker`, which identifies
   the quotient kernel with membership in a^2. `a.toCotangent` is the
   actual quotient map, not a private construction.
6. The other three terms: `H1Cotangent A C`,
   `C ⊗[B] KaehlerDifferential A B`, `KaehlerDifferential A C`.
   Verdict: exact. I read Kaehler/Basic.lean's definition, universal
   derivation `D`, and `linearMapEquivDerivation`; these give precisely
   the differential dependency's universal pair, despite using the
   equivalent diagonal-ideal implementation.
7. Existence of a sequence of C-module maps: the existential `i`, `δ`,
   and `w` have the successive domains and codomains above and are all
   `→ₗ[C]`. Verdict: exact. All objects and assumptions precede this
   existential. The node gives no formula for the first map, so no
   additional canonical-map equality is required.
8. Initial zero and exactness at H_1: `Function.Injective i`.
   Verdict: exact.
9. Exactness at a/a^2: `Function.Exact i δ`. Verdict: exact.
10. Exactness at the tensor term: `Function.Exact δ w`. Verdict: exact.
    I read Algebra/Exact/Basic.lean: additive `Function.Exact f g` means
    `g y = 0` iff y lies in the image of f, so both clauses express
    image equals kernel and force both composites to vanish.
11. Terminal zero and exactness at Omega[C/A]: `Function.Surjective w`.
    Verdict: exact. No clause of the five-term sequence is omitted.
12. Delta formula for every element of the ideal:
    `∀ x : a, δ (a.toCotangent x) = 1 ⊗ₜ[B] KaehlerDifferential.D A B x`.
    Verdict: exact; the subtype coercion uses the actual element of B.
13. W formula for every c in C and b in B:
    `∀ (c : C) (b : B), w (c ⊗ₜ[B] KaehlerDifferential.D A B b) =
      c • KaehlerDifferential.D A C (Ideal.Quotient.mk a b)`.
    Verdict: exact. The quotient class is the prescribed b-bar. These
    formulas and linearity determine the two maps on their generators.

Edge cases: a = 0 gives C = B, zero conormal, and the assumed zero H_1;
a = top gives the zero quotient ring and zero C-modules. Zero rings and all
characteristics are allowed by CommRing without Nontrivial. Infinite ideals
and infinitely generated projective differential modules are included. The
independent ring universes u and v impose no equality or size restriction;
there are no test-object quantifiers in a smaller universe. Empty index sets,
empty schemes and n = 0 are not objects or binders of this node; in particular
no presentation or generator count is restricted by the statement.

Independent duplicate searches (2026-10-11), using alternative wording:

- LeanFinder through msearch.py: "conormal sequence of quotient algebra
  injective first cotangent homology projective module of differentials".
  Eight hits. I opened `Algebra.FormallySmooth.kerCotangentToTensor_injective_iff`:
  it equates injectivity of the conormal differential with vanishing of
  quotient H_1, not this exact sequence with H_1 as its kernel.
  `Extension.h1Cotangentι_injective` is the inclusion for a presentation,
  not an identification with the canonical H_1 over A.
- Loogle through msearch.py: `Ideal.Cotangent, Algebra.H1Cotangent`.
  One hit, the same injectivity criterion; no matching full assertion.
- LeanSearch through msearch.py: "exact sequence first cotangent homology
  conormal quotient projective differentials". Internal Server Error;
  recorded as unavailable, with no mathematical verdict from that service.
- rg for conormal, quotient/smooth, exact/Cotangent, and the proposed full
  declaration name in Mathlib's Kaehler and Extension modules, the source
  WeilConjectures tree, and repository lean/Sheaf. No full matching statement.
  I read the global exactness signatures in JacobiZariski.lean and the
  presentation comparison in Extension/ExtendScalars.lean. They provide
  parts of the assertion, while `exact_liftBaseChange_map_of_flat` assumes
  C flat over B, not merely Omega[B/A] projective. The Mathlib module's TODO
  expressly distinguishes this stronger flatness from the Stacks Tor condition.
  Project matches are other conormal assertions or docstring citations to
  this item. No collision in dag/lean_names_upstream.json.

H5/H6/H8/H9 check: the sole theorem ends `:= by sorry`, with no definitions,
instances, extra axioms, or proved statements. The module and declaration
source docstrings carry this node's blueprint id. The four numbered proof
steps reproduce the node's four steps and name all their mathematical inputs.
The single Mathlib import supplies the notions used. All variables and both
universes are explicitly bound, and all lines are at most 100 characters.
A direct string comparison verified `lean.statement` is verbatim the signature
from `theorem` through the text before `:= by`.

Validation: scompile.py compiled the delivered module on the server in 1.5 s,
exit code 0, with no errors or warnings. The unchanged statement is suitable
for delivery; the second reading added only this review report.
