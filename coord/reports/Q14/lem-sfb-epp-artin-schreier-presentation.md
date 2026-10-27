## Worker report

Item: `lem-sfb-epp-artin-schreier-presentation`, group Q14, stage 2.
Module: `Sheaf.FieldTheory.ArtinSchreierPresentation`.
The two theorems together state the entire node. Both proofs are `sorry`; no new
notion, auxiliary axiom, new node or dependency repair is needed. The node copy
changes only `lean`. Source read: `literature/stacks-project/fields.tex`, lines
3315–3354, section-Artin-Schreier (Tag 09I7) and lemma-Artin-Schreier (Tag 09DY).
The full eight-step DAG proof is supplied in the two theorem docstrings.

Hypotheses and clauses of the forward statement:

- Prime p is `(p : ℕ) (hp : p.Prime)`.
- Fields E ⊆ F are `(E : Type u) (F : Type v) [Field E] [Field F]
  [Algebra E F]`; the inclusion is the injective `algebraMap E F`.
- Characteristic p is `[CharP E p] [CharP F p]`.
- Normality and separability are `[Normal E F] [Algebra.IsSeparable E F]`.
  Mathlib Normal states algebraicity and splitting of all minimal polynomials;
  for fields this is equivalent to the node's irreducible-polynomial wording.
  An irreducible polynomial with a root is associated to that root's minpoly.
- Degree p is `(hdegree : Module.finrank E F = p)`. Since p is nonzero, this
  also excludes infinite-dimensional spaces, whose finrank is zero.
- The witnesses are `∃ (z : F) (a : E)`.
- z outside E is `z ∉ Set.range (algebraMap E F)`.
- The equation is `z ^ p - z = algebraMap E F a`.
- F = E[z] is `Algebra.adjoin E ({z} : Set F) = ⊤`, a subalgebra equality,
  rather than the weaker field-generation statement.
- The quotient presentation is `∃ e : AdjoinRoot (X ^ p - X - C a) ≃ₐ[E] F`.
  `AdjoinRoot f` is defined as `E[X] ⧸ Ideal.span {f}`, with the quotient's
  standard E-algebra structure, so this is the node's exact quotient algebra.
- Evaluation gives that isomorphism: for every `q : E[X]`,
  `e (AdjoinRoot.mk (X ^ p - X - C a) q) = aeval z q`.
  This specifies the canonical map, rather than an arbitrary isomorphism.

Hypotheses and clauses of the converse:

- `quotient_field_or_product` has only `(p : ℕ) (hp : p.Prime) (E : Type u)
  [Field E] [CharP E p] (a : E)`. In particular it does not assume an existing
  degree-p extension or inherit the forward theorem's hypotheses.
- With Q denoting the actual type `AdjoinRoot (X ^ p - X - C a)` for this
  paragraph only, the field branch is `(∃ h : IsField Q, @Normal E Q _
  h.toField _) ∧ Algebra.IsSeparable E Q ∧ Module.finrank E Q = p`.
  `h.toField` extends Q's existing ring operations with their determined
  inverses, allowing Normal to be typed. It does not choose a new algebra or
  replace the quotient by an unspecified field. Normal's algebra parameter
  elaborates from the same standard quotient coefficient structure.
- The other branch is `Nonempty (Q ≃ₐ[E] (Fin p → E))`: the product has exactly
  p factors and its standard pointwise operations and coefficient embedding.
- These branches are joined by `∨`.
- The additional conjunction is
  `Nonempty (Q ≃ₐ[E] (Fin p → E)) ↔ ∃ u : E, a = u ^ p - u`.
  It gives both directions of the node's “exactly when”. The field and product
  branches are automatically exclusive because p ≥ 2 and E is nontrivial.

Recorded dependency declarations used, with their full source signatures and
docstrings inspected:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` and
  `algebraMap`; algebra structures specify the coefficient embedding.
- `def-weil-pbc-separable-algebraic-extension`:
  `Mathlib.FieldTheory.Separable`, `Algebra.IsSeparable` (all elements have
  separable minimal polynomials, including algebraicity).
- `def-pc-field-characteristic`: `Mathlib.Algebra.CharP.Defs`, `CharP`.
- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`,
  `Polynomial`, `Polynomial.X`, `Polynomial.C`.
- `def-weil-pbc-algebra-hom-quotient`: `Mathlib.Algebra.Algebra.Hom`,
  `AlgHom`; `Mathlib.RingTheory.Ideal.Quotient.Operations`,
  `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`. The imported
  `Mathlib.RingTheory.AdjoinRoot` gives the literal quotient wrapper and its
  inherited coefficient algebra, plus `AdjoinRoot.mk` for representatives.
- `def-weil-vector-space-dimension`: `Mathlib.LinearAlgebra.Dimension.Finrank`,
  `Module.finrank`.
- Existing supporting notions: `Mathlib.FieldTheory.Normal.Defs`, `Normal`;
  `Mathlib.Algebra.Algebra.Subalgebra.Lattice`, `Algebra.adjoin`;
  `Mathlib.Algebra.Field.IsField`, `IsField`, `IsField.toField`.

Public imports expose the statement's definitions; ordinary imports supply
all already stated proof dependencies. Galois.Basic supplies the fixed-field
and automorphism-cardinality results; Cyclic.Basic the prime-order cyclic
result; LinearIndependent.Basic the character theorem; AdjoinRoot the monic
basis; AlgebraicClosure the algebraic closure; Separable and SeparableDegree
the polynomial and simple-extension separability results; Normal.Basic the
splitting-field normality result (and its finite-dimensional splitting-field
interface through its imports). No project dependency has a separate Lean
module that needs to be imported here: all recorded dependencies are Mathlib.

Edge cases checked mathematically before writing:

- p = 2 is included; the proof's exponent p - 2 is zero and N^0 is identity.
- p = 0 and p = 1 are excluded precisely by primality, as the node requires.
- a = 0 and a = u^p-u give p distinct base-field roots and the product branch.
- Over E = F_p the only Artin–Schreier coboundary is 0; nonzero a gives the
  field branch, so the statement includes prime base fields.
- Over an algebraically closed characteristic-p field every a has a root,
  and the product branch applies; no nonexistent degree-p extension is
  required for the converse.
- E = F cannot meet degree p for prime p. Infinite extensions do not meet
  the nonzero finrank hypothesis. A field cannot be the zero ring.
- The independent universes u and v impose no equality or size restriction
  on the forward field extension; the quotient and the product naturally
  lie in E's universe.

Searches made, before writing (2026-10-24):

- `msearch.py ... leanfinder "A normal separable field extension of prime
  degree p in characteristic p has a generator z with z^p-z in the base field
  and Artin Schreier quotient is a field or split product"`: 8 hits, including
  Kummer-extension and finite-field results; no exact statement.
- `msearch.py ... leansearch "Artin Schreier polynomial X^p - X - a over a
  characteristic p field is irreducible or splits into linear factors"`:
  8 hits, mostly general splitting and finite-field splitting results, no
  arbitrary-a Artin–Schreier dichotomy.
- `msearch.py ... loogle "IsGalois, CharP"`: 0 hits.
- `msearch.py ... grep "ArtinSchreier|artin_schreier|artinSchreier"`: 0 hits
  in Mathlib.
- `rg -n 'ArtinSchreier|artin_schreier|artinSchreier'` in both
  `lean/WeilConjectures` and `lean/Sheaf`: existing affine-space covers,
  sheaves and reciprocal-polynomial extensions. The full upstream
  `WeilConjectures.FieldTheory.ArtinSchreierExtension` was read: it assumes
  irreducibility of the reciprocal polynomial, constructs a root and
  translations, and supplies neither the arbitrary normal degree-p
  presentation nor the quotient dichotomy. It cannot replace this node.
- Search for the item id in `lean/WeilConjectures`: no existing binding.
- Search of `dag/lean_names_upstream.json` and the FieldTheory sources for
  the proposed declaration names: no existing declarations with these names.

Validation: `scompile.py Q14 lem-sfb-epp-artin-schreier-presentation` compiled
both the sandbox and actual module-path versions in 2.5 s and 1.8 s, with no
errors or warnings. There are exactly two postponed theorem proofs, both
corresponding to clauses of this DAG node. No statement correction or
STATEMENT-DISPUTED issue was found.

## Second reading by Q14

A separate self-check reopened the node and completed module. The dispatcher
prohibits starting another agent; the maintainer's independent review follows
delivery. The six recorded statement-dependency interfaces are used directly.
The forward theorem includes each of primality, two fields, coefficient
inclusion, both characteristic assumptions, normality, separability and degree;
its witnesses include outside-base, equation, subalgebra generation, quotient
isomorphism and evaluation characterization. The converse has separate binders,
so its full quantification is preserved. Its disjunction includes normality,
separability and degree in the field branch, exactly p factors in the product
branch, and both directions of the coboundary criterion. The existential
IsField witness affects only the field structure needed to type Normal,
retaining the same quotient multiplication and coefficient embedding. No
extra structure is assumed. Both theorem docstrings identify the source and
carry all eight steps of the node proof. No mismatch requiring a change was
found. No independent second reader is claimed in this report.

Dry-run repair: the initial signature extraction matched the word “theorem”
in a docstring. The node record now extracts only the actual declaration at
the start of its line; the Lean statement itself was unchanged.
