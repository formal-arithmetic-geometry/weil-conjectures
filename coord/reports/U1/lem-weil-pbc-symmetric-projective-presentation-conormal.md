## Worker report

The module `lean/Sheaf/RingTheory/SymmetricProjectivePresentationConormal.lean` states
`Algebra.symmetric_projective_presentation_conormal`, with exactly one `sorry` proof.
No definitions, auxiliary axioms, new nodes, dependency replacements, or statement corrections.

Source read: Stacks Project `smoothing.tex`, proof of Lemma 07CE, lines 357–430,
including equation-sequence and equation-sequence-localized. The repository's literature
copy is absent on this machine; the full source was read at
`/home/ubuntu/c1-stacks-review/smoothing.tex`. The node's projective case and its six
proof steps are included in the theorem docstring. The corrected projective restriction
already belongs to the node and was retained.

Hypotheses and objects, clause by clause:

- A commutative ring R: `(R : Type u) [CommRing R]`, with `universe u` explicitly bound.
- P = R[x₁,…,xₙ]: `MvPolynomial (Fin n) R`; n and m are arbitrary natural numbers.
- I = (f₁,…,fₘ): `I : Ideal (MvPolynomial (Fin n) R)`, `f : Fin m → I`,
  and `hf : Ideal.span (Set.range (fun j ↦ (f j).1)) = I`. Using elements of I
  packages precisely their membership; it adds no assumption.
- A = P/I: the literal quotient type `MvPolynomial (Fin n) R ⧸ I`, everywhere.
- M = I/I² as an A-module: Mathlib `I.Cotangent`, with its existing quotient-module instance.
- M projective: `[Module.Projective (MvPolynomial (Fin n) R ⧸ I) I.Cotangent]`.
- q sends the j-th basis vector to f_j mod I²: the A-linear map `q` and
  `hq : ∀ j, q (Pi.single j 1) = I.toCotangent (f j)`.
  These equations determine q uniquely on the finite free module; q is not a new assumption
  of surjectivity or splitting. Such q always exists by the universal property of a free module.
- K = ker q: `LinearMap.ker q`, literally, with the submodule's module structure.
- C = Sym_A(M): the literal `SymmetricAlgebra (MvPolynomial (Fin n) R ⧸ I) I.Cotangent`.
- Q = P[y₁,…,yₘ]: `MvPolynomial (Fin m) (MvPolynomial (Fin n) R)`.
- The canonical Q → C: `φ`, with `hφC` prescribing its coefficient map
  `P → P/I → C` and `hφX` prescribing y_j ↦ ι(q(e_j)). These specify the canonical
  map uniquely by polynomial evaluation, rather than imposing additional mathematical
  hypotheses. It exists as `MvPolynomial.eval₂Hom` of the prescribed coefficient map
  and variables, without any surjectivity assumption.
- The reduced presentation A[y] → C: the A-algebra map `α`, with `hαX` prescribing
  the same degree-one generators. This is uniquely the evaluation `MvPolynomial.aeval`
  from the polynomial dependency, and exists unconditionally.
- J = ker(Q → C): the kernel of `Extension.ofSurjective φ.toIntAlgHom hφ`.
  Its underlying ring is exactly Q and its algebra map is exactly φ.
  `RingHom.toIntAlgHom` only reinterprets a ring map as a Z-algebra map; it does not
  change the ring, the map, the kernel, or its conormal module.

Conclusions, clause by clause:

- Q → C surjective: `∃ hφ : Function.Surjective φ`. The additional existential
  `hα : Function.Surjective α` records that the reduced map is indeed the resulting
  presentation referred to in the node, and permits use of Mathlib's extension conormal.
- Conormal modules J/J² and L/L²: respectively
  `(Extension.ofSurjective φ.toIntAlgHom hφ).Cotangent` and
  `(Extension.ofSurjective α hα).Cotangent`. Mathlib gives them the canonical C-module
  structure using the surjective presentation; there is no choice of module structure
  added as a hypothesis.
- Identify the reduced conormal with K ⊗_A C: the C-linear equivalence `lam`, with
  `lam (c ⊗ₜ k) = c • Extension.Cotangent.mk y` whenever the underlying y is
  the linear form `∑ j, MvPolynomial.C (k.1 j) * MvPolynomial.X j`.
- First map: the C-linear `i`, characterized by
  `i (c ⊗ₜ I.toCotangent x) = c • Extension.Cotangent.mk y` whenever
  `y.1 = MvPolynomial.C x.1`. This is exactly (f mod I²) ⊗ c ↦ c(f mod J²).
- Second map: the C-linear `p`, characterized by
  `lam (p (Extension.Cotangent.mk x)) = Extension.Cotangent.mk y` whenever
  `y.1 = MvPolynomial.map (Ideal.Quotient.mk I) x.1`.
  Thus lam ∘ p is precisely coefficient reduction modulo I on conormal representatives.
- The representative conditions in these three formulas are not vacuous: the linear
  form of k lies in ker α because q(k) = 0; C(x) lies in ker φ because x ∈ I;
  and reduction sends ker φ into ker α because α after reduction equals φ
  (check on coefficients and variables). Each formula therefore specifies the map
  on all the stated generators/representatives, not merely on an arbitrary subset.
- The displayed sequence is short exact: `Function.Injective i`, `Function.Exact i p`,
  and `Function.Surjective p` encode exactness at the three nonzero terms.
- Splitting: existence of a C-linear `s` with `p.comp s = LinearMap.id`.
- J/J² ≅ (M ⊕ K) ⊗_A C: the first `Nonempty` C-linear equivalence, with
  `I.Cotangent × LinearMap.ker q` for the two-term direct sum.
- (M ⊕ K) ⊗_A C ≅ C^m: the second `Nonempty` C-linear equivalence to `Fin m → C`.
  Finite products are finite direct sums; tensor factors are swapped throughout to
  `C ⊗[A] M`, Mathlib's form with its C-module structure. The canonical tensor swap
  relates this exactly to the node's M ⊗_A C and preserves the generator formulas.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial` and `MvPolynomial.algHom_ext`; `Mathlib.Algebra.MvPolynomial.Eval`,
  `MvPolynomial.aeval` (and `MvPolynomial.eval₂Hom`, `MvPolynomial.map`). The full
  signatures and docstrings of the recorded declarations were read in the pinned source.
- `lem-weil-pbc-symmetric-algebra-universal-property` is a Mathlib leaf: its
  `mathlib_match` supplies `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`,
  `SymmetricAlgebra`, `SymmetricAlgebra.ι`, `SymmetricAlgebra.lift`,
  `SymmetricAlgebra.lift_ι_apply`, `SymmetricAlgebra.algHom_ext`. Their full source,
  including the tensor-algebra quotient and commutative-ring instance, was read.
  The literal type and canonical inclusion appear in the theorem; no private replacement.
- Supporting existing notions: `Mathlib.RingTheory.Ideal.Cotangent`, `Ideal.Cotangent`,
  `Ideal.toCotangent`; `Mathlib.RingTheory.Extension.Basic`,
  `Algebra.Extension.ofSurjective`, `Algebra.Extension.Cotangent`,
  `Algebra.Extension.Cotangent.mk`; `Mathlib.Algebra.Module.Projective`,
  `Module.Projective`; `Mathlib.Algebra.Exact.Basic`, `Function.Exact`.

Edge cases checked before writing: n = 0 permits P = R; m = 0 forces I = 0,
M = K = J/J² = 0 and C = A, so both isomorphisms have zero modules on either side.
For I = ⊤, A is the zero ring, M = K = C = 0; J = Q and J² = J, so the entire
sequence is zero. For I = 0 with redundant zero generators and m > 0, q = 0,
K = A^m, C = A, and the kernel is generated by all y variables, agreeing with
J/J² = C^m. No nontriviality, characteristic, smoothness, or regularity assumption
is imposed. All the literal constructions lie in R's universe u, without excluding
any commutative ring. No statement dispute or node fault found.

Searches made:

- `msearch.py ... leanfinder`, query: "split conormal exact sequence symmetric algebra
  of projective module over quotient polynomial ring". Eight hits: smooth cotangent
  retractions/projectivity and `IsSymmetricAlgebra`; no statement giving this sequence
  and its specified maps/isomorphisms.
- `msearch.py ... loogle`, query: "SymmetricAlgebra, Algebra.Extension.Cotangent".
  Zero hits.
- `msearch.py ... grep`, query: "conormal|Cotangent", directory `RingTheory/Extension`.
  Twenty-five hits on existing extension/conormal API, with no matching symmetric
  projective conormal-sequence theorem.
- `msearch.py ... leansearch`, query: "conormal sequence symmetric algebra projective
  module over quotient polynomial ring split exact". Service unavailable (Internal
  Server Error); recorded as unavailable, not a negative result.
- `rg 'SymmetricAlgebra|conormal.*Sym'` in Mathlib `RingTheory/Extension` and
  `LinearAlgebra/SymmetricAlgebra`: symmetric-algebra construction/universal property
  only, no theorem matching the entire node.
- `rg 'SymmetricAlgebra|symmetric-projective-presentation-conormal'` in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's `lean/Sheaf`:
  no upstream matches; existing project `CotangentComplexSymmetricAlgebra` states
  only the general surjective linear-form map and differential formulas, not this
  projective split exact sequence. `ImprovePresentationSmoothConormalFree` cites
  the item in its proof docstring but does not state it.
- `grep -rn 'lem-weil-pbc-symmetric-projective-presentation-conormal'` in upstream
  `WeilConjectures`: no matches. `rg 'symmetric_projective_presentation_conormal'`
  in Mathlib, upstream, project Lean, and `dag/lean_names_upstream.json`: no matches.

Validation: server `scompile.py` succeeded with no errors or warnings in 3.4 seconds.
The initial compile required an explicit type on the section `s` and replacing the
obsolete `Mathlib.Algebra.Exact` import with `Mathlib.Algebra.Exact.Basic`; both repaired.
The final module contains no temporary checks, local notation, local instances, or
`let`/`show ... from` binders.

## Second reading by U1

I independently read the sandbox node and Lean module, both statement-dependency
nodes and their recorded Mathlib signatures, and Stacks smoothing.tex lines
325–430 and more-algebra.tex lines 2067–2110 in `/home/ubuntu/c1-stacks-review/`.
The source uses a finitely presented R-algebra through a finite polynomial
presentation and finite ideal generators, exactly as made explicit by this node.
The section's Noetherian remark is conditional, not a standing assumption.
The projective restriction already belongs to the base node. There is no
`statement_change` in this delivery, nor any new node or dependency module.
In this projective case, a local split free presentation has coordinate-variable
relations, which justify the conormal identification and left exactness beyond
the general 07EV assertion. I checked the proof docstring against every node step.

My object, hypothesis, and conclusion inventory, matched to the actual signature:

| Node item | Lean rendering and verdict |
| --- | --- |
| Commutative R | `(R : Type u) [CommRing R]`; no domain, field, Noetherian or nonzero assumption. PASS. |
| n and m finite, possibly zero | `(n m : ℕ)` and `Fin n`, `Fin m`. PASS. |
| P = R[x₁,…,xₙ] | `MvPolynomial (Fin n) R`, the recorded polynomial notion. PASS. |
| I = (f₁,…,fₘ) | Ideal binder `I`, `f : Fin m → I`, and `hf : Ideal.span (Set.range (fun j ↦ (f j).1)) = I`; the subtype packages precisely generator membership. PASS. |
| A = P/I | Literal `MvPolynomial (Fin n) R ⧸ I`. PASS. |
| M = I/I² as an A-module | `I.Cotangent`, defined as `I ⧸ (I • ⊤)` with its quotient-ring module instance. PASS. |
| M projective | `[Module.Projective (P ⧸ I) I.Cotangent]`, exactly a summand of a free module. PASS. |
| q(e_j) = class of f_j | A-linear binder q and `hq : ∀ j, q (Pi.single j 1) = I.toCotangent (f j)`. These basis equations determine q. PASS. |
| K = ker q | Literal `LinearMap.ker q`. PASS. |
| C = Sym_A(M) | Literal `SymmetricAlgebra (P ⧸ I) I.Cotangent`, inclusion `SymmetricAlgebra.ι`. PASS. |
| Q = P[y₁,…,yₘ] | `MvPolynomial (Fin m) (MvPolynomial (Fin n) R)`. PASS. |
| Q → C extends P → A → C | Ring map φ and hφC prescribing precisely the quotient then algebra map. PASS. |
| y_j maps to ι(q(e_j)) | hφX. PASS. |
| J = ker(Q → C) | Kernel of `Extension.ofSurjective φ.toIntAlgHom hφ`; Ring = Q and underlying map = φ. PASS. |
| Q → C surjective | Existential `hφ : Function.Surjective φ`. PASS. |
| Resulting reduced presentation A[y] → C | A-algebra map α with hαX and existential surjectivity hα. PASS. |
| Reduced conormal ≅ K ⊗ C | C-linear equivalence lam from `C ⊗[A] LinearMap.ker q` to the reduced extension cotangent, with the linear-form equation. PASS. |
| First map (f mod I²) ⊗ c ↦ c(f mod J²) | C-linear i and its formula for every c and x : I, with constant polynomial representative y. PASS. |
| Second map induced by reduction | C-linear p with `lam (p (Extension.Cotangent.mk x)) = Extension.Cotangent.mk y` whenever y is coefficient reduction of x modulo I. PASS. |
| Short exact sequence | `Function.Injective i ∧ Function.Exact i p ∧ Function.Surjective p`; exactness is image = kernel. PASS. |
| Splitting as C-modules | Existential C-linear s with `p.comp s = LinearMap.id`. PASS. |
| J/J² ≅ (M ⊕ K) ⊗ C | First `Nonempty` C-linear equivalence to `C ⊗[A] (I.Cotangent × LinearMap.ker q)`. Finite products give the two-term direct sum. PASS. |
| (M ⊕ K) ⊗ C ≅ C^m | Second `Nonempty` C-linear equivalence to `Fin m → C`. PASS. |

The q, φ, and α binders introduce canonical data without extra hypotheses:
q exists by the finite free basis, φ by `MvPolynomial.eval₂Hom`, and α by
`MvPolynomial.aeval`; their equations uniquely determine them. Surjectivity of
α expresses the resulting presentation referred to by the node, not an added
assumption. The quantifiers introduce these data before the maps and their
formulas, exactness, section, and equivalences. The reversed tensor order uses
the canonical tensor swap and supplies the C-action, with exactly the node's
pure-tensor formulas.

I checked especially that no representative implication is vacuous. For every
k in ker q, α(Σ k_j y_j) = ι(q(k)) = 0, by linearity and basis expansion.
For x in I, φ(C(x)) = 0 by hφC. For x in ker φ, coefficient reduction belongs
to ker α: α composed with reduction equals φ by hφC, hφX, hαX and polynomial
extensionality. Thus each y required in the formulas exists. A kernel subtype
representative is unique for a fixed polynomial, and `Cotangent.mk` is
surjective. These formulas cover all the indicated generators.

Dependency signatures opened: MvPolynomial in Basic, aeval and aeval_X in Eval,
and algHom_ext in Basic give exactly the first node. SymmetricAlgebra's quotient
of the tensor algebra by commutation, its ι, CommRing instance, lift,
lift_ι_apply and algHom_ext give the second node. Supporting signatures read:
Ideal.Cotangent and toCotangent; Module.Projective; Function.Exact;
Algebra.Extension.ofSurjective, ker, Cotangent, Cotangent.module,
Cotangent.mk and mk_surjective. The extension cotangent is the kernel modulo
its square with the canonical target-ring action through lifts. Integer-algebra
reinterpretation changes neither the ring, map, kernel, nor conormal module.
No private replacement or missing notion was found.

Edge cases: n = 0 gives P = R. With m = 0, hf forces I = 0 and all sequence
terms are zero modules. With I = 0 and redundant zero generators, q = 0,
K = A^m, and J is generated by the y variables, giving J/J² = C^m. With
I = ⊤, including the zero base ring, A and C are zero rings, J = Q and
J² = J, so all displayed modules vanish. Empty schemes are not objects of
this ring statement; the corresponding empty-spectrum case A = 0 is included.
There is no characteristic restriction. All carriers are canonically built
from R in universe u, with no independently quantified carrier or test-algebra
universe excluded.

Independent searches, with different wording from the worker:

- LeanFinder: "kernel of symmetric algebra presentation projective module free
  conormal split sequence"; eight hits including IsSymmetricAlgebra,
  SymmetricAlgebra.instModuleFree and projective-module API; none this sequence.
- Loogle: `SymmetricAlgebra, Module.Projective`; zero hits.
- LeanSearch: "ideal modulo square of ideal polynomial presentation symmetric
  algebra split exact projective conormal"; Internal Server Error, recorded as
  unavailable, not evidence of absence.
- msearch grep: `SymmetricAlgebra|split.*exact|conormal` in RingTheory/Extension;
  two conormal documentation hits. Direct rg on Extension and SymmetricAlgebra
  source gives the construction and general cotangent API, not this theorem.
- Direct rg for SymmetricAlgebra, the node id and declaration name in upstream
  WeilConjectures, project lean/Sheaf and dag/lean_names_upstream.json found no
  upstream duplicate. I opened cotangentComplex_symmetricAlgebra: it states a
  general surjective linear-form map and differential formulas, not the
  projective equivalence or this split sequence. I also read the signature of
  improve_presentation_smooth_conormal_free: it assumes Smooth and asserts
  existence of another presentation, not this result.

No mismatch found; no Lean or node edits required. One named theorem has proof
sorry; there are no definitions or proved helpers, no local notation or local
instances, and no unbound variables or universes. Docstrings carry the source,
blueprint tag, and all node proof steps/dependencies; the imports, namespace,
topic and line lengths follow the conventions. The node's lean.statement is
the source signature verbatim (also equal to the parser's signature after its
whitespace normalization). Fresh server scompile passed in 3.4 seconds with
no errors or warnings. Only this second-reading report was added.
