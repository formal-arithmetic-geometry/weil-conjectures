## Worker report

The module `Sheaf.RingTheory.CompletionFiniteQuotient` states
`AdicCompletion.completion_finite_quotient`, with its proof `sorry`. No definitions,
new nodes, dependency modules, or statement corrections are needed.

Hypotheses and objects, clause by clause:
- The commutative Noetherian local ring is `(R : Type u) [CommRing R]
  [IsNoetherianRing R] [IsLocalRing R]`; its unique maximal ideal is
  `m := IsLocalRing.maximalIdeal R`.
- The positive integer exponent is `(p : ℕ) (hp : 1 ≤ p)`. Natural numbers with this
  bound represent precisely the integers at least one. The coefficient is `(f : R)`.
- The quotient `R[z]/(z^p-f)` is `S := AdjoinRoot (X ^ p - C f)`.
  Mathlib defines AdjoinRoot literally as `Polynomial R ⧸ Ideal.span {X ^ p - C f}`,
  not as an arbitrary algebra or a field extension. Its quotient map is `AdjoinRoot.mk`;
  its structural map `φ := algebraMap R S` is the quotient of the coefficient inclusion.
- The hypothesis that this quotient is local is
  `[IsLocalRing (AdjoinRoot (X ^ p - C f))]`; its maximal ideal is `n`.
- The two completions are `Rhat := AdicCompletion m R` and
  `Shat := AdicCompletion n S`; their canonical maps are `ι` and `ιS`, respectively,
  given by `algebraMap`. Mathlib's algebra instance sends a ring element to its compatible
  sequence of classes modulo the powers of the ideal.
- The completed base acts through `g : Rhat →+* Shat`. The first conjunct specifies
  its induced-quotient-system meaning: for every completed element `a`, level `k`, and
  representative `r` with `evalₐ m k a = Ideal.Quotient.mk (m ^ k) r`, the corresponding
  coordinate of `g a` is `Ideal.Quotient.mk (n ^ k) (φ r)`. Every coordinate has a
  representative, so these equations specify exactly the inverse limit of the maps
  `R/m^k → S/n^k`. This avoids introducing a duplicate definition or requiring an
  unspecified algebra instance. Existence of this induced map is part of the conclusion,
  not an extra assumption on the input.
- The first asserted isomorphism is the ring equivalence
  `θ : AdjoinRoot (X ^ p - C (ι f)) ≃+* Shat`.
- Its full compatibility with both maps from `R[z]` is the equation, for every
  `q : R[X]`, `θ (AdjoinRoot.mk _ (Polynomial.map ι q)) = ιS (AdjoinRoot.mk _ q)`.
  Thus coefficients are mapped by ι and the variable remains the variable.
- The second asserted isomorphism is `γ : (Rhat ⊗[R] S) ≃+* Shat`, with the specified
  formula `γ (a ⊗ₜ[R] c) = g a * ιS c` for all `a` and `c`. Setting `a=1` or `c=1`
  gives preservation of the two structural maps. Since γ is a ring equivalence, those
  identities give precisely its S-algebra and Rhat-algebra compatibilities. Conversely,
  the algebra compatibilities give the displayed pure-tensor formula. The statement
  therefore uses one ring equivalence with both compatibilities rather than two unrelated
  algebra equivalences. There is no lost algebra-linearity clause.

Dependency declarations read and used:
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs` (imported transitively by AdjoinRoot); its docstring
  and definition identify it with finite generation of every ideal.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`
  (transitively imported by AdjoinRoot); read its finitely supported coefficient structure.
- `def-weil-pbc-adic-completion`: `AdicCompletion`,
  `Mathlib.RingTheory.AdicCompletion.Basic`, with the ring/algebra instance and `evalₐ`
  in `Mathlib.RingTheory.AdicCompletion.Algebra`. Read the compatible-family definition,
  algebra instance, and the quotient projection signatures and docstrings.
Additional existing Mathlib constructions: AdjoinRoot and AdjoinRoot.mk in
`Mathlib.RingTheory.AdjoinRoot`, maximalIdeal in
`Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs`, and tensor product in
`Mathlib.RingTheory.TensorProduct.Basic`.

Edge cases checked: p=1 gives S=R and the identity-type comparison; f=0 allows nilpotents
and is not excluded; no characteristic condition or primality condition on p is imposed;
p=0 is precisely excluded by the node's hypothesis; zero rings are excluded by locality
(exactly one maximal ideal), as IsLocalRing includes Nontrivial. At quotient level k=0
both quotients are zero rings and the coordinate condition is harmless. R need not be
complete, reduced, a domain, or a field. Universe u is arbitrary; all other types here
are constructions from R, so one explicit universe suffices. No auto-implicit binders.

Searches (actual calls recorded in searches.jsonl):
- msearch leanfinder: “The completion of a finite local polynomial quotient R[z]/(z^p-f)
  is the quotient over the completed Noetherian local ring, compatibly with the tensor
  product”. Eight hits: Weierstrass quotient comparisons and completion infrastructure;
  none state the finite local quotient theorem.
- msearch loogle: `AdicCompletion, AdjoinRoot`: zero hits.
- msearch leansearch: “completion of a finite local algebra over a Noetherian local ring
  tensor product”: service unavailable (Internal Server Error).
- msearch grep: `AdjoinRoot|quotient|ofTensorProductEquivOfFiniteNoetherian`, restricted to
  RingTheory/AdicCompletion: quotient infrastructure and finite-module ingredients, no
  completion-of-AdjoinRoot theorem.
- rg in WeilConjectures: `AdjoinRoot|CompletionFiniteQuotient|completion_finite_quotient`:
  AdjoinRoot uses in Kummer and etale theory; no matching theorem.
- rg in lean/Sheaf with the same pattern: no matching theorem.
- rg for the item id and for completion/AdjoinRoot cross-occurrences in WeilConjectures:
  no hits. rg in dag/lean_names_upstream.json for the proposed declaration: no hits.

The local literature checkout is absent. Source inspected at
[Stacks 07PR](https://stacks.math.columbia.edu/tag/07PR), the degree-p proof step, and
[Stacks 07N9](https://stacks.math.columbia.edu/tag/07N9), the finite-extension completion
statement and proof. They support the quotient identity and the tensor comparison.
The declaration docstring records all six DAG proof steps for stage 3.
No statement fault or disputed edge case was found.

## Second reading by F1

Independent reading of the sandbox node and module against Stacks Tags 07PR,
07N9 and 00MA. The local Stacks checkout is absent; I read the online tags and
also the raw `more-algebra.tex` label `lemma-helper-G-ring` and `algebra.tex`
label `lemma-completion-finite-extension` from stacks/stacks-project. The 07PR
ambient field, characteristic and inseparability assumptions explain its application;
they are not hypotheses of the general finite-local-algebra completion argument.
07N9 supplies that argument for any Noetherian base and finite ring map. Thus the
node's general positive exponent and arbitrary characteristic are justified.

Object, hypothesis and conclusion checklist (each verdict: exact):

- A commutative Noetherian local ring R: `(R : Type u) [CommRing R]
  [IsNoetherianRing R] [IsLocalRing R]`. There is no domain, field, completeness,
  reducedness or characteristic assumption. Its named maximal ideal m is
  `IsLocalRing.maximalIdeal R`; uniqueness makes this canonical choice equivalent
  to introducing the unique ideal explicitly.
- The completion and its map: `Rhat := AdicCompletion m R` and
  `ι := algebraMap R Rhat`, the compatible quotient classes of each coefficient.
- An integer p at least one and an element f: `(p : ℕ) (hp : 1 ≤ p) (f : R)`.
  These naturals parametrize precisely the allowed integer exponents.
- The specified polynomial quotient C and structural map: Lean calls it
  `S := AdjoinRoot (X ^ p - C f)` and `φ := algebraMap R S`.
  Read AdjoinRoot.lean: this is literally the quotient of `Polynomial R` by
  `Ideal.span {X ^ p - C f}`, and `AdjoinRoot.of` is `mk` composed with
  the constant-polynomial inclusion. The letter S changes no object.
- C local, its maximal ideal and its completion: the input instance
  `[IsLocalRing (AdjoinRoot (X ^ p - C f))]`, `n := IsLocalRing.maximalIdeal S`,
  `Shat := AdicCompletion n S`, and `ιS := algebraMap S Shat`.
  No extra finiteness or continuity instance is demanded of the input.
- The completed-base action is the existential ring homomorphism
  `g : Rhat →+* Shat` with the first conjunct. For every a, k and representative r
  of its k-th coordinate, the k-th coordinate of g(a) is the class of φ(r).
  Every quotient element has a representative, so this condition determines g
  uniquely, and its coordinates are exactly the induced maps R/m^k → C/n^k.
  Such maps are well-defined because the finite integral local extension contracts
  n to m (node proof step 2). In particular g(ι(r)) = ιS(φ(r)); existence of g is
  asserted, not assumed. The universal quantification over representatives adds
  no condition beyond being this induced map.
- First conclusion: `∃ θ : AdjoinRoot (X ^ p - C (ι f)) ≃+* Shat` is precisely
  the requested ring isomorphism. The following `∀ q : R[X]` equation compares
  `θ (AdjoinRoot.mk _ (Polynomial.map ι q))` with
  `ιS (AdjoinRoot.mk _ q)`, hence gives the full commutative diagram from R[z],
  coefficient by coefficient with the variable fixed. No stronger completed-base
  linearity is silently required of θ.
- Second conclusion: `∃ γ : (Rhat ⊗[R] S) ≃+* Shat` and
  `∀ (a : Rhat) (c : S), γ (a ⊗ₜ[R] c) = g a * ιS c`.
  Taking c = 1 and a = 1 gives compatibility with the completed-base and S
  structure maps, respectively. Multiplicativity then gives linearity for both
  scalar actions on every tensor, and the inverse inherits both compatibilities.
  Conversely the two algebra compatibilities give the stated pure-tensor formula.
  This is one comparison map with both algebra structures, exactly as requested.
  The same g specifies the completed-base action throughout. θ and γ are
  existentially quantified after the input data, without requiring any unrequested
  compatibility between the two isomorphisms.

Dependency signatures independently opened: `Polynomial (R : Type*) [Semiring R]`
(Algebra/Polynomial/Basic.lean), `IsNoetherianRing R := IsNoetherian R R`
(Noetherian/Defs.lean, with `isNoetherianRing_iff_ideal_fg`), and
`AdicCompletion I M` as compatible families in the quotients by `I ^ n • ⊤`
(AdicCompletion/Basic.lean). For M = R these quotients identify with R/I^n;
Algebra.lean's `evalₐ (n : ℕ) : AdicCompletion I R →ₐ[R] R ⧸ I ^ n`
makes that identification explicitly. Its algebra instance sends constants to
compatible quotient classes. These are the declarations of all three statement
dependency nodes, not private substitutes. Also read AdjoinRoot.mk, its algebraMap
identity, IsLocalRing and maximalIdeal. No new definition nodes or dependency
modules occur in this delivery; no statement correction occurs.

Edge cases: p = 1 is allowed and gives the linear quotient; p = 0 is excluded by
exactly the node's bound. f = 0 and nilpotents are allowed. IsLocalRing extends
Nontrivial, matching exactly one maximal ideal and correctly excluding the zero
ring. At k = 0 both coordinate quotients are zero rings and the implication is
harmless. There is no empty index choice or scheme in this statement; its inverse
systems run over all naturals. Universe u is bound and arbitrary; quotient,
polynomial, tensor and completion constructions from R introduce no additional
independent universe restriction. All binders and the one universe were checked
by eye; no free or auto-implicit variables remain.

Independent searches, using different phrases from the worker:

- msearch leanfinder: `completion of a finite local algebra tensor comparison at
  maximal ideals`, eight hits. The relevant hit is
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`; I opened its signature.
  It is a linear equivalence with the m-adic completion of a finite module, not
  the n-adic ring completion plus polynomial presentation and both compatibilities.
- msearch loogle: `AdicCompletion, Polynomial`, zero hits.
- msearch leansearch: `completion of finite local polynomial quotient equals base
  change to completed ring`; service returned Internal Server Error. This is
  unavailable, not evidence of absence.
- rg in Mathlib/RingTheory/AdicCompletion for AdjoinRoot, quotient and completion
  comparisons; opened `AdjoinRoot.tensorAlgEquiv` independently. It gives base
  change of AdjoinRoot only and is an ingredient, not this statement.
- rg for `AdicCompletion`, completion/tensor and completion/quotient phrases in
  all WeilConjectures and lean/Sheaf: adic infrastructure and other completion
  statements, no equivalent theorem. Searches of the proposed full name and
  dag/lean_names_upstream.json found no collision.

No mismatch found and no Lean or node change needed. The module has a single
named theorem with `by sorry`, no definitions or proved auxiliary declarations.
The module and theorem docstrings cite the source and exact blueprint id; the
six numbered proof steps track the node's six steps, including the topology
comparison inside 07N9 and both final compatibility assertions. All lines meet
the 100-character convention. The node's lean.statement is the file's signature
verbatim. This second reading adds this independent report only.
