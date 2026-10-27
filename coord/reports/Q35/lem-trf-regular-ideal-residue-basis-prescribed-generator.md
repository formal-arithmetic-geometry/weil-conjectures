## Worker report

The module `Sheaf.RingTheory.RegularIdealResidueBasis` states
`RingTheory.Sequence.regularIdeal_residue_basis_prescribed_generator` with a single
`sorry` proof. It introduces no definitions or additional nodes. The node is unchanged
outside its new `lean` record.

Sources read: `literature/stacks-project/algebra.tex`,
`lemma-regular-quasi-regular` (Tag 00LN), especially (1) and the homogeneous-coordinate
proof, and `lemma-ci-well-defined` (Tag 00SE), especially its last paragraph extending
an element with nonzero residue to a minimal generating set by Nakayama. No Noetherian
or regular-local-ring hypothesis is needed for the extracted regular-sequence-ideal
assertion; those hypotheses in the surrounding 00SE statement concern its ambient
surjection comparison, rather than this linear algebra and Nakayama argument.

The hypothesis and clause correspondence is:

- A commutative local ring is `(R : Type u) [CommRing R] [IsLocalRing R]`.
  The maximal ideal is `IsLocalRing.maximalIdeal R`; the residue field is written
  literally as `R ⧸ IsLocalRing.maximalIdeal R`, definitionally the recorded
  `IsLocalRing.ResidueField R`. Mathlib supplies its field and quotient module structures.
- The length is `(b : ℕ)`, including zero. The displayed ideal and its generating
  sequence are parameterized as `(I : Ideal R) (z : Fin b → I)` with
  `hI : Ideal.span (Set.range (fun i ↦ (z i : R))) = I`.
  This is an explicit parameterization of the node's instruction “put I=(z_i)”.
  Giving the generators as elements of `I` merely bundles their known memberships:
  every original family of ring elements produces precisely these subtype elements,
  and forgetting their memberships recovers the original family. The equality `hI`
  fixes exactly the ideal in the node, with no finiteness or nonzero assumption added.
- The membership of the generators in the maximal ideal is `hz`; their regularity
  is `hreg : IsRegular R (List.ofFn (fun i ↦ (z i : R))))`.
- The submodule denoted by mI inside I is
  `IsLocalRing.maximalIdeal R • (⊤ : Submodule R I)`. Its image under the inclusion
  of `I` into `R` is the product ideal `IsLocalRing.maximalIdeal R * I`:
  its elements are finite sums of maximal-ideal elements times elements of `I`.
  Consequently the quotient type in the statement is exactly the node's `I/mI`,
  rather than a quotient of `R` by the product ideal.
- The existential basis `v : Module.Basis (Fin b) (R ⧸ maximalIdeal R) (I ⧸ ...)`
  together with `∀ i, v i = (...).mkQ (z i)` says the residue classes of the given
  generators, in their given order, form a residue-field basis.
- The existential conormal basis `c : Module.Basis (Fin b) (R ⧸ I) I.Cotangent`
  and `∀ i, c i = I.toCotangent (z i)` fix the degree-one conormal coordinates.
  `c.equivFun.symm` is the map `(R/I)^b → I/I²` taking coefficients to their sum
  against the classes of the generators; the analogous map for `v` is the residue
  coordinate isomorphism.
- The existential `q : I.Cotangent →ₗ[R] (I ⧸ ...)` is fully characterized by
  `∀ x : I, q (I.toCotangent x) = (...).mkQ x`. Since `I.toCotangent` is surjective,
  this fixes `q` uniquely as the canonical quotient projection. No unspecified or
  arbitrary comparison map replaces the canonical one. `Function.Surjective q` and
  `LinearMap.ker q = maximalIdeal R • (⊤ : Submodule R I.Cotangent)` explicitly
  identify its quotient. The R-action on `I.Cotangent` factors through `R/I`, so
  this kernel is exactly `(m/I)(I/I²) = mI/I²` in the source notation.
- The formula quantified over `a : Fin b → R` is the commuting square on lifted
  coefficients: first reduce each coefficient modulo I and use conormal coordinates,
  then apply `q`; or first reduce each coefficient modulo m and use residue
  coordinates. These give the same result. Every finite coefficient tuple over
  `R/I` lifts to `R`, and m/I is the kernel of the coefficient reduction, so this
  is exactly the claimed descent of the conormal coordinate isomorphism upon
  quotienting by m/I. It specifies the coordinate compatibility, not just two
  unrelated free-module assertions.
- `∀ (r : ℕ) (y : Fin r → R), Ideal.span (Set.range y) = I → b ≤ r`
  states the bound for every finite generating list, including repeated entries.
- The prescribed element is `x : I` with
  `(x : R) ∉ IsLocalRing.maximalIdeal R * I`; hence both memberships in the
  node's `I \ mI` are present. Its conclusion begins with `1 ≤ b`.
  The family `w : Fin b → I` is the replacement list. The condition
  `∀ i, i.val = 0 → w i = x` puts `x` first; because `1 ≤ b`, the zero index
  exists. Its remaining entries are exactly the required `b-1` lifts.
  The second basis `v` and its value formula identify the residues of this very
  family as a basis; its span equality says this same family generates `I`.
  No regularity of `w` is asserted.
- The final implication `b = 0 → I = ⊥ ∧ Subsingleton (I ⧸ ...)` explicitly
  states both zero-length conclusions. When `I=0`, its unique element is zero
  and belongs to mI, so the prescribed-element assertion has no instances.

Dependency declarations read and used:

- Statement dependency `def-weil-pbc-regular-sequence`:
  `Mathlib.RingTheory.Regular.RegularSequence`, `RingTheory.Sequence.IsRegular`.
  Read its docstring and full structure extending `IsWeaklyRegular` with
  `top_ne_smul`; the module is publicly imported.
- Statement dependency `def-weil-pbc-free-module`:
  `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`, whose full class is
  existence of a `Module.Basis`. Here actual `Module.Basis` witnesses state the
  node's prescribed bases, rather than only their freeness. The module is publicly
  imported. Basis and quotient signatures were also read in Mathlib source.
- Proof dependency `lem-weil-pbc-regular-sequence-conormal-free`:
  `WeilConjectures.RingTheory.RegularSequenceConormal`,
  `RingTheory.Sequence.regularSequence_conormal_free`; read the whole statement
  and proof docstring. Imported privately as a proof dependency.
- Proof dependency `lem-sfb-independent-family-spanning-cardinality`:
  `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`,
  `linearIndependent_le_span''`; read its full signature and docstring.
  Imported privately.
- Proof dependency `lem-weil-pbc-nakayama-local-generators`:
  `Mathlib.RingTheory.LocalRing.Module`, `IsLocalRing.map_mkQ_eq_top`;
  read the signature and neighboring finite-module/Nakayama API. Imported privately.
- `Mathlib.RingTheory.Ideal.Cotangent` publicly supplies the actual conormal module
  and its projection. `Cotangent I` is defined as `I ⧸ I • ⊤`; no new definition
  of this notion is made.

Edge cases checked before writing and again against the final signature:

- `b=0`: `Fin 0` and the list are empty, `hI` forces `I=0`, and both coordinate
  modules and both quotient modules are zero. Empty bases and zero maps give the
  stated conclusions. The prescribed-element antecedent has no instances.
- `b=1`: a nonzero residue of `x` replaces the sole residue basis vector, and
  Nakayama gives `I=(x)`; the existential family has exactly one entry, forced to be x.
- An empty or repeated generating list is allowed by the bound clause. Repetition
  cannot artificially increase the independent residue dimension.
- For a field, the only possible ideal generated by such a regular sequence in
  the maximal ideal is zero with empty sequence. A nonempty zero generator is
  not regular, so no false positive case is included.
- For `R=k[t]_(t)`, `I=(t²)`, `x=t³` is excluded because it lies in mI, even though
  it is a nonzero element of I. An x in I outside mI, for example t², is admitted.
- No Noetherianity, completeness, characteristic, permutation-regularity or
  regularity of the replacement family is assumed. Only the original finite
  generating family makes I a finite module for Nakayama.
- The arbitrary explicit universe `u` retains all sizes of commutative local rings.

Searches (all made on 2026-10-24; raw wrapper records are in `searches.jsonl`):

- LeanFinder via `msearch.py`: “An ideal generated by a regular sequence in a
  local ring has residue basis its generators and every element outside m I
  extends to a minimal generating list”. Eight related hits, including
  `IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal`,
  `Module.exists_basis_of_span_of_maximalIdeal_rTensor_injective`,
  `IsLocalRing.basisQuotient` and `Module.exists_basis_of_basis_baseChange`.
  None states this theorem; basisQuotient concerns a free algebra quotient,
  and the lifting statements require tensor injectivity and finite presentation.
- Loogle via `msearch.py`: `RingTheory.Sequence.IsRegular, Ideal.Cotangent`.
  Zero hits.
- Mathlib grep via `msearch.py` in `RingTheory`:
  `regular.*(basis|cotangent)|residue.*basis`. Four hits in regular-local-ring
  dimension characterizations, with no exact match.
- LeanSearch via `msearch.py`: “The residue classes of a regular sequence form
  a basis of I modulo m I and any element outside m I extends to a minimal
  generating set”. Eight related hits, including `IsLocalRing.span_eq_top_of_tmul_eq_basis`,
  `RingTheory.Sequence.IsRegular` and `Module.exists_basis_of_basis_baseChange`.
  No exact match; the Nakayama theorem provides only the last proof step.
- `rg` of `regular.*(residue|prescribed)|residue.*basis` in both
  `lean/WeilConjectures` and `lean/Sheaf`, and targeted residue-basis/prescribed-generator
  searches in both `RingTheory` directories: no exact statement. Found related
  residue differential bases, flat algebra bases and semilocal submodule bases,
  which have different modules or hypotheses.
- The item id search in `lean/WeilConjectures` found no existing attachment.
- Exact proposed declaration-name search across Mathlib, both project roots and
  `dag/lean_names_upstream.json` found no collision.

Validation: `scompile.py Q35 lem-trf-regular-ideal-residue-basis-prescribed-generator`
compiled the delivered module in sandbox and library module mode with no errors
or unexpected warnings (reported 1.4 s and 1.7 s). Every variable and universe is
explicitly bound. No disputed statement or node correction was necessary.

## Second reading by Q35

I reopened the node and final module and reread the signature clause by clause.
This is this single dispatcher's worker's rereading; the maintainer supplies the
independent delivery review, and no second agent was started.

The node's local-ring and regularity hypotheses match the first binders and `hz`,
`hreg`. The `z : Fin b → I`/`hI` parameterization neither enlarges nor restricts the
original family: I is still exactly its span. The two bases have the exact quotient
scalars and generators stated in the node. In particular, the residue denominator
is a submodule of I, not an ideal quotient of R. The conormal reduction q is fixed
on every representative and its kernel is the required maximal-ideal multiple;
the lifted-coefficient equation is the actual quotient compatibility. The generator
bound quantifies over arbitrary ring-valued finite lists. The prescribed family
has b entries with first entry x, its own residue basis, and its own generating
ideal equality, without an added regularity clause. The explicit b=0 implication
and impossible prescribed-element antecedent handle the empty case. No mismatch
was found and no statement changes were made during this rereading.
