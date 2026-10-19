## Worker report

The module `Sheaf.RingTheory.NormalRingFieldExtensionDescent` states
`Algebra.normal_ring_of_normal_tensor_field`, with its proof left `sorry`.
The node is unchanged except for its `lean` record. No new nodes, dependency modules,
or statement corrections are needed. Source read: `literature/stacks-project/algebra.tex`,
label `lemma-descent-normal` (Tag 033G), including the full local proof.
The theorem docstring carries all six DAG proof steps and their dependencies.

Hypothesis and clause correspondence:

- Fields F and E are `(F : Type u) (E : Type v) [Field F] [Field E]`.
- The field extension F ⊆ E is `[Algebra F E]`. Its unital map is `algebraMap F E`,
  automatically injective because F is a field; no algebraicity or separability is assumed.
- The commutative F-algebra B is `(B : Type w) [CommRing B] [Algebra F B]`.
  In particular there is no `Nontrivial B`, domain, Noetherian, or finite-type assumption.
- The commutative tensor algebra is `B ⊗[F] E`, using Mathlib's existing algebra tensor
  multiplication and unit, not a newly defined ring. `Algebra.TensorProduct.tmul_mul_tmul`
  and `Algebra.TensorProduct.one_def` give exactly the node's multiplication and unit.
  These identify the object; the statement adds no redundant equalities as hypotheses.
- Normality of this tensor algebra is the binder `h`, quantifying over every ideal q
  with `[q.IsPrime]` and asserting both `IsDomain (Localization.AtPrime q)` and
  `IsIntegrallyClosed (Localization.AtPrime q)`.
- Normality of B is the conclusion with the identical conjunction for every ideal p
  of B with `[p.IsPrime]`.
- All three carrier universes u, v, w are explicit and independent. No quantified
  class of test fields or rings is restricted to a potentially vacuous smaller universe.

Statement dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, imported through
  `Mathlib.RingTheory.TensorProduct.Basic`; the latter supplies the commutative algebra
  structure with its standard pure-tensor multiplication and unit.
- `def-weil-pbc-normal-ring`: its recorded INLINE FORM, using `IsDomain`,
  `IsIntegrallyClosed` from `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, and
  `Localization.AtPrime` from `Mathlib.RingTheory.Localization.AtPrime.Basic`.
  This leaf explicitly records that there is no named normal-ring predicate to import.

Proof dependency imports are present: `Mathlib.LinearAlgebra.Basis.VectorSpace`
(`Module.Free.of_divisionRing`), `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`
(`Module.FaithfullyFlat` and its scalar-extension instance),
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
(`PrimeSpectrum.comap_surjective_of_faithfullyFlat`,
`Module.FaithfullyFlat.of_flat_of_isLocalHom`,
`Ideal.comap_map_eq_self_of_faithfullyFlat`), and `Mathlib.RingTheory.RingHom.Flat`
(`RingHom.Flat.localRingHom`). All proof dependencies are Mathlib leaves or the
normal-ring inline definition; no project proof dependency module is missing.

Edge cases checked mathematically before writing:

- B = 0 is allowed: both spectra are empty and both normality conditions are vacuous.
- B = F × F is allowed: it is normal but not a domain, so global `IsDomain B`
  would be an incorrect strengthening. The statement only demands local domains.
- E = F recovers normality under the canonical tensor isomorphism.
- Transcendental, inseparable, and infinite field extensions are all included.
- Non-Noetherian B is included. The proof uses no optional Noetherian localization clause.
- A nonreduced algebra such as F[ε]/(ε²) fails the premise after every field extension;
  nilpotents are not made invisible by this statement.

Searches for an existing statement (2026-10-15):

- `msearch.py ... leanfinder "Normality of a commutative algebra descends along extension
  of the scalar field"`: eight hits, all field-extension `Normal` statements, including
  `Normal.tower_top_of_normal`, `IntermediateField.restrictScalars_normal`, and
  `AlgHom.normal_bijective`; none is normality of a ring at its primes.
- `msearch.py ... loogle "IsIntegrallyClosed, TensorProduct"`: zero hits.
- `msearch.py ... grep
  "IsIntegrallyClosed.*[Tt]ensor|[Tt]ensor.*IsIntegrallyClosed|normal.*descent|descent.*normal"`:
  zero Mathlib hits.
- `rg` with the same pattern over the slopmaster2 project's `WeilConjectures` and
  this group's `lean/Sheaf`: normalized sheaf gluing, normalization approximation,
  Hankel series, and comments citing this pending node; none states this theorem.
- Searching the item id in upstream and project sources found only references to it
  in `GeometricallyNormalPerfectClosureCriterion.lean`, with no declaration for it.
- `rg` for `normal_ring_of_normal_tensor|normal_of_normal_tensor|normal_of_tensor`
  in upstream sources, project statements, and `dag/lean_names_upstream.json`: no hits.

No STATEMENT-DISPUTED issue or node fault was found. The second reading is intentionally
left to the separate reader, as required by the dispatcher brief.


## Second reading by NY

Read the node copy, its Lean module, all four statement dependency nodes and all
seven proof dependency nodes. Read Stacks Algebra, lemma-descent-normal (Tag 033G),
its full proof and preceding descent-section introduction, and
 definitions definition-domain-normal (0309) and definition-ring-normal (00GV).
The section imposes no extra finiteness or domain assumptions. Tag 033G assumes
only faithful flatness and normality of the target. Its specialization to scalar
field extension is precisely this node. No statement correction is needed.

Object, hypothesis and conclusion inventory, matched item by item (H3):

1. A field F: `(F : Type u) [Field F]`. PASS. Read `Field` in
   Mathlib.Algebra.Field.Defs: it extends CommRing and DivisionRing, including
   nontriviality and inverses for nonzero elements.
2. A field E extending F: `(E : Type v) [Field E] [Algebra F E]`. PASS.
   Read the recorded `Algebra` declaration in Mathlib.Algebra.Algebra.Defs:
   its `algebraMap : F →+* E` is a unital ring map, with scalar multiplication
   determined by it. Over a field it is injective. Thus this is the dependency
   def-pc-field-extension's notion, with no algebraic or separable restriction.
3. A commutative F-algebra B: `(B : Type w) [CommRing B] [Algebra F B]`.
   PASS. There is no domain, Nontrivial, Noetherian or finite-type instance for B.
   The centrality axiom of Algebra is automatic for a commutative target and its
   scalar action is determined by the unital map, so it adds no restriction.
4. The commutative algebra B tensor_F E: `B ⊗[F] E`. PASS. Read TensorProduct's
   quotient construction in Mathlib.LinearAlgebra.TensorProduct.Defs and the
   multiplication and One instances in Mathlib.RingTheory.TensorProduct.Basic.
   `Algebra.TensorProduct.tmul_mul_tmul` gives exactly
   `(b ⊗ e)(b' ⊗ e') = bb' ⊗ ee'`, and `one_def` gives `1 ⊗ 1`.
   These are its actual ring operations, not extra hypotheses.
5. Normality of that tensor algebra: the entire binder `h`, namely
   `∀ (q : Ideal (B ⊗[F] E)) [q.IsPrime],
   IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)`.
   PASS. Every prime is quantified, and both the domain and integral-closedness
   clauses are present. Read Localization.AtPrime in AtPrime.Basic: localization
   at the prime complement. Read IsIntegrallyClosed in IntegrallyClosed: integral
   closedness in FractionRing, with isIntegrallyClosed_iff giving the elementwise
   integral criterion. Together with IsDomain this is exactly a normal domain.
6. Conclusion, normality of B: `∀ (p : Ideal B) [p.IsPrime],
   IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
   PASS. Same two clauses and prime quantifier as in the node, following the
   normal-ring dependency's explicitly recorded INLINE FORM. A global domain
   assumption or conclusion would be wrong and neither is present. The hypothesis
   h precedes the universally quantified conclusion as required.
7. Scope exclusions: PASS. Nothing else is assumed about B or E/F. The explicit
   independent universes `u v w` cover all carrier sizes. There is no quantified
   test-object universe that could make a premise vacuous.

Edge cases: B = 0 is permitted; it and its tensor algebra have no primes, so the
normality clauses are vacuous, as in the source. Products such as F × F are
permitted, and show why local domains rather than a global domain are essential.
E = F is included. Arbitrary infinite, transcendental and inseparable extensions,
all characteristics, and non-Noetherian algebras are included. No indexed family,
scheme, degree n or additional empty-object case occurs in this statement.

Independent searches (H4), using queries different from the worker's:

- LeanFinder via msearch: "A faithfully flat extension of commutative rings
  reflects normality at all prime localizations". Eight hits: going down,
  prime lifting, flat localization, and local flat-to-faithfully-flat lemmas.
  None states descent of normality.
- Loogle via msearch: `IsIntegrallyClosed, Localization.AtPrime`. Two hits:
  IsIntegrallyClosed.of_localization_maximal and IsIntegrallyClosed.of_localization.
  Both assume a global domain and infer global integral closedness from local
  integral closedness; neither is scalar-extension descent for arbitrary B.
- Mathlib grep via msearch:
  `IsNormalRing|isNormalRing|normal_ring|integrallyClosed.*faithfully|faithfully.*integrallyClosed`.
  Zero hits.
- Direct rg over the project's lean/Sheaf and the slopmaster2 WeilConjectures tree
  for `normal_ring|isnormalring|integrallyclosed.*tensor|tensor.*integrallyclosed|
  normality.*descen|descen.*normality` (case insensitive). Project hits concern
  regular or smooth rings, etale ascent, finite products, or comments citing this
  pending node. No normality descent statement exists there.
- Opened the upstream tensor-related hit
  Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct: it requires a domain,
  a weakly etale algebra and an algebraic fraction-field extension and concludes
  integral closedness in a specified tensor algebra. It is a different statement.
  Also opened IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn:
  its IsIntegrallyClosedIn premise is additional and its conclusion is global
  integral closedness, so it is not this node.
- Searched dag/lean_names_upstream.json for the declaration and normality descent;
  no match. The existing normality notions are used directly, without copies.

Dependency/import and delivery checks: the Mathlib declarations recorded for
faithfully-flat scalar base change (free vector spaces and faithful-flat tensor
base change), spectrum surjectivity, flat localization, local faithful flatness
and ideal contraction were opened and their signatures checked. They impose the
hypotheses stated by the corresponding nodes; no dependency module is missing.
There are no new nodes or dependency modules in this delivery (H12/H13), and no
statement_change to review. The six numbered proof paragraphs in the theorem
docstring follow all six node proof steps, with their dependency ids. Both
source and blueprint references are present. There are no definitions, private
copies, local instances or local notation; the only theorem proof is `sorry`.
Every universe and variable is explicitly bound. The node lean.statement was
compared programmatically with the file signature and is verbatim equal; all
Lean lines are at most 100 characters.

Mismatches and repairs: none found. The Lean module and node are unchanged; only
this independent second-reading section was appended to the report. Server
scompile.py compiled the sole delivered module cleanly in 1.2 seconds, at nice 19,
two threads and a 60-second limit, with no errors or warnings.
