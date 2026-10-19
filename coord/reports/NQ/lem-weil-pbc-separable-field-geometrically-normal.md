## Worker report

The module `Sheaf.FieldTheory.SeparableFieldGeometricallyNormal` states
`Algebra.normal_tensorProduct_of_isSeparableExtension`, with its sole proof `sorry`.
The node is unchanged except for its `lean` record. There are no new notions,
dependency repairs, statement corrections, or disputed statements.

Hypothesis and conclusion correspondence:

- “Let k be a field”: `(k : Type u) [Field k]`.
- “K/k a field extension”: `(K : Type v) [Field K] [Algebra k K]`.
- “separable, meaning every finitely generated subextension is separably generated”:
  `(hK : IsSeparableExtension k K)`. The imported definition quantifies over
  `F : IntermediateField k K`, with `F.FG → IsSeparablyGenerated k F`.
- “for every field extension E/k”: the arbitrary argument `(E : Type w)` with
  `[Field E] [Algebra k E]`. Universes u, v, w are independently explicit;
  this is a theorem parameter, not a bounded test-field hypothesis.
- “commutative tensor-product algebra K tensor_k E”: `K ⊗[k] E`, Mathlib's module
  tensor product with its canonical commutative algebra multiplication from
  `Mathlib.RingTheory.TensorProduct.Basic`.
- “each prime localization is an integrally closed domain”:
  `∀ (p : Ideal (K ⊗[k] E)) [p.IsPrime],
  IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
  Both domain and integral-closure clauses are included, using the mandated inline form.
- “No algebraicity or finite generation of either extension”: there are no
  `IsAlgebraic`, `FiniteType`, `Module.Finite`, or `FG` assumptions on K or E.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs, for all three fields.
- `Algebra`, Mathlib.Algebra.Algebra.Defs, for the two specified extensions.
- `Algebra.IsSeparableExtension` and `Algebra.IsSeparablyGenerated`,
  Sheaf.FieldTheory.SeparableExtension. Their full definitions and docstrings were read.
- `TensorProduct`, Mathlib.LinearAlgebra.TensorProduct.Defs, with canonical ring
  structure from Mathlib.RingTheory.TensorProduct.Basic.
- `Localization.AtPrime`, Mathlib.RingTheory.Localization.AtPrime.Basic;
  `IsIntegrallyClosed`, Mathlib.RingTheory.IntegralClosure.IntegrallyClosed;
  and `IsDomain`, the recorded normal-ring interface.

The stated proof dependencies are imported without `public`: perfect closure,
`Algebra.isReduced_tensorProduct_of_isSeparablyGenerated`, module flatness,
`RingHom.Flat`, and `Algebra.normal_tensor_perfectClosure_iff`. The theorem docstring
records all five proof steps, including the finite-tensor reducedness argument,
normalized coordinate-functional retraction, Frobenius powers, explicit inverses,
and tensor-factor swaps. No import into another node is part of this delivery.

Source checked directly: literature/stacks-project/algebra.tex,
label lemma-separable-field-extension-geometrically-normal (Tag 0C30), lines
46974–46990. It assumes exactly a separable field extension and concludes geometric
normality. Its proof passes through the perfect-closure tensor being a field.

Edge cases checked mathematically before writing:

- K = k or E = k: the appropriate tensor product is the other field, which is normal.
- Arbitrary characteristic: no positive-characteristic assumption is present;
  the proof docstring treats q = 1 and q = p separately.
- Transcendental and infinitely generated extensions remain allowed. In particular,
  this uses IsSeparableExtension rather than the algebraic IsSeparable predicate.
- The tensor product need not be a domain (e.g. a split nontrivial finite separable
  extension after scalar extension); the conclusion is local at primes, as required.
- All three fields are nonzero by Field; there is no spurious empty or zero-field case.
- Independent universe parameters allow extensions represented in different universes.

Searches made via msearch.py for this item:

- LeanFinder: “a separable field extension is geometrically normal: tensor with any
  extension has integrally closed domain prime localizations”: eight hits, concerning
  geometrically reduced algebras, unramified extensions, and Galois normal closures;
  none asserts normal prime localizations after arbitrary field extension.
- Loogle: `IsIntegrallyClosed, TensorProduct`: zero hits.
- Mathlib grep: `geometrically.normal|normal.*tensor.*separ|integrallyClosed.*tensor`:
  zero hits.
- LeanSearch: “A separable field extension is geometrically normal”: unavailable,
  service Internal Server Error. Other searches completed.
- rg of WeilConjectures and lean/Sheaf with the same regular expression and the node id:
  only related geometric-normality modules in Sheaf; no matching theorem. In particular,
  the perfect-closure criterion assumes normality of a tensor and does not prove it for
  a separable field extension.
- rg of dag/lean_names_upstream.json, WeilConjectures and lean/Sheaf for the chosen
  declaration name, module name and node-id suffix: no matches.

Validation: scompile.py compiled the delivered file cleanly on the server, nice 19,
two threads, 60 seconds per file (reported 1.2 seconds). No local compiler was run.


## Second reading by NQ

Independent reading of the repository node, sandbox node and complete Lean module,
Stacks algebra.tex Tags 0C30 and 037Z (lines 46885–46990), the section introductions,
and the separability definition 030O (lines 9904–9931). The source assumes only a
field and a separable extension; there is no ambient Noetherian or finite-type
convention. Tag 037Z defines geometric normality by all field extensions.

Object/hypothesis/conclusion checklist, in the order of the node:

- Base field k: `(k : Type u) [Field k]`. Exact; Mathlib Field is a commutative,
  nontrivial division ring, as required by def-weil-field.
- Field extension K/k: `(K : Type v) [Field K] [Algebra k K]`. Exact;
  def-pc-field-extension records Algebra, whose algebraMap is the specified
  unital field homomorphism and is necessarily injective. No extra tower is assumed.
- Separability of K/k: `(hK : IsSeparableExtension k K)`. Exact. Opened
  Sheaf.FieldTheory.SeparableExtension: its definition is
  `∀ F : IntermediateField k K, F.FG → IsSeparablyGenerated k F`.
  The latter definition gives a transcendence basis and Algebra.IsSeparable over
  its adjoined intermediate field, exactly 030O; FG is generation as a field.
- Every extension E/k: `(E : Type w) [Field E] [Algebra k E]`. Exact universal
  theorem parameters, with no separability hypothesis on E. Moving these
  independent parameters before hK changes no quantifier dependency.
- Commutative tensor algebra: `K ⊗[k] E`. Exact Mathlib TensorProduct, the
  quotient construction recorded by def-weil-pbc-module-tensor-product. Opened
  RingTheory.TensorProduct.Basic: one_def and tmul_mul_tmul give unit 1 tensor 1
  and multiplication (a tensor b)(c tensor d) = ac tensor bd.
- Every prime localization is a domain: `∀ (p : Ideal (K ⊗[k] E)) [p.IsPrime],
  IsDomain (Localization.AtPrime p)`. Exact. Read AtPrime.Basic: AtPrime is
  localization at p.primeCompl. The prime instance is universally bound, not
  an assumption that the whole tensor algebra is a domain.
- The same localization is integrally closed: the conjunction
  `∧ IsIntegrallyClosed (Localization.AtPrime p)`. Exact. Opened
  IntegralClosure.IntegrallyClosed: this means integral closure in FractionRing;
  together with IsDomain it is exactly the normal-domain condition. This is
  precisely the recorded inline interface of def-weil-pbc-normal-ring.
- Neither extension need be algebraic or finitely generated: no such binder
  occurs. Exact, and no dimension, cardinality, characteristic or finiteness
  hypothesis is hidden in the imported separability definition.

Edge cases: K=k and E=k specialize to normal fields. Finite split separable
base changes may produce products, so the prime-local formulation is essential
and correct. Transcendental and infinitely generated extensions are included.
All characteristics are covered, including characteristic zero; the proof text
explicitly handles q=1. Fields exclude zero rings by definition, as does the
source. There is no index family, scheme or degree n in this statement; an
empty transcendence basis and generation by the empty set remain allowed in
the dependency definitions. Independent explicit universes u,v,w admit fields
of different sizes: E is an arbitrary theorem parameter, not a test family in
a possibly too-small universe. No variable or universe is unbound.

Independently searched with msearch.py:

- LeanFinder: “prime localizations of a tensor product of a separable field
  extension with a field are normal domains”: eight hits, including integral
  closure localization comparisons, geometric reducedness, and linear-disjoint
  tensor domain results. None states this normality assertion.
- Loogle: `TensorProduct, IsIntegrallyClosed`: zero hits.
- rg of Mathlib, upstream WeilConjectures, and project lean/Sheaf with
  `geometrically.?normal|normal.*tensorProduct|tensorProduct.*normal|integrallyClosed.*tensor|tensor.*integrallyClosed`:
  no exact theorem. Opened the upstream WeaklyEtale.isIntegrallyClosedIn_tensorProduct
  hit: it assumes weak etaleness and an algebraic extension and concludes relative
  integral closure, not arbitrary separable geometric normality. The project
  perfect-closure criterion and geometrically-normal-tensor-normal theorem assume
  the normality input this item establishes; neither duplicates it.
- rg of dag/lean_names_upstream.json, upstream and project for the proposed
  declaration and module names found no collisions. The worker's LeanSearch
  service failure is recorded above; the independent successful searches suffice
  to check the proposed interface without inventing a replacement notion.

Opened the recorded proof interfaces too: the separably-generated tensor theorem
has independent field/algebra universes and a reduced-algebra argument; the
perfect-closure criterion has the normal-ring inline conclusion and all-field
quantification in a joint universe, usable here by universe lifts. Their imports
are ordinary proof imports. The Mathlib perfect closure, flatness, and ring-map
flatness imports agree with the node's remaining proof dependencies.

No new nodes, dependency modules or statement_change occur. No mismatch was
found; the Lean module and node record were preserved. The module and theorem
docstrings give the source and blueprint id; all five node proof steps are
present, including finite-tensor reduction, normalized coordinate retraction,
Frobenius powers, explicit inverse and tensor swaps. There are no definitions,
private copies or proved helpers; the sole theorem proof is sorry. The node's
lean.statement agrees verbatim with the signature before `:=`.

Validation repeated independently: scompile.py NQ
lem-weil-pbc-separable-field-geometrically-normal
lean/Sheaf/FieldTheory/SeparableFieldGeometricallyNormal.lean passed cleanly
on the server (1.1 seconds; nice 19, two threads, 60 seconds per file). It also
compiled the side-only perfect-closure criterion overlay (1.3 seconds). No local
compiler or library build was run. Second reading changes only this report.
