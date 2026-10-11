## Worker report

Module: `Sheaf.AlgebraicGeometry.SpreadFiniteSeparableExtension`.
Declaration: `AlgebraicGeometry.exists_spread_finite_separable_extension`.
One theorem statement, with `sorry`; no definitions or proofs added. The node is unchanged except for its `lean` record.

Hypotheses and conclusions, clause by clause:

- A Noetherian integral domain: `(A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]`.
- Its fraction field K: `(K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]`.
- The field extension K'/K: `(L : Type w) [Field L] [Algebra K L]`. Here L denotes K'. `[Algebra A L] [IsScalarTower A K L]` records the composite structural map A -> K -> L, rather than an additional mathematical restriction; the composite structure always exists.
- Finite-dimensional over K: `[FiniteDimensional K L]`. No numerical dimension is used or imposed.
- Separable algebraic: `[Algebra.IsSeparable K L]`. Its docstring and `Algebra.IsSeparable.isAlgebraic` confirm that algebraicity is already included.
- A nonzero c in A: `∃ c : A, c ≠ 0 ∧ ...`.
- A[c^{-1}]: `∃ S : Subalgebra A L, IsLocalization.Away c S ∧ ...`. This is a model of the principal localization inside L, not an extra finiteness hypothesis. The injection A -> L follows from the field extension and fraction-field maps; any abstract localization maps injectively into L for c != 0. Conversely this predicate identifies S with the principal localization via its universal property.
- The A[c^{-1}]-algebra A': `∃ B : Subalgebra S L, ...`, with its canonical S-algebra structure. The subalgebra representation chooses the embedding of the domain A' in its given fraction field L; it imposes no extra restriction on the abstract algebra promised by the node. Conversely the represented B is such an abstract algebra. All maps here agree with the given A -> K -> L.
- Finite algebra: `Module.Finite S B`.
- Etale algebra: `Algebra.Etale S B`.
- A domain: `IsDomain B` (also inferable for a subalgebra of a field, but retained to render the explicit clause).
- Fraction field K': `IsFractionRing B L`, using the canonical inclusion, not just an unstructured field isomorphism.
- Consequently Spec(A') -> Spec(A[c^{-1}]) finite: `IsFinite (Spec.map (CommRingCat.ofHom (algebraMap S B)))`.
- The same morphism etale: `Etale (Spec.map (CommRingCat.ofHom (algebraMap S B)))`.
- The same morphism surjective: `Surjective (Spec.map (CommRingCat.ofHom (algebraMap S B)))`.

Dependencies used, with the recorded signatures and docstrings read in the pinned source:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`; fields and their algebra structure give the extension.
- `def-weil-vector-space-dimension`: `Mathlib.LinearAlgebra.Dimension.Finrank`, `Module.finrank`; the node uses finite dimensionality rather than a specified value of dimension, so `FiniteDimensional K L` renders this hypothesis and the module providing the recorded notion is imported.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`, `Algebra.IsSeparable`; incorporates algebraicity, as its docstring explains.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`; its affine-local ring-map definition renders the scheme conclusion. `Algebra.Etale` is the corresponding algebra notion.
- Supporting existing Mathlib notions: `Subalgebra`, `IsLocalization.Away`, `IsFractionRing`, `IsNoetherianRing`, `Module.Finite`, `IsFinite`, `Surjective`, `Spec.map`. No new notion is needed.

Edge cases checked before writing: the extension of degree one works with alpha = 0 and a linear minimal polynomial; A may itself be a field, when c = 1 is possible; arbitrary characteristic is included, and separability ensures a nonzero discriminant even in positive characteristic. Zero rings and zero fields are excluded exactly by the domain and field hypotheses. No degree-zero extension exists between fields. No unnecessary proper-extension hypothesis or choice of characteristic is imposed. Universes u, v, w are independent; S and B are both subtypes of L and therefore their spectra have the same universe without restricting the universes of A or K. No vacuous test-object quantifier occurs.

Searches made:

- `msearch.py ... leanfinder "finite separable extension of fraction field spreads to finite etale algebra over localization"`: eight hits, including `Algebra.Etale.exists_subalgebra_fg`, `Algebra.Etale.iff_exists_algEquiv_prod`, localization etaleness, and `Algebra.exists_etale_of_isEtaleAt`; none has the required finite domain with the prescribed fraction field after principal localization of the base.
- `msearch.py ... loogle "Algebra.Etale, IsFractionRing"`: zero hits.
- `msearch.py ... grep "exists.*[Ee]tale|[Ee]tale.*[Ff]raction" RingTheory`: 22 hits on Noetherian descent, totally split algebras, standard smooth presentations and etale loci; no exact spreading theorem.
- `rg` of the source `WeilConjectures` and the project's `lean/Sheaf` for `spread.*[Ss]eparable|finite.*separable.*[Ee]tale|lem-weil-pbc-spread-finite-separable-extension`: no source match; project siblings include `GenericFiniteAlgebraSplitting`, which refers to this item in its proof docstring but does not state it.
- Search of Mathlib, the source, the project and `dag/lean_names_upstream.json` for the proposed full declaration name: no collision.

The cited blueprint source file is not materialized on this machine (only literature lists/import tools are present). The node's complete source-attributed three-step proof and its parent's recorded finite-algebra calculation were read. The declaration docstring reproduces those proof steps and names all four proof dependencies. No statement correction or mathematical dispute was necessary.

Server validation: `scompile.py P1 lem-weil-pbc-spread-finite-separable-extension <module>` succeeded in 2.3 seconds, exit 0, with no errors or warnings.

## Second reading by P1

I independently opened the delivered node and Lean module, all four statement-dependency
nodes, and their recorded Mathlib declarations. I recovered the actual blueprint source
by a read-only SSH read of the server's literature/blueprint/master/blueprint/
sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-finite-pushforward-generic-constructible.md.
Its finite-algebra calculation starts with a Noetherian domain A and fraction field K,
and explicitly constructs the finite free etale domain inside K' after denominator and
nonzero-discriminant inversion. The surrounding hypotheses about Z and E are used to choose
K', not to spread a given finite separable extension. Galoisness is not needed for this
calculation: finite separability gives precisely the primitive element it uses.

I also fetched and read the actual Stacks fields.tex and algebra.tex and their tags table
in the sandbox scratchpad: Fields 030N (primitive element), 09G1 (the algebraic simple
extension is the minimal-polynomial quotient), Algebra 00UB (standard etale definition),
00UC (standard etale implies etale), and 00GQ (injective integral ring maps give surjective
spectra). Their hypotheses match the node's construction. One inherited bibliographic
inaccuracy is present in proof step 1 of the node: 09GN is the degree/minimal-polynomial
lemma, while the primitive-element theorem is 030N. The dependency's own source and the
maintainer's existing review already identify 030N correctly. The Lean docstring cites
that dependency, rather than repeating the inaccurate tag. No mathematical statement
correction is required, and I did not edit the node's proof/source fields.

The node's objects, hypotheses and conclusion, in order, matched independently:

- Object A, a Noetherian integral domain: `(A : Type u) [CommRing A] [IsDomain A]
  [IsNoetherianRing A]`. Exact; Noetherian is retained even though the construction works
  more generally.
- Object K, its fraction field: `(K : Type v) [Field K] [Algebra A K]
  [IsFractionRing A K]`. Exact: IsFractionRing is localization at all nonzero divisors,
  which for the given domain are exactly its nonzero elements.
- Object K'/K, a field extension: `(L : Type w) [Field L] [Algebra K L]`.
  Exact; L denotes K'. The dependency's `Algebra` class supplies algebraMap, the given
  field homomorphism. `[Algebra A L] [IsScalarTower A K L]` expresses its composite with
  A -> K. Such a structure always exists and the tower fixes its algebraMap to that
  composite, so this introduces no additional restriction on the field extension.
- Finite-dimensional as a K-vector space: `[FiniteDimensional K L]`. Exact: Mathlib
  defines this as Module.Finite over a field; no degree is prescribed by the node.
  The dimension dependency's Module.finrank was read, but no numerical finrank belongs
  in this statement.
- Separable algebraic: `[Algebra.IsSeparable K L]`. Exact: the recorded class requires
  every minimal polynomial to be separable, and its isAlgebraic instance supplies
  algebraicity. An extra algebraicity hypothesis would be redundant.
- There exists a nonzero element c of A: `∃ c : A, c ≠ 0 ∧ ...`. Exact.
- The principal localization A[c^{-1}]: `∃ S : Subalgebra A L,
  IsLocalization.Away c S ∧ ...`. Exact model with the specified A-action. Reading
  Subalgebra and Away confirms that the first contains the image of A and the second
  is the localization universal property at powers of c. The domain/fraction-field
  injection and c != 0 let this localization embed in L. Every abstract such
  localization is isomorphic to this image as an A-algebra, so no model is excluded.
- Object A', an algebra over that localization: `∃ B : Subalgebra S L, ...`.
  Exact image presentation inside the prescribed fraction field. The induced S -> B
  and B -> L are inclusions. An abstract domain with that compatible fraction field
  embeds in L and can be replaced by its image, preserving every requested property.
  This uses existing Mathlib Subalgebra, not a private definition.
- Finite as an S-algebra: `Module.Finite S B`. Exact finite-module condition.
- Etale as an S-algebra: `Algebra.Etale S B`. Exact existing algebra notion;
  Mathlib uses finite presentation and formal etaleness, equivalent to the source.
- A' is a domain: `IsDomain B`. Exact explicit clause; also inherited by a subring
  of the field L. It is a conclusion, not an extra hypothesis.
- Its fraction field is the given K': `IsFractionRing B L`. Exact, along the induced
  embedding; no unrelated field isomorphism is substituted for the prescribed maps.
- Spec(A') -> Spec(A[c^{-1}]) is finite:
  `IsFinite (Spec.map (CommRingCat.ofHom (algebraMap S B)))`. Exact.
- That same map is etale:
  `Etale (Spec.map (CommRingCat.ofHom (algebraMap S B)))`. Exact use of the etale
  dependency's affine-local definition; I read its Etale signature and docstring.
- That same map is surjective:
  `Surjective (Spec.map (CommRingCat.ofHom (algebraMap S B)))`. Exact underlying-point
  surjectivity, as the Mathlib class says. All three clauses use the same algebraMap.

Quantifier order is A, K, the extension L with its hypotheses, then c, its localization S,
and finally B with all the listed properties. No finiteness, characteristic, normality,
proper-extension or geometric connectedness condition has been added.

Edge cases: the degree-one extension is allowed (choose a linear polynomial); the case
where A is already a field admits c = 1. Finite fields, imperfect fields and all positive
characteristics are included, provided the stipulated extension is separable. Characteristic
zero is included. Zero rings are excluded by IsDomain and zero fields by Field, exactly
as in the node; no degree-zero field extension or empty spectrum is possible here.
There is no index set, zero sheaf or integer n in this statement. Universes u, v, w are
independent and explicitly declared; subtypes S and B live in w, so their scheme map is
well-typed in one universe without restricting A or K. Field embeddings already give
any size relation needed to represent the rings inside L. No test-object universe
quantifier or hidden unbound variable occurs.

Independent searches, using wording different from the first worker:

- LeanFinder: `An integral model of a finite separable fraction field extension is
  finite etale after inverting a nonzero base element`: eight hits, including localization
  etaleness, Algebra.exists_etale_of_isEtaleAt and Algebra.Etale.exists_subalgebra_fg.
  I opened the latter's actual signature: it descends an already etale algebra to
  finitely generated subalgebras, without the principal-localization, prescribed
  fraction field, finite-domain and spectrum-surjectivity conclusions here.
- Loogle: `IsLocalization.Away, Algebra.Etale`: one localization-etaleness lemma,
  not this statement about extending the fraction field.
- Logged Mathlib grep: `fraction.*[ée]tale|[ée]tale.*fraction|separable.*localiz|
  localiz.*separable` in RingTheory: six hits concerning integral closure, Dedekind
  localization and a Galois-group comment; no spreading theorem.
- LeanSearch: `finite separable fraction field extension has a finite etale model
  after principal localization`: attempted and logged; service returned Internal Server
  Error, so no absence verdict is inferred from that service.
- Direct rg of source WeilConjectures and project lean/Sheaf with `integral model`,
  separable/spread in both orders, and finite-etale/fraction wording found unrelated
  integral models and GenericFiniteAlgebraSplitting, which uses this lemma in its
  proof docstring and does not state it. I opened that module. Direct name searches
  of Mathlib, source, project and dag/lean_names_upstream.json found no collision.

No new definition nodes or dependency modules were delivered; all needed notions are
existing Mathlib notions and each recorded dependency is usable. No hollow definition,
private notion, local notation or proved helper appears. Both docstrings name the source
and blueprint id. The theorem docstring carries all three proof steps and all four proof
dependencies, including the injective-integral lying-over argument. The sole theorem
has proof `by sorry`, as stage 2 requires. All imports support notions in the statement,
lines are within 100 characters, namespace and module placement follow conventions.

Verdict: no Lean/node signature mismatch found. I left the correct module and lean record
unchanged and appended this source-verified second reading, including the inherited tag
note. The node's lean.statement is verbatim the file's signature up to `:=`.
Server scompile.py compilation succeeded (exit 0, 2.4 seconds, no warnings or errors).
