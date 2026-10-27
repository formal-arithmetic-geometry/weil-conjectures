## Worker report

The module `Sheaf.AlgebraicGeometry.QCSeparatedQuasicoherentComplexModel` states
`AlgebraicGeometry.exists_quasicoherent_complex_of_compactSpace_of_isSeparated`.
Its only proof is `sorry`. No definitions, additional nodes, dependency repairs, or
statement corrections were needed. The node statement and dependency lists are unchanged.

Clause-by-clause reading:

- A scheme X is the binder `(X : Scheme.{u})`.
- Quasi-compactness is `[CompactSpace X]`, the recorded topological finite-subcover
  property, with no Hausdorff condition.
- Absolute separatedness is `[X.IsSeparated]`. Mathlib's class is separatedness of
  `terminal.from X`; the terminal scheme is Spec Z, and `IsSeparated` is precisely
  the closed-immersion diagonal condition. This imposes neither properness nor
  finite type nor a field base.
- The shared `[HasDerivedCategory.{w} (SheafOfModules.{u}
  (moduleRings X.toRingedSpace))]` chooses the localization and its morphism universe.
  It is the exact interface of the recorded derived-category definition, not a
  mathematical restriction or a new abelian instance.
- Every K in D_QCoh(O_X) is rendered as `(K : schemeDerivedCategory X)` together
  with `(hK : schemeDerivedQCohProperty X K)`. The recorded predicate requires
  quasi-coherence of every cohomology sheaf in integer degree. A full-subcategory
  object is equivalently this ambient object and its membership proof.
- The existential F is a `CochainComplex (SheafOfModules.{u}
  (moduleRings X.toRingedSpace)) ℤ`. Its built-in differentials square to zero;
  neither a bounded category nor a one-sided complex is used.
- Every term is quasi-coherent: `(∀ i : ℤ, (F.X i).IsQuasicoherent)`.
- The required isomorphism in D(O_X) is
  `Nonempty (DerivedCategory.Q.obj F ≅ K)`, using the recorded localization Q.
- There are no boundedness binders on K or F, and the isomorphism is in the
  derived category itself, not merely a family of cohomology isomorphisms.

Recorded statement dependencies used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, exposing
  `AlgebraicGeometry.IsSeparated` and `AlgebraicGeometry.Scheme.IsSeparated`.
  Only separatedness is required, not the node's other properness notions.
- `def-pc-derived-category`: `WeilConjectures.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedCategory` and `schemeDerivedQCohProperty`.
  Read their complete definitions; they use the shared SheafOfModules carrier
  and Mathlib's Abelian instance, avoiding a second category on X.Modules.
- `def-pc-cochain-complex-modules`:
  `Mathlib.Algebra.Homology.HomologicalComplex`, `CochainComplex`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, exposing
  `SheafOfModules.IsQuasicoherent`. The conjunction
  `Scheme.Modules.IsQuasiCoherentFiniteType` would add an unwanted finite-type
  condition, so it is not used.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.

All these modules are public imports. Every currently recorded module of the
proof dependencies is imported without `public` (unless already a statement
import), including the Mathlib modules given by mathlib_match. The only omitted
proof import is `lem-sfb-affine-open-derived-qcoh-criterion`: the node currently
has neither a Lean record nor a Mathlib match. It is not needed to type the
statement; its role is explicitly preserved in step 5 of the proof docstring.
No unstated proof dependency was guessed or replaced by a weaker theorem.

The docstring records all five proof steps of the node: the abelian QCoh
subcategory and exact inclusion; separatedness and affine open inclusions;
exact affine pushforward and its termwise derived functor; the functorial
unbounded K-injective comparison and its unit normalization; and the affine-open
criterion followed by essential surjectivity and a complex representative.

Source reading: opened `literature/stacks-project/perfect.tex` at
`proposition-quasi-compact-affine-diagonal` (08DB), its complete statement and
proof, and `lemma-nonzero-some-cohomology` (0BQR), in particular the first
paragraph that explicitly applies the proposition on a quasi-compact separated
scheme to obtain a complex of quasi-coherent modules. Closed immersions are
affine, so separated schemes satisfy 08DB's affine-diagonal hypothesis.

Edge cases checked before writing:

- Empty X is allowed: no nonemptiness, point, or nonzero object is required;
  the zero complex gives the expected model in the trivial module category.
- K = 0 is allowed; no nonzero-cohomology hypothesis from the later 0BQR use
  was imported into this independent representative theorem.
- Affine X is included, with the standard affine derived equivalence giving
  the expected special case.
- Arbitrarily unbounded complexes are retained, including cohomology in
  infinitely many positive and negative degrees.
- Non-Noetherian quasi-compact separated schemes, including affine schemes
  over arbitrary commutative rings, are not excluded.
- Nonseparated schemes such as the doubled-origin affine line do not satisfy
  the separatedness binder; quasi-separatedness alone was not substituted.
- Scheme/module universe u and localization morphism universe w remain
  explicit and independent, exactly as in the shared dependency interface.

Searches made (2026-10-24):

- `msearch.py ... leanfinder "Every unbounded derived object with quasi coherent
  cohomology on a quasi compact separated scheme is represented by a complex of
  quasi coherent module sheaves"`: eight hits, chiefly
  `DerivedCategory.exists_iso_Q_obj_of_isGE`, `_of_isLE`, `_of_isGE_of_isLE`,
  homology-bound instances, and local quasicoherent presentation data. None
  gives the unbounded geometric assertion about quasi-coherent terms.
- `msearch.py ... loogle '"Quasicoherent", "equivalence"'`: zero hits.
- `msearch.py ... leansearch "On a quasi compact separated scheme every object
  with quasi coherent cohomology in the unbounded derived category is represented
  by a complex of quasi coherent sheaves"`: eight hits, including bounded
  representatives, localization instances, and `SheafOfModules.isQuasicoherent`
  and presentation constructors. None is this statement.
- `msearch.py ... grep 'quasi.?coherent.*derived|derived.*quasi.?coherent|coherator'`:
  zero Mathlib hits.
- `rg -n -i 'quasi.?coherent.*derived|derived.*quasi.?coherent|quasicoherent.*model|qcSeparated'`
  in `lean/WeilConjectures` and `lean/Sheaf`: related affine equivalences,
  derived pullback/pushforward and Cech comparisons. Read the affine-only
  private `affine_qcoh_representative` in
  `WeilConjectures.AlgebraicGeometry.KoszulOpenHomRestrictionSurjective`:
  its scheme is explicitly Spec A, so it does not state the present theorem.
- The narrower termwise-quasicoherence signature search found affine
  resolution/comparison statements, not the general separated theorem.
- `grep -rn 'lem-sfb-qc-separated-quasicoherent-complex-model'
  lean/WeilConjectures`: zero hits.
- Searched the proposed declaration name in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q130

The dispatcher requires a single worker and explicitly forbids starting other
agents. This section records a separate rereading by the same worker; it does
not claim an independent reviewer. The maintainer's independent review remains
part of delivery.

Reopened the node statement and the complete module. `Scheme.{u}` matches X;
`CompactSpace X` matches quasi-compactness; `X.IsSeparated` matches the absolute
closed-immersion diagonal; K and hK match precisely membership in the shared
D_QCoh full subcategory. The existential is an integer-indexed complex in the
same module category, its first conjunct applies quasi-coherence to every
term, and its second conjunct gives Q(F) isomorphic to that very K in the
same derived category. There is no finite-type, Noetherian, field,
nonemptiness, cohomological bound, or term bound. The explicit universe binder
uses the published shared interface. All seven statement dependencies are
publicly imported, and the source and five proof steps are in the theorem's
docstring. No mismatch was found and no statement was changed during rereading.
