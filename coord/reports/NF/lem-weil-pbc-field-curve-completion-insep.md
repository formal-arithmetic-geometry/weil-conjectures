## Worker report

The module `Sheaf.AlgebraicGeometry.FieldCurveCompletionInsep` states
`AlgebraicGeometry.exists_field_curve_completion_insep`, with its sole proof `sorry`.
Source read: Stacks Project, `varieties.tex`, label
`lemma-dim-1-projective-completion-after-insep` (Tag 0GK5), its five assertions and full proof.
The statement has not been corrected or disputed. No new notion or node is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Field k: `(k : Type u) [Field k]`.
- Separated finite type k-scheme X: `(X : Scheme.{u})`,
  `[X.Over (Spec (.of k))]`, `[IsSeparated (X ↘ Spec (.of k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]`, and
  `[QuasiCompact (X ↘ Spec (.of k))]`. Finite type means the last two properties.
- Dimension at most one: `hdim : topologicalKrullDim X ≤ 1`.
- Finite purely inseparable extension: existential `K`, `Field K`, `Algebra k K`,
  with `Module.Finite k K ∧ IsPurelyInseparable k K`.
- Finite index set: `Fin n`, for existential `n : ℕ`. Every finite set can be so indexed.
- Base change: the literal `pullback (X ↘ Spec (.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))`; its K-structure is `pullback.snd`.
- Reduced irreducible components and their normalizations: `C : Fin n → Scheme`,
  `hC : ∀ i, IsIntegral (C i)`, and closed immersions `c i` into X_K;
  their ranges belong to `irreducibleComponents X_K`, are pairwise distinct
  (`Function.Injective`), and exhaust all components. Integral means reduced and
  irreducible, so a closed immersion with this support is exactly the reduced induced
  component scheme, not a choice of an arbitrary thickening. Components of X_K and
  of its reduction have identical supports and identical reduced induced schemes:
  on an affine chart their rings are A/p, equivalently (A/√0)/(p/√0).
  Thus this is exactly the componentwise formulation in the node, without constructing
  another normalization or requiring X_K itself to be integral or reduced.
  `e i : Y i ≅ @Scheme.normalization (C i) (hC i)` uses the recorded definition.
- Coproduct normalization map: `ν : (∐ Y) ⟶ X_K` and
  `ν = Sigma.desc (fun i ↦ (e i).hom ≫ @Scheme.fromNormalization (C i) (hC i) ≫ c i)`.
  This specifies the map, not just a normal source or a surjectivity predicate.
- Finite separable fields: `L : Fin n → Type u`, the existential field and K-algebra
  structures, and `Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i)` for every i.
- Completions and open inclusions: `B`, `j i : Y i ⟶ B i`, and
  `q i : B i ⟶ Spec (.of (L i))` are precisely the displayed objects and maps.
  `IsOpenImmersion (j i) ∧ DenseRange (j i) ∧ Nonempty (Y i)` says dense nonempty image.
- Smooth projective geometrically irreducible dimension at most one over L i:
  `Smooth (q i) ∧ IsHProjective (q i) ∧ GeometricallyIrreducible (q i) ∧
  topologicalKrullDim (B i) ≤ 1`.
- Diagram over K: `p i : Y i ⟶ Spec (.of K)` is equated both to the normalized
  component map followed by `pullback.snd`, and to `j i ≫ q i ≫ Spec.map (algebraMap K (L i))`.
  Together with the equation for ν, this makes the coproduct diagram commute.
- All displayed schemes are finitely presented over K: each relevant structure map
  has the three conjuncts `LocallyOfFinitePresentation`, `QuasiCompact`, and
  `QuasiSeparated`, exactly the convention in def-weil-pbc-scheme-conventions.
  These are stated for Y i via p i, B i via q i followed by the field spectrum map,
  Spec (L i) via that spectrum map, ∐ Y via `Sigma.desc p`, and X_K via `pullback.snd`.
  Spec K has its identity structure map. No finiteness condition is imposed on the
  auxiliary component enumeration beyond what is inherent in reduced components.
- Empty index precisely for empty X: `n = 0 ↔ IsEmpty X`.

Dependency declarations read and used:

- Mathlib: `Field` (Algebra.Field.Defs), `Scheme`/`Scheme.Hom`
  (AlgebraicGeometry.Scheme), `topologicalKrullDim` (Topology.KrullDimension),
  `IsPurelyInseparable` and `Module.Finite` (FieldTheory.PurelyInseparable.Basic
  and RingTheory.Finiteness.Defs), `Algebra.IsSeparable` (FieldTheory.Separable),
  `pullback`/`pullback.snd` (CategoryTheory.Limits.Shapes.Pullback.HasPullback),
  `irreducibleComponents` (Topology.Irreducible), `IsOpenImmersion`
  (AlgebraicGeometry.OpenImmersion), `Smooth` (AlgebraicGeometry.Morphisms.Smooth),
  and `GeometricallyIrreducible` (AlgebraicGeometry.Geometrically.Irreducible).
- Reduction was read in Mathlib.AlgebraicGeometry.IdealSheaf.Basic and Subscheme:
  `Scheme.nilradical`, `IdealSheafData.subscheme`, `IdealSheafData.subschemeι`.
  Its module is imported; the equivalent reduced-component presentation above needs
  no newly named reduction construction.
- Coproducts use Mathlib.AlgebraicGeometry.Limits, `∐ Y`, `Sigma.desc`, and its
  existing coproduct instance. No new coproduct lemma is stated.
- `Scheme.normalization` and `Scheme.fromNormalization` from
  WeilConjectures.Mathlib.AlgebraicGeometry.Normalization, source lines 179–190,
  with explicit integral-instance arguments `hC i`.
- `IsHProjective` from WeilConjectures.AlgebraicGeometry.Morphisms.Projective;
  see the dependency-record repair below.
- Scheme conventions are a convention-only record: separatedness, finite type,
  finite presentation and quasi-separatedness are the recorded Mathlib predicates.

The stated proof dependencies are imported, with non-public imports:
HomeomorphPurelyInseparableBaseChange (`isHomeomorph_baseChange_of_isPurelyInseparable`),
Morphisms.ProjectiveBaseChange (`projective_base_change`),
GlobalSectionsProperVariety (`globalSections_finite_field_of_isVariety`),
ProperGeometricallyReducedGlobalSectionsSeparable
(`proper_geometricallyReduced_globalSections_isSeparable`),
SteinFactorizationAffine (`Scheme.Hom.steinFactorization_affine`), and
EtaleCoproductOfFiniteSeparableFields (`etale_sigmaDesc_spec_of_finite_separable`).
Their signatures and docstrings were read. Mathlib.Noetherian, Morphisms.Etale, and
Morphisms.FlatMono are imported for the Mathlib proof-dependency leaves. The remaining
proof dependencies have no recorded Lean declarations and are described in the seven
numbered proof steps in the declaration docstring.

Edge cases checked: X empty permits n=0 and K=k, with empty component and field families;
zero-dimensional components are allowed (dimension is ≤1, never =1), including purely
inseparable residue fields that become nonreduced after extension. Reduction precedes
normalization componentwise, so these nilpotents cause no incorrect integral assumption
on X_K. In characteristic zero the trivial purely inseparable extension is allowed.
Reducible and nonreduced X are included. Fields, schemes and existential extension fields
share universe u; finite field extensions and finite families have models there, and no
quantification over test fields in an independent smaller universe is introduced.
All variables and universe u are bound explicitly; no let, local notation, local
instance, private definition, or proof beyond sorry occurs.

Searches actually run:

- msearch leanfinder: “Separated finite type curve over a field has smooth projective
  normalization components after finite purely inseparable extension”. Eight unrelated
  Earlier search returned Weierstrass minimal-model/reduction hits. The current rerun
  returned eight relative-normalization declarations; no matching statement.
- msearch loogle: `IsPurelyInseparable, AlgebraicGeometry.Smooth`.
  Current rerun: zero hits. The earlier normalization-name query reported an unknown identifier.
- msearch grep: `normalization|projective.*completion`, AlgebraicGeometry.
  Hits in relative normalization and Zariski's main theorem, no matching completion result.
- msearch leansearch: “Finite purely inseparable extension gives smooth projective
  completions of normalization components of a curve”. Service unavailable (HTTP 500);
  recorded as unavailable, not as no match.
- rg in upstream WeilConjectures, side lean/Sheaf and dag/lean_names_upstream.json:
  `completion.insep|completion_after_insep|projective_completion|0GK5|` followed by the
  item's exact id; no matching theorem. A separate search for the proposed full name,
  `field_curve_completion`, and `0GK5` also gave no hits.
- rg for normalization and irreducible components found the existing integral
  normalization API and ReducedCurveNormalization's finite component enumeration.
  The latter produces a modification over an algebraically closed field, not this
  inseparable-extension/projective-completion statement, so it was not duplicated.

Validation: scompile.py compiled the delivered module cleanly on the server, nice 19,
two threads, 60 seconds per file; actual compile 2.0 seconds, no errors or warnings.
The delivery dry run is the final check below.

## Dependency modules

`def-kun-projective`: no new module is written. Its old record pointed to the side module
Sheaf.AlgebraicGeometry.Morphisms.Projective, which defines the same names now provided by
the live upstream library. Importing it together with the required published proof modules
failed with duplicate `AlgebraicGeometry.IsHProjective.mk`, attributed by Lean to upstream
WeilConjectures.AlgebraicGeometry.Morphisms.Projective. The latter source was read directly
on the server (the pinned local upstream checkout does not contain that newer module).
Its full declaration and docstring specify a closed immersion into projective space on
some finite coordinate type. This is equivalent to the node's Fin (N+1) convention:
nonempty finite coordinate types can be reindexed; zero coordinates force an empty source,
which also embeds into P^0. The dependency copy changes only `lean`, with `existing: true`
and a note explaining this repair. Its statement and other fields are unchanged. The
item uses this existing declaration rather than writing another projectivity predicate.

## Validation

The current worker reread Stacks 0GK5, the normalization and projectivity sources,
the dependency records, and the full statement, including its reduced-component
encoding and empty case. No mathematical statement changes were needed. The published
upstream projectivity source was obtained with `scompile.py --source`; the permitted
lean-only dependency repair is retained. The old preflight/source-lookup failures
are resolved by the current tooling.

The required server compile and `deliver2.py NF
lem-weil-pbc-field-curve-completion-insep --no-push` now pass, except for the independent
second reading explicitly reserved for the next worker. The dry run prints OK; no
delivery was pushed. No local compilation, tool modification, or upstream edit was made.

## Second reading by NF

Independent second reader: read the sandbox node, full Lean module, and Stacks
`varieties.tex:9303`, Tag 0GK5, including the entire proof and preceding completion
argument. The ambient k is a field; no perfectness, algebraic closedness,
integrality, or positive-dimensionality is assumed. I independently matched the
following object/hypothesis/conclusion list against the signature:

1. Field k and a k-scheme X: `(k : Type u) [Field k] (X : Scheme.{u})`
   and `[X.Over (Spec (.of k))]`. Exact.
2. X separated and finite type: `IsSeparated`, `LocallyOfFiniteType`, and
   `QuasiCompact` on its specified structure morphism. Exact; the latter two
   together express finite type, without a new Noetherian hypothesis.
3. Dimension at most one: `hdim : topologicalKrullDim X ≤ 1`. Exact, with
   Mathlib's bottom dimension for the empty space, rather than dimension = 1.
4. A finite purely inseparable extension k'/k: existential `K`, `Field K`,
   `Algebra k K`, `Module.Finite k K ∧ IsPurelyInseparable k K`. Exact.
5. A finite set I: existential `n : ℕ` and `Fin n`. Exact up to reindexing,
   including the empty finite set; this introduces no ordering requirement.
6. The scalar extension X_K: the literal scheme pullback of the given structure
   map along `Spec.map (CommRingCat.ofHom (algebraMap k K))`, with `pullback.snd`
   as K-structure. Exact; no arbitrary replacement base-change morphism.
7. The reduced irreducible components: `C`, integral structures `hC`, and closed
   immersions `c` whose ranges are components, are injectively indexed, and
   exhaust `irreducibleComponents X_K`. Exact. On each affine chart a reduced
   closed subscheme is cut out by a radical ideal, uniquely determined by its
   closed support. An irreducible component therefore gives precisely A/p;
   reduction first gives the identical quotient (A/sqrt(0))/(p/sqrt(0)). Thus
   these are exactly the node's reduced components of (X_K)_red, without an
   additional reducedness assumption on X_K and without a private definition.
8. Their normalized schemes and canonical map: `e i : Y i ≅
   @Scheme.normalization (C i) (hC i)` and the equation expressing `ν` as
   `Sigma.desc` of `e.hom ≫ Scheme.fromNormalization ≫ c`. Exact, including
   scheme structure and the morphism, rather than merely normal sources.
9. Finite separable fields k_i/K: `L`, its existential field and K-algebra
   structures, and `Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i)`.
   Exact; there is no forced identification between different constant fields.
10. Completion objects and maps: `B`, `j`, `q`, and `p`; `IsOpenImmersion (j i)`,
    `DenseRange (j i)`, `Nonempty (Y i)`. Exact dense nonempty open inclusions.
11. Smooth, projective, geometrically irreducible completions over k_i:
    `Smooth (q i) ∧ IsHProjective (q i) ∧ GeometricallyIrreducible (q i)`
    with `topologicalKrullDim (B i) ≤ 1`. Exact. These properties are on q,
    not merely on the composite to Spec K.
12. Diagram over K: the component normalization composite to `pullback.snd`
    equals `p i`, and `j i ≫ q i ≫ Spec.map (algebraMap K (L i)) = p i`.
    Along with the equation for ν, these give the required coproduct diagram.
    The arrows to X and Spec k are canonical pullback/field structure arrows.
13. All displayed schemes finitely presented over K: the LFP/QC/QS triples
    occur on `p i`, the B-to-K composite, the L_i-to-K spectrum map,
    `Sigma.desc p`, and `pullback.snd`. Exact. Finite coproducts of the B_i
    and Spec L_i inherit this, as does the identity on Spec K. The auxiliary
    C_i enumerate components and are not extra objects of the node's diagram.
14. Empty index exactly for empty X: `(n = 0 ↔ IsEmpty X)`. Exact.

Dependency audit: opened every statement-dependency node and its record. Read
`Scheme.normalization` and `fromNormalization` at upstream Normalization.lean
179–190: they require integral schemes and use the function field, precisely
as supplied by hC. Read Mathlib's signatures/definitions for Scheme, the
morphism properties above, irreducibleComponents, topologicalKrullDim,
IsPurelyInseparable, Algebra.IsSeparable, the ideal-sheaf subscheme, open
immersions, and scheme coproducts (Limits.lean 175–250). Their scopes fit these
objects. The convention-only node supplies no additional predicate to import.
Read the six recorded proof modules and their signatures; the declaration's
seven proof steps preserve the node's reduction, projective completion,
geometric normalization, constant-field/Stein argument, base refinement,
restriction, and finite-presentation route.

The only dependency repair is `def-kun-projective`, with no new module or node.
Fetched the actual published source with `scompile.py --source
WeilConjectures.AlgebraicGeometry.Morphisms.Projective` and read its full
IsHProjective declaration: a finite coordinate type and a closed immersion
whose composite with the structural projection is f. This is the node's
finite projective-space embedding convention. A nonempty finite coordinate
set is reindexed by Fin (N+1); the empty coordinate case has empty projective
space, so only an empty source, which embeds into P^0 as well. The worker's
lean-only existing-record repair is sound and avoids duplicate declarations.
There are no new definition nodes or sibling modules to audit.

Edge cases: X empty allows n=0; all component families and their conditions
are then empty. Nonempty zero-dimensional X is retained, even with inseparable
residue fields or nilpotents. Reducible/nonreduced X is allowed. Characteristic
zero allows the trivial purely inseparable extension; characteristic p is
unrestricted. Every finite field extension and finite family has a model in
u; the signature is polymorphic in u and imposes no equality between independent
site universes or quantification over a smaller test-field universe. All
variables are explicitly bound. No extra instance on X or arbitrary map
replaces a canonical construction.

Independent searches, using different wording from the worker:
- LeanFinder through msearch: “A curve over an imperfect field admits regular
  projective compactifications of its normalized irreducible components after
  a radicial field extension”. Eight Weierstrass-curve results, no match.
- Loogle through msearch: `IsPurelyInseparable, GeometricallyIrreducible`.
  No hits; the service did not recognize the latter unqualified name, so this
  is not claimed as evidence of nonexistence by itself.
- rg in Mathlib AlgebraicGeometry, upstream WeilConjectures AlgebraicGeometry,
  and the project's lean/Sheaf/AlgebraicGeometry, with `compactification`,
  `compactif`, `completion`, `0GK5`, and `field_curve_completion_insep`.
  Opened upstream Curve/Compactification.lean's closest candidate,
  `exists_smooth_properCompactification_of_perfectField`: it assumes a perfect
  field, smooth relative dimension one and geometric connectedness, and gives
  a proper compactification, not this inseparable-extension/componentwise
  theorem. The side ReducedCurveNormalization uses the existing normalization
  API but is over an algebraically closed field and gives a modification,
  not the present conclusion. No exact existing statement found.

Verdict: no mathematical mismatch found; no Lean signature, docstring, or node
repair was necessary in this second reading. The worker's correct statement
and projectivity-record repair are retained. Nothing is proved: the delivered
module has exactly one named theorem with proof `sorry`, its source/blueprint
and complete proof route in the docstring, and no definition with missing data.
Checked programmatically that lean.statement is verbatim the theorem signature;
checked by eye the explicit universe/binders and absence of file-local notation,
instances, hidden let/show binders, or private notions.

Validation by this reader: scompile.py on the absolute sandbox module path
compiled cleanly on the server in 1.9 seconds, nice 19, two threads, 60 seconds
limit. An initial invocation with a relative path from the read-only checkout
could not locate the sandbox file; using the absolute sandbox path resolved
that invocation error without any tool or source modification.
