## Worker report

The module `Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent`
states `AlgebraicGeometry.Scheme.finiteEtaleFieldLimitDescent`, with `sorry`, as the
conjunction of the node's three clauses. The source is Stacks Project,
`literature/stacks-project/pione.tex`, label `lemma-limit`, Tag 0BTV, and its
explicit references to Limits 01ZM, 01ZO and 07RP. I read that source and the
node's nine proof steps. No statement correction, dependency repair or new node
is needed. Only the node's `lean` field changes.

Hypotheses and objects:

- `K L : Type u`, `[Field K] [Field L] [Algebra K L]` express the field extension,
  using the recorded `Algebra` declaration (Mathlib.Algebra.Algebra.Defs).
- `[Algebra.IsSeparable K L]` is exactly the recorded separable algebraic extension
  (Mathlib.FieldTheory.Separable). Its definition says every element has separable
  minimal polynomial and already implies algebraicity; no extra algebraicity
  assumption is needed.
- `X₀ : Over (Spec (.of K))` is the K-scheme with its structural map. The three
  instances `[IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom]
  [QuasiCompact X₀.hom]` give precisely separated and finite type, following the
  convention node. They impose neither geometric connectedness nor nonemptiness.
- `E : IntermediateField K L` with `FiniteDimensional K E` is precisely a finite
  intermediate field. `E ≤ E'` is containment, with equality permitted.
- Every `X_E` is written as the existing `pullback X₀.hom
  (Spec.map (CommRingCat.ofHom (algebraMap K E)))`. Replacing E by L gives X_L.
  This uses the recorded fibre product, `CategoryTheory.Limits.pullback`, and
  its projections, in Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback.
- Covers and morphisms use the existing `Scheme.FiniteEtale` category. Its objects
  are the full subcategory of `X.Etale` having finite structural map, and its
  morphisms are all X-morphisms. This is the finite-cover clause of the recorded
  dependency `def-galois-categories`, whose module
  WeilConjectures.AlgebraicGeometry.GaloisCategories is imported. The category is
  originally defined in WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale.
  No geometric point is required for this clause of that dependency.

Conclusions, clause by clause:

1. The first conjunct quantifies over every `P : X_L.FiniteEtale` and gives
   `∃ (E) (_ : FiniteDimensional K E) (P_E : X_E.FiniteEtale), Nonempty (...)`.
   The isomorphism is in `X_L.FiniteEtale`, between the existing finite-etale
   pullback functor's value on P_E and P. Thus it is exactly an isomorphism over
   X_L, and its source is P_E times X_L over X_E.
2. The second conjunct quantifies over every finite E, every pair of covers,
   and every `f` between their X_L base changes. It produces finite E', `h : E ≤ E'`,
   and a morphism `f'` between their X_E' base changes, with
   `finiteEtaleFieldRefinementMap X₀ h P_E ≫ f'.hom.left =
   f.hom.left ≫ finiteEtaleFieldRefinementMap X₀ h Q_E`.
   The refinement maps have components projection to the original cover and
   projection to X_L followed by X_L → X_E'. Hence this is exactly the base-change
   equality in (2): a map into Q_E' is determined by its cover and X_E' projections;
   the X_L projection is already fixed because f is an X_L-morphism. Equivalently,
   this is conjugation by the unique associativity identifications preserving both
   projections. It does not quantify over arbitrary comparison isomorphisms.
3. The third conjunct takes every pair `f_E h_E : P_E ⟶ Q_E` with equal images
   under `FiniteEtale.pullback (fieldBaseChangeMap X₀ E.val)` and produces finite
   E' containing E at which the two images under pullback along the inclusion
   agree. These are equalities in the actual finite-etale category, not merely
   isomorphism classes or equal maps on geometric points.

The two helpers belong to the canonical arrows needed by this statement, under
the brief's authorization for helpers in the owning module. `fieldBaseChangeMap`
is exactly `pullback.map` with components id and Spec of the given algebra
homomorphism. `finiteEtaleFieldRefinementMap` is again `pullback.map` with identity
on P_E and the canonical map X_L → X_E'. Both have complete data; their commuting
conditions are verified directly by Spec functoriality and the pullback
projection identities. They add no alternative notion of covers, fields or
base change, and are all recorded in `lean.declarations`. No additional theorem
is postponed for their construction. The only postponed theorem is the main
statement, with all nine natural-language proof steps in its docstring.

The existing functor is
`AlgebraicGeometry.Scheme.FiniteEtale.pullback` from
WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality; I read its object
and map definitions. Proof-only imports include the recorded spreading-out module
WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit (object, morphism,
equality clauses), Sheaf.AlgebraicGeometry.DescendFinite, and
WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent, plus the Mathlib modules
recorded for the permanence, qcqs and Spec-limit proof dependencies. The two proof
nodes without a recorded declaration, `lem-kun-algebraic-separable-smooth` and
`lem-trf-finite-morphism-finite-presentation`, have no import yet; the proof
instructions still name them. No statement depends on their unstated interfaces.

Edge cases checked: X₀ or either cover may be empty. Finite étale is not required
to be surjective, connected, Galois or equipped with an action. Every characteristic
is allowed. E may equal the bottom field, E' may equal E, and L/K may be trivial
or finite. For infinite L/K the finite stages remain actual intermediate fields,
with no finiteness condition on L/K. A zero field is excluded by Field, exactly as
in the source. All fields and schemes have the same arbitrary universe u; the
intermediate fields have underlying types in u, and no unrelated index universe
or size assumption is introduced. There are no auto-bound variables, lets,
file-local notation, or private definitions in the signatures.

Searches, all actually run:

- msearch.py leanfinder: "Finite etale covers and morphisms over a separable
  algebraic field extension descend to finite intermediate fields". Eight hits,
  including Algebra.FormallyEtale.of_isSeparable_aux,
  Algebra.Etale.iff_exists_algEquiv_prod, and IntermediateField.Lifts results;
  none gives descent of covers over a general separated finite-type scheme with
  both morphism descent and eventual equality.
- msearch.py loogle: `AlgebraicGeometry.Scheme.FiniteEtale`. Zero hits; the service
  does not know this project's declaration.
- msearch.py grep: `finite.?[Ee]tale.*([Ll]imit|[Dd]escen)|([Ll]imit|[Dd]escen).*finite.?[Ee]tale`
  in Mathlib/AlgebraicGeometry. Zero hits.
- msearch.py leansearch: "Finite etale schemes and their morphisms descend to
  finite intermediate fields in a separable algebraic extension". Eight hits,
  including Scheme.Etale, IsFinite, Algebra.Etale.exists_subalgebra_fg and
  finiteExts. None states the three clauses for finite étale covers of X_E.
- rg in the source WeilConjectures and the project's lean/Sheaf for finite-etale
  limit/descent, canonical field-base-change names, and the item's id. Relevant
  existing declarations are the finite-etale category and pullback functor above;
  general spreading-out theorems are proof tools, not the statement itself.
  Existing finite-etale henselian/stalk descent and the private limit-stage
  helpers do not give this whole statement. The downstream Weil-transport module
  cites this item in its proof docstring, but does not state it. Source search by
  the exact id found no upstream binding. `dag/lean_names_upstream.json` and source
  searches show no clash for any of the three introduced names.

Validation: scompile.py compiled the complete module in both sandbox and library
positions with no errors or warnings. The first helper-only experiment exposed a
missing reassociated pullback projection simplification in the second helper;
adding `pullback.lift_snd_assoc` repaired it. The required delivery dry run follows.

## Second reading by Q75

This is the author's self-check; the maintainer provides the independent review.
With the node and final file open, I checked all three conjuncts against all three
numbered clauses. The first is an actual over-base isomorphism. The second ranges
over arbitrary morphisms and uses the canonical projections, whose construction
was checked for the correct source P_L and target P_E'. Its equation is equivalent
to the requested pulled-back morphism equality by the fibre-product universal
property. The third is eventual equality of the two maps, with finite dimension
required at the original and refined fields. The Field, Algebra, separability,
separatedness, local finite type and quasi-compactness hypotheses match the node
exactly. The maps use E.val and IntermediateField.inclusion h, so the embeddings
and containment are fixed rather than existentially substituted. No extra
connectedness, geometric point, nonemptiness, surjectivity or group structure is
present. I also checked the helper docstrings and all nine proof steps. No
mathematical mismatch or disputed statement was found, and no node correction
was made.
