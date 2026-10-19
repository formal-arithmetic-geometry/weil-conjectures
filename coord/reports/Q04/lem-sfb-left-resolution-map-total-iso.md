## Worker report

This is an existing-declaration delivery for `lem-sfb-left-resolution-map-total-iso`.
The declarations are in
`WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap` on `slopmaster2`.
The current published source was also read using `scompile.py --source`; it agrees
with the source checkout. No module is written, no notion is redefined, and the
node changes only in `lean`. The primary declaration is
`HomologicalComplex₂.mapTotalIso`. Its supporting declarations recorded in
`lean.declarations` are `HomologicalComplex₂.mapTotalXIso`,
`HomologicalComplex₂.ι_mapTotalXIso_hom`,
`HomologicalComplex₂.mapTotalIso_hom_naturality`, and
`HomologicalComplex₂.mapTotalIso_inv_naturality`.

The node's own source is this exact source module, lines 27–145. Its blueprint
ancestor is `lem-sfb-derived-monoidal`, whose current proof in
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md` uses preservation
of the coproducts involved in K-flat resolutions. The source module already
provides all the requested canonical comparison data and equalities.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Preadditive categories C and D: the source variables `{C D : Type*}`,
  `[Category C] [Category D] [Preadditive C] [Preadditive D]`.
  Source and target categories have independent object and morphism universes.
- Additive functor F: `(F : C ⥤ D) [F.Additive]`.
- Integer-indexed commuting bicomplex B: specialize
  `K : HomologicalComplex₂ C c₁ c₂` to
  `c₁ = c₂ = ComplexShape.up ℤ` and `K = B`.
  `HomologicalComplex₂` is the existing abbreviation
  `HomologicalComplex (HomologicalComplex C c₂) c₁`.
  Its objects are `(K.X p).X q`, horizontal maps are `(K.d p (p+1)).f q`,
  and vertical maps are `(K.X p).d q (q+1)`. The two square-zero conditions
  are the outer and inner complex laws; horizontal differentials are chain
  maps, which is precisely commuting, rather than anticommuting, squares.
- Diagonal total and its sign convention: specialize `c = ComplexShape.up ℤ`.
  `ComplexShape.π c₁ c₂ c (p,q)` becomes `p+q`, `ε₁` is 1, and `ε₂` is
  `p.negOnePow`, the unit representing the sign `(-1)^p` for every integer p.
  Thus `K.total c` is the diagonal coproduct total with differential
  `d₁ + (-1)^p d₂`. This is also stated explicitly in the module docstring
  of `Mathlib.Algebra.Homology.TotalComplex` and implemented in `d₁`, `d₂`
  and the total differential there. `K.ιTotal c p q n h` is its summand
  injection with `h : p+q = n`.
- Applying F to B: `(F.mapHomologicalComplex₂ c₁ c₂).obj K` applies
  `F.mapHomologicalComplex c₂` and then the outer complex functor, so it
  applies F to exactly the objects and both differentials of B.
- Existence of the diagonal coproducts of B: `[K.HasTotal c]` abbreviates
  `K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c)`, exactly the family of
  coproduct-existence assumptions on each diagonal. It assumes no unrelated
  colimits and does not impose any boundedness.
- Preservation of every diagonal coproduct of B:
  `[F.PreservesTotalComplex K c]` abbreviates, for every n,
  `PreservesColimit (Discrete.functor
  (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) n)) F`.
  These are precisely the specified diagonal diagrams.
- Existence of the diagonal coproducts of FB: the source's
  `HomologicalComplex₂.hasTotalOfPreserves` supplies
  `((F.mapHomologicalComplex₂ c₁ c₂).obj K).HasTotal c` from the preceding
  existence and preservation assumptions. The node's explicit existence
  hypothesis for FB is therefore already a consequence of its other
  hypotheses, and no additional restriction on FB is hidden in the API.
- Canonical degreewise comparison c_B^n and its invertibility:
  `mapTotalXIso F K c n` has source `Tot(FB)^n` and target `F(Tot(B)^n)`.
  Its actual construction is `asIso (Limits.sigmaComparison F s)`, where
  s is the diagonal family. `sigmaComparison` is the coproduct descent map
  with components `F.map` of the original injections. The source lemma
  `ι_mapTotalXIso_hom F K c p q n h` states
  `ιTotal(FB) ≫ (mapTotalXIso F K c n).hom = F.map (ιTotal B)`.
  This is exactly the equation in the node (Lean's `≫` writes composition
  in diagrammatic order); the coproduct universal property gives uniqueness.
  Being an `Iso` supplies an inverse and both inverse identities in each n.
- Isomorphism of complexes c_B: `mapTotalIso F K c` has type
  `((F.mapHomologicalComplex₂ c₁ c₂).obj K).total c ≅
  (F.mapHomologicalComplex c).obj (K.total c)`.
  It is constructed by `HomologicalComplex.Hom.isoOfComponents
  (mapTotalXIso F K c)`; thus its components are the canonical maps already
  characterized, not an arbitrary choice of a natural isomorphism.
  The target functor applies F termwise to objects and differentials of Tot(B).
  The supplied chain-map compatibility is part of this actual isomorphism.
- Every bicomplex map φ:B→B′: the source uses `{K L}` and `(φ : K ⟶ L)`.
  Its naturality lemmas have `[L.HasTotal c]` and
  `[F.PreservesTotalComplex L c]`, giving exactly the same hypotheses for B′;
  existence of the mapped total follows as above.
- Forward naturality: `mapTotalIso_hom_naturality F φ c` states
  `total.map ((F.mapHomologicalComplex₂ c₁ c₂).map φ) c ≫
  (mapTotalIso F L c).hom = (mapTotalIso F K c).hom ≫
  (F.mapHomologicalComplex c).map (total.map φ c)`.
  This is `c_B′ ∘ Tot(Fφ) = F(Tot(φ)) ∘ c_B`.
- Inverse naturality: `mapTotalIso_inv_naturality F φ c` states
  `(F.mapHomologicalComplex c).map (total.map φ c) ≫
  (mapTotalIso F L c).inv = (mapTotalIso F K c).inv ≫
  total.map ((F.mapHomologicalComplex₂ c₁ c₂).map φ) c`.
  This is `c_B′⁻¹ ∘ F(Tot(φ)) = Tot(Fφ) ∘ c_B⁻¹`.

The generic source declarations are used at the integer cochain shapes above;
the ability to instantiate them at other shapes adds no hypothesis to this node.
The `[DecidableEq I]` source binder is the standard decidable equality when
`I = ℤ`. No source or statement correction is needed.

Dependency declarations read in full, including their docstrings:

- `def-weil-preadditive-category` is a Mathlib leaf with
  `mathlib_match.declaration = CategoryTheory.Preadditive`, from
  `Mathlib.CategoryTheory.Preadditive.Basic`. Its Hom abelian groups and
  bilinear composition are exactly the node's preadditive structure.
- `def-weil-pbc-additive-functor` is a Mathlib leaf with
  `mathlib_match.declaration = CategoryTheory.Functor.Additive`, from
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`. Its `map_add` field
  expresses additivity; `mapAddHom` packages each Hom map as a homomorphism.
  These exact classes occur in the source comparison's variables.

The construction and proof were read to check that the object is canonical:
`mapTotalXIso` inverts the preserved-coproduct comparison; its injection lemma
uses `ι_comp_sigmaComparison`; `mapTotalIso` checks the differential equation
on injections using additivity and the two signed differentials. Forward
naturality is checked on each component and its summands. Inverse naturality
follows by canceling the forward isomorphism. These are already implemented
upstream, so this delivery introduces no theorem proof or postponed theorem.
The DAG has no additional proof-dependency imports to supply.

Edge cases checked by reading the constructions: n=0; negative p and q
(`Int.negOnePow`, not a natural-number-only exponent); zero differentials;
identity F and identity φ; unrestricted unbounded bicomplexes with infinite
countable diagonal coproducts. There is no first-quadrant or bounded-support
assumption. The comparison uses the actual diagonal coproducts, and its
universal property also covers any degenerate or empty summand family in the
generic source. No abelian-category, exactness, faithfulness, or global
coproduct-preservation assumption is inserted.

Searches performed for this item (logs are in sandbox `searches.jsonl`):

- LeanFinder via `msearch.py`: “Canonical natural isomorphism between the
  total of an additive functor applied to an integer indexed bicomplex and
  the additive functor applied to its total”. Eight hits, including
  `HomologicalComplex₂.total.mapIso`, concern generic total or shift
  constructions, without this additive-functor comparison.
- Loogle via `msearch.py`:
  `HomologicalComplex₂.mapTotalIso, HomologicalComplex₂.mapTotalXIso`.
  No hits; the project-specific `mapTotalIso` name is unknown in Loogle's
  Mathlib environment.
- Mathlib grep via `msearch.py`: `mapTotalIso|mapTotalXIso` restricted to
  `Algebra/Homology`. No hits.
- LeanSearch via `msearch.py`: “canonical comparison isomorphism additive
  functor total complex bicomplex naturality”. Eight related total-shift,
  bifunctor, and derived-category results; no exact Mathlib match.
- Source read and grep: the node's `lean_audit.slopmaster2.decls` names all
  five exact declarations in
  `WeilConjectures/FromJoel/Algebra/Homology/TotalComplexMap.lean`.
  Their full signatures and bodies were read; `scompile.py --source` confirms
  the same current source. Grep for the item id under `WeilConjectures`
  has no hits, and `dag/lean_names_upstream.json` has no `mapTotalIso` hit.
- Project-side grep `mapTotalIso|mapTotalXIso` under `lean/Sheaf` finds uses
  in existing total/tensor and Cartan–Eilenberg modules; these already use
  the same upstream comparison, not another definition of it.

Validation: `scompile.py` compiled the scratch probe importing the upstream
module and checking all five recorded declarations cleanly, with no warnings.
The expanded signatures confirm that each declaration has precisely the
parameters described above. `#print axioms` for each of the five reports only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Both wrapper
passes succeeded (24.4 seconds and 2.3 seconds). The dry run and final delivery
additionally check the existing names through the wrapper's generated probe
and run server preflight.
There are no new nodes, dependency repairs, or statement faults.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
