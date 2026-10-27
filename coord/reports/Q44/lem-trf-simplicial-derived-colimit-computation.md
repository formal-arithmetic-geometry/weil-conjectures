## Worker report

The module `Sheaf.CategoryTheory.SimplicialDerivedColimitComputation` states
`CategoryTheory.SimplicialDerivedColimit.computation_exists`. Its only postponed proof is
this theorem. All auxiliary declarations expand the objects and the simultaneous canonical
comparison assertion; none chooses data from an unproved existence theorem.

Source read: `literature/stacks-project/sites-cohomology.tex`, Lemma
`lemma-compute-by-cosimplicial-resolution` (08Q9, lines 10229–10296), together with Examples
08PG and 08PH and Remark 08PD. The source's projective-resolution double complex is the
normalization used in `ResolutionRoof`. The DAG's two-sided bar proof supplies the equivalent,
choice-free comparison and its complete reindexing naturality.

Hypotheses and clauses, matched to Lean:

- The working universe is the explicit `universe u`; indexing categories are `E : Type u`
  with `[SmallCategory E]`, coefficient rings `R : Type u` with `[CommRing R]`, coefficient
  modules `ModuleCat.{u} R`, and derived morphisms use the recorded standard `u+1`
  localization. This is `def-weil-size-convention`, which has no declaration to import.
- We write `E = Dᵒᵖ`, so `F : Eᵒᵖ ⥤ ModuleCat R` is the covariant diagram of the node.
  Conversely every original `D` is covered by `E := Dᵒᵖ` and the canonical double-opposite
  equivalence `CategoryTheory.opOpEquivalence D`; this is a change of notation, with no
  restriction on objects or morphisms.
- `Q : SimplicialObject Eᵒᵖ` is the given simplicial object, using Mathlib's recorded
  `CategoryTheory.SimplicialObject`. For `T : E`, `Q ⋙ yoneda.obj T` has values
  `Hom_E(Q_n.unop,T) = Hom_D(T,Q_n)`. `IsResolution Q` asserts the existence of inverse
  maps to and from the constant singleton and both homotopy identities. `Relation.EqvGen`
  of `Nonempty (SSet.Homotopy a b)` allows exactly the finite zigzags in Stacks' definition;
  a single cylinder homotopy is not imposed as a stronger assumption. No chosen contraction
  appears in the comparison data.
- `evaluationComplex Q` is precomposition by `Q`, followed by the actual Mathlib alternating
  face complex and extension along `ComplexShape.embeddingDownNat`. Thus its degree `-n`
  is `F(Q_n)`, its differential is the alternating sum of `F(d_i)`, and its positive terms
  are zero. `evaluationTerm` is the actual extension isomorphism to this term.
- `derivedColimit B F` is `(B.models E R).derived` applied to `F[0]` through
  `DerivedCategory.Q`. `B` is the existing `CategoryColimitBarSystem`, not a second
  definition of derived colimit. The theorem works for every such recorded system; its
  existing existence theorem supplies one. There is no new left-derived-functor assumption.
- `Computation.comparison F Q hQ` is the isomorphism in the full derived category from
  `Q(s(F(Q)))` to `derivedColimit B F`. It is not merely an isomorphism on each cohomology.
- Computation by projective resolutions is explicit: `projectiveResolution` supplies a
  resolution `a : P ⟶ F[0]`, `P.IsStrictlyLE 0`, termwise `Projective (P.X i)`, and
  `QuasiIso a`. For EVERY such resolution, `computation` supplies `ResolutionRoof`.
  `resolutionDoubleComplex Q P` is the actual double complex of `P^p(Q_q)`, constructed
  by `mapHomologicalComplex`; its total is Mathlib's signed cochain total. The roof maps
  are fixed on the `p=0` and `q=0` summands by `evaluationEdge` and `colimitEdge`, and
  zero on every other summand by the two off-edge equations. Both maps are quasi-isos.
  `ResolutionRoof.canonical` identifies the comparison with precisely
  `Q(toEvaluation)⁻¹ Q(toColimit)`, followed by the inverse of the canonical projective
  computation `Lcolim(Q(a))⁻¹ ε_P`. In particular no arbitrary isomorphism is accepted.
- The bar terms, their coproduct isomorphisms, positive-degree zeros, and canonical derived
  comparison are the existing `(B.models E R).bar`, `.coordinates`, `.positive`, and
  `.model`. If `c` is an `E` chain, reversing it gives a `D` chain with coefficient
  `F(op c.right)` at its FIRST vertex. The old differential numbers faces in the reverse
  order. `forwardGenerator B F n c = (-1)^(n(n+1)/2) • B.generator ...` changes coproduct
  coordinates by an invertible sign. `forwardDifferential` explicitly asserts the node's
  first-vertex alternating sum: `j.rev` deletes the corresponding `E` vertex, and
  `categoryBarFaceCoefficient` applies `F` exactly at the coefficient vertex. Its adjacent
  sign ratio is `(-1)^(n+1)`, as required for reversal of `n+2` faces. This uses the same
  existing bar complex with signed coordinates, not an unrelated replacement.
- For `u : E ⥤ D`, the node's covariant indexing functor is `u.op : Eᵒᵖ ⥤ Dᵒᵖ`.
  `φ : R →+* S` is the ring map, and
  `t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ` is exactly its semilinear natural map.
  The chain map is `B.map u φ t`. `forwardMap` states its generator formula in the node's
  first-vertex coordinates, with no extra sign on source-to-target generators.
  `derivedMap` is its actual image under localization and the canonical bar comparisons,
  including `mapDerivedCategoryFactors.inv`, so targets are truly restricted derived
  objects.
- `evaluationMap` and `evaluationFormula` specify the map `s(F'(k) ∘ θ_Q)` on EVERY term:
  first `t.app (Q_n)`, then `G.map (k_n)`. This chain map is determined on all nonzero
  terms; the positive terms are zero.
- `naturality` is the exact equality
  `Q(evaluationMap) ≫ restrictionFactors.inv ≫ Res(comparison_Q') = comparison_Q ≫ HMap`.
  Its only contractibility hypotheses are `hQ : IsResolution Q` and
  `hQ' : IsResolution Q'`. `k : Q ⋙ u.op ⟶ Q'` is arbitrary, and there is no assumption
  on `Q ⋙ u.op`. Taking indexing and ring identities gives naturality in `F` and `Q`.
- `identity` and `composition` state identity and composition for the DERIVED maps, with
  the canonical restriction-of-scalars identity/composition and exact-functor localization
  isomorphisms explicitly present. Composition accepts the componentwise specified composite
  transformation `a`, so it does not silently identify separately bundled scalar actions.
- All restriction in these formulas is `ModuleCat.restrictScalars φ`, its degreewise
  `mapHomologicalComplex`, and its induced exact derived functor. The recorded bar system's
  `scalarIso`, `scalarFormula` and `scalarCanonical` identify the bar complex after scalar
  restriction. Our formulas use precisely those bar maps and the canonical localization
  factors. Specializing naturality to identity indexing, `F = G ⋙ restrictScalars φ` and
  identity `t` supplies compatibility of the simplicial comparisons with restriction.

Dependency declarations read and used:

- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`:
  `CategoryTheory.SimplicialObject`, `.δ`, `.σ` (full signatures and docstrings read).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory.standard` (full signatures and docstrings read).
- `Sheaf.CategoryTheory.DerivedColimitBar`: `CategoryColimitBarSystem`,
  `categoryColimitBarSystem_exists`, `CategoryColimitBarModel`, its canonical `.model` and
  universal `.comparison`, `CategoryColimitBarModel.generator`, `categoryBarDelete`,
  `categoryBarFaceCoefficient`, plus the standard coefficient/presheaf localization instances.
  The new definition node `def-trf-derived-colimit-bar-system` owns these existing data
  and is added to `stmt_deps`; the existence theorem stays only in `proof_deps`.
- Proof imports: `Sheaf.CategoryTheory.DerivedCategory.BoundedAboveAcyclicComputation`
  (`exists_boundedAbove_projective_resolution`, `boundedAbove_acyclic_leftDerived_computation`);
  `Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance`
  (`SSet.Homotopy.chainComplexMap`, `.congr_homologyMap`, the recorded Mathlib match);
  `WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns`
  (`HomologicalComplex₂.total.quasiIso_map_of_isStrictlyGE_of_isStrictlyLE`). Their full
  recorded signatures and surrounding documentation were read. The bar module is
  public because its existing definitions are used in statements; its existence theorem is
  a proof dependency only. No proof import closes a cycle.

Searches actually run with `batch2/msearch.py Q44 <item>`:

- LeanFinder: `simplicial object contractible representable evaluations compute derived
  colimit bar complex natural reindexing`. Eight hits, concerning Dold–Kan normalization and
  denormalization (`natTransPInfty_app`, `Γ₂N₁.natTrans_app_f_app`, `Γ₀.obj`,
  `Idempotents.DoldKan.N`, and related declarations). None states this result.
- Loogle: `"colimit", "simplicial"`. Eight hits: ordinary limits in simplicial/cosimplicial
  categories and the coproduct decomposition of split simplicial objects. No derived result.
- Mathlib grep: `derivedColimit|simplicialDerived|categoryColimit`. Zero hits.
- LeanSearch: `derived colimit of a diagram computed by a simplicial object with contractible
  representables`. Eight hits: ordinary simplicial-category colimits, representable colimit
  presentations and split simplicial coproducts. No matching derived computation.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item ID: only the downstream
  cotangent-resolution module's proof docstring cites this item. No existing statement.
  Searches for simplicial/colimit and homotopy-equivalence terminology found the bar system
  and the actual alternating-face/extension construction. The generic `negativeComplex`
  helper in the downstream cotangent module is not imported: we use Mathlib's composite
  directly, specialized to evaluation on `Q`, with no second generic definition.

Edge cases checked mathematically before and after writing:

- If the indexing category is empty, it admits no simplicial object `Q`; the comparison
  quantification is consequently empty. Bar coproducts and the projective-resolution clause
  still make sense and are zero. No `Nonempty E` binder was added.
- For a one-object identity category and constant `Q`, the complex is the unnormalized
  singleton complex: differential identity for positive even chain degrees and zero for odd
  degrees, and the roof induces the identity on degree zero. It is not incorrectly replaced
  by a complex with zero differentials in every degree.
- At `n=0`, the sign on the forward generator is one, the term coordinates and the two
  projective-roof edge maps give the exact colimit augmentation. In degree one the two faces
  cancel in the singleton case.
- Arbitrary modules, including nonflat modules such as `ℤ/2` over `ℤ`, are allowed.
  Tensoring the contraction only uses sums and compositions. No flatness or finiteness
  hypothesis is present.
- Zero ring, zero diagram and empty coproducts cause no exceptional assumptions; the sign
  coordinate changes remain invertible. In characteristic two they become identity.
- Nontrivial scalar restriction, such as `ℤ → ℤ/2`, is explicit in both chain maps and
  derived localization factors. The intermediate `uQ` is never treated as a resolution.

No statement correction, dependency-module repair or STATEMENT-DISPUTED flag is needed.
The new definition node records ownership of existing data, as requested in the return.
The original statement and proof remain unchanged. The main theorem proof is `sorry`, as
required for stage 2.

## Second reading by Q44

I reread the node and final module in a separate pass in this worker session; no independent
worker agent was started, as the dispatcher's brief prohibits that. Independent maintainer
review follows delivery. This pass checked the following substantive points:

1. The representable evaluation uses `Hom_E(Q_n.unop,T)`, giving the required direction
   `Hom_D(T,Q_n)`, rather than its opposite. The `IsResolution` hypothesis admits finite
   zigzags of homotopies and therefore does not require a stronger single-homotopy contraction.
2. `evaluationComplex` really uses the unnormalized alternating complex and extends to
   nonpositive integer cochain degrees. The projective double complex has horizontal
   cochain degree `p` and vertical degree `-q`; its total sign is the Mathlib cochain sign.
3. The roof normalization matches EVERY bounded-above projective resolution. The `p=0`
   map uses `a.f 0` and the actual degree-zero single-complex isomorphism; the `q=0` map
   uses the actual colimit cocone. The equation has the orientation
   `a_Q ; (Lcolim(Qa))⁻¹ ; ε_P = Q(e_Q)⁻¹ ; Q(e_P)`.
4. Forward bar coordinates were checked at adjacent degrees, including zero: their ratio
   is `(-1)^(n+1)` and the face is `j.rev`. Equal signs in source and target cancel from
   the reindexing generator formula.
5. The semilinear comparison square has the localization factor in the direction
   `Q(Res C) → Res(Q C)`. The two comparison isomorphisms are in full derived categories,
   and the only resolution assumptions are on `Q` and `Q'`. Identity and composition
   include the canonical scalar-action and derived-functor coherence isomorphisms.
6. Initial compiler findings were interface elaboration issues: expose the actual evaluation
   composite to instance synthesis, annotate its bicomplex return type, and bind the
   quasi-isomorphism instance of a projective augmentation. These changes added no
   mathematical hypothesis to the asserted computation.

Validation: the final module passed `batch2/scompile.py` on the server in both its sandbox
and final module names, with no errors or warnings (27.2 s and 28.6 s). A single unused
parameter warning in the earlier run was removed by naming the parameter `_t`; it remains
constrained by the subsequent term formula. The module has one named theorem with `sorry`,
no other postponed proof, no overlong line, and no auto-bound variables. The node signature
was compared verbatim with the final file; only `lean` and the addition of the new bar-system
definition node to `stmt_deps` differ from the repository copy.


## New nodes

`def-trf-derived-colimit-bar-system` records the existing type
`CategoryTheory.CategoryColimitBarSystem` and its auxiliary definitions from the unchanged
published `Sheaf.CategoryTheory.DerivedColimitBar` (lines 45–354). Its `lean.existing` is true;
there is no second module or second definition. The node defines data and laws, with no
existence assertion. Its point, localization, model, generator, canonical resolution,
reindexing, scalar, exactness and homotopy clauses were matched against the full structures
`CategoryColimitPoint`, `CategoryColimitBarModel` and `CategoryColimitBarSystem`. The main
signature is verbatim `structure CategoryColimitBarSystem` before `where`.

The source is Stacks 08PF/08PG/08PH/08PD, in particular the complex and generator formula in
`example-left-derived-colimits`, and the augmented bar/prism interface of the existing lemma.
This data package is what step 1 of the item's proof uses. The new node inherits the item's
chapter/unit and nearest blueprint ancestor `lem-trf-local-term-locality`, with the item
prepended to its via path. It cites the seven definition nodes underlying that interface.

Fresh searches via `msearch.py` on 2026-10-22: LeanSearch query
`bar model system for derived colimit of module presheaves with coproduct coordinates and scalar restriction`
returned eight ordinary presheaf-colimit/scalar-restriction hits, no bar-system definition;
Loogle query `CategoryColimitBarSystem, CategoryColimitBarModel` returned zero hits (unknown
first identifier); Mathlib grep query
`CategoryColimitBarSystem|CategoryColimitBarModel|categoryBarDelete|categoryBarFaceCoefficient`
returned zero hits. Actual outputs/digests are recorded in the new node and `searches.jsonl`.
The same `rg` across `lean/WeilConjectures` and `lean/Sheaf` finds the defining declarations
only in `DerivedColimitBar.lean`, plus their consumers. DAG search finds the existing theorem
record and its consumers, but no definition node owning these types. Blueprint search
`derived colimit` returns only `det-sf-comparison-affine-continuity` and
`sk-prop-sf-comparison`, both site-cohomology comparisons, not this data definition; the
broader `bar` search likewise supplies no duplicate category-colimit bar-system definition.
No other node or module is changed. Empty categories, zero rings and nonflat coefficients
are allowed by the existing data type; this ownership record introduces no new assumptions.

## Repair of return L (immutable head ce2713fb1917)

H2 / theorem stmt_dep: replaced the added `lem-trf-derived-colimit-bar` statement dependency
with the new definition node `def-trf-derived-colimit-bar-system`. The lemma remains in
`proof_deps`, unchanged from the live base. `computation_exists` quantifies over an arbitrary
bar system and uses its definitions; it does not invoke `categoryColimitBarSystem_exists`.
The new `existing: true` record owns the existing structures, maps and instances without
changing their published module or introducing duplicate names. The delivered Lean file and
its theorem signature are unchanged from the saved packet reviewed in that immutable head.
Comparison with the current read clone found that the original saved item's only changed
fields were `lean` and `stmt_deps`; the repair preserves this field boundary. The wrapper
rebases the delivery onto the current server branch.

Second reading of the repair: reread the item, its arbitrary `B` binder, the model/system
structures and their docstrings, and the new node. Every new-node clause names data already
present in those structures, including canonical augmentation normalization and scalar maps.
The item now cites a definition for its signature and a theorem for its proof, exactly as
requested. There is no mathematical statement change and no new postponed proof.
