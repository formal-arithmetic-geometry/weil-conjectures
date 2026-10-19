## Worker report

This delivery states `lem-coef-framed-projective-diagram-resolution` in
`Sheaf.CategoryTheory.FramedProjectiveDiagramResolution`.  The main declaration is
`HomotopicalAlgebra.FramedProjective.exists_resolution`; its proof is `sorry`, and all
construction definitions have actual data.  The module uses the recorded Reedy and
Kan--Quillen dependency modules.  There are no new DAG nodes, dependency repairs,
statement corrections, or `STATEMENT-DISPUTED` findings.

### Hypotheses and every clause

- `{J : Type w} [SmallCategory J]` is the fixed small ordinary indexing category;
  `{M : Type u} [Category.{v} M]`, `[HasColimits M]`, and the explicit
  `[HasColimitsOfSize.{max u w v, max u w v} M]` supply the containing universes for
  the displayed coproducts and multicoequalizers.  No nonemptiness of `J` is assumed.
- `P : ModelCategory (J ⥤ M)` is the assumed projective model structure.  `hPW`
  identifies its weak equivalences with `(weakEquivalences M).functorCategory J`, and
  `hPF` identifies its fibrations with the objectwise fibrations.
- `A : SimplexCategory ⥤ J ⥤ M` is the curried form of
  `A : J → M^Δ`.  `coefficient A j` is the cosimplicial object with value
  `(A.obj q).obj j` and maps `(A.map f).app j`.
- `hA` says for every `j` and every simplex `q` that the Reedy latching map of
  `coefficient A j` is a cofibration in `M`; this is exactly objectwise Reedy
  cofibrancy of each `A_j^bullet`.
- `hconst` says every cosimplicial structure map `(A.map a).app j` is a weak
  equivalence, for every simplex arrow and every `j`.
- The conclusion is `Nonempty (Resolution P A)`.  Its `obj` is the cosimplicial
  diagram `PA : Δ ⥤ J ⥤ M`, and `augmentation : obj ⟶ A` is the natural augmentation.
- `barShape` is the reversed outer bar shape.  Its left indices are
  `(m,n, α : [m] ⟶ [n], c : [n]`-chain in `Over j`)`, and its right indices are
  `(n,c)`.  `barCoefficient A q p j c` is the actual inner coend
  `A_{c_0}^bullet ⊗_Δ (Δ^q × Δ^p)`, formed by the existing
  `framedHornCoend` colimit of elements.
- `barIndex` uses the two canonical outer maps: the first applies the first-chain
  map to coefficients, and the second applies `Δ^α` to the outer simplex.  Thus
  `barObject A q j := multicoequalizer (barIndex A q j)` is exactly the displayed
  outer coend modulo simplex-operator and chain relations.  `barInjection` is its
  canonical coprojection for every `p` and chain `c`.
- `stageIso q j : (PA)^q(j) ≅ barObject A q.len j` renders the displayed formula
  clause by clause, including the coproduct over all chains and the outer coend.
- `collapse` and `augmentation_formula` state that each canonical chain summand is
  sent by the augmentation through the inner collapse and then by the composite
  chain arrow to `j`; the composite is written explicitly using the chain map from
  its first to last vertex followed by the final arrow to `j`.
- `reedy_cofibrant` is the projective Reedy latching cofibration for every simplex
  degree.  `augmentation_weak` says every component of `epsilon` is a weak
  equivalence.  `structure_weak` says every cosimplicial structure map of `PA`, at
  every object `j`, is an objectwise weak equivalence.

The definition `coefficient` is a genuine cosimplicial object.  `barShape`,
`barCoefficient`, `barCoefficientMap`, `barIndex`, `barObject`, and `barInjection` use
only ordinary category-theoretic colimits and have no postponed data.  The sole
postponed result is the named theorem `exists_resolution`.

### Dependencies read and used

- `lem-coef-reedy-model-structure`, declaration
  `HomotopicalAlgebra.Reedy.model_structure` in
  `Sheaf.CategoryTheory.ReedyModelStructure`.  I read its full signature and
  docstring, including the latching map convention and the objectwise weak/fibration
  equalities.  The module uses `Reedy.latchingTo` and the recorded cofibration class.
- `lem-coef-kan-quillen-right-proper`, declaration
  `SSet.KanQuillen.right_proper_kan_quillen` in
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`.  I read its full signature and
  docstring; the ordinary Kan model structure and horn/boundary facts are part of the
  proof plan documented on `exists_resolution`.

### Edge cases checked

Degree `p = 0` is included: `Fin.last 0` and the identity chain are valid, and the
outer multicoequalizer has the expected degree-zero summand.  Degree `q = 0` is
included because `barCoefficient` uses `stdSimplex.obj ⦋q⦌` without a positivity
hypothesis.  Identity arrows in `J` remain in the chain coproduct and are imposed by
the multicoequalizer relations.  An empty `J` introduces no object binder and all
objectwise clauses are vacuous; no `[Nonempty J]` was added.  Identity simplex maps
use the existing product map and coend relations.  No properness, combinatorial
assumption, simplicial enrichment, or fibrancy assumption is introduced.

### Searches and source

The required searches found no exact existing declaration:

1. `msearch.py ... leanfinder "framed projective diagram resolution with
   cosimplicial weak equivalence augmentation"` returned eight unrelated Cech,
   cofibrant-resolution, and extra-degeneracy hits; none has this chain coend.
2. `msearch.py ... loogle "Reedy.latchingTo, framedHornCoend, multicoequalizer"`
   returned zero hits.
3. `msearch.py ... grep "framed.*projective|diagram.*resolution"
   Mathlib/CategoryTheory` returned zero hits.
4. Direct `rg` over `WeilConjectures/` found no framed projective diagram resolution;
   direct `rg` over `lean/Sheaf` found only the related bar and weighted-coend
   modules.  The exact item-id grep in the upstream source returned no hit.
5. `tools/blueprint_refs.py search lem-coef-framed-projective-diagram-resolution`
   returned zero blueprint nodes.

The related `SimplicialBarProjectiveResolution` and
`ProjectiveFrameWeightedCoend` modules were read.  Their inputs require a simplicial
tensor/enrichment or state a weighted adjunction, so neither is the node's statement
and neither is duplicated.  The source place is Hirschhorn §§16.4--16.5 and
19.2--19.4 as recorded by the node; the module and every declaration carry the
blueprint id and source description.

### Validation

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q128
lem-coef-framed-projective-diagram-resolution
.../FramedProjectiveDiagramResolution.lean` compiled the sandbox file and the
library-overlay file with no errors and no warnings.  `autoImplicit` is false and all
variables and universes are explicitly bound.  No shared-library or source-checkout
file was modified.

## Second reading by Q128

I reread the node statement, the complete module, and both dependency declarations.
The small-category, model-structure, objectwise Reedy, homotopical-constancy, and
empty-index hypotheses are all present in the theorem signature.  The `Resolution`
fields account for the exact chain coend (`barIndex`/`barObject`), the canonical
augmentation on every chain coprojection, projective Reedy cofibrancy, componentwise
weak equivalence of the augmentation, and objectwise weak equivalence of every
cosimplicial structure map.  The `p = 0`, `q = 0`, identity-arrow, and empty-`J`
cases remain in the quantifiers.  The second compilation above was run after this
reading and is clean.
