## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePresentationLimitIsomorphismDescent`
states `AlgebraicGeometry.Scheme.Modules.finitePresentation_iso_descent_affineLimit`.
Its only theorem proof is `sorry`. No Lean definitions, axioms, or proved theorems are added.
A new DAG definition node records ownership of an existing canonical comparison.

Read the complete node and its dependency records and source declarations. Read
`literature/stacks-project/limits.tex`, lemma-descend-modules-finite-presentation
(Tag 01ZR), especially clauses (2) and (3), and lemma-descend-invertible-modules
(Tag 0B8W), proof of (2). The latter explicitly increases the stage until the
specified descended evaluation is an isomorphism. No statement correction is needed.

Hypothesis and clause correspondence:

- The small nonempty directed set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. A preorder is the project's directed-set convention;
  antisymmetry is not imposed. The index and schemes share universe `u`, as required
  by the project's inverse-limit size convention. There is no extra index universe.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. For `hik : i ≤ k`, the transition
  `q_ki` is `D.map (homOfLE hik).op`, with source `D.obj (op k)` and target
  `D.obj (op i)`. Functoriality supplies the transition identities and compositions.
- Quasi-compactness is `[∀ j : Iᵒᵖ, CompactSpace (D.obj j)]`, without Hausdorffness.
- Quasi-separatedness is `[∀ j : Iᵒᵖ, QuasiSeparatedSpace (D.obj j)]`.
  Mathlib's `quasiSeparated_iff_quasiSeparatedSpace` identifies this with the node's
  quasi-separated terminal morphism. No separatedness assumption is added.
- Affine transitions are `[∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f)]`.
  This also includes identity transitions, which are affine automatically.
- The scheme `Z` and its specified projections are `c.pt` and `c.π.app (op i)` for
  `c : Cone D`. Cone naturality is the displayed compatibility of the projections;
  `hc : IsLimit c` is exactly the unique-factorization universal property for every
  scheme and compatible family. No chosen limit or affine apex is substituted.
- The fixed stage is `(i : I)`. The fixed finite-stage models are
  `(F_i G_i : (D.obj (op i)).Modules)`.
- Their local finite-free presentations are `hF : F_i.IsFinitePresentation` and
  `hG : G_i.IsFinitePresentation`. Mathlib's class says locally a cokernel of a map
  between finite coproducts of the ring sheaf, exactly the node's finite free
  presentation. No extra flatness, local freeness, or quasi-coherence hypothesis
  is imposed.
- Tensor pullbacks are always `Scheme.Modules.tensorPullback`, whose object is
  the explicit sheafified tensor construction. The supplied `φ` is an actual
  isomorphism between the pullbacks of those fixed models along `c.π.app (op i)`.
- The conclusion provides `∃ (k : I) (hik : i ≤ k)` and the two explicitly typed
  morphisms `u_k`, `v_k` between direct transition pullbacks of `F_i`, `G_i`.
- The first equation `u_k ≫ v_k = 𝟙 (...)` is the node's `v_k ∘ u_k = 1_F`;
  Lean's `≫` writes composition in the order in which arrows are applied.
- The second equation `v_k ≫ u_k = 𝟙 (...)` is the node's `u_k ∘ v_k = 1_G`.
- The third equation conjugates the pullback of `u_k` by
  `affineLimitTensorPullbackComparison D c hik F_i/G_i` and equates it to `φ.hom`.
  The comparison goes from the iterated pullback to the direct pullback: hence
  its `.inv` precedes the mapped arrow and its `.hom` follows it.
- The fourth equation does the same for `v_k`, with F and G exchanged, and equals
  `φ.inv`. Thus the specified isomorphism and its specified inverse both descend.
- These equations use the existing `affineLimitTensorPullbackComparison`, not an
  arbitrary comparison isomorphism. Its definition is the inverse of the
  section-normalized composition comparison, followed by the cone equation's
  equality transport. The final explanatory sentence follows from the four
  equations and introduces no further hypothesis or conclusion.

Dependency declarations used (all are public through the imported descent module):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`, with its scheme-space equivalence above.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent `SheafOfModules` specialization underlying `Scheme.Modules`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionComp` and its uniquely
  section-normalized adjunction. The underlying functor is from the publicly
  imported `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation`, read with its local presentation data.
- `Sheaf.AlgebraicGeometry.FinitePresentationAffineLimitDescent`:
  `Scheme.Modules.affineLimitTensorPullbackComparison`, used in the statement;
  `Scheme.Modules.finitePresentation_descent_affineLimit`, whose second and third
  clauses are used in the docstring's proof plan. The plain comparison definition
  is now owned by `def-trf-affine-limit-tensor-pullback-comparison`, recorded
  `existing: true` on this module. The item cites that definition node in
  `stmt_deps`; the theorem node `lem-trf-fp-modules-affine-limit-descent` stays
  in `proof_deps` only. The same public import exposes the comparison used by
  the statement; no mathematical statement or proof is changed.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionAssociativity`:
  `Scheme.Modules.tensorPullbackCompositionIso_associativity`, imported only for
  the proof plan as required by `proof_deps`.

Edge cases checked before writing: the index is nonempty as required; a singleton
index and identity transitions allow `k = i` (no strict inequality is demanded).
Preorders with distinct equivalent indices are allowed. Empty schemes and an empty
limit are not excluded. Zero modules and rank-zero local presentations are allowed.
The statement imposes no nonzero, reduced, noetherian, characteristic, flatness, or
local freeness condition. When `φ` is the identity, the same two specified-lift
equations remain meaningful. Arbitrary supplied `φ` is retained, not replaced by
`Nonempty` of an unspecified isomorphism. Both inverse identities are checked with
their correct source objects.

Searches for an existing statement or notion:

- `msearch.py leanfinder`: “A specified isomorphism of finitely presented sheaves
  of modules on a directed inverse limit of qcqs schemes with affine transition
  morphisms descends to a later stage together with its inverse”. Eight hits:
  affine-limit statements about scheme morphisms or structure-sheaf sections,
  and the local finite-presentation data class; no module-isomorphism descent.
- `msearch.py loogle`: `Scheme.Modules.tensorPullback, IsFinitePresentation`
  returned no hits and reported the project-specific pullback name unknown.
  Retried with `SheafOfModules.IsFinitePresentation`: five hits, identifying the
  existing finite-presentation class and its quasi-coherence/finite-type consequences,
  but no descent theorem. Reused that class.
- `msearch.py grep` of Mathlib:
  `(iso|isomorphism).*(descend|[Ff]inite[Pp]resentation)|(descend|[Ff]inite[Pp]resentation).*(iso|isomorphism)`.
  Twenty-five hits concern ring properties, scheme morphisms, and invariance of
  finite presentation under an isomorphism, not this descent assertion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for finite-presentation/descent,
  iso/descent combinations, and `finitePresentation.*(iso|Iso)|[Ii]so.*finitePresentation`:
  found the affine-limit descent theorem and its canonical comparison, reused here;
  other hits concern different notions (scheme morphisms, scalar extensions,
  inverse-image comparisons), not all four specified equations for fixed models.
- `grep -rn lem-trf-fp-module-limit-isomorphism-descent lean/WeilConjectures`:
  no hits. The project's `RigidifiedLineBigOpenExtension` docstring mentions the
  DAG item as a proof dependency, not an existing declaration of it.
- `rg` in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`
  for the new declaration name: no duplicate declaration.

The required server compilation via `scompile.py` completed cleanly in library
module mode (3.8 seconds), with no errors or warnings.

## Second reading by Q19

A separate reading pass in this worker, with the node and completed file open,
checked the universal limit hypothesis, directedness and all four equations.
No additional worker was started, as the dispatcher brief prohibits that;
the maintainer supplies the independent review.

In particular, `u_k ≫ v_k` has the F pullback as source, and `v_k ≫ u_k`
has the G pullback as source. The comparison inverse starts each transported map
at the direct limit pullback, and the comparison forward map ends it there, so
both comparisons have the correct orientations. The two equations end in the
supplied `φ.hom` and `φ.inv`, respectively. The finite presentation class was read
in Mathlib (local cokernels of finite free modules), rather than confused with
finite generation or finite presentation of a scheme morphism. No mismatch was
found in the mathematical statement. The return identified one ownership defect
in the DAG record, repaired below by a new definition node. No statement change
or dependency-module repair is needed.


## New nodes

`def-trf-affine-limit-tensor-pullback-comparison` owns the existing
`AlgebraicGeometry.Scheme.Modules.affineLimitTensorPullbackComparison` in
`Sheaf.AlgebraicGeometry.FinitePresentationAffineLimitDescent`. Its Lean record is
`existing: true`, without a new module or copied definition, as expressly allowed
by the return. Source: Stacks 01ZR (2), the canonical base-change identification,
and 0097 (`sheaves.tex`, lemma-push-pull-composition-modules), the canonical
composition isomorphism. The node introduces an arbitrary small preorder, a scheme
diagram and a cone, and defines the comparison from iterated tensor pullback to
direct pullback. The existing definition is exactly the inverse of
`tensorPullbackSectionComp`, evaluated at M, followed by `eqToIso` along `c.w`.
The section-normalized adjunction has unit `m ↦ 1 ⊗ m`, fixing the comparison.
The node cites `def-pc-scheme`, `def-weil-sheaf-of-modules-category`, and
`def-pc-module-pullback`, precisely the notions it uses.

New-node hypothesis and construction correspondence: `{I : Type u} [Preorder I]`
is its small preordered set; `(D : Iᵒᵖ ⥤ Scheme.{u})` is its inverse diagram;
`(c : Cone D)` supplies its scheme Z and projections. `{i j : I} (hij : i ≤ j)`
is its comparable pair of indices. `(M : (D.obj (op i)).Modules)` is its arbitrary
module. The result has source the tensor pullback along `c.π.app (op j)` of the
transition pullback along `D.map (homOfLE hij).op`, and target the tensor pullback
along `c.π.app (op i)`. The body uses the inverse section-normalized composition
comparison and equality transport along `c.w (homOfLE hij).op`. The node does not
assume directedness, nonemptiness, IsLimit, finite presentation, quasi-compactness,
quasi-separatedness, or affine transitions, since none is required by the existing
definition. In particular, arbitrary cones and zero modules are allowed; i = j
and identity transitions are allowed. With empty I there is no pair of indices
or M to supply, so this definition creates no spurious existence assertion.

Searches are recorded with their returned output in the new node's
`mathlib_searches`: LeanSearch for the canonical cone-projection comparison
returned eight generic categorical pullback/gluing comparisons; LeanFinder for
composition of module pullbacks returned eight general sheaf-pullback composition
and free-sheaf comparisons, including Mathlib `Scheme.Modules.pullbackComp` for
the different chosen pullback functor. The Mathlib grep for
`affineLimitTensorPullbackComparison|tensorPullbackSectionComp|tensorPullback.*[Cc]omp`
returned zero hits. Direct source-library grep found no definition of these names;
project grep found this exact existing comparison and its section-normalized
composition constructor, both reused. The DAG ownership search found only the
statement node `lem-trf-fp-modules-affine-limit-descent` listing the comparison in
`lean.declarations`; no definition node already owns it. The blueprint search
`tools/blueprint_refs.py search "tensor pullback"` found zero matching blueprint
nodes. `ancestor` gives `lem-trf-local-term-locality`; the new record identifies
the specific eventual-isomorphism step in that ancestor's descent input and
copies the item's via chain with the item prepended. The item is reached from
a target/former target, so the new definition has `import_flags: []`.

## Repair of return H2

The returned immutable head was `b5c789450944`. The retained sandbox version was
compared with current main: only its item `lean` and added `stmt_deps` differed;
current main still has the original statement without a Lean record. Its live
comparison module was also read through `scompile.py --source`: the real
comparison remains the same `tensorPullbackSectionComp.symm` then `eqToIso`
construction. The prescribed delivery wrapper rebases the repaired packet onto
current main when building the delivery commit.

H2 is repaired by adding the definition node above and replacing the added
`lem-trf-fp-modules-affine-limit-descent` entry in the item's `stmt_deps` with
`def-trf-affine-limit-tensor-pullback-comparison`. The theorem node remains in
`proof_deps`, where its map-descent and equality-descent conclusions are used.
The item `lean.note` and this report now name the correct definition owner.
The new node's `lean.note` explains its existing attachment and why no theorem
conclusion is used by the comparison construction. No existing dependency node,
Lean definition, theorem signature, proof plan, or item statement is changed.

The repair reading reopened the new definition node alongside the full existing
source definition and checked every binder, orientation, and equality transport.
It then reopened the item record and verified that its statement dependencies
contain the definition owner and its proof dependencies retain the descent
theorem. All four previously accepted conclusions remain byte-identical in the
Lean file. No other numbered return point was given.
