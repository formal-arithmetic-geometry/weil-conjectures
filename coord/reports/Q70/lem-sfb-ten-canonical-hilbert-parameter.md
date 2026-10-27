## Worker report

The statement is `AlgebraicGeometry.ten_canonical_hilbert_parameter` in
`Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter`. Its only postponed proof is
`sorry`. It asserts the existence of the full presentation, whose helper definitions are
inlined without any `sorry` in the same item module. The theorem has its complete
thirteen-step DAG proof and sources in its docstring. The original five statement
dependencies and the original statement and proof are retained; the eight existing
notion dependencies requested in the return are added to `stmt_deps`.

The earlier worker's stale-assignment diagnosis confused the reviewed stage-1 split
with a stage-2 binding. The live node has no Lean binding: Q39's accepted split does
not already deliver this statement. I read that split and its review and continued
with the requested statement.

Clause-by-clause rendering (field names below are in
`AlgebraicGeometry.TenCanonicalHilbert`):

- Any field and genus at least two: theorem arguments `(k : Type u) [Field k]`
  and `(g : ℕ) (_hg : 2 ≤ g)`. There is no algebraic-closure, characteristic,
  perfection, or infinitude assumption on k. All schemes use the same explicitly
  bound universe u, as do the recorded stable-family and Hilbert interfaces.
- The numbers d, r and P: `polynomial g` is the rational polynomial
  `C (20 * ((g : ℚ) - 1)) * X + C (1 - (g : ℚ))`. `Series.rank` is
  `IsFiniteLocallyFreeOfRank (19 * (g - 1))`. `Coordinates g` has
  `(19 * (g - 1) - 1) + 1` elements, lifted to universe u. Under `2 ≤ g` this
  is exactly r, and the projective space has dimension r-1. The n+1 form is
  required by the recorded Hilbert-polynomial interface; it does not change r.
- Z is exactly the polynomial component of the full Hilbert representation:
  `Hilbert.H`, `representation`, `HP`, `inclusion`, `index`, `index_eq`,
  `coproduct`, and `component`. `representation` uses the dependency's
  `properHilbertPresheaf` with ambient `standard g (Spec (.of k))`.
  `component` uses `HasProjectiveFibreHilbertPolynomial` with its identity
  embedding and characterizes factorization uniquely on every test scheme.
  The full represented functor already consists of flat finitely presented
  closed families. `projective` uses `IsHProjective`; `finite_type` uses
  `LocallyOfFiniteType ∧ QuasiCompact`. Thus projectivity and finite type
  refer to the structural morphism, in the node's stated conventions.
- The asserted Euler polynomial is explicit in `Presentation.euler_polynomial`:
  for every T-point of J, point t of T and integer m, the actual Hilbert
  closed family's twist has Euler characteristic
  `20 * ((g : ℤ) - 1) * m + 1 - (g : ℤ)`. This is not an arbitrary
  polynomial index whose interpretation has been omitted.
- The locally closed locus is `Presentation.J`, `inclusion`, and
  `locally_closed : IsImmersion inclusion.left`. Its ambient component is
  `hilbert.HP hilbert.index`, rather than an unrelated projective scheme.
- The stable unpointed family is the dependency's `StablePointedModuli
  (Spec (.of k)) g 0`, including all its stability and geometric-genus
  conditions and its actual cartesian curve arrows. No private stable-curve
  predicate is introduced.
- The dualizing line is `Series.omega` with the existing
  `NodalDualizingDatum X.projection omega`. This supplies invertibility and
  the normalized local regular-immersion Ext description of the nodal
  relative dualizing line, not merely an arbitrary invertible module.
- The direct image is the definition `sections X omega`, literally
  `(Scheme.Modules.pushforward X.projection).obj (omega.tensorPow 10)`.
  `Series.rank` and `quasicoherent` state its finite local freeness.
  `Series.base_change` makes the actual adjoint-defined `moduleBaseChangeMap`
  an isomorphism for every `a : T ⟶ X.base.left`; no flatness condition on a.
- Evaluation is the actual `tensorPullbackSectionAdjunction` counit in
  `evaluation`. Its surjectivity is `Series.evaluation_surjective`. The
  `embedding`, `commutes`, `closed`, and `classifies` fields express the
  induced closed immersion and its identification with the quotient map.
  `bundle` is relative Proj of the existing canonical symmetric graded
  algebra, with the existing `TautologicalQuotient`/`Classifies` interface.
  Consequently the projective bundle has the quotient convention.
- A projective frame is `Frame D a`, an isomorphism in `Over T` from the
  actual pulled-back projective bundle to standard projective space. It is
  not a basis or a linear trivialization. `baseEmbedding` is the actual
  fibre-product pullback of evaluation's closed immersion.
- Representing framed curves up to framed isomorphism is `Hilbert.Classifies`,
  `Presentation.represents`, and `all_points`. `Classifies` requires the
  unique isomorphism of the pulled-back curve with the Hilbert closed family
  to commute with both embedding and base projection. Thus the correspondence
  is pinned to the embedded family rather than an arbitrary bijection.
  `represents` gives a unique Hilbert point for every frame. `all_points`
  supplies a framed stable family for every J-point, with an isomorphism of
  its base to the given test scheme. Framed automorphisms are trivial since
  the embedding is a closed immersion.
- The allowed base line is `Presentation.hyperplane_twist`. It asserts
  `O_C(1) ≅ omega^10 ⊗ f^*N` for an `N` satisfying the existing
  `Scheme.Modules.IsInvertible`, using actual tensor pullback throughout.
  It does not choose a trivialization or demand global equality with omega^10.
  This is the stated local-on-T condition: such N is Zariski locally trivial;
  conversely local trivializations glue a base line since a stable family's
  functions are universally base functions, as explained in proof step 6.
- The group scheme is `Presentation.G : Grp (Over (Spec (.of k)))` together
  with `automorphisms` and `automorphisms_natural`. These identify its group
  of points on every scheme test, naturally, with the automorphism group of
  projective (r-1)-space, with its actual composition law. For r≥2 this is
  precisely PGL_r = GL_r/scalars as a group scheme. This functor-of-points
  characterization includes projective transformations that do not lift to a
  global matrix; using GL_r(T)/T-units as the set of points would be wrong.
  `Action` is only an abbreviation for Mathlib's `ModObj G.X J`, and
  `Action.act` is evaluation of its action morphism on a categorical product.
- `Presentation.action` is the scheme action on J. Its ambient coordinate
  interpretation is forced by `frames_equivariant`, `frames_classify`, and
  `all_points`: the Hilbert map of the postcomposed frame is that of the
  corresponding group translate. This expresses invariance, with the action
  on the actual Hilbert closed families specified rather than arbitrary.
- The frame torsor is `(equivalence.functor.obj X).space` over its `base`.
  `frame_base`, `frames`, `frames_natural`, and `frames_equivariant` identify
  its entire functor of points with projective frames, naturally and with
  the correct postcomposition action. `zariski` gives a section on a Zariski
  neighbourhood of each base point. Scheme-valued simple transitivity in
  `Pair.transitive` plus sections is exactly the usual local product torsor.
- Quotient objects are `Pair action`: a scheme over its variable base,
  compatible group action, simple transitivity on every test, an fppf
  covering map admitting a section, and an equivariant map to J. Allowing
  fppf torsors here loses none of the statement: the equivalence and
  `zariski` imply any pair with map to J is isomorphic to a Zariski frame
  torsor. No globally chosen section is assumed.
- Quotient arrows are `Pair.Hom`, actual equivariant scheme maps over the
  base map and commuting with the maps to J. The record has a concrete
  category instance and `Pair.forget`. Over a fixed base, torsor maps are
  isomorphisms, giving exactly the groupoid of the statement.
- The natural groupoid equivalence is `Presentation.equivalence` with
  `commutes` over the base-scheme category. It is an equivalence of total
  categories over schemes, so gives the fibre equivalences and their
  base-change compatibility. `frames_classify` fixes the object map to the
  actual evaluation construction. `arrows` fixes the arrow map: the
  cartesian curve map and the induced frame map yield the same embedded
  curve map. Thus the equivalence preserves every curve automorphism and
  is not merely an equivalence between sets of isomorphism classes.

Dependency declarations read and used:

- `Field` from Mathlib (`def-weil-field`, mathlib status).
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `AlgebraicGeometry.StablePointedModuli`, its `Hom`, and `forget`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact` (the original
  dependency's recorded note explicitly requires their conjunction).
- `Sheaf.AlgebraicGeometry.ProjectiveHilbertPolynomialRepresentability`:
  `exists_projective_hilbert_polynomial_representation`,
  `NumericalHilbertPolynomial`, `HasProjectiveFibreHilbertPolynomial`;
  the represented functor is the existing `properHilbertPresheaf`.
- `Sheaf.AlgebraicGeometry.NodalDualizingDatum`: `NodalDualizingDatum`.
- `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank`:
  `Scheme.Modules.IsFiniteLocallyFreeOfRank`, with the recorded generic
  `SheafOfModules.IsFiniteLocallyFreeOfRank` specialization.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction` and tensor pullback.
- `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`:
  `SymmetricAlgebraSheaf.gradedAlgebraData` and its relative Proj.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`:
  `ProjectiveBundleQuotientGeometry.TautologicalQuotient`, `Classifies`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `ProjectiveSpace.twist`, and the existing `eulerCharFiber` interface.
- `WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`:
  `Scheme.Modules.moduleBaseChangeMap` (the canonical map owned by the
  recorded base-change lemma, not a newly chosen map).
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, `.Mod`, and `.Over`:
  `Grp`, `ModObj`, the slice cartesian structure and internal action.

The proof imports all available recorded proof-dependency modules, with plain
`import`; statement dependencies use `public import`. The pending geometric
inputs remain named in the full natural-language proof, rather than being
invented as extra assumptions of the theorem.

Edge cases checked: g=2 gives r=19, d=20, P(m)=20m-1 and P^18; natural
subtraction never truncates an intended positive rank. The theorem makes no
claim for g<2. Test schemes may be empty, nonreduced, non-Noetherian or
non-quasi-compact; all quantified base-change maps and frame tests include
these cases. Empty bases have unique empty frames and vacuous Zariski-point
conditions. Reducible stable nodal fibres and elliptic tails use the recorded
stable-curve definition, not a smooth-curve replacement. Nontrivial base lines
and projective automorphisms without global linear lifts are included. Torsor
and frame conditions quantify over all schemes, not just geometric points.
No statement dispute or source-based correction is asserted.

Searches: `msearch.py` LeanFinder for the original Hilbert/ten-canonical/frame
statement returned only generic affine-space declarations; Loogle for expected
projective/Hilbert names did not identify this statement (one exploratory query
used an unknown ProjectiveSpectrum name). LeanSearch and LeanFinder for the
presentation datum returned only generic scheme/Proj/affine-space declarations.
Mathlib grep for `TenCanonical|ProjectiveFrame|relativeDualizing` in
AlgebraicGeometry returned no hits. Project searches in `lean/WeilConjectures`
and `lean/Sheaf` found the existing unrelated Verdier and polynomial-diagonal
relative dualizing constructions and VectorProjectiveFrameModel, none with
this stable-curve Hilbert presentation. The exact item-id search found only
uses in other theorem docstrings. DAG grep for the presentation name and
`tools/blueprint_refs.py search 'ten-canonical Hilbert presentation'` found no
existing definition node (zero blueprint matches). Existing projective bundle,
Hilbert, stable-family, and nodal-dualizing definitions were reused. A final
Mathlib source search found `ModObj`, and the initially drafted action record
was replaced with that existing definition. The wrapper's exact search records remain in searches.jsonl; the reviewed search
results are summarized above. No new definition node is delivered.

Source read: Morrison arXiv:0810.2340 §3.3, Definition 9 and projective frames
on pp.15–16, with the quotient discussion after Corollary 11 on p.17, via
https://arxiv.org/pdf/0810.2340; the arbitrary-field descent formulation follows
the node's explicit thirteen-step proof and its existing Stacks inputs.

## Repair of A6 + H12

The saved packet was first checked unchanged with `deliver2.py --no-push`:
commit 9fcec96b344 passed preflight and compilation. That did not repair the
landing refusal recorded for immutable head 154e9c95c986, so this packet makes
the maintainer's prescribed substantive packaging change instead of re-pushing
that packet. The saved item differs from the current shared node only in
`lean` and `stmt_deps`; all other current node fields are retained.

Removed the new node `def-sfb-ten-canonical-hilbert-presentation` and its separate
module. Inlined its complete declaration block into the item's module, unchanged
except for replacing the owning blueprint tag by
`lem-sfb-ten-canonical-hilbert-parameter`. Every named helper is listed in the
item's `lean.declarations`. The theorem signature and its thirteen-step proof
docstring are unchanged. No `import_flags`, target, citer or upstream source is
edited. This follows the return's simulated-check repair and does not try to
repair the upstream reachability chain.

The statement dependency list is exactly the original five plus:
`def-trf-nodal-dualizing-datum`, `def-amb-finite-locally-free-module`,
`def-pc-module-pullback`, `def-trf-canonical-symmetric-graded-algebra`,
`def-per-projective-bundle-quotient-data`, `def-sc-invertible-module`,
`def-pc-projective-space-twist`, and
`lem-weil-pbc-module-base-change-map-open-restriction`.
The quotient data dependency records the existing `TautologicalQuotient` and
`Classifies` definitions actually used in `Series`. The geometric theorem
`lem-trf-projective-bundle-quotient-geometry` remains a proof dependency.

The declaration-block comparison verifies exact preservation of all helper
signatures and bodies after the blueprint-tag substitution. The current item
statement and all proof steps are byte-for-byte preserved as JSON field values.
The signature recorded in `lean.statement` is verbatim from the final module.
All universes and binders remain explicit with auto-implicit variables disabled.
The only postponed theorem is `AlgebraicGeometry.ten_canonical_hilbert_parameter`.

Validation of the repaired single-module packet: the prescribed `scompile.py`
passed in sandbox and library modes (29.2 s and 30.9 s), with no errors or
non-sorry warnings. Delivery preflight is run next. No shared-repository source
or Git state was edited directly; only the authorized wrappers refresh and build
delivery worktrees.

## Second reading by Q70

Repair self-check by the same worker, as the dispatcher brief prohibits starting
other agents; the maintainer performs the independent delivery review. I reopened
the current node and the merged file and checked the clause map above against
`Series`, `Hilbert`, and `Presentation`. The field and genus binders, the exact
polynomial and Hilbert component, normalized dualizing line, rank-r direct image,
arbitrary canonical base-change isomorphisms, counit evaluation, closed embedding,
projective frames, base-line twist, PGL point functor, equivariant frame torsors,
Zariski sections, and the category equivalence on objects and arrows are preserved.
The g=2 arithmetic and arbitrary/empty-base cases above still apply.

The defect found was the separate unreachable helper node, exactly as the return
states. The repair places those helpers in the owning item module and records
their declarations there, with the precise eight added notion dependencies.
No mathematical clause changed. Automated self-checks confirm one Lean module,
one node file, one `sorry`, no overlong lines, a verbatim recorded theorem
signature, and no item-node changes outside `lean` and `stmt_deps`.
