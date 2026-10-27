## Worker report

The module `Sheaf.AlgebraicTopology.FreeNormalizedHomologySurjectivityTransfer` states
`AlgebraicTopology.free_normalized_homology_surjectivity_transfer`, with one `sorry` and no
new definitions. The node is unchanged except for its `lean` record. Source read directly:
`literature/stacks-project/simplicial.tex`, Tag 08P2, label
`lemma-homotopy-equivalence`, evaluation square and surjectivity paragraph (5895–5932).
The source uses the opposite end face for its differential; the node deliberately uses
Mathlib's positive-face kernels and differential d_0. Its proof works directly with this
convention because every face of a normalized cycle vanishes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Simplicial abelian groups X and Y: `{X Y : SimplicialObject AddCommGrpCat.{u}}`.
  The universe `u` is arbitrary and explicitly declared. A common universe for X and Y
  loses no objects or maps: both can be taken in a common universe.
- Additive simplicial morphism f: `(f : X ⟶ Y)`. A morphism in this functor category is
  a natural transformation whose components are abelian-group homomorphisms. There are
  no additional hypotheses such as a homotopy equivalence or termwise surjectivity.
- For a simplicial set S, the degreewise free group F(S) and its simplicial operators
  are Mathlib's composite `S ⋙ AddCommGrpCat.free`. The source of `free` is `Type u`,
  so this accepts `S : SSet.{u}`. `free.obj α` is literally
  `AddCommGrpCat.of (FreeAbelianGroup α)` and `free.map a` is
  `AddCommGrpCat.ofHom (FreeAbelianGroup.map a)`. Thus its operators and F(a) send
  `[s]` to `[S(φ)(s)]` and `[a(s)]`, exactly as in the node, by
  `FreeAbelianGroup.map_of_apply`. No new free group or arbitrary map is introduced.
- The underlying simplicial set UZ is `Z ⋙ forget AddCommGrpCat`, using the same
  `SimplicialObject (Type u)` that Mathlib abbreviates as `SSet`.
- Evaluation epsilon_Z is `Functor.whiskerLeft Z AddCommGrpCat.adj.counit`.
  Read `AddCommGrpCat.adj`: its hom equivalence is built from
  `FreeAbelianGroup.lift.symm`. Its counit is the lift of the identity function,
  hence sends `[z]` to z and finite sums to the same integral sums. As a natural
  transformation it is already a simplicial morphism with additive components.
- Normalization, its differential and its induced chain maps are exactly
  `normalizedMooreComplex AddCommGrpCat`, on objects and maps. Read
  `NormalizedMooreComplex.objX`: degree zero is the top subobject and positive degree
  is the intersection of kernels of `X.δ k.succ`. The top subobject represents all
  of X_0. `objD` restricts `X.δ 0`; `obj` uses `ChainComplex.of`, so the outgoing
  differential in degree zero is zero. `map` restricts each component of f.
  This uses Mathlib's constructions, including their existing complex and functor laws.
- Homology is Mathlib's `HomologicalComplex.homology`, namely cycles modulo boundaries;
  `HomologicalComplex.homologyMap` is the induced map for the restricted chain map.
- The first conjunct is the evaluation square: `whiskerLeft X adj.counit ≫ f` equals
  `whiskerRight (whiskerRight f (forget AddCommGrpCat)) free ≫ whiskerLeft Y adj.counit`.
  Category composition reads from left to right, giving exactly f epsilon_X =
  epsilon_Y F(Uf).
- The second conjunct quantifies `∀ (n : ℕ) (y : (N(Y)).cycles n)`. The cycle object
  comes with the monomorphism `(N(Y)).iCycles n` into its normalized chain group.
  Composing with `Subobject.arrow (NormalizedMooreComplex.objX Y n)` identifies
  this cycle with its actual simplex in Y_n. Every normalized cycle is represented
  uniquely this way, since the cycle inclusion is a kernel.
- The existential `z : (N(F(UY))).cycles n` states that the requested lift belongs
  both to the normalized subgroup and to the kernel of its outgoing differential.
  Its first equality sends z through the cycle inclusion and the normalized subgroup
  inclusion, and requires that the result equal precisely
  `FreeAbelianGroup.of (inclusion y) - FreeAbelianGroup.of (0 : Y _⦋n⦌)`.
  This specifies the actual element [y]-[0_n], not an unspecified lift.
- The second equality says the degree-n map of `N(epsilon_Y)` sends the lifted
  normalized element to `(N(Y)).iCycles n y`, giving evaluation equal to y inside
  the normalized group itself. The inclusion in the free ambient group is monic,
  so the existential specifies the asserted canonical cycle uniquely.
- The last conjunct quantifies over every fixed `n : ℕ`. Its antecedent is
  `Function.Surjective (HomologicalComplex.homologyMap (N.map (F(Uf))) n)`;
  its consequent is `Function.Surjective (HomologicalComplex.homologyMap (N.map f) n)`.
  Surjectivity is only assumed in this one degree. There is no requirement in the
  other degrees and no stronger isomorphism conclusion.

Dependency declarations used:

- `def-weil-pbc-simplicial-object`: Mathlib module
  `Mathlib.AlgebraicTopology.SimplicialObject.Basic`, declarations
  `CategoryTheory.SimplicialObject`, `CategoryTheory.SimplicialObject.δ` and `.σ`.
  Read the full definitions: functors from `SimplexCategoryᵒᵖ`, faces and degeneracies
  induced by the corresponding order-preserving maps.
- `def-weil-pbc-simplicial-set`: Mathlib module
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`, declaration `SSet`.
  The dependency is a Mathlib node; its `mathlib_match` is the recorded interface.
  Only its simplicial-set clause is used here; degeneracy/finite-subset clauses are
  not hypotheses of this item.
- Additional existing Mathlib API: `AddCommGrpCat.free`, `AddCommGrpCat.adj` in
  `Mathlib.Algebra.Category.Grp.Adjunctions`; the abelian instance in
  `Mathlib.Algebra.Category.Grp.Abelian`; `normalizedMooreComplex`,
  `NormalizedMooreComplex.objX` in `Mathlib.AlgebraicTopology.MooreComplex`;
  `HomologicalComplex.cycles`, `.iCycles`, `.homologyMap` in
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`.
  All statement imports are public; both proof dependencies are also statement
  dependencies, so no further proof-only import is required.

Edge cases checked before writing:

- n=0: N_0 is the whole degree-zero group and its outgoing differential is zero.
  Both occurrences of `cycles 0` are therefore unrestricted. The formula subtracts
  the degree-zero zero generator and never invokes a face of degree -1.
- n=1: the sole positive face is d_1, and the cycle condition adds d_0=0; both
  faces of [y]-[0] vanish. The next differential out of N_0 is zero.
- y=0: the specified lift is [0]-[0]=0, not [0]. The generator of the zero
  simplex itself is nonzero in the free abelian group, which is why subtraction
  must be retained.
- X or Y the zero simplicial group: the free group on its underlying singleton is
  not zero. The formula and the implication still make sense without identifying
  that free group with zero.
- Identity f: the free homology map and the original homology map are identities;
  the evaluation square and cycle lift remain the stated ones.
- Constant X=0 and Y=Z: the free homology map is not surjective in degree zero,
  so the statement does not incorrectly conclude surjectivity of 0→Z.
- A normalized simplex need not be a cycle. Quantifying over `.cycles n`, rather
  than just N(Y)_n, retains exactly the cycle hypothesis needed for [y]-[0].

Searches made (2026-10-24):

- `msearch.py ... leanfinder "Surjectivity on normalized homology of the free abelian
  underlying simplicial map implies surjectivity on original simplicial abelian group
  homology"`: 8 hits, led by `groupHomology.chainsMap_f_map_epi`,
  `groupHomology.chains₁ToCoinvariantsKer_surjective`, `groupHomology.chainsMap_id_f_map_epi`
  and homology-projection epis. Their returned types concern group representations or
  chain maps under stronger hypotheses, not this evaluation square or normalized-cycle lift.
- `msearch.py ... loogle '"NormalizedMooreComplex", "surjective"'`: 0 hits.
- `msearch.py ... grep '(free|FreeAbelianGroup).*(surject|homology)|
  (surject|homology).*(free|FreeAbelianGroup)' AlgebraicTopology`: 0 hits.
- `msearch.py ... leansearch "Lift normalized cycles by subtracting the zero generator
  under free abelian evaluation"`: 8 hits, including `FreeAbelianGroup.lift_apply_of`,
  `FreeAbelianGroup.liftAddGroupHom`, lift-negation lemmas and zero-generator lemmas.
  These provide the free-group formula, not the simplicial normalized-cycle theorem.
- `rg -n 'normalizedMooreComplex|NormalizedMooreComplex'` in `lean/WeilConjectures`
  and `lean/Sheaf`: no matches at the initial read. A subsequent broader search
  `'normalizedMooreComplex|NormalizedMooreComplex|[Ff]ree.*[Ss]implicial'` finds the
  parent's docstring and Cech/semisimplicial free constructions. Read
  `Sheaf.AlgebraicTopology.SimplicialAbelianSetHomotopyQuasiIso`: it states the
  stronger-hypothesis homotopy-equivalence theorem for alternating complexes, not
  this fixed-degree transfer or its evaluation/cycle-lift clauses.
- `grep -rn 'lem-trf-free-normalized-homology-surjectivity-transfer'` in
  `lean/WeilConjectures`: no matches. Search of `dag/lean_names_upstream.json`
  for the normalization and new declaration names: no match.
- Read Mathlib's `MooreComplex.lean`, `Grp/Adjunctions.lean`, `FreeAbelianGroup.lean`
  and `ShortComplex/HomologicalComplex.lean` directly. These supply every construction
  required, so no missing-notion node, dependency repair or statement correction is needed.

Validation: `scompile.py Q51 lem-trf-free-normalized-homology-surjectivity-transfer <file>`
compiled both the sandbox module and the intended module path cleanly. The only theorem
has proof `sorry`; no definitions or ancillary theorems were added.

## Second reading by Q51

Self-check of the node and completed file, with no separate agent started as instructed;
the maintainer performs the independent delivery review. Re-read all clauses against the
file: X/Y and additive f are the declared functor-category objects and morphism; F and U
are the exact free/forget composites; the counit is evaluation; the normalization uses the
specified positive-face kernels and d_0. The first conjunct is the correct evaluation
square, the second includes both the exact [y]-[0] formula and its evaluation inside N(Y),
and the third is the same-degree surjectivity implication. The existential lift uses the
monic cycle and normalized-subgroup inclusions, so it neither drops normalization nor
asserts only an unspecified lift. All n are natural numbers, including zero. There is
no extra additive structure assumed for y↦[y]-[0], and no homotopy hypothesis on f.

The first compiler run exposed an unopened namespace for `whiskerLeft` and `whiskerRight`;
opened `CategoryTheory.Functor`. The next run was clean. Added the explicit public import
of `SimplicialObject.Basic` to match the dependency's recorded module directly. No
mathematical mismatch or statement fault was found; no disputed flag is needed.
