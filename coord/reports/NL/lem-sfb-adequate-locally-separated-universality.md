## Worker report

The module `Sheaf.AlgebraicGeometry.AdequateLocallySeparatedUniversality` states
`CategoryTheory.adequateModuliSpace_universal_schemes_separatedSpaces`. Its only theorem
has proof `sorry`. No definitions, helper theorems, or dependency repairs are introduced.
The source was read online: Alper, arXiv:1005.2398v3,
https://arxiv.org/pdf/1005.2398v3, §2 printed p.7, Proposition 7.1.1 and Theorem 7.2.1
printed pp.35–37. The source's diagonal convention requires the correction below.

Hypothesis and conclusion correspondence:

- The field is `{k : Type u} [Field k]`, using Mathlib `Field`, whose full definition
  and docstring in `Mathlib.Algebra.Field.Defs` were read (line 180).
- The algebraic stack over k is `F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k)))`
  with `hF : IsAlgebraicModuliStack F`. This retains the full fibred category and
  its automorphisms, with a smooth surjective atlas, without imposing DM or finite type.
- The space Y is `Y : AlgebraicSpace (Spec (CommRingCat.of k))`; the map is the actual
  `φ : BasedFunctor F (discreteModuli Y.obj.obj)`.
- Adequacy is exactly `hφ : IsAdequateModuliSpace F hF Y φ`. It includes qcqs,
  the canonical structure-sheaf isomorphism, and power lifting on every affine
  étale base change; none is replaced by a stronger cohomological condition.
- The corrected absolute-diagonal assumption on X is `hFdiag`. It quantifies over
  every scheme T and map t to the actual self 2-fibre product of the structural
  morphism. `HasSpaceBaseChange (moduliRelativeDiagonal (moduliBaseStructure F))`
  supplies an algebraic-space presentation with its specified projection p;
  `MapIsQuasiCompact p ∧ MapToSchemeIsSeparated Z T p` imposes precisely the
  two properties of that projection. This tests the absolute diagonal, not the
  relative diagonal of φ, and does not require it to be scheme-representable.
- The corrected assumption on Y is `hYdiag`, quasi-compactness of the actual absolute
  diagonal `prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj)`. A space diagonal is a representable
  monomorphism, so it is separated automatically; no hollow separatedness premise
  is introduced.
- The first conjunct quantifies over every `T : Over (Spec (CommRingCat.of k))`,
  with no separatedness, quasi-compactness, quasi-separatedness, or finite-type
  restriction on T, and every `h : BasedFunctor F (discreteModuli (yoneda.obj T))`.
- Its `∃! g : Y.obj.obj ⟶ yoneda.obj T` is unique factorization through Y. The equation
  is `Nonempty (ModuliTwoIso (φ.comp (discreteModuliMap g)) h)`. Because the targets
  are discrete fibred groupoids, this expresses equality of stack morphism classes
  up to 2-isomorphism. Natural transformations from the space sheaf to the
  representable presheaf are exactly the scheme-target k-morphisms.
- The second conjunct quantifies over every algebraic space T/k, assuming exactly
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)` for its absolute
  diagonal. This is the closed-immersion diagonal hypothesis, tested on schemes.
  It then asserts the same unique factorization for each actual map h to T.
- Thus both clauses express the canonical precomposition bijection on morphism
  classes, including its injectivity and surjectivity. There is no conclusion
  for arbitrary nonseparated algebraic spaces.

Dependency declarations used (their source signatures and docstrings were read):

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field, a Mathlib leaf).
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`:
  `CategoryTheory.IsAdequateModuliSpace` (def-sfb-adequate-moduli-space).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith` (def-trf-algebraic-space).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, provided by the adequate-space dependency.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `CategoryTheory.ModuliTwoIso`,
  `discreteModuli`, `discreteModuliMap`, `moduliTwoFiberProduct`, `HasSpaceBaseChange`
  (def-sfb-stable-pointed-moduli-groupoids, now cited directly).
- `Sheaf.AlgebraicGeometry.RelativeModuliInertia`: `CategoryTheory.moduliBaseStructure`
  (def-sfb-relative-moduli-inertia, now cited directly).
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.moduliRelativeDiagonal` (def-sfb-dm-stack-morphism-properties,
  now cited directly). This definition is general for based categories, despite
  the module's name; no DM assumption is introduced.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsQuasiCompact`, `MapToSchemeIsSeparated`
  (def-sfb-proper-curve-moduli, now cited directly).
- The sole already-stated separate proof dependency is imported nonpublicly:
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`,
  `AlgebraicGeometry.IsImmersion.instDiagonalScheme` (lem-weil-pbc-diagonal-immersion).
  Its complete signature and docstring were checked around line 198.
  The three other proof lemmas have no Lean records or Mathlib matches, so there
  are no modules to import for them. They are named in the five-step proof docstring.
  The adequate-space proof dependency is already a public statement import.

Edge cases checked: empty stack/space/scheme targets, identity adequate maps,
nonreduced sources, nonseparated scheme targets (including doubled origins), arbitrary
characteristic including positive characteristic, and general non-DM stacks. Existence
of an h into an empty target is handled by the quantified h; it is not assumed.
Neither target clause assumes nonemptiness or finite type. The base site's scheme
universe is u; F has independent explicit morphism/object universes v,w, and there
are no auto-bound variables or extra universe equalities. The target diagonal is
closed only in the second conjunct. The source diagonal is not required closed,
finite, unramified, or affine. No counterexample to the corrected statement was found.

Searches actually made:

- `msearch.py leanfinder`, query “An adequate moduli space is universal for morphisms
  to schemes and separated algebraic spaces”: eight hits, all scheme morphism
  properties (`IsProper`, `IsSeparated`, `IsPreimmersion`, etc.); none is this theorem.
- `msearch.py leansearch`, query “Adequate moduli spaces are universal for morphisms
  to schemes and separated algebraic spaces”: eight hits, properness, integral maps,
  quasi-separatedness and universal closedness for schemes; no adequate-moduli theorem.
- `msearch.py loogle`, query `"BasedFunctor", "discreteModuli"`: zero hits.
- `msearch.py grep`, query `adequateModuli|IsAdequateModuli|adequate_moduli`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for adequate-moduli names and the proposed declaration: no existing theorem;
  the project has the adequate-moduli definition, which is used unchanged.
- `rg` for the item id in `lean/WeilConjectures`: no hits. Searches for
  `discreteModuli`, `ModuliTwoIso`, diagonal, separatedness, and quasi-compactness
  in the project's stack and space modules found the reused interfaces above.
- A full JSON scan of `dag/nodes` for the item in stmt_deps or proof_deps found
  exactly the one citer listed below; text-only matches in blueprint provenance
  were excluded from this dependency audit.

Validation: `scompile.py NL lem-sfb-adequate-locally-separated-universality` compiled
both the sandbox module (10.0 s) and its library-path version (11.4 s), with no errors
or warnings. The theorem proof is deliberately postponed. No global build or direct
repository mutation was run.

## Statement corrected

The old statement is preserved verbatim in `statement_change.old_statement`. It
asserted universality for arbitrary adequate moduli spaces of algebraic stacks in
this project's general sense, without mentioning absolute diagonal properties.
Alper §2 explicitly works with quasi-compact separated diagonals. This convention
is absent from `IsAlgebraicModuliStack` and `IsAdequateModuliSpace`, and is now explicit
in lem-sfb-adequate-geometric-fibres-submersion. The corrected statement adds this
source convention to X and Y. In the space case only quasi-compactness is a substantive
assumption, since its representable monomorphic diagonal is automatically separated.
No scheme-target case is dropped, and no target is required to be finite type.

The corrected statement cites four already-landed definition nodes for the actual
structural morphism, scheme-test diagonal, and properties used in these hypotheses.
Their records and statements were read; no node or declaration is duplicated. The
proof's first step now explicitly invokes the source convention. `old_stmt_deps`
and `old_proof` preserve the original fields; proof_deps is unchanged.

Citer audit (every node with a direct statement/proof dependency on this item):

- `lem-sfb-affine-pgl-finite-stabilizer-quotient`: holds. Its quotient stack has
  affine diagonal; its invariant spectrum Y is affine; the comparison coarse space
  Q has finite diagonal. Thus the two adequate maps compared in proof step 5 satisfy
  the explicit diagonal convention. Its statement and proof remain valid, and the
  citer is not edited.

This item is a supporting lemma, not the blueprint unit's statement. The correction
therefore changes no unit statement. There are no new nodes or dependency modules.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
