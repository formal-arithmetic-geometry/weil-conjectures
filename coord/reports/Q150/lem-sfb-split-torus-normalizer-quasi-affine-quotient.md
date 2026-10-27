## Worker report

Item: `lem-sfb-split-torus-normalizer-quasi-affine-quotient` (Q150, stage 2).
The module is `Sheaf.AlgebraicGeometry.SplitTorusNormalizerQuasiAffineQuotient`.
It constructs the normalizer on test schemes, the right-coset relation and presheaf,
the fppf quotient sheaf, and its canonical map; its sole theorem is
`AlgebraicGeometry.exists_smooth_quasiAffine_splitTorusNormalizer_quotient`, with `sorry`.
All six helper definitions belong to notions explicitly introduced in this item's
statement; no independent notion, new node, or dependency repair is needed.

Hypothesis and clause correspondence:

- Any base scheme S: `{S : Scheme.{u}}`; there is no nonemptiness, field,
  Noetherian or connectedness binder.
- A group scheme over S: `G : Grp (Over S)` (and similarly `T`). This is the
  bundled internal group object with multiplication, identity, inverse and group laws.
  Its scheme is `G.X.left` and its structure map is `G.X.hom`.
- Smooth and affine: `[Smooth G.X.hom] [IsAffineHom G.X.hom]`.
- Finite presentation in the stipulated sense:
  `[LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
  [QuasiSeparated G.X.hom]`. All three clauses are visible, even though affine
  and smooth imply the latter properties in this situation.
- Integer rank r >= 0: `(r : ℕ)` includes zero.
- Closed subgroup T in G: `(i : T ⟶ G)` is a group-object homomorphism and
  `[IsClosedImmersion i.hom.hom.left]` is its scheme-level closed immersion.
- Identification with the split multiplicative torus of rank r:
  `hT : Nonempty (yonedaGrpObj T.X ≅ relativeSplitTorusFunctor S r)`.
  The recorded `relativeSplitTorusFunctor` is the product over `Fin r` of the
  units of global functions, with their group laws and pullback restrictions.
  Thus this is an isomorphism of group-valued functors, including their naturality,
  not a bijection on geometric points or an assumption of maximality.
- G(W) = Hom_S(W,G) is the Hom group `(W ⟶ G.X)`, with the internal group
  object's group law; `(yonedaGrpObj G.X).map f.op` is restriction along f.
- N(W) is `torusNormalizerSections i W`. The intersection ranges over EVERY
  `V : Over S` and EVERY `f : V ⟶ W`. For each it takes the inverse image under
  restriction of `Subgroup.normalizer (Set.range (fun t : V ⟶ T.X ↦ t ≫ i.hom.hom))`.
  Mathlib's set normalizer is exactly the group of elements conjugating that set
  onto itself. Closed immersion makes the image T(V) the subgroup functor T in G.
  In particular, infinitesimal and nonreduced test schemes are included.
- `torusNormalizerSubfunctor i` is the supremum of all subfunctors with sections
  in these explicit subgroups. This is an exact construction: if n is a section
  over W satisfying the all-tests condition, then each restriction f*n satisfies
  the same condition because further tests compose with f. The image of the
  Yoneda map determined by n is consequently one of the subfunctors in the
  supremum, so n belongs to it. Conversely every subfunctor included in that
  supremum has sections in N. Thus its sections are exactly N(W), with the
  inherited restrictions, and there is no extra stability assumption or omitted
  section. This is real lattice data, independent of any postponed theorem.
- `torusNormalizerCosetRelation i` is the inverse image of this subfunctor under
  `yoneda.map ((fst G.X G.X)⁻¹ * snd G.X G.X)`. The product in `Over S` is the
  scheme fibre product. On sections this says g inverse*h belongs to N(W),
  equivalently h belongs to gN(W). These are precisely the cosets of the action
  a.g = g*a inverse used by the node, rather than a quotient group (N need not
  be normal in G).
- `torusNormalizerCosetPresheaf i` is the coequalizer of that relation's two
  projections. Colimits of presheaves are pointwise. Since N(W) is an actual
  subgroup, the displayed relation is already an equivalence relation, and its
  coequalizer is the set G(W)/N(W); the coequalizer construction supplies its
  restriction maps and canonical projection without arbitrary choices.
- The topology is the recorded `Scheme.fppfTopology.over S` on `Over S`.
  `torusNormalizerQuotientSheaf i` is literally `presheafToSheaf` of the coset
  presheaf, after `uliftFunctor.{u+1,u}`. The test objects and maps are unchanged;
  the value lift is bijective on every section and permits sheafification on this
  large site. It imposes no equality of object and section universes.
- Represented by an S-scheme X: the conclusion quantifies `(X : Over S)` and an
  isomorphism `e : yoneda.obj X ⋙ uliftFunctor.{u+1,u} ≅
  (torusNormalizerQuotientSheaf i).obj`. Thus representation is on ALL test
  S-schemes. Being sheaf is inherited through this isomorphism.
- X to S smooth and quasi-affine: `Smooth X.hom ∧ IsQuasiAffineHom X.hom`, using
  the dependency's relative quasi-affine predicate, not just absolute
  quasi-affineness of X or a weaker separatedness conclusion.
- The map G to X is an S-morphism `(q : G.X ⟶ X)` and has
  `Smooth q.left ∧ Surjective q.left`.
- Its CANONICAL nature is retained: `torusNormalizerQuotientMap i` is the
  coequalizer projection followed by `toSheafify`. The final equality
  `Functor.whiskerRight (yoneda.map q) uliftFunctor ≫ e.hom =
  torusNormalizerQuotientMap i` identifies q with precisely this map, so the
  smooth surjection cannot be an unrelated map.
- There are no reductivity, connectedness or maximality hypotheses.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- The convention node `def-weil-pbc-scheme-conventions` has no declaration;
  its finite-presentation convention is rendered with the three existing classes.
  `QuasiCompact` and `QuasiSeparated` are the recorded Mathlib classes in the
  respective `Morphisms.QuasiCompact` and `Morphisms.QuasiSeparated` modules.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.RelativeTorus`:
  `AlgebraicGeometry.relativeSplitTorusFunctor`, and its documentation for
  `AlgebraicGeometry.IsRelativeTorus`. The split identification, which is the
  dependency's M_(S,r), is used directly rather than imposing merely local splitness.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; the cartesian structure of
  `Over S` supplies these fibre products as its tensor products.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over`:
  `GrothendieckTopology.over`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, `sheafificationAdjunction`; concrete sheafification gives the
  instances for lifted sets.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`:
  `AlgebraicGeometry.IsQuasiAffineHom` (preimages of affine opens are quasi-affine),
  and proof dependency `Scheme.IsQuasiAffine.of_locallyQuasiFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
  `AlgebraicGeometry.Surjective` (surjectivity on underlying scheme points).
- Structural APIs: `CategoryTheory.Grp`, `GrpObj`, `yonedaGrpObj`,
  `CartesianMonoidalCategory.fst` and `.snd`, the scoped group law on Hom,
  `Subgroup.normalizer`, `.comap`, `Subfunctor` and `.preimage`, and the
  presheaf `coequalizer` and `.π`. These are existing Mathlib definitions.

Already stated proof dependencies are imported privately: free flat group-space
quotients (`AlgebraicSpace.free_flat_groupSpace_quotient`); represented scheme spaces
(`AlgebraicSpace.schemeSpace`); the separated locally quasi-finite schemehood
criterion (`AlgebraicSpace.exists_scheme_of_separated_locally_quasi_finite`);
`locallyOfFiniteType_of_flat_lfp_source`; `Smooth.of_comp_of_flat_of_surjective`;
`Smooth.flat_and_locallyOfFinitePresentation`; finite-type cancellation, relative
gluing and directed affine covers, fibre-product restriction, and etale calculus.
Proof dependencies with no Lean declaration or Mathlib match are documented in the
eight-step proof docstring and are not fabricated as imports. No import cycle is
introduced. The proof is postponed in its entirety.

Source verification: read Conrad's cited PDF online at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Theorem 2.3.1 on printed
p.67, its proof on pp.68-71, and Remark 2.3.5 on p.71. The theorem covers arbitrary
multiplicative-type subgroups, hence the specified split torus, with no maximality
or reductivity assumption. Its relative quasi-affine convention is given in
Remark 2.3.2. The additional finite-presentation hypothesis in this DAG node has
been retained exactly. No correction to the node statement is required.

Edge cases checked mathematically before finalizing the statement:

- r = 0: the finite product is the trivial group; all sections normalize T;
  N = G and the quotient sheaf is terminal, represented by S. Its canonical map
  is the given smooth structure map, surjective because of the group unit.
- Empty S: every S-scheme is empty, all Hom groups and cosets are singleton,
  and X is the empty scheme; smoothness and surjectivity cause no excluded case.
- Nonmaximal and central T: the normalizer can be all of G, again giving S.
- Nonconnected G and arbitrary non-Noetherian S: neither is restricted by a
  binder or by the test category; the proof works locally and glues.
- Positive characteristic and nonreduced tests: no invertibility or reducedness
  condition appears in the normalizer or torus functor. The proof's torsion
  reduction explicitly includes noninvertible torsion orders.
- Right-coset orientation: g inverse*h in N gives h = gn; this is the same orbit
  relation as g maps to ga inverse because N is closed under inversion.

Searches for existing statements/notions:

1. `msearch.py ... leanfinder "The fppf quotient of a smooth affine group scheme
   by the normalizer of a split torus is represented by a smooth quasi-affine
   scheme"`: eight hits, including `Scheme.IsQuasiAffine`, the affine-to-quasi-affine
   instance, a Galois-category quotient lemma, and affine transition-limit facts;
   none states this group-scheme quotient theorem.
2. `msearch.py ... loogle '"normalizer", "Scheme"'`: zero hits.
3. `msearch.py ... grep 'normalizer|torus|reductive' AlgebraicGeometry`: zero hits.
4. `rg` of `lean/WeilConjectures` for the exact item id, and of
   `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for all
   seven proposed declaration names: no existing declaration.
5. Broader `rg` of the project and Mathlib for normalizers, quotient presheaves,
   group schemes and split tori found `RankOneRoots.normalizer`. Its signature
   is restricted to rational points over a field with algebra scalar-extension
   tests, not the relative functor on arbitrary schemes; it cannot serve here.
   The relative split torus was found and reused from the recorded dependency.
6. Mathlib searches for presheaf quotients and subfunctors found the existing
   `Subfunctor` lattice/preimage and functor-category coequalizers; these are reused
   for the constructions. `Subgroup.normalizer` and its conjugation-image
   characterization were read in `Algebra.Group.Subgroup.Defs` and `.Basic`.

No STATEMENT-DISPUTED finding, statement correction, new node or dependency repair.

## Second reading by Q150

The assigned worker reread the node and the complete module after construction;
the independent delivery review remains the maintainer's responsibility, as in
this dispatch. In this rereading the base is unrestricted, finite presentation has
all three clauses, the split-torus identification is natural and group-valued,
and the normalizer tests every map V to W. The supremum subfunctor does not lose
sections: the restrictions of each normalizing section themselves generate an
admissible subfunctor, as explained above. The inverse-image relation has the
correct coset orientation, and its coequalizer is pointwise. The sheafification
uses the actual fppf over-topology and a common value-universe lift. The
representing isomorphism and final equality retain the canonical map, and both
smoothness conclusions plus relative quasi-affineness and point surjectivity
are separate explicit conjuncts. No mathematical mismatch or node-field change
was needed. An initially mistyped Mathlib import path was corrected from
`Mathlib.GroupTheory.Subgroup.Basic` to `Mathlib.Algebra.Group.Subgroup.Basic`.

## Validation

`scompile.py` passed on the server: the sandbox compilation took 39.3 seconds and
the module-path compilation took 2.5 seconds, with no errors or warnings.
`deliver2.py --no-push` printed `OK (dry run): commit e48514a1353 passes the
preflight and compiles; nothing pushed`. The node differs from its read-only base
only in `lean`; its recorded theorem signature is verbatim, all source lines are
at most 100 columns, all variables/universes are explicit, and the sole `sorry`
is the main theorem. Only the prescribed `scompile.py` and `deliver2.py` wrappers
were used; no shared source or git state was edited directly.
