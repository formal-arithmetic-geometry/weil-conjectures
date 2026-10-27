## Worker report

Item: lem-sfb-etale-affine-pairs-test-quasiseparated.
Module: Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleAffinePairsQuasiSeparated.
Declaration: AlgebraicGeometry.AlgebraicSpace.isAbsolutelyQuasiSeparated_iff_etale_affine_pairs.
One theorem is stated, with its sole proof `by sorry`. No definitions or helper nodes are added.
The node copy changes only `lean`.

### Hypotheses and clauses

- An algebraic space over Spec Z is `(X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))`.
  The lifted integers retain the arbitrary scheme universe u; they do not restrict X to small schemes.
  AlgebraicSpace bundles the fppf sheaf, representable diagonal and existence of an atlas.
- Absolute quasi-separatedness is exactly the dependency's `IsAbsolutelyQuasiSeparated X`.
  The node's description by the absolute diagonal explains this established notion, rather than
  adding a hypothesis or requiring relative quasi-separatedness over an arbitrary base.
  Here the base is explicitly Spec Z, so every product in the proof is absolute.
- “If and only if” is the displayed `↔`.
- “For every pair of affine schemes U,V” is `∀ (U V : Over (Spec ...))`, followed by
  `IsAffine U.left → IsAffine V.left →`. Over Spec Z encodes the schemes and their unique
  absolute structure maps; it does not impose a further geometric hypothesis.
- The two maps to X are natural transformations
  `(a : yoneda.obj U ⟶ X.obj.obj) (b : yoneda.obj V ⟶ X.obj.obj)`.
  Their representable étaleness is `IsEtale a → IsEtale b →` using the recorded presheaf notion,
  which already includes representability. Neither map is required to be surjective.
- The sheaf fibre product U x_X V is specified by its underlying presheaf
  `Limits.pullback a b`. Representables are fppf sheaves, and limits of sheaves have the
  corresponding presheaf limits, so this is exactly the stated sheaf fibre product.
- Its being a quasi-compact scheme is
  `∃ P : Over (Spec ...), Nonempty (yoneda.obj P ≅ Limits.pullback a b) ∧ CompactSpace P.left`.
  The isomorphism specifies the representing scheme, rather than merely some compact scheme.
  Any two representing schemes are uniquely isomorphic by Yoneda, and compactness is invariant
  under scheme isomorphism. Thus existential representation imposes exactly compactness of
  U x_X V. It does not choose data from an unproved existence theorem.
- No quasi-compactness, separation, Noetherian or nonemptiness hypothesis on X appears.

### Dependency declarations read and used

- def-trf-algebraic-space: Sheaf.AlgebraicGeometry.AlgebraicSpace,
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace`,
  `IsRepresentableWith`, and `IsEtale`. Full definitions and docstrings read: IsEtale
  quantifies over scheme tests with actual representing pullback squares and Etale projections.
- def-sfb-space-absolute-quasi-separated:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated,
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`.
  Its body tests all affine Over S objects and compactness of the point space of the pullback.
- lem-trf-space-fibre-products-etale-covers:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers,
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
  The last theorem uses precisely an isomorphism between a representable presheaf and a pullback.
- def-pc-scheme and def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
  Affineness is Mathlib's `IsAffine` (Mathlib.AlgebraicGeometry.AffineScheme).
- def-weil-etale-morphism: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  `AlgebraicGeometry.Etale`, used inside the recorded representable IsEtale definition.
- def-weil-pbc-quasi-compact-scheme: Mathlib.Topology.Defs.Filter, `CompactSpace`.
  This notion requires no Hausdorff assumption.

Statement-dependency modules are public imports; already public mathematical types are not copied.
The plain proof imports cover the recorded plan: AlgebraicSpaceAffineEtaleCover,
SpaceQuasiCompactAffineTests, AlgebraicSpaceQuasiCompactFppfLocal,
ChartwiseEtalePermanence, and Mathlib's AffineScheme, Pullbacks, OpenImmersion,
Morphisms.Etale, Morphisms.QuasiSeparated, Morphisms.Basic, and
CategoryTheory.Limits.Shapes.Pullback.HasPullback (some already public for the statement).
These supply, respectively, the atlas and point-topology theorem; scheme-test and representable
comparison; descent; étale permanence; affine qcqs; fibre products of spectra; open-immersion
base change; étaleness of open immersions; qcqs permanence; locality; categorical pullbacks.
The declaration docstring contains all seven proof steps of the DAG, including the bridge from
scheme tests to quasi-compact space tests and the final verification of the affine-test definition.

### Sources and edge cases

Read literature/stacks-project/spaces-properties.tex, lemma-characterize-quasi-separated
(Tag 0AHR), including its reduction to Spec Z and its affine-open atlas argument.
Read decent-spaces.tex, lemma-locally-Noetherian-decent-quasi-separated (Tag 0BB6), whose proof
explicitly invokes the criterion for affine étale pairs. The Noetherian and decency assumptions
in that subsequent application do not belong to this criterion.

Checked before writing: empty X and empty affine charts are allowed and their fibre product is
empty, hence quasi-compact. No nonempty ring or chart assumption is used. Infinite disjoint affine
atlases are allowed: locality on the target does not require a finite atlas. For scheme X this
specializes to the usual criterion by intersections of affine open charts. Gluing two affine
schemes along a non-quasi-compact open produces a non-quasi-separated scheme; its two affine
open étale charts violate precisely the right-hand condition. The doubled affine line remains
allowed and is quasi-separated despite being nonseparated. Arbitrary non-Noetherian affine
schemes remain allowed. All tests and representing schemes use the same arbitrary universe u.

No statement correction, dependency repair, or STATEMENT-DISPUTED flag is needed.

### Searches

Read the withdrawn example Sheaf/CategoryTheory/CompactObject.lean and its node; the recorded
upstream WeilConjectures/CategoryTheory/CompactObject.lean supplies the current full example.
Searched Mathlib and both project roots before writing. No existing theorem gives this criterion.
The actual msearch query/result records follow (also retained in searches.jsonl):

- grep: `AlgebraicSpace|quasiSeparated.*etale|etale.*quasiSeparated`: 0 hits; no match.
- loogle: `"AlgebraicSpace", "QuasiCompact"`: 0 hits; no match.
- leanfinder: `An algebraic space is absolutely quasi separated if and only if fibre products of every pair of affine etale scheme charts are quasi compact`: 8 hits; only scheme quasi-separatedness and diagonal/intersection lemmas, not this algebraic-space criterion.
- leansearch: `An algebraic space is quasi separated exactly when all fibre products of pairs of affine etale charts are quasi compact`: 8 hits; only scheme quasi-separatedness and diagonal/intersection lemmas, not this algebraic-space criterion.

- rg on lean/WeilConjectures and lean/Sheaf for IsAbsolutelyQuasiSeparated,
  quasiSeparated.*etale, etale.*quasiSeparated and the node id: the existing definition,
  its consumers and a proof-docstring citation, but no statement of this equivalence.
- grep -rn for the node id in lean/WeilConjectures: no match.
- rg for etale_affine_pairs, quasiSeparated_iff.*affine and AbsolutelyQuasiSeparated.*iff
  in both project roots and dag/lean_names_upstream.json: no matching declaration name.

### Validation

The module compiled through the prescribed scompile.py against the live server library,
in both sandbox and library mode, without errors or warnings. No local/global build was run.
The final delivery is additionally validated by deliver2.py --no-push.

## Second reading by Q02

Self-check only: this dispatcher-started worker was instructed not to start another agent;
the maintainer's independent delivery review remains the independent second reading.
I reopened the node and signature: the base is Spec Z with universe lift; both source schemes
are affine; both maps are representable étale without surjectivity; the conclusion is compactness
of the scheme representing their actual fibre product; the equivalence uses exactly the recorded
absolute affine-test notion. The isomorphism witness does not weaken the conclusion to the
existence of an unrelated compact scheme. The diagonal language is the node's explanation of
absolute quasi-separatedness; the seven-step proof checks that explanation directly. No mismatch
or statement change was found. All variables and the universe are explicit; no file-local notation,
private definition, extra hypothesis or hidden choice is introduced.
