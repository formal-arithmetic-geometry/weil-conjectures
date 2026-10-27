## Worker report

States `AlgebraicGeometry.AlgebraicSpace.exists_closed_relation_schematic_neighbourhood`
in `Sheaf.AlgebraicGeometry.ClosedRelationSchematicNeighbourhood`. The sole theorem has
proof `by sorry`; no definition, auxiliary axiom, or additional theorem is introduced.
The node is unchanged except for `lean`. No statement correction or dependency repair
is needed.

Source read: `literature/stacks-project/spaces-morphisms.tex`, Tag 03XX,
`proposition-locally-quasi-finite-separated-over-scheme`, especially the paragraph
beginning “Let (U, R, s, t, c)” and the final paragraph (local lines 10651–10701).
The module docstring describes the representation choices; the theorem docstring
contains all six proof steps with their DAG dependencies.

Hypothesis correspondence:

- The arbitrary scheme S is `{S : Scheme.{u}}`; T is `T : Over S`, with
  `[IsAffine T.left]`. Objects and maps over S use the recorded scheme category
  and its slice, retaining every scheme in the project's size convention.
- The algebraic space is `X : AlgebraicSpace S`; the morphism over T is the actual
  natural transformation `f : X.obj.obj ⟶ yoneda.obj T`.
- The chartwise locally quasi-finite hypothesis is `hlocal`, quantified over every
  `H : Over S`, representable étale chart `v`, and structure morphism `c` whose
  Yoneda image is `v ≫ f`. The predicate is the recorded
  `Scheme.Hom.IsLocallyQuasiFinite`, including Stacks' finite-type requirement.
- The closed relative diagonal is `hdiag`: `IsRepresentableWith` of
  `IsClosedImmersion m.left` applied to `Limits.pullback.diagonal f`. This tests
  the actual relative diagonal against every scheme.
- The affine atlas and affine relation are `U R : Over S` with their two
  `IsAffine` instances. Its map is `p`, with `hp : IsEtale p` and
  `hpsur : IsSurjective p`, both using the recorded representable scheme-test
  predicates.
- `b` and `hb` specify the atlas composite to T. The projections are `s t`;
  `hR : IsPullback (yoneda.map s) (yoneda.map t) p p` says that R represents the
  kernel pair, including its maps, rather than an unrelated relation.
- `j`, `hjs`, `hjt` specify the relation map into the actual scheme fibre product
  `Limits.pullback b b`, and `hj` says that its underlying scheme map is closed.
- The quotient identification with X is `η`, `hηp`, `hη`: the presheaf
  coequalizer maps to X, its composite with the quotient map is p, and composition
  with η is bijective on maps to every fppf sheaf. This is exactly sheafification's
  universal property from def-weil-pbc-sheafification. The sectionwise coequalizer
  is H mapped to U(H)/R(H), because hR specifies the kernel equivalence relation.
  This does not assume a global small-valued sheafification functor on the big site.
- The chosen point is `u₀ : U.left`. Its image q is `b.left u₀` and its image x
  in X is `schemePointMap p u₀`.

Conclusion correspondence:

- `T'`, `a`, `q'` give an affine scheme over S, an étale map to T, and a point
  satisfying `a.left q' = b.left u₀`. `IsIso (a.left.residueFieldMap q')`
  expresses that the *induced* residue-field map is an isomorphism, not merely
  that the fields admit an unrelated isomorphism.
- `U' A`, `g gA` are the two induced open subschemes of `U ×_T T'`.
  Both inclusions are open immersions and their underlying images satisfy
  `IsCompl`. Complementary open images are also closed; open immersions retain
  exactly the induced scheme structures. This is the stated clopen disjoint
  union, expressed without selecting arbitrary coproduct isomorphisms.
- `u' : U'.left` belongs to U' by its type. Its two projection equations give
  its images u₀ and q'. `IsFinite (g ≫ Limits.pullback.snd b a).left`
  gives finiteness over T'; `IsAffine U'.left` gives the requested affineness.
- `R' B`, `k kB`, their open-immersion clauses and complementary image sets
  give the second clopen decomposition in `R ×_T T'`, whose structure map is
  `s ≫ b`. The two structure maps `s ≫ b`, `t ≫ b` agree from hR and hb.
  `IsFinite (k ≫ Limits.pullback.snd (s ≫ b) a).left` and
  `IsAffine R'.left` give its finiteness over T' and affineness.
- `s' t'` are the restricted projections. Their compatibility equations identify
  them with s and t on the U coordinate; the next equation identifies the common
  T' coordinate of k with that of s'. The kernel-pair clause below identifies
  the T' coordinate for t' as well.
- `s'.left.IsFiniteLocallyFree`, `t'.left.IsFiniteLocallyFree` and the two
  `Etale` clauses are precisely the two requested finite locally free étale maps.
- `Q`, `c : Q ⟶ T'`, `IsAffine Q.left` give the affine T'-scheme quotient.
  `e : U' ⟶ Q` is its quotient map, with `e ≫ c = g ≫ pullback.snd b a`.
- `z : yoneda.obj Q ⟶ Limits.pullback f (yoneda.map a)` is the canonical map
  into X_T'. Its two projection equations identify the composite with the
  restricted atlas and with c. These equations and the sheaf quotient property
  determine z: no arbitrary map replaces the canonical quotient comparison.
- `IsPullback (yoneda.map s') (yoneda.map t') (yoneda.map e ≫ z)
  (yoneda.map e ≫ z)` says R' is the *full* restricted relation of the atlas
  in X_T'. With the coordinate equations this identifies its inclusion into
  R_T' with the full restriction along g, including scheme structure.
- The explicit `Presheaf.IsSheaf` clause and `η'` with its quotient-map equation
  and universal hom-set bijections say that h_Q is the fppf sheaf quotient U'/R'.
  As for η, these bijections use the universal property of sheafification on
  the presheaf coequalizer rather than imposing a global sheafification instance.
- `IsRepresentableWith (fun _ _ m ↦ IsOpenImmersion m.left) z` identifies h_Q
  with an open subspace V' of X_T'. An explicit name for that image is unnecessary;
  z itself specifies the inclusion and identifies its domain with V'.
- `W : OpenSubspace X` uses the recorded open-subfunctor definition. The scheme
  `Z : Over S` and isomorphism `eW : yoneda.obj Z ≅ W.val.toFunctor` represent W.
- Equality between the two `Set.range (schemePointMap ...)` sets is exactly
  equality of the image of |V'| in |X| and |W|. Both sides live in the recorded
  `Point X.obj.obj`, the quotient of field-valued representatives; they are not
  an equality of atlas point sets or of raw sections over a selected field.
- The final membership is `schemePointMap p u₀ ∈ Set.range (...)`, namely x∈|W|.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, `IsRepresentableWith`; their full scheme-test definitions.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite` and its `IsQuasiFiniteAtPoint` definition.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `sheafificationAdjunction`, the universal property used by η and η'.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, its
  `fppfPrecoverage`, and the over-site exposed by the algebraic-space module.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`; the latter is used directly.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree` (finite, flat, locally finitely presented).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`,
  `PointRepresentative.Rel`, `schemePointMap`; the actual quotient construction
  and residue-field definition of the last map were read.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `Limits.pullback`, its projections and pullback squares.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.

Every stated proof dependency's module is imported, using plain imports when
used only by the proof. The Mathlib permanence leaves are supplied by Finite,
Affine, Proper and Etale. The atlas-presentation, finite-restriction,
finite-flat-quotient, fibre-product, relation-finding-opens, and quasi-affine-image
modules were read and are imported under their recorded paths.

Edge cases checked before writing: empty U has no u₀, so the pointwise theorem
has no nonvacuity assumption; empty complementary pieces A and B are permitted
by IsCompl; the chosen U' is nonempty through u', while other relation components
need not be nonempty by fiat. A nonclosed point u₀ is allowed: only residue fields
and the existing point-class quotient are used. No algebraically closed field,
Noetherian, finite-presentation hypothesis on X→T, or quasi-compactness hypothesis
on X is added. Arbitrary characteristic and all schemes in universe u remain
allowed. When the relation is the diagonal, the quotient and restricted open can
be the corresponding identity pieces. A residue-field extension at u' does not
change the class of the original point. No extra compactness conclusion for W
from the stronger proof-dependency interface is included.

Searches actually run:

- `msearch.py`, leanfinder: “A finite clopen restriction of a closed affine etale
  equivalence relation has an affine quotient open in the base changed algebraic
  space and a schematic image neighbourhood”. Eight hits, including
  `ExistsHomHomCompEqCompAux.h𝒰S`, `reduce_to_affine_nbhd`, `Scheme.Etale`, and
  affine-open lemmas; none states this result.
- `msearch.py`, loogle: `"Etale", "quotient"`. Six ring-theoretic quotient hits
  in FormallyEtale and StandardEtalePair; no algebraic-space neighbourhood theorem.
- `msearch.py`, grep: `AlgebraicSpace|schematic.*neighbou|(etale|étale).*(relation|quotient)`.
  Three StandardEtale.lean documentation hits; no match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for schematic neighbourhoods,
  closed relations and restricted-relation neighbourhoods found the recorded
  ProperEtaleRelationFiniteNeighbourhood and the downstream representability
  assembly, not this complete statement. `grep -rn` for the exact item id in
  WeilConjectures returned no hits. Exact name/module checks in these two trees
  and `dag/lean_names_upstream.json` returned no pre-existing declaration.

Validation: scompile.py compiled both the sandbox and final library module
cleanly, with no errors or warnings. An initial compile resolved bare `pullback`
to the algebraic-space module's module-pullback functor; all categorical pullbacks
were then qualified as `Limits.pullback`. The final source has no probes or local
notation and every line is at most 100 characters. The theorem signature in the
node record is extracted verbatim from the delivered file.

## Second reading by Q123

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
