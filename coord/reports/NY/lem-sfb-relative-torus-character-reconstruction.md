## Worker report

This delivery states `AlgebraicGeometry.RelativeCharacter.reconstruction`, with the only
postponed proof `:= by sorry`. Its conclusion is `Nonempty Reconstruction`, whose `data`
contains the equivalence, actual section and point equivalences and natural base-change
isomorphisms. Its `valid` field imposes every equation and geometric property below.
No construction is selected from this theorem, and all definitions have real data.
The original item statement is unchanged.

Clause-by-clause correspondence (names in namespace `AlgebraicGeometry.RelativeCharacter`):

- Arbitrary scheme S: every construction and every assertion binds `S : Scheme.{u}`;
  `Reconstruction` packages all bases at once so that arbitrary base-change laws can be
  stated. The single universe u is the existing Scheme universe. Coefficient groups live
  in u+1, as required by the recorded ordinary inverse image.
- Small etale abelian sheaves: `Sheaf S.smallEtaleTopology AddCommGrpCat.{u+1}`.
- Lattice, locally Z^r with finite variable rank: `free S r` uses the recorded
  `constantSheaf` on `ULift (Fin r → ℤ)`; `IsLattice` gives an etale jointly surjective
  family U i and ranks r i with ordinary inverse-image isomorphisms. `Lattice S` is the
  full subcategory, so its morphisms are all additive sheaf maps.
- Multiplicative group: `RelativeSplitTorus.model S 1` is the existing integral Laurent
  Hopf model base-changed to S. All higher split ranks use its `model S r`. Its coordinate
  is the recorded Laurent coordinate. No second Laurent model is defined.
- Commutative group scheme and fppf torus: `Torus S` is the full subcategory of
  `CommGrp (Over S)` satisfying the landed `IsRelativeTorus P.X`. Its group laws are
  Mathlib's group-object diagrams; the predicate is an fppf covering with variable finite
  ranks and isomorphisms to the units functor, equivalent to the displayed Laurent model.
- Character sections: `Characters P T` is the group of group-scheme maps from the
  actual `change T.hom` of P to the rank-one model. `Data.characters` is an additive
  equivalence from `X E P` on each etale U to these characters. `characters_restrict`
  uses `characterChange`, defined by canonical pullback and split-model comparisons;
  `characters_map` is exactly precomposition with the pulled-back group map.
- Contravariant equivalence: `Data.equivalence S : (Torus S)ᵒᵖ ≌ Lattice S` includes
  functors on all morphisms, natural unit/counit isomorphisms and triangle identities.
  `X E P` and `D E M` are the underlying objects of its functor and inverse.
- Representing quasi-inverse on every S-scheme T: `Data.represent` is an additive
  equivalence between `Additive (T ⟶ (D E M).X)` and the actual Hom group
  `(Etale.upperStar AddCommGrpCat T.hom).obj M.obj ⟶ T.left.gmSheaf`.
  `represent_restrict` gives naturality on EVERY map of test schemes, using the ordinary
  upper-star composition isomorphism and the canonical units comparison in
  `functionalChange`. `represent_map` gives precomposition with every lattice map.
  This is representability as a group functor, with its group law pinned, rather than
  a bare existential bijection or an unrelated equivalence of categories.
- Natural evaluation identifications: `counit_evaluation` says the inverse counit sends
  m to the character x ↦ h_x(m); `unit_evaluation` says the inverse opposite-unit sends
  x to the functional chi ↦ chi(x). Both equations are tested on every etale U and
  every U-point. `value` evaluates the Laurent coordinate, and `functionalValue` uses
  the existing units sheaf, so these are equalities of the actual global functions.
  Equality after forgetting a unit to its value detects equality of units. These tests
  characterize the sheaf/group morphisms: restrict to all etale V over U and use Yoneda.
- Arbitrary scheme base change: `Stable` states stability as part of the conclusion;
  it is never an extra hypothesis. `torusPull` is actual group-object pullback and
  `latticePull` is the recorded ordinary inverse image. `Data.character_baseChange`
  and `Data.dual_baseChange` are natural isomorphisms of these functors.
  `character_baseChange_evaluation` pins the character comparison to pullback of
  characters, tested against every pulled-back point and every local section pulled
  from U. Such pulled sections locally generate inverse image. `baseChange_mate`
  pins the dual comparison to its canonical counit mate, giving compatibility of both
  evaluation identifications. `character_baseChange_id` and
  `character_baseChange_comp` explicitly impose identity and successive-base-change
  coherence, using the existing `Over.pullbackId`, `Over.pullbackComp`,
  `Etale.upperStarId` and `Etale.upperStarComp`. Coherence of the mate follows as well.
- Every trivializing U: `local_split` quantifies over EVERY morphism f:T→S and rank r,
  and an isomorphism of the pulled-back lattice with `free T r`; it concludes a
  group-scheme isomorphism between the actual pullback of D and `model T r`.
- Smooth: `smooth` uses the recorded Mathlib `Smooth`.
- Affine: `affine` uses `IsAffineHom`, defined by inverse images of affine opens affine.
- Faithfully flat: `flat` and `surjective` use `Flat` and `Surjective`.
- Finite presentation: `finitePresentation` is the convention's conjunction of
  `LocallyOfFinitePresentation`, `QuasiCompact` and `QuasiSeparated`.
- Algebraically closed geometric fibres: `geometric_fibre` quantifies over every
  algebraically closed Ω of the scheme universe and every `s : Spec Ω ⟶ S`. It gives
  rank r with the ordinary pullback of the lattice constant free of that rank and
  the group-scheme fibre split of the same rank. Over Spec Ω the small etale topos
  is the point topos, so this is precisely the rank of the geometric stalk M_s.
- Rank zero: all r are ℕ without positivity assumptions, and `Fin 0 → ℤ` is the zero
  group. The rank-zero model is the existing trivial model. The empty base is admitted
  by the empty etale/fppf family; no Nonempty or connectedness binder is present.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Sites.Etale: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- Mathlib.CategoryTheory.Sites.Sheaf: `Sheaf`; ConstantSheaf: `constantSheaf`.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: `Etale.upperStar`,
  `Etale.upperStarComp` and its adjunction; UpperLowerStar.Coherence: `upperStarId`.
- WeilConjectures.AlgebraicGeometry.Sites.Gm: `Scheme.gmSheaf` and
  `Scheme.upperStarGmSheafToGmSheaf`; Sites.UpperStarSections: `Etale.pullSection`.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions: actual scheme pullbacks
  are `Limits.pullback` and the ordinary slice functor `Over.pullback`, as its docstring
  specifies; its module-only base-change construction is not substituted for them.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`; Morphisms.FinitePresentation:
  `LocallyOfFinitePresentation`; Morphisms.Affine: `IsAffineHom`; `Flat`, `Surjective`,
  `QuasiCompact` and `QuasiSeparated` are the scheme-conventions leaf declarations.
- Mathlib.AlgebraicGeometry.Sites.Fpqc: `Scheme.fppfPrecoverage`, used in the existing
  relative-torus predicate; Mathlib group objects: `CommGrp`, `Grp`, `mapCommGrp`.
- Sheaf.AlgebraicGeometry.RelativeTorus: `IsRelativeTorus` and its split units functor.
- Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf: `integerModel`, `model`,
  `coordinate`, `LaurentAlgebra` and `integralProjection`, now owned by
  `def-sfb-relative-split-torus-laurent-model`. Its theorem
  `matrix_sheaf_classification` is used only by the proof. The module is public
  because its plain definitions are used in the statement.

All recorded available proof-dependency modules are imported privately by the theorem,
except the public split-model module above. The three algebraic-space statements
`lem-sfb-fppf-local-algebraic-space`, `lem-sfb-representable-fppf-etale-open-descent` and
`lem-sfb-smooth-space-cover-etale-sections` have no recorded Lean module and hence no
import; they remain named in the proof docstring. There is no import cycle.

Edge checks: rank zero, empty base, disconnected bases with differing ranks, nilpotent
bases, zero rings in affine models, arbitrary non-etale base change, arbitrary etale
chart/test maps, and geometric fields in every characteristic. Crucially, the units
comparison is only a morphism under arbitrary base change, never assumed invertible.
The additive equivalences preserve group structures. Group schemes are not assumed
separated/smooth/affine as a definition of torus: those are conclusions for D.

Searches actually run through msearch.py (full response digests in the new node):

- LeanFinder: “Tori over an arbitrary scheme are contravariantly equivalent to etale
  locally constant sheaves of finite free abelian groups by characters”: eight hits,
  all condensed locally constant functors/discreteness, none relative scheme duality.
- Loogle: `"AlgebraicGeometry", "torus"`: zero hits.
- Mathlib grep in AlgebraicGeometry: `\btorus\b|\btori\b|characterSheaf|latticeSheaf`:
  zero hits. Broader project rg found the field-only multiplicative-type material and
  the two relative modules reused above, not a relative reconstruction theorem.
- LeanSearch: “An etale locally constant sheaf of finite free abelian groups is a
  lattice sheaf and a relative torus is an fppf locally split commutative group scheme”:
  eight hits, including Sheaf.IsConstant and constant-sheaf characterizations; none
  defines the finite-free variable-rank lattice category or reconstruction interface.
- Explicit rg in both lean/WeilConjectures and lean/Sheaf for torus/tori, relative torus,
  characterSheaf/latticeSheaf and declarations named IsTorus found the landed relative
  torus predicate (reused). `grep -rn` for this item's id upstream found no declaration.
  DAG grep for lattice sheaves found this item and its consumers, plus the unrelated
  pro-etale sheaf of integral lattice classes. Blueprint searches for “relative torus”,
  “lattice sheaf”, “character reconstruction” and “etale lattice” each found zero nodes.
  Blueprint ancestor reports None, consistently with the item's existing blueprint.

Source reading: Stacks groupoids.tex, example-multiplicative-group (022U), gives the
relative units functor and integral Laurent Hopf construction. Milne printed pp.232--234,
Lemma 12.4, Remark 12.6 and Theorem 12.9(a), give evaluation, monomial comultiplication
and contravariant duality. The relative descent extension is the seven-step proof in the
item, reproduced in full substance in the theorem docstring. The Lan PDF remains absent
locally, as already recorded by the node; no claim of reading that absent file is made.
No statement correction and no STATEMENT-DISPUTED finding.

## New nodes

`def-sfb-relative-character-duality-data` defines the missing finite free etale lattice
category and the precise reconstruction datum and its normalization conditions. It reuses
all existing notions, in particular def-sfb-relative-torus, the relative Laurent Hopf model,
ordinary inverse image and the units sheaf. Data and Prop-valued conditions are separate
for elaboration efficiency within ONE module. Defining a reconstruction datum asserts no
existence; the item's sole theorem asserts its Nonempty. The new node cites every notion
it is built from. Its sources, blueprint searches, real search digests and lack of an
existing exact interface are recorded in its JSON. The original item cites this definition node and the integral-model definition node
below. The relative-torus predicate is cited through this node; the matrix theorem
remains solely a proof dependency. No existing dependency node is edited.


`def-sfb-relative-split-torus-laurent-model` records the five existing declarations
`LaurentAlgebra`, `integerModel`, `model`, `integralProjection` and `coordinate` in
`Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf`, with `existing: true`.
For each n, the first two give the integral finite-support Laurent algebra and its
commutative Hopf spectrum; `model B n` gives its actual base change along the unique
map to Spec Z; `integralProjection B n` is the projection; `coordinate B n i` pulls
back the basis monomial of `Pi.single i 1`. This covers every clause of the definition.
The source is Stacks 022U and finite products, also Milne Examples 12.1--12.2 and
Remark 12.6. The new real searches are recorded verbatim as msearch response digests
in the node: LeanSearch found eight Hopf-algebra ingredients, Loogle three
AddMonoidAlgebra Hopf declarations, Mathlib grep zero exact integral-model names.
Project search found exactly the unchanged split-matrix module for this interface;
DAG search found no definition node recording it. Blueprint search found two unrelated
Laurent references. The landed `def-sfb-relative-split-torus` instead records the
global-sections-algebra construction and does not record the integral projection or
coordinates needed here. No construction is redefined. Rank zero has no coordinates;
empty, disconnected and nonreduced bases are admitted.

## Repair of return f0a2f5276586

H2 is repaired by adding the existing-declaration definition node above, replacing
`lem-sfb-relative-split-torus-matrix-sheaf` by it in both statement-dependency lists
and in the duality-data node's TeX reference. The matrix theorem remains in the item's
`proof_deps`. The advisory direct `def-sfb-relative-torus` edge has been removed from
the item; the new duality-data node retains its necessary edge to that predicate.
The original item statement and proof plan are unchanged. Both Lean files are
byte-for-byte unchanged from the returned delivery, as requested. Their SHA256 values:

- RelativeCharacterDualityData.lean:
  `49eb4d87a02d9b73badc310c797c175dde1bb4ceaccd19728ac06e829bae0001`
- RelativeTorusCharacterReconstruction.lean:
  `9e15df095ef3282e5b0dbb7f97e3e2e5a55fa57d17b73fd95a78ad93fc86af1f`

The maintainer's return independently checked the mathematics clause by clause and
requested no mathematical or Lean changes. This repair changes dependency ownership
only; compilation and delivery validation are rerun below.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
