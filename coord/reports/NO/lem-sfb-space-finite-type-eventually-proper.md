## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFiniteTypeEventuallyProper` states
`AlgebraicGeometry.AlgebraicSpace.exists_proper_stage_of_locallyOfFiniteType`.
Its sole theorem has proof `sorry`. It introduces no definitions and makes no statement
correction. The source was read directly in `literature/stacks-project/spaces-limits.tex`,
Situation `situation-descent-property` (084W), lines 1448–1458, and Lemma
`lemma-eventually-proper` (08K1), lines 1805–1853. The source explicitly assumes only
local finite type; its proof first descends separatedness and then applies weak Chow.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Work over Spec Z: every base is an `Over (Spec (CommRingCat.of (ULift.{u} ℤ)))`;
  `ULift` puts the integer ring in universe `u` without changing the scheme it represents.
  `W₀` is in the recorded category `AlgebraicSpace` over that same base.
- The size convention is implemented by the explicit `universe u`, `Scheme.{u}`
  through the base and diagram, and `I : Type u`; no smaller independent test universe
  is introduced. `set_option autoImplicit false` forbids auto-bound variables.
- A small nonempty directed set: `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. A preorder is the current directed-set convention and does
  not require an extra antisymmetry assumption.
- The inverse system `(T_i)` is `D : Iᵒᵖ ⥤ Over (Spec …)`. Its objects are actual schemes
  over Spec Z. `haff : ∀ i, IsAffine (D.obj i).left` is affineness of every base scheme.
  `htrans` says every transition scheme morphism is `IsAffineHom`. This explicit
  clause is already automatic for maps between affine schemes, but states the given
  diagram condition and imposes no stronger restriction.
- `T = lim T_i`: `c : Cone D` and `hc : IsLimit c`, so `c.pt` is the specified scheme
  limit over Spec Z and `c.π.app (op i₀)` is its specified projection. Limits in the
  slice have the same underlying scheme limit (the index is nonempty and directed).
- Distinguished index: `i₀ : I`, with no least-element assumption.
- The morphism `h_i0 : W_i0 → T_i0` is `h₀ : W₀ ⟶ schemeSpace (D.obj (op i₀))`.
  `schemeSpace` is the existing actual representable fppf sheaf, not a chosen unrelated
  algebraic space or an arbitrary comparison map.
- Quasi-compactness of `W_i0`: `hqc` is exactly existence of `U : Over Spec Z` and
  `a : yoneda.obj U ⟶ W₀.obj.obj` with `CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`.
  Thus it is a quasi-compact scheme with a representable surjective etale atlas.
- Quasi-separatedness: `hqs : MapIsQuasiCompact (prod.lift (𝟙 W₀.obj.obj)
  (𝟙 W₀.obj.obj))`. This is the absolute diagonal over Spec Z, tested by the existing
  scheme-test quasi-compactness predicate. Over the affine separated scheme Spec Z this
  agrees with absolute quasi-separatedness. No separatedness of `W₀` is required.
- Local finite type: `hlft : MapIsLocally (@LocallyOfFiniteType) h₀`, using the recorded
  all-compatible-etale-chart predicate and Mathlib's finite-generation scheme predicate.
- `W = W_i0 ×_{T_i0} T`: the term `enlargedFibreProductFst` has first factor the
  Yoneda image of `c.π.app (op i₀)` and second factor `h₀`. Its source is therefore
  the actual sheaf product `T ×_{T_i0} W₀` and its target is `schemeSpace c.pt`.
  Exchanging the displayed two factors identifies this with the node's `W`, with the
  same projection to `T`. No arbitrary pullback object or morphism is quantified over.
- Properness at the limit: `hproper : MapIsProper (…)`. The recorded definition is
  separatedness, finite type (quasi-compactness and local finite type), and universal
  closedness after every algebraic-space base change.
- Conclusion: `∃ (j : I) (hj : i₀ ≤ j), MapIsProper (…)`, where the projection now
  uses the Yoneda image of `D.map (homOfLE hj).op : T_j → T_i0`. Thus its source is
  `T_j ×_{T_i0} W₀` and its target is `T_j`, exactly the required base-changed map.
- There is no finite-presentation, flatness, initial separatedness, initial properness,
  representability of `h₀`, or nonemptiness of `W₀` hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  including the locally ringed space and local-affineness data and the morphism signature.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective`; the category is
  the full subcategory of fppf sheaves with representable diagonal and an atlas.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` (closure plus universal property), `etaleCover_pullback`,
  and `etale_fibreProduct_isScheme`. These supply the recorded sheaf product interface.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsProper` (and its defining `MapIsSeparated`, `MapIsFiniteType`,
  `MapIsUniversallyClosed`). `MapIsQuasiCompact` comes from its public dependency
  `Sheaf.AlgebraicGeometry.ProperCurveModuli` and was read in full.
- `def-weil-size-convention` is a metatheoretic convention with no definiendum;
  its record is implemented by explicit universes rather than an extra object.
- Added the already landed definition owners `def-trf-scheme-algebraic-space` and
  `def-sfb-space-sheaf-fibre-product` to `stmt_deps`. Both record existing declarations
  in `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: the former owns `schemeSpace`
  (with its property theorem `schemeSheaf_isAlgebraicSpace`); the latter owns
  `enlargedFibreProduct` and `enlargedFibreProductFst`. Their full node statements,
  signatures, docstrings and real definitions were reread for this repair. These are
  the actual Yoneda sheaf and sheaf-pullback definitions. The statement does not use
  the conclusion of `lem-trf-space-enlarged-etale-ringed-site-model`, so that theorem
  node is absent from the repaired statement dependencies. No new node or dependency
  module is created, and the existing public import remains the correct module.
- Stated proof dependency modules are imported without `public`: point-open calculus,
  scheme closed-immersion descent, projective space, and Mathlib properness, immersion
  and quasi-separatedness. The unrecorded space proof dependencies remain future work;
  the complete eight-step natural-language proof is in the theorem docstring.

Edge cases checked before writing: an empty index set is excluded exactly by `Nonempty I`;
`i₀` need not be least; the conclusion permits `j = i₀`; singleton/constant systems retain
precisely the same properness assertion. Empty source and empty affine schemes (the zero
ring) are allowed. Nonseparated initial sources are allowed; separatedness is descended
in the proof, not added to the statement. Arbitrary characteristics and nonflat affine
transitions remain allowed. No finite presentation of any map is inferred or assumed.

Searches for existing statements and constructions:

- `msearch.py … leansearch "Properness descends to a stage for a locally finite type
  algebraic space over an affine inverse limit"`: eight hits, scheme `IsProper` facts
  and affine property descent; none is the algebraic-space statement.
- `msearch.py … leanfinder "A finite type quasi separated algebraic space over an
  affine inverse limit is eventually proper without finite presentation"`: eight hits,
  including `Scheme.exists_isQuasiAffine_of_isLimit`, `Scheme.exists_isAffine_of_isLimit`,
  finite/proper scheme facts and projective spectrum quasi-compactness; none is exact.
- `msearch.py … loogle "AlgebraicGeometry.IsProper, AlgebraicSpace"`: zero hits;
  the service does not know the identifier `AlgebraicSpace`.
- `msearch.py … grep "eventually.*[Pp]roper|[Pp]roper.*isLimit" AlgebraicGeometry`:
  zero Mathlib hits. The wrapper recorded these searches in `searches.jsonl`.
- `rg -n "eventually.*[Pp]roper|[Pp]roper.*isLimit|exists_isProper_baseChange"`
  in both `lean/WeilConjectures` and `lean/Sheaf`: the upstream
  `WeilConjectures.AlgebraicGeometry.EventuallyProper.exists_isProper_baseChange_of_isLimit`
  was read and is about schemes, not arbitrary algebraic spaces. Other hits are consumers,
  scheme proper-support descent or unrelated colimit facts. None is an exact match.
- `rg -n "lem-sfb-space-finite-type-eventually-proper" lean/WeilConjectures`: no hits.
- Searches in `lean/Sheaf/AlgebraicGeometry` for scheme-space constructors and fibre
  products found `schemeSpace` and `enlargedFibreProductFst`, which are used directly;
  searches for qcqs predicates confirmed the existing scheme-test quasi-compactness API.

No STATEMENT-DISPUTED flag, node fault or statement correction remains. The module passed
`scompile.py NO lem-sfb-space-finite-type-eventually-proper <module file>` in sandbox and
library modes, both in 1.5 seconds, with no errors or non-sorry warnings.

## Second reading by NO

This is the author's second reading; the dispatcher forbids starting another agent and
reserves the independent review to the maintainer. I reopened the node and the final
module and checked the binders and conclusion in order. Spec Z, universe `u`, the preorder,
nonempty directedness, affine schemes and transitions, the cone universal property,
distinguished index, initial algebraic space, atlas qc, diagonal qs and chartwise local
finite type each have the rendering recorded above. The sole properness assumption is
at the limit. Both product projections land in the base factor, with the first factor
ordered as base and the second as source; the conclusion uses exactly the transition
from `j` to `i₀` and requires `i₀ ≤ j`. The initial compile exposed unresolved bundled
endpoints in `ObjectProperty.homMk`; both endpoints are now explicitly `schemeSpace`
of the appropriate base scheme, and the compiler accepted them. No mathematical
hypothesis or conclusion changed. The report explicitly distinguishes the scheme-only
upstream theorem from this algebraic-space statement and records the two added landed
definition dependencies. I also checked the theorem's eight proof steps against all eight
node proof steps and that the JSON signature is verbatim from the final file.


## Repair of returned delivery cae67053b4a8

H2 is repaired by replacing the added theorem dependency
`lem-trf-space-enlarged-etale-ringed-site-model` with the two landed definition owners
`def-trf-scheme-algebraic-space` and `def-sfb-space-sheaf-fibre-product`. The former
owns `schemeSpace`; the latter owns `enlargedFibreProduct` and
`enlargedFibreProductFst`. The node's `lean.note` and dependency discussion above now
name those owners and explain that the enlarged-site theorem conclusion is not used.

Comparison with the current shared node found differences only in `lean` and
`stmt_deps`; all other accepted node fields are retained exactly. The repair adds
only the two landed definition nodes to that current base list. The Lean file is
byte-identical to the returned delivery (SHA256
`b99ab041967eec13ea3fd1fb64b93c185687c4dbf60c6fc43bba2c04e21b81f2`), and
`lean.statement` is still verbatim from its theorem signature. The prescribed
`deliver2.py` wrapper refreshes the current base and constructs the repaired delivery.

Second reading of H2: I reopened both definition nodes and the definitions at lines
79, 230 and 236 of `EnlargedEtaleRingedSite.lean`. The actual Yoneda sheaf supplies
both base endpoints; the actual sheaf pullback and its first projection supply the
properness maps in the assumption and conclusion. Those plain definitions account
for every use of that module in the statement. The node now cites their owners,
while retaining exactly the mathematical statement independently accepted in the
return. The independent maintainer review remains separate from this author check.
