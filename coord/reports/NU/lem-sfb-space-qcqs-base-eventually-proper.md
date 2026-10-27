## Worker report

Item: `lem-sfb-space-qcqs-base-eventually-proper`, group NU, stage 2.
Module: `Sheaf.AlgebraicGeometry.SpaceQcqsBaseEventuallyProper`.
Declaration: `AlgebraicGeometry.AlgebraicSpace.eventually_proper_over_qcqs_scheme_limit`.
The only new declaration is the theorem with proof `by sorry`. No data is postponed.
The mathematical statement, source, accepted split and proof dependencies are unchanged.
Three existing landed definition nodes are appended to `stmt_deps` to name the exact
interfaces used: `def-sfb-space-morphism-properties`, `def-trf-scheme-algebraic-space`,
and `def-sfb-space-sheaf-fibre-product`. No new node or dependency repair is necessary.

Hypothesis-by-hypothesis and clause-by-clause reading:

* Work over Spec Z and the size convention: `Spec (.of (ULift.{u} ℤ))` is the
  universe-u integral base, with `J : Type u`, `Scheme.{u}`, and the already published
  universe-polymorphic `AlgebraicSpace` framework. `ULift` preserves the integer ring.
* Small nonempty directed set: `[Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]`.
  No antisymmetry or least-element hypothesis is added.
* Inverse system of schemes: `D : Jᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ)))`.
  An object of this over-category is a scheme with its integral structure map.
  Since `specULiftZIsTerminal` makes this base terminal, this is equivalent to the
  category of schemes, via `Over.equivalenceOfIsTerminal specULiftZIsTerminal`.
  Thus retaining integral structure maps adds no restriction or choice of structure.
* Each base is quasi-compact: `hqc : ∀ j, CompactSpace (D.obj (op j)).left`.
  This is the usual topological quasi-compactness of schemes, equivalent to the
  quasi-compact surjective etale scheme atlas formulation in the node. Scheme
  identity atlases and the image of a quasi-compact atlas give the two implications.
* Each base is quasi-separated: `hqs : ∀ j, QuasiSeparatedSpace (D.obj (op j)).left`.
  For schemes this is Mathlib's quasi-separatedness, equivalently a quasi-compact
  diagonal. It does not impose separatedness.
* Affine transitions: `haff : ∀ i j (h : i ≤ j),
  IsAffineHom (D.map (homOfLE h).op).left`. The opposite morphism points from stage
  j to stage i. The scheme morphism notion is Mathlib's actual affine morphism.
* Specified inverse limit: `c : Cone D` and `hc : IsLimit c` include the projections
  and all compatibility equations. Forgetting from the over-category of the terminal
  integral base preserves and reflects this limit by its equivalence with schemes.
* Distinguished stage: `j₀ : J`. The original finitely presented space and map are
  `Z₀ : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))` and
  `f₀ : Z₀ ⟶ schemeSpace (D.obj (op j₀))`.
* Finite presentation is all three hypotheses `hlfp`, `hfqc`, `hfqs`:
  `MapIsLocallyOfFinitePresentation f₀`, `MapIsQuasiCompact f₀.hom.hom`, and
  `MapIsQuasiCompact (pullback.diagonal f₀.hom.hom)`. The last is relative
  quasi-separatedness. The first uses all compatible etale scheme charts and
  Mathlib's scheme `LocallyOfFinitePresentation` predicate.
* The limiting space Z is the existing `enlargedFibreProduct` of the scheme-space
  image of the cone projection `c.π.app (op j₀)` and `f₀`. Its projection to T is
  `enlargedFibreProductFst` of those maps. `hproper` applies `MapIsProper` to this
  precise projection. The scheme map is carried to sheaves by the actual fppf
  Yoneda functor, then bundled with `ObjectProperty.homMk`; it is not arbitrary.
* Proper means exactly `MapIsSeparated ∧ MapIsFiniteType ∧ MapIsUniversallyClosed`.
  These expand to a representable closed relative diagonal, quasi-compactness and
  locally finite type on compatible etale charts, and closed point maps after every
  algebraic-space base change. The point topology is the published atlas topology.
  `MapIsQuasiCompact` tests the source on every affine scheme as specified by the node.
* The stage spaces Z_k use the same sheaf-pullback projection, now with Yoneda of
  `D.map (homOfLE (hj.trans hk)).op`, the transition from k to j₀. The factor order is
  T_k first and Z₀ second, so the first projection has exactly target T_k; pullback
  symmetry identifies this with the node's notation Z₀ ×_{T_j₀} T_k.
* Conclusion: `∃ j, ∃ hj : j₀ ≤ j, ∀ k (hk : j ≤ k), MapIsProper (...)`.
  This supplies a bound above j₀ and properness at every later stage, including j
  itself by k=j, hk=le_rfl. There is no `IsAffine` hypothesis on any base scheme.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its locally affine
  locally ringed space structure, and `Scheme.Hom` for `.left` scheme maps.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`; morphisms
  are the full subcategory's maps of actual fppf sheaves.
* `def-weil-size-convention` has a convention-only Lean record, not a declaration;
  the explicit universe u and the existing sites implement it.
* `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, affine-local finite presentation.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, closed embedding and surjective stalk maps.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, sheaf pullback closure and its universal property,
  with `etaleCover_pullback` and `etale_fibreProduct_isScheme` for the recorded proof.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsLocallyOfFinitePresentation`, `MapIsSeparated`,
  `MapIsFiniteType`, `MapIsUniversallyClosed`, `MapIsProper`.
  `MapIsQuasiCompact` is the original declaration in its public dependency
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`, not a duplicate.
* `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct` and `enlargedFibreProductFst`, owned by the two existing
  definition nodes appended to the statement dependencies. Their data are the Yoneda
  sheaf and actual sheaf pullback; algebraicity is only a Prop-valued proof field.

The stated proof dependencies are imported as plain imports. These include
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality.flat_proper_fp_locality`,
which selects properness and finite presentation separately, and
`WeilConjectures.AlgebraicGeometry.LimitAffineTransition` with
`AlgebraicGeometry.exists_limit_affine_transition` for restricted scheme limits.
The Mathlib match modules for finite affine covers, open immersion base change,
affine permanence, fppf coverings and flatness are also imported. The affine-base
`lem-sfb-space-eventually-proper` currently has neither a Lean record nor a Mathlib
match, so it has no module to import; its unchanged proof-dependency entry and the
full proof docstring preserve that proof obligation for stage 3. It is not needed
to type this theorem, and no proof dependency was restated as a new declaration.

Source check: read `literature/stacks-project/spaces-limits.tex`,
Situation `situation-descent-property` (084W) and `lemma-eventually-proper` (08K1),
including its affine-target reduction and proper base-change persistence. The supplied
node is its finitely presented-space, qcqs scheme-base specialization. No correction
or disputed statement was found.

Edge cases checked before writing and on rereading:

* Empty scheme stages and empty limit remain permitted: no point or source is
  required nonempty. The proof's empty affine cover case takes bound j₀.
* The index cannot be empty, exactly as required. A singleton diagram recovers
  properness of the same map. Arbitrary directed preorders are permitted.
* j₀ is not required to be least, and the bound includes j₀ via `hj`.
* Non-affine, non-separated qcqs bases are permitted; only their transitions are affine.
* The limiting scheme may be empty although early stages are not; no surjectivity
  assumption is added on transition morphisms or limit projections.
* Z₀ is an algebraic space, with no representability, flatness, reducedness,
  connectedness, characteristic or fibre-dimension assumption added.
* Identity/later-stage maps use their actual Yoneda images. No extra comparison map,
  arbitrary isomorphism, data choice, or universe equality is assumed.

Searches made with the prescribed msearch.py, using this item's sandbox log:

* LeanFinder: “A finitely presented algebraic space over a limit of quasi compact
  quasi separated schemes with affine transitions is eventually proper if its
  pullback to the limit is proper” — 8 results, only scheme limit/finite-type and
  scheme properness declarations. No algebraic-space assertion.
* LeanSearch: “Eventual properness of algebraic spaces over inverse limits of qcqs
  schemes” — 8 results, all scheme properness or compactness of scheme limits.
* Loogle: `"IsProper", "eventually"` — 0 results.
* Mathlib grep: `AlgebraicSpace|eventually.*[Pp]roper|proper.*[Ll]imit` in
  AlgebraicGeometry — 16 results; none states the algebraic-space eventual theorem.
* Project rg on `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `eventually.*[Pp]roper|[Pp]roper.*eventually`, plus `MapIsProper`,
  `MapIsQuasiCompact`, `schemeSpace`, `enlargedFibreProductFst`: no exact theorem.
  `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit`
  (module `WeilConjectures.AlgebraicGeometry.EventuallyProper`) concerns
  scheme sources, so does not cover a general algebraic space. Strict-local and
  curve-limit consumers mention the affine-base theorem but do not state this result.
  The existing general morphism properties and pullback constructors were reused.
* DAG searches for ownership located the three existing definition nodes named above;
  no missing notion needed a new definition node.

Validation: the module compiled separately on the server with scompile.py. The first
attempt identified an implicit source metavariable for the bundled Yoneda map; adding
explicit source and target annotations fixed it. The second attempt compiled both the
sandbox and library module cleanly. Final dry run and delivery also recompile this file.

Dry run: deliver2.py --no-push printed OK; preflight and per-file compilation passed.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
