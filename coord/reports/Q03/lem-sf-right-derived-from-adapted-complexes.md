## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.RightDerivedFromAdaptedComplexes`
states `CategoryTheory.Functor.exists_rightDerivedFunctor_of_adapted_complexes`.
Its only proof is `sorry`. No new definition or other DAG statement is introduced.
The item's JSON changes only in `lean`.

Statement correspondence:

- The abelian categories are `{A : Type uA}`, `{B : Type uB}` with independent
  `[Category.{vA} A]`, `[Category.{vB} B]`, `[Abelian A]`, and `[Abelian B]`.
  `[HasDerivedCategory.{wA} A]` and `[HasDerivedCategory.{wB} B]` select the
  localized categories in independently chosen morphism universes, following
  the recorded abstract-derived-category interface and its size convention.
- The homotopy category of integer-indexed cochain complexes is
  `HomotopyCategory A (ComplexShape.up ℤ)`. Its objects are complexes, with
  homotopic maps identified. `DerivedCategory.Qh (C := A)` is precisely the
  localization from that category, rather than the localization `Q` from complexes.
- `G` has source that homotopy category and target `DerivedCategory B`.
  `[G.CommShift ℤ] [G.IsTriangulated]` expresses the given exact functor for the
  canonical shifts and cone triangles. Additivity follows from these instances.
- The adapted class is `𝓘 : Set (HomotopyCategory A (ComplexShape.up ℤ))`.
  `h_replacements` quantifies over every complex `K` and supplies an object `I`,
  a map `r : K ⟶ I`, membership in `𝓘`, and the quasi-isomorphism predicate.
  It does not assume the choices are functorial.
- `h_inverts` quantifies over both endpoints in the class and every arrow between
  them, assuming it is a quasi-isomorphism and concluding `IsIso (G.map s)`.
- The existential `RG` has source `DerivedCategory A` and target `DerivedCategory B`;
  `α : G ⟶ DerivedCategory.Qh ⋙ RG` has exactly the required direction.
- `RG.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))`
  expresses the entire universal property, not merely existence of some comparison.
  In Mathlib's `Functor.Derived.RightDerived`, its sole field is
  `RG.IsLeftKanExtension α`. `Functor.KanExtension.Basic` defines this as the
  initiality of the left extension `(RG, α)`; its `homEquivOfIsLeftKanExtension`
  identifies `RG ⟶ T` with `G ⟶ Qh ⋙ T` by `u ↦ α ≫ whiskerLeft Qh u`.
  Thus every functor `T` and natural transformation `β` has a unique `u` with
  `β = α ≫ whiskerLeft Qh u`, exactly the node's equation in Lean composition order.
  Neither `T` nor `β` is restricted by exactness or shift compatibility.
- The final universally quantified implication is precisely that `α.app I` is
  an isomorphism for every `I ∈ 𝓘`.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (via `DerivedCategory.Basic`).
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Qh` and its localization instance, from
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
  `HomotopyCategory.quasiIso` in `Mathlib.Algebra.Homology.Localization` says that
  every cohomology map is an isomorphism.
- `def-weil-triangulated-category`: `Functor.CommShift` and
  `Functor.IsTriangulated` from `Mathlib.CategoryTheory.Triangulated.Functor`,
  transitively publicly imported by `DerivedCategory.Basic`.
- `lem-pur-homotopy-category-triangulated`: the triangulated instance in
  `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`, together with the exact
  `Qh` instance in `DerivedCategory.Basic`. The canonical structures are used;
  no arbitrary alternative triangulation is supplied as a hypothesis.

The stated proof dependencies are all Mathlib leaves. Their source signatures
were read and their modules are imported without `public`: the two calculus
instances in `DerivedCategory.Fractions`, `Localization.exists_leftFraction`
and `MorphismProperty.LeftFraction.map_eq_iff` in `Localization.CalculusOfFractions`,
and `Localization.lift`, `fac`, `liftNatTrans`, and `natTrans_ext` in
`Localization.Predicate`. The theorem docstring expands all eight proof steps,
including fraction independence, composition, naturality and uniqueness.

Source check: read `literature/stacks-project/derived.tex`, Situation
`situation-derived-functor`, Definition `definition-everywhere-defined`,
`equation-everywhere`, and the statement and proof of
`lemma-find-existence-computes` (Tag 06XN). The source has exactly the two
adapted-class hypotheses above.

Edge cases checked: an empty adapted class cannot satisfy `h_replacements`,
since an abelian category has a zero complex. The zero category and zero complex
are allowed. There is no boundedness, injectivity, enough-injectives, closure
under cones or shifts, repleteness, or functorial-replacement assumption.
All object, original morphism and derived morphism universes are independent
between `A` and `B` and explicitly bound. No automatic implicit variables,
local notation, private copies, or `let` binders occur in the signature.

Searches for existing declarations:

- `msearch.py leansearch`, query "right derived functor existence from a class
  of adapted complexes with quasi-isomorphism replacements": eight results,
  including `HasRightDerivedFunctor`, `totalRightDerived`, and pointwise-derived
  predicates. These define or assume existence; they do not establish it from
  the two adapted-class hypotheses.
- `msearch.py leanfinder`, query "A functor on the homotopy category has a right
  derived functor computed on an adapted class if every complex admits a
  quasi-isomorphism into the class and quasi-isomorphisms within the class are
  inverted": eight results, including `rightDerivedToHomotopyCategory`,
  the quasi-isomorphism calculus, `Qh`, `HasRightDerivedFunctor.mk'`, and exact
  induced derived functors. None has the item's assertion.
- `msearch.py loogle`, query
  `CategoryTheory.Functor.HasRightDerivedFunctor, CategoryTheory.Functor.IsRightDerivedFunctor`:
  two hits, the total-right-derived instance and `HasRightDerivedFunctor.mk'`;
  both assume the requisite universal property already exists.
- `msearch.py grep`, query
  `hasRightDerivedFunctor_of|hasPointwiseRightDerivedFunctor_of|adapted`, in
  `CategoryTheory/Localization`: two hits in `DerivabilityStructure/Derives.lean`,
  requiring an established right derivability structure.
- `rg` across Mathlib, `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for adapted-derived name combinations and the
  proposed declaration name found no duplicate. Broader searches found classical
  acyclic resolutions and injective constructions, and universal-property APIs,
  but no theorem with this arbitrary adapted class. `grep -rn` for the item id
  in `WeilConjectures` returned no hit. The nearby
  `EverywhereDefinedDerivedFunctors` and `FiniteCDDerivedUpperBound` side modules
  were read; their hypotheses and conclusions are different from this node.

No mathematical statement fault or correction was found.

Validation:

- The required file compilation succeeds with `scompile.py` using the current
  side-overlay configuration. The inherited overlay source had a stale duplicate
  `AlgebraicGeometry.ProEt.overPullbackId`; the local overlay used for this run
  omits that already-published duplicate while retaining the two K-flat side
  modules. The requested module itself compiles in both sandbox and library
  modes, with only the expected `sorry` declaration warning suppressed by the
  project options.
- The required dry run was then executed as
  `SHAREDREPO_WT_SLOTS=100 NT_OVERLAY_SOURCE=/home/ubuntu/nt-overlay-Q03
  python3 /home/ubuntu/weil-launcher-nt/deliver2.py Q03
  lem-sf-right-derived-from-adapted-complexes --no-push`.
  It printed `OK (dry run)`: the commit compiles and passes preflight
  except for the second reading, which the second reader writes; nothing was
  pushed.

The stale duplicate is an overlay/tooling issue only; this module imports no
pro-etale overlay declaration. No project source or launcher tool was edited.


## Second reading by Q03

I reread the node statement, its dependency records, the Lean declaration, and the
Stacks source before delivery.

- The two abelian categories are rendered by `{A : Type uA}` and `{B : Type uB}`,
  independent `Category` structures, `Abelian` instances, and independent
  `HasDerivedCategory` universes. Verdict: exact match to the node's
  `\mathcal A,\mathcal B` hypotheses; no Noetherian, boundedness, or universe
  restriction was added.
- The homotopy category and localization are rendered by
  `HomotopyCategory A (ComplexShape.up ℤ)` and
  `DerivedCategory.Qh (C := A)`. Verdict: exact match to `K(\mathcal A)` and
  `Q_{\mathcal A}`; `Qh` is the homotopy-category localization required by the
  node, rather than the raw-complex `Q`.
- The functor is rendered by
  `G : HomotopyCategory A (ComplexShape.up ℤ) ⟤ DerivedCategory B` with
  `[G.CommShift ℤ] [G.IsTriangulated]`. Verdict: this is the canonical
  Mathlib expression of an exact functor between the stated triangulated
  categories; additivity is supplied by the `IsTriangulated` instance.
- The adapted class is rendered by
  `𝓘 : Set (HomotopyCategory A (ComplexShape.up ℤ))`. Verdict: same class of
  complexes as the node.
- The replacement hypothesis is rendered by `h_replacements`: for every `K` it
  supplies `I`, `r : K ⟥ I`, `I ∈ 𝓘`, and the homotopy-category quasi-isomorphism
  predicate. Verdict: all four clauses and arrow direction match; no functorial
  choice is assumed.
- The inversion hypothesis is rendered by `h_inverts`: for `I,J ∈ 𝓘` and every
  quasi-isomorphism `s : I ⟥ J`, it concludes `IsIso (G.map s)`. Verdict: exact
  endpoints, predicate, and conclusion; no closure or extra hypothesis appears.
- The output is rendered by `∃ RG : DerivedCategory A ⟤ DerivedCategory B` and
  `α : G ⟥ DerivedCategory.Qh ⋆ RG`. Verdict: exact object and natural
  transformation direction from the node.
- The universal property is rendered by
  `RG.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))`.
  Reading Mathlib's `IsRightDerivedFunctor` and `IsLeftKanExtension` confirms it
  is the full universal property for every `T` and `β`, with equation
  `α ≫ whiskerLeft Qh u = β`, i.e. the node's
  `β = (u ∘ Q_A)α`, and uniqueness of `u`.
- The computation clause is rendered by
  `∀ I, I ∈ 𝓘 → IsIso (α.app I)`. Verdict: this is exactly the node's
  final clause (the target is definitionally `RG (Q_A I)`).

I checked the source Situation 05S8: its saturated, triangulation-compatible
system is instantiated here by the canonical homotopy-category quasi-isomorphism
property and its Mathlib localization/triangulated instances. The source lemma
06XN has precisely the two adapted-class conditions used above. The edge cases
remain covered: the zero category and zero complex are allowed; `n = 0` and
characteristic assumptions are irrelevant; an empty adapted class cannot satisfy
`h_replacements`; and all category, morphism, and derived-category universes are
independently bound.

I repeated the three required searches (LeanSearch, LeanFinder/Loogle, and grep)
with adapted-complex and right-derived queries over Mathlib, `WeilConjectures`,
`lean/Sheaf`, and `dag/lean_names_upstream.json`. They found only APIs that assume
an existing derived functor or derivability structure, not this existence theorem.
The recorded dependency declarations were opened and match their nodes; no new
notion or dependency repair is needed.

No mismatch was found, so no Lean or node statement was changed. Compilation with
`scompile.py` succeeds for the module (sandbox and library modes), with only the
expected postponed theorem. The delivery dry run is the final check.
