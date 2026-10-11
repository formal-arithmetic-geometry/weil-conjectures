## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteCoproductLfpQcqs` states
`AlgebraicGeometry.finite_coproduct_lfp_qcqs`, with one `sorry` proof. It defines no new notion.
The node is unchanged except for `lean`; no statement correction or dependency module is needed.

Hypothesis and clause correspondence:

- The finite set A, possibly empty, is `{A : Type v} [Finite A]`. No `Nonempty`,
  enumeration, or decidable equality is assumed. Universes `u v` are explicitly declared;
  finiteness supplies the smallness instance required for scheme coproducts even when v > u.
- The schemes V_a and S are `(V : A → Scheme.{u}) (S : Scheme.{u})`.
- Each morphism g_a is `(g : ∀ a : A, V a ⟶ S)`.
- The coproduct V is Mathlib's `∐ V`, with canonical coprojections `Sigma.ι V a`.
  The unique induced morphism g is `Sigma.desc g`; `Sigma.ι_desc` gives exactly
  `Sigma.ι V a ≫ Sigma.desc g = g a`. Thus no extra morphism or compatibility hypothesis
  is required: the node's uniquely specified objects are instantiated canonically.
- Clause (1), quasi-compactness, is
  `(∀ a : A, CompactSpace (V a)) → CompactSpace ↥(∐ V)`.
  `CompactSpace` means quasi-compactness, without a Hausdorff assumption.
- Clause (1), quasi-separatedness, independently is
  `(∀ a : A, QuasiSeparatedSpace (V a)) → QuasiSeparatedSpace ↥(∐ V)`.
  Mathlib's `quasiSeparatedSpace_iff_quasiSeparated` identifies this with
  quasi-separatedness of the structure morphism `terminal.from`, i.e. the unique map
  to Spec Z. This is exactly the scheme convention, not a property of g over S.
- Clause (2) is independently
  `(∀ a : A, LocallyOfFinitePresentation (g a)) →
  LocallyOfFinitePresentation (Sigma.desc g)`.
- The conjunction contains all three independent implications. It does not require all
  three antecedents simultaneously, and assumes no property of S.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`, imported through `Mathlib.AlgebraicGeometry.Limits`.
- `lem-weil-pbc-scheme-coproduct-family`: its Mathlib match in
  `Mathlib.AlgebraicGeometry.Limits` provides
  `AlgebraicGeometry.instHasColimitsOfShapeDiscreteSchemeOfSmall`,
  `AlgebraicGeometry.sigmaOpenCover`, and `AlgebraicGeometry.disjoint_opensRange_sigmaι`.
  Read their signatures and available docstrings; the statement uses the resulting
  coproduct and `Sigma.desc`, not a private disjoint-union construction.
- `def-weil-pbc-scheme-conventions`: convention record (no module/declaration of its own).
  Followed its pointers to Mathlib's quasi-separatedness. Read `QuasiSeparated` and
  `quasiSeparatedSpace_iff_quasiSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, imported through FinitePresentation.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, imported directly.
  Its all-affine-pairs definition agrees with the recorded pointwise characterization.

Sources checked: the local Stacks tex files are absent on this machine. Read the source
online at [Tag 01KO](https://stacks.math.columbia.edu/tag/01KO) (affine-cover criterion)
and [Tag 01TQ](https://stacks.math.columbia.edu/tag/01TQ) (local finite presentation).
The declaration docstring records all three proof steps and the named proof dependencies.

Edge cases checked before writing:

- A empty: the initial empty scheme is quasi-compact and quasi-separated, and its map
  to S is locally of finite presentation by the pointwise condition. All antecedents
  are vacuous, and no empty case is excluded by the binders.
- Singleton A: the coproduct is isomorphic to its sole summand and the three clauses
  reduce to invariance under that isomorphism.
- Empty summands, including an entirely empty family of underlying spaces, cause no
  issue; distinct summands have empty intersections. S may itself be empty.
- Quasi-separated but non-quasi-compact summands are allowed in the second implication;
  quasi-compact but non-quasi-separated summands are allowed in the first.
- No Noetherian, separated, field, or characteristic assumption is introduced.

Searches made using `/home/ubuntu/weil-launcher/msearch.py` (recorded in searches.jsonl):

- LeanSearch: “A finite coproduct of quasi-compact quasi-separated schemes is
  quasi-compact quasi-separated and the induced morphism is locally of finite
  presentation if each component is”. Service unavailable (Internal Server Error).
- LeanFinder: “finite coproducts of schemes preserve quasi-separatedness and
  quasi-compactness and locally finite presentation”. Eight results: finite morphism
  binary coproduct, existence/disjointness of scheme coproducts, affine finite
  coproducts, and related instances; no statement containing these three clauses.
- Loogle: `AlgebraicGeometry.LocallyOfFinitePresentation, CategoryTheory.Limits.Sigma.desc`.
  Zero hits.
- Mathlib grep: `sigmaDesc|[Qq]uasiSeparatedSpace.*(sigma|coprod)|[Cc]ompactSpace.*(sigma|coprod)`
  in AlgebraicGeometry. Twelve hits, including `IsZariskiLocalAtSource.sigmaDesc`, which
  gives only the lfp clause. Read it and `Scheme.OpenCover.compactSpace`, which gives only
  compactness. None gives the complete statement.
- Project/source rg: `finite.*coproduct|[Qq]uasiSeparated.*(sigma|coprod)|finite_coproduct_lfp_qcqs`
  in WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json. Hits are unrelated
  cohomology, module coproducts, Galois categories, or uses of finite scheme coproducts.
- Source grep for `lem-weil-pbc-finite-coproduct-lfp-qcqs`: no hits.
- Name collision rg for `finite_coproduct_lfp_qcqs` across Mathlib, WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json: no hits before creating the module.

Validation: server single-file compilation and deliver2.py dry run; only the expected
sorry warning is permitted. No local Lean build, direct repository write, or direct git
command was run. The prescribed delivery dry-run tool manages its own temporary commit.


## Second reading by H1

Independent reading of the node, the delivered file, all four statement dependency
nodes, and their Mathlib declarations found no mismatch. No Lean or node change was
needed; this section records the second reading.

Object/hypothesis/conclusion checklist (each verdict: exact):

1. A finite set A, possibly empty: `{A : Type v} [Finite A]`. There is no
   nonemptiness, decidable equality, chosen enumeration, or extra smallness binder.
2. Arbitrary schemes V_a and S: `(V : A → Scheme.{u}) (S : Scheme.{u})`.
   `Scheme` is Mathlib's locally ringed space with affine neighbourhoods, and
   `Scheme.Hom` is a morphism of locally ringed spaces, as def-pc-scheme requires.
3. Arbitrary component morphisms: `(g : ∀ a : A, V a ⟶ S)`. No property of S
   is assumed. In particular there is no field, Noetherian, or separated assumption.
4. The coproduct V with its canonical inclusions: `∐ V`, `Sigma.ι V a`.
   I opened Limits.lean: its `[Small.{u} σ]` colimit instance supplies the categorical
   coproduct, `sigmaOpenCover` has the schemes g i and maps `Sigma.ι g i`, and
   `disjoint_opensRange_sigmaι` says distinct ranges are disjoint. These are precisely
   the recorded declarations of lem-weil-pbc-scheme-coproduct-family. Finite A
   allows the requisite coproduct for independent index and scheme universes.
5. The unique induced map to S: `Sigma.desc g`. The coproduct universal property
   gives `Sigma.ι V a ≫ Sigma.desc g = g a` and uniqueness. Choosing the canonical
   coproduct and induced map renders the node's specified objects without adding
   a hypothesis or changing the order of its substantive quantifiers.
6. Clause (1), compactness independently: `(∀ a : A, CompactSpace (V a)) →
   CompactSpace ↥(∐ V)`. I read CompactSpace: it requires compactness of univ,
   with no separation axiom. Thus it is exactly quasi-compactness here.
7. Clause (1), quasi-separatedness independently: `(∀ a : A,
   QuasiSeparatedSpace (V a)) → QuasiSeparatedSpace ↥(∐ V)`.
   The convention node is explicitly a collection of pointers, not an absent
   bundled definition. Its diagonal criterion is `QuasiSeparated` in Mathlib;
   `quasiSeparatedSpace_iff_quasiSeparated (X : Scheme)` identifies the topological
   class with `QuasiSeparated (terminal.from X)`, the scheme's map to Spec Z.
   I also read `quasiSeparatedSpace_iff_forall_affineOpens`, matching the affine
   intersection criterion. This does not impose quasi-separatedness on g over S.
8. Clause (2), locally of finite presentation independently: `(∀ a : A,
   LocallyOfFinitePresentation (g a)) → LocallyOfFinitePresentation (Sigma.desc g)`.
   I read the class in FinitePresentation.lean, its HasRingHomProperty instance,
   and `HasRingHomProperty.iff_exists_appLE`. The all-affine-pairs definition is
   equivalent to the pointwise definition in def-sbc-locally-finite-presentation.
9. The three implications are joined by conjunction. Each assumption governs only
   its own conclusion, as in the node; they are not assumed simultaneously.

Source reading: the repository has no local Stacks .tex checkout. I obtained the
upstream schemes.tex and morphisms.tex read-only into this item's scratchpad and
read the exact labels `lemma-characterize-quasi-separated` and
`lemma-locally-finite-presentation-characterize`, as well as the online pages
[01KO](https://stacks.math.columbia.edu/tag/01KO) and
[01TQ](https://stacks.math.columbia.edu/tag/01TQ). Both introduce just a morphism
of arbitrary schemes. There is no ambient finiteness or base hypothesis to add.
Taking the base Spec Z in 01KO gives the scheme criterion. A quasi-compact open
is a finite union of affine opens, so the node's compact-intersection wording is
exactly the source's finite-affine-union wording. 01TQ supplies the all-affine-pairs
and open-cover criteria used in the node and Lean.

Edge cases: A empty is admitted; the initial scheme is empty, both topological
properties hold, and the local finite presentation condition is vacuous. Empty
summands and empty S are admitted, whenever the given morphisms exist. A singleton
reduces to its sole summand up to the canonical isomorphism. Neither implication
in clause (1) requires the other property. There are no characteristic or n
parameters, and no zero-ring or zero-generator case is excluded. Both universes
u and v and every variable are explicitly bound; schemes of different sizes can
be placed in a common universe, and the finite index need not have that universe.

Independent searches (using different wording from the worker):

- LeanFinder via msearch.py: `disjoint union schemes compact quasi separated
  locally finitely presented morphisms`. Eight hits, including the binary finite
  morphism desc instance, finite scheme coproducts, disjointness, diagonal
  compactness, and finite coproducts of affines. None states all three clauses.
- Loogle via msearch.py: `QuasiSeparatedSpace, "sigma"`. Zero hits.
- LeanSearch via msearch.py: `A disjoint union of finitely many schemes is compact
  and quasi separated, and its map to a scheme is locally finitely presented when
  each restriction is`. Service unavailable, Internal Server Error; no verdict
  is inferred from this unavailable search.
- rg in Mathlib Limits.lean and Morphisms/Basic.lean for `quasiSeparatedSpace`,
  `QuasiSeparatedSpace`, `sigmaDesc`, and `CompactSpace`: sigmaDesc supplies the
  local-at-source clause only, not this complete theorem. Reading
  Topology/QuasiSeparated.lean and searching it for sigma/Sigma/coprod/sum found
  no coproduct theorem giving the whole statement.
- rg in WeilConjectures and repository lean/Sheaf for `coproduct.*quasi`,
  `quasi.*coproduct`, `finite_coproduct_lfp_qcqs`, and `QuasiSeparatedSpace.*∐`:
  unrelated module and cohomology statements only, no duplicate declaration.

No new definition nodes, dependency modules, or statement correction are present
or necessary. The sole theorem has a sorry proof; there are no definitions to be
hollow. The docstring carries each of the node's three proof steps and their
named dependencies, and both docstrings contain the correct blueprint id and
sources. Both imports are used by the signature. All lines are at most 100
characters. I checked the node's lean.statement against the file's signature
verbatim with an assertion; it agrees. Validation uses the prescribed server
single-file compiler and deliver2 preflight, not a local or global build.
