## Worker report

The module `Sheaf.AlgebraicGeometry.IntersectionStructureSections` states
`AlgebraicGeometry.Scheme.sections_intersection_structure_colimit`, with `sorry` as its
entire proof. Its six helpers have concrete data: the subtype inclusion, its structure-sheaf
inverse image, its global-section ring, the canonical restriction unit, the restriction
diagram of distinct indicated opens, and the continuous map of intersections induced by a
scheme morphism. These helpers belong to the canonical construction named by this node;
all seven declarations are listed in `lean.declarations`. No additional DAG notion or
dependency repair is required. The node is changed only in `lean`.

Source read: `literature/stacks-project/more-groupoids.tex`, lines 2968–2993,
equation `equation-sections-of-intersection`, preceding Tag 0APJ. It gives the formula for
any sheaf on the given scheme. This node is its structure-sheaf specialization. The theorem
docstring carries all eight steps of the node's natural-language proof.

Hypotheses and objects, matched individually:

- A scheme X: `(X : Scheme.{u})`.
- Quasi-separatedness: `[QuasiSeparatedSpace X]`. Mathlib's
  `quasiSeparatedSpace_iff_quasiSeparated X` identifies this with quasi-separatedness of
  the terminal scheme morphism. No quasi-compactness or separatedness of X is imposed.
- A nonempty set-indexed family: `{I : Type v} [Nonempty I]` and
  `(U : I → X.Opens)`. The original indexing universe remains arbitrary.
- Every indicated open is quasi-compact: `hqc : ∀ i, IsCompact (U i : Set X)`.
- The family after finite-intersection refinement is directed by reverse inclusion:
  `hdir : ∀ i j, ∃ k, U k ≤ U i ⊓ U j`. No order on I, injectivity of U, or affine
  transition hypothesis is imposed. This is the refined family explicitly used by the node.
- E is the intersection, with the subspace topology:
  `TopCat.of {x : X // ∀ i : I, x ∈ U i}`. E is not declared to be an open or a scheme.
- The sheaf on E: `intersectionStructureSheaf X U` uses the recorded
  `TopCat.Sheaf.pullback CommRingCat (intersectionInclusion X U)` on `X.sheaf`.
- Its section ring is `intersectionSections X U`, evaluation at `op ⊤`.
- The specified rho_i is `intersectionRestriction X U (U i) (fun x hx ↦ hx i)`.
  This is the actual adjunction unit evaluated at U_i followed by the presheaf map from
  its inverse-image open to all of E; the latter inclusion follows from E ⊆ U_i.
  For an open subspace, structure-sheaf sections are precisely `X.presheaf.obj (op (U i))`.
  The open-embedding and composition-unit identifications in proof step 4 identify this
  direct X-to-E formula with the node's unit for E → U_i.

Conclusions, matched individually:

- Clause (a) is the first conjunct: every `s : intersectionSections X U` has an index i
  and `a : X.presheaf.obj (op (U i))` whose image under the specified rho_i equals s.
- Clause (b) is the second conjunct: equality of the two rho_i images yields an original
  index k, an inclusion `hki : U k ≤ U i`, and equality after applying exactly
  `X.presheaf.map (homOfLE hki).op`. It does not replace eventual equality with stalkwise
  equality or pass to an arbitrary neighbourhood.
- The commutative-ring colimit is the third conjunct: there exists a natural family ι
  into the specified section ring; each `ι.app V` equals the actual restriction unit;
  `Nonempty (IsColimit (Cocone.mk (intersectionSections X U) ι))` is precisely its
  universal property. Thus the induced canonical map from any chosen colimit is an
  isomorphism. This uses the dependency's universal-property interface, and requires
  neither a chosen colimit object nor a choice of any map as an extra hypothesis.
- The abelian-group and set versions are the next two `IsColimit` assertions, using the
  same cocone under `forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat` and
  `CategoryTheory.forget CommRingCat`. They concern the same sections and the same units.
- The diagram index is `{V : X.Opens // V ∈ Set.range U}ᵒᵖ`: its arrows run from larger
  opens to smaller ones, with the structure-sheaf restriction as transition. It is a
  nonempty directed poset by `[Nonempty I]` and hdir, hence filtered. Identifying repeated
  opens is cofinal in the original reverse-inclusion family, so this is exactly the
  node's colimit. Crucially this index is in Type u even if the supplied family is in
  Type v; no unjustified size equality or large-colimit assumption is used.
- Naturality is the final conjunct. It quantifies over `g : X ≅ Y` and corresponding
  opens V with `hUV : ∀ i, U i = g.hom ⁻¹ᵁ V i`; this is exactly that g carries the
  indicated opens and their intersection to the corresponding ones. `intersectionMap`
  is the concrete induced continuous map E → E'. The unique morphism t of ring sheaves
  over that map is characterized on EVERY open W of Y by the inverse-image adjunction
  unit equation with `g.hom.app W`. This characterizes the actual inverse-image
  transport, independently of the colimit theorem, by the adjunction universal property.
  It is not an arbitrary section-ring map assumed in a hypothesis. `HEq` only identifies
  the definitionally matching inverse-image opens on the two sides. Evaluating t at
  `op ⊤` and restricting its pushforward value to all of E gives the section-ring map.
  The following equation, for EVERY i, is exactly
  `rho'_i ≫ g_E^sharp = g_i^sharp ≫ rho_i`.
  Together with the displayed colimit universal properties this is naturality of the
  canonical identification; applying the two forgetful functors gives the identical
  assertion in abelian groups and sets. No qs or qc assumption is added on Y: it follows
  from g and the data on X when needed. A relabelling of the family is absorbed by
  taking V with the original index I; the diagram itself uses distinct opens.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, and its `Scheme.sheaf`/`Scheme.presheaf` interfaces.
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, `AlgebraicGeometry.QuasiSeparated`;
  the absolute scheme version is the equivalent `QuasiSeparatedSpace X` above.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.Cocone`, `IsColimit`, and the chosen-colimit universal property.
- `def-weil-pbc-topological-inverse-image`: `Mathlib.Topology.Sheaves.Functors`,
  `TopCat.Sheaf.pullback`, `pullbackPushforwardAdjunction`, and `pushforward`.
  These are used with their own adjunction units throughout. Mathlib's `pullbackIso`
  identifies the chosen left adjoint with presheaf inverse image followed by
  sheafification. That is an adjunction comparison, not a claim of definitional equality:
  `Adjunction.unit_leftAdjointUniq_hom_app` transports the units, as required by the
  dependency's note. The formal statement does not mix the two different units.

Proof-only imports retain the stated proof dependencies: Mathlib's spectral-space,
filtered ring/set colimit, and preservation-of-sheafification modules;
`Sheaf.Topology.SetsInverseImageComposition` and
`Sheaf.Topology.SpectralLimitPullbackSections` with their recorded declarations
`TopCat.Sheaf.exists_sets_inverseImage_comp` and `TopCat.Sheaf.spectralLimit_pullback_sections`.
The scheme quasi-separated module also supplies the affine-open criterion and scheme
spectral-space inputs; `Topology.Sheaves.Functors` imports sheafification. No missing
proof prerequisite has been restated.

Edge cases checked before writing:

- I empty is excluded exactly by the node's `[Nonempty I]`.
- The intersection E may be empty, as may X or a family member. No nonemptiness or scheme
  structure on E is used. Its ring of sections can be the zero ring; all three colimit
  assertions allow that ring and its underlying singleton group/set.
- A singleton or constant family yields restriction to that open; repeated indices are
  retained in (a), (b), and naturality, and identified only in the colimit diagram.
- No quasi-compactness of X, affineness of members, or affine inclusion maps are assumed.
- Arbitrary family cardinalities are permitted; the actual diagram has the universe of
  the scheme's opens. The coefficient rings, spaces and sections have universe u.
- Identity isomorphisms and an empty intersection impose the same unit equations and
  restriction squares as the general case. No identity/arbitrary-transport case is dropped.

Searches performed for an existing declaration:

- `msearch.py leanfinder`: “Sections of the structure sheaf on a directed intersection
  of quasi compact opens in a quasi separated scheme are the filtered colimit of
  sections”. Eight hits, including `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`
  and `exists_appTop_π_eq_of_isLimit`; their types impose affine transition maps and a
  scheme limit, and do not give this arbitrary subspace intersection statement.
- `msearch.py loogle`: `TopCat.Sheaf.pullback, CategoryTheory.Limits.IsColimit`:
  successful search with zero hits.
- `msearch.py leansearch`: “Sections of an inverse image sheaf on an intersection of
  compact open subsets are the filtered colimit of sections on those opens”. Eight
  hits concerning finite-union sheaf gluing and open-immersion section isomorphisms;
  none gives the intersection formula.
- `msearch.py grep`, Mathlib/AlgebraicGeometry:
  `sections.*(inter|[Cc]olimit)|([Cc]olimit|[Ii]nter).*sections`: seven documentation
  hits in ResidueField, Cover/Directed, IdealSheaf/Subscheme, QuasiSeparated, Flat and
  Affine; no matching statement.
- `rg` of `lean/Sheaf` and the upstream `WeilConjectures` sources for intersection and
  section terms found spectral-limit and Cech material, plus affine-transition limit
  constructions, but no theorem on structure-sheaf sections over this intersection.
- An exact item-id search in upstream `WeilConjectures` returned no match. The proposed
  declaration/helper names were also searched in `dag/lean_names_upstream.json`, the
  side Lean library, upstream and Mathlib's algebraic geometry sources: no collisions.

Validation: `scompile.py Q65 lem-a1-sections-intersection-structure-colimit
lean/Sheaf/AlgebraicGeometry/IntersectionStructureSections.lean` passed both sandbox and
library-path compilation without warnings (4.5 s and 11.8 s in the successful run).
Initial elaboration issues were repaired by typing the subspace binder, using the existing
two-step forgetful functor to abelian groups, qualifying `CategoryTheory.forget`, and
silencing unused implicit functor-law binder names. No theorem has been proved.

No statement correction, new nodes, dependency modules, or mathematical disputes.

## Second reading by Q65

Independent maintainer second reading, 2026-10-18, of immutable delivery
6bcd655dc2528a35b6a6b2de1d6626ea2ac4e20b. This reader did not write the delivery.
The original heading contained only a disclaimer that no second reading had occurred.
This complete replacement report supplies the required substantive reading (H11).
The worker report above is preserved; no Lean or node change is needed.

I read the item and all four statement-dependency nodes from the immutable snapshot,
the complete module and its docstrings, and the exact dependency declarations in the
read-only Mathlib and side-project sources. The source is Stacks, more-groupoids.tex,
lines 2968–2993, equation-sections-of-intersection preceding Tag 0APJ. It assumes a
quasi-separated scheme and a nonempty family of quasi-compact opens, refined to be
directed, and gives the formula for any sheaf. The node is its structure-sheaf case.

Object and hypothesis comparison:

- Scheme: `X : Scheme.{u}` is Mathlib's locally affine locally ringed space, with
  `Scheme.Hom` the locally ringed-space morphisms (Scheme.lean:42,74). Correct.
- Quasi-separated: `[QuasiSeparatedSpace X]` agrees with the terminal morphism's
  quasi-compact diagonal by `quasiSeparatedSpace_iff_quasiSeparated` (:133).
  This is the recorded dependency's absolute notion; no extra compactness,
  separatedness, Noetherianity or affine hypothesis occurs. Correct.
- Family: `{I : Type v} [Nonempty I]`, `U : I → X.Opens`, `hqc` asserting compactness
  of every underlying open, and `hdir` asserting a member inside every binary
  intersection exactly render the nonempty refined family in the statement. Correct.
- Intersection: `intersectionInclusion` uses the subtype of points lying in all U_i,
  with its actual subspace topology. It neither assumes openness nor equips the
  intersection with a scheme structure. Correct.
- Structure sheaf: `intersectionStructureSheaf` is the recorded `TopCat.Sheaf.pullback`
  of `X.sheaf`; `intersectionSections` evaluates it at the top open. The chosen abstract
  left adjoint is canonically compared with presheaf inverse image plus sheafification
  by `pullbackIso`/`Adjunction.leftAdjointUniq`. The module consistently uses that
  abstract adjoint's own unit; it never identifies the two choices definitionally.
- Restriction: `intersectionRestriction` evaluates that unit at an ambient open and
  then restricts its preimage to the whole intersection. For U_i the containment
  witness is `fun x hx ↦ hx i`. The open-embedding restriction identification and
  composition-unit equation make this exactly the node's rho_i. Correct.

Conclusion comparison:

- (a): the first conjunct quantifies over every section s and produces an original
  index i and section a with rho_i(a)=s. Correct quantifier order and map.
- (b): the second conjunct starts with two sections on the same original U_i and
  equality of their rho_i images, then produces original k, `U k ≤ U i`, and equality
  after `X.presheaf.map (homOfLE hki).op`. Correct eventual equality, not merely germ
  equality or extension to an unspecified neighbourhood.
- Colimit: the third conjunct fixes each component of the natural cocone to the
  actual restriction and asserts `Nonempty (IsColimit ...)` in commutative rings,
  abelian groups and sets using the same cocone and the standard forgetful functors.
  `IsColimit` is the universal property in the dependency, hence equivalently the
  canonical comparison is an isomorphism. Its index consists of distinct indicated
  opens, opposite to inclusion, and its transition maps are genuine restrictions.
  Repeated labels give canonically identical objects/maps and can be identified.
  Nonemptiness and hdir make this index filtered. Correct.
- Naturality: the final conjunct covers every scheme isomorphism g and matching family
  with U_i=g^{-1}(V_i). `intersectionMap` is the actual induced continuous map.
  The unique sheaf morphism t is characterized on every ambient open by the unit
  equation with `g.hom.app W`; the pullback adjunction and composition of direct
  images prove this characterization determines the canonical transport. Thus it is
  not an arbitrary map. `HEq` handles the equal inverse-image opens. The last square
  is precisely rho'_i followed by transport equals g_i^sharp followed by rho_i.
  Colimit uniqueness gives naturality of the canonical comparison in all three
  categories, including reindexing (families can be relabelled using the same I).

Universes and edge cases:

- I may have any universe v. The distinct-open index is in Type u, because membership
  in `Set.range U` is a proposition. The intersection subtype is also in Type u.
  This legitimately avoids a large-colimit assumption without restricting v=u.
- Empty I is excluded as in the node. Empty X, an empty member, and an empty total
  intersection are allowed. The empty space has a singleton section set and the
  zero section ring; no `Nontrivial` or nonempty-intersection hypothesis is present.
- Singleton families, constant/repeated opens, and identity isomorphisms are covered.
  The ambient scheme need not be quasi-compact; its selected members are compact.
- No extra test-category or coefficient-universe equalities are imposed. All variables
  are bound; the recorded statement is verbatim equal to the module signature.

Dependency and proof-plan checks:

I read `SpectralLimitPullbackSections.lean` and `SetsInverseImageComposition.lean`,
including `TopCat.Sheaf.spectralLimit_pullback_sections` and
`TopCat.Sheaf.exists_sets_inverseImage_comp`. The former's small directed spectral
system, spectral transition maps, pointwise limit and initial topology hypotheses
are supplied by steps 1–2 on the distinct opens contained in a fixed U_i. The latter
has exactly the unit equation and uniqueness needed in step 4. The spectral theorem
allows an empty limit. Ring/set representatives and sheafification comparison are
provided by the imported Mathlib filtered-colimit and PreservesSheafification APIs;
`sheafifyComposeIso` and `sheafComposeIso_hom_fac` preserve the units. The eight-step
proof docstring accounts for surjectivity, eventual equality, all algebraic operations,
and naturality. All recorded proof dependencies are available through these imports;
there is no missing helper or dependency-interface repair.

Independent searches used alternative phrases for compact-open intersection sections,
section continuity, inverse-image sheaves and colimits across Mathlib,
WeilConjectures and lean/Sheaf, plus exact declaration-name searches. The Mathlib
`exists_appTop_π_eq_of_isLimit` and `nonempty_isColimit_Γ_mapCocone` in
AffineTransitionLimit.lean:842,961 require affine scheme transition maps and a scheme
limit; they do not state this arbitrary subspace-intersection result. Other hits
concern finite gluing, stalks, rational functions, étale continuity or the already
cited general spectral-limit tool. No duplicate notion or declaration was found.
The six helpers are concrete specializations/compositions of existing APIs, not
alternative foundational definitions.

The immutable item, report and module were byte-compared with the requested commit.
Only `lean` changed in the item relative to its parent. There is no statement_change,
new node, or dependency module, so no §1(C) citer audit is required. All seven
recorded declarations have source/blueprint docstrings; the theorem docstring follows
all eight proof steps. The only theorem proof is `sorry`; no definition contains
`sorry`. Helper functor laws and continuity witnesses use existing proofs. No line
exceeds 100 characters, no private notation/instance is introduced, and names/imports
follow the conventions.

The route-pivot dropped list at origin/newtargets-dag was checked against every direct
statement/proof dependency: no intersection. There is no repair note for this item.
The delivered theorem uses ordinary topological inverse images and Zariski opens;
it introduces neither dropped enhancement machinery nor a pro-étale substitute.

Read-only environment observation: the group clone's checked-out `newtargets-dag`
HEAD moved during the review (observed 5f483440d1b112da8e93f946ef0edaabe9f039f3,
then 3952542ba7fb0a17ed1b87fd986bf0c1b11f5983; its reflog shows concurrent
reset/checkout bookkeeping). This reader issued no mutating Git command and did not
move any branch. Delivery judgments use the fixed snapshot, byte-verified against
6bcd655dc2528a35b6a6b2de1d6626ea2ac4e20b, rather than that moving context checkout.

Compiler reproduction:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q65
lem-a1-sections-intersection-structure-colimit
snapshot/lean/Sheaf/AlgebraicGeometry/IntersectionStructureSections.lean`

returned exit 0 with no diagnostics, for sandbox `Sheaf/Stage2/Sandbox0.lean`
(28.6 s) and library `Sheaf/AlgebraicGeometry/IntersectionStructureSections.lean`
(21.5 s). The installed wrapper is the 2026-10-17 server-overlay implementation;
its output names a private `/dev/shm/nt-tmp/nt-local-compile-586syka4/.lbuild`.
This independently reproduces the worker's successful per-file check, using the
prescribed wrapper and unchanged 60-second file limit. No direct SSH command,
global/lake build, live Lean edit, delivery or repository mutation was performed.

Finding: H11, the original second-reading section was only a placeholder. Corrected
by this full independent reading. No mathematical or Lean-statement defect found.
Verdict: FIX, report replacement only.
