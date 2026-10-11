## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleInverseImageSectionDescription` states
`AlgebraicGeometry.etaleInverseImageSectionDescription`, with its sole proof `sorry`.
It introduces no new definition and changes only the item's `lean` record.

Source checked: [Stacks Tag 09XN](https://stacks.math.columbia.edu/tag/09XN), the
proof paragraph beginning “By construction”; it supplies exactly the étale local
representatives and commuting diagram asserted in this node. The local literature
checkout is absent on this machine, so the original Stacks page was read directly.

Hypotheses and clauses, in order:

- Schemes and morphism `g:T → S`: `(S T : Scheme.{u}) (g : T ⟶ S)`.
- Sheaf of sets on the small étale site of S: the recorded Mathlib notion
  `(F : Sheaf S.smallEtaleTopology (Type (u + 1)))`.
- Every section of `g⁻¹F` over T: the binder `s` is an element of
  `((Scheme.etaleSetPullback g).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 T)))`.
  The identity object is T itself in its small étale site; this is a global section,
  without an arbitrary auxiliary object or extra hypothesis.
- After an étale covering `{T_a → T}`: existential `I`, `Z : I → T.Etale`, and
  `π : ∀ i, Z i ⟶ Scheme.Etale.mk (𝟙 T)`, with `Sieve.ofArrows Z π` covering for
  `T.smallEtaleTopology`. By `Scheme.ofArrows_mem_smallEtaleTopology_iff` this is
  exactly joint surjectivity, and the arrows are étale since they are maps between
  schemes étale over T. The index universe u suffices: a jointly surjective family
  can be reduced to one member for every point of T, with all schemes in universe u.
- For each a, an étale object `V_a → S`: `∀ i, ∃ (V : S.Etale)`.
- A factorization commuting with g: `a : Z i ⟶
  (MorphismProperty.Over.pullback @Etale ⊤ g).obj V`. This is a T-morphism to
  `V ×_S T`; projection to V gives the requested factorization. Conversely, every
  commuting factorization gives precisely such a map by the pullback universal
  property. No étaleness of the map to V is imposed.
- A section `t_a ∈ F(V_a)`: `(t : F.obj.obj (op V))`.
- The restricted section equals the pullback of `t_a`: the final equality has
  restriction of s along `(π i).op` on the left, and restriction along `a.op` of
  the adjunction-unit image of t on the right. This is the exact pulled-back-section
  convention of the composition-units dependency.

Dependencies read and used:

- `def-weil-pbc-etale-sheaf-of-sets`: `CategoryTheory.Sheaf`,
  `Mathlib.CategoryTheory.Sites.Sheaf`, full subcategory of presheaves satisfying
  `Presheaf.IsSheaf`; `Scheme.smallEtaleTopology`, `Mathlib.AlgebraicGeometry.Sites.Etale`.
- `lem-weil-pbc-sets-etale-inverse-image-composition-units`:
  `AlgebraicGeometry.etaleSetInverseImageCompositionUnits`, module
  `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`. Its full signature
  and docstring were read. Its inverse image and section-pullback convention are
  used verbatim, expanded without that file's local notation: `Scheme.etaleSetPullback`
  (from `Sheaf.AlgebraicGeometry.EtaleSheaves`) and the unit of
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`
  (`Mathlib.CategoryTheory.Sites.Pullback`). This imported statement has no additional
  notion or hypothesis to repair. Its composition and associativity clauses are not
  asserted again here.

Edge cases checked: T empty admits an empty covering and the per-member condition
is vacuous; no nonempty-cover binder excludes this. With g the identity, the unit
is the canonical identity pullback comparison and ordinary restriction gives the
local representation. Empty-valued F causes no assertion without a section s.
Neither properness, flatness, finiteness, separatedness, nor a field hypothesis
is present. There is no bound on characteristic. The coefficient universe u+1
is the shared dependency encoding and admits arbitrary sets by universe enlargement.

Searches (2026-10-11):

- msearch LeanSearch: “Sections of an inverse image sheaf locally arise from sections
  of the original sheaf”: unavailable (Internal Server Error).
- msearch LeanFinder: “Every section of inverse image sheaf on small etale site locally
  comes from a section on an etale object of the base”: eight hits, including
  smallEtaleTopology, etaleTopology, Etale.forget, and localization results; no match.
- msearch Loogle: `CategoryTheory.Functor.sheafPullback, CategoryTheory.Adjunction.unit`:
  two sheafFiberComapIso component lemmas; no match.
- msearch grep: `sheafPullback|locally.*(surj|section)` in CategoryTheory/Sites:
  pullback construction and general locally surjective lemmas; no specialized statement.
- rg over `WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry` for
  sections, inverse images, local pullbacks, `etaleSetPullback`, and `Etale.mk` found the
  existing inverse-image definitions and unrelated assertions, no exact statement.
- grep of the exact node id in `WeilConjectures` found no declaration.
- Targeted rg in `WeilConjectures/SixFunctors` and `lean/Sheaf/AlgebraicGeometry` for
  `inverseImageSectionDescription|inverse_image_section|locally.*pullback` found only
  unrelated constructible and pro-étale material.

Server single-file compile: exit 0, 1.9 seconds, no errors or warnings.
No statement dispute or node fault was found. The module carries the complete
three-step natural-language proof from the node; none is proved at this stage.

## Second reading by E1

Independent second reading on 2026-10-11. Read the item's statement and all three
proof steps, both statement-dependency nodes, the dependency theorem's actual
signature and docstring, and the definitions used by the signature. Read Stacks
Tag 09XN, `lemma-describe-pullback`, including its full proof, and the original
`etale-cohomology.tex` from the Stacks project's upstream raw source because the
local literature checkout is absent. Source URLs:
https://stacks.math.columbia.edu/tag/09XN and
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex.
The local-representative paragraph is construction of inverse image for an
individual morphism; it does not use the fpqc assumption or the compatibility
of different sections from the surrounding descent argument. Specializing tau
to etale gives exactly this node. No statement correction is needed.

Objects, hypotheses, and conclusion clauses, listed before matching the Lean:

- Arbitrary schemes S and T: `(S T : Scheme.{u})`. Pass; no geometric properties
  or field, ring, finiteness, or separation hypotheses.
- An arbitrary morphism g from T to S: `(g : T ⟶ S)`. Pass; g is not required to
  be etale, surjective, flat, or proper.
- A sheaf F of sets on the small etale site of S:
  `(F : Sheaf S.smallEtaleTopology (Type (u + 1)))`. Pass. The recorded
  `CategoryTheory.Sheaf` is the full subcategory defined by `Presheaf.IsSheaf`
  (Mathlib Sites/Sheaf.lean:302), and `Scheme.smallEtaleTopology` is the topology
  of jointly surjective etale families (Sites/Etale.lean:51,61).
- Every global section s of the etale inverse image on T: the section binder
  evaluates `((Scheme.etaleSetPullback g).obj F).obj` at
  `op (Scheme.Etale.mk (𝟙 T))`. Pass; this is T as an object of its own site,
  with the universal quantification of s outside the existential covering.
  `Scheme.etaleSetPullback` in EtaleSheaves.lean is the concrete left Kan extension
  followed by sheafification, matching the inverse image used by the dependency.
- An etale covering of T, allowed to depend on s: `∃ (I : Type u)
  (Z : I → T.Etale) (π : ∀ i, Z i ⟶ Scheme.Etale.mk (𝟙 T))`, followed by
  membership of `Sieve.ofArrows Z π` in `T.smallEtaleTopology` at that object.
  Pass. `Scheme.ofArrows_mem_smallEtaleTopology_iff` identifies this membership
  with joint surjectivity. Maps between etale objects over T are etale; the
  family does not acquire an extra hypothesis.
- For every member, an etale object V over S: `∀ i : I, ∃ (V : S.Etale)`.
  Pass; V may vary with i, and no finite-cover bound is imposed.
- A factorization over S from that member through V:
  `(a : Z i ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj V)`.
  Pass. Read `Over.pullback` in MorphismProperty/OverAdjunction.lean:101:
  its object is the fibre product with T. A morphism in this over category
  commutes with the map to T; its projection to V is exactly the source's
  commuting square with g. Conversely the square gives this morphism by the
  fibre-product universal property. The property on arrows is `⊤`, so the map
  to V has no additional etaleness requirement.
- A section t of F over V: `(t : F.obj.obj (op V))`. Pass; it is the original
  sheaf's section, not an arbitrary section of its inverse image.
- Equality with the restriction of s: the left side is the inverse-image
  presheaf's map on `(π i).op` applied to s. The right side is its map on
  `a.op` applied to the image of t under the component at `op V` of
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous ... .unit.app F`.
  Pass. Read Mathlib Sites/Pullback.lean:70-78: this is the adjunction of the
  concrete pullback used in `Scheme.etaleSetPullback`, not the abstract chosen
  left adjoint. It is also exactly the unit expanded from the recorded
  `etaleSetInverseImageCompositionUnits` dependency. Its value is a section
  on the base change of V; restriction along a supplies the asserted pullback.

Edge cases: I may be empty, with no Nonempty instance. If T is empty, the empty
family is covering by the joint-surjectivity characterization and its local
conditions are vacuous. If S is empty, existence of g forces T empty. An empty
section set creates no inhabitant s to which the conclusion must apply. The
terminal sheaf and identity g cause no change in quantifier order or restriction.
Zero objects and n = 0 are not notions of this set-valued statement; there is no
integer or characteristic restriction. All scheme objects have universe u and
all coefficient sets have u+1, the established inverse-image encoding. Universe
enlargement admits any given set-valued sheaf. A covering indexed in a larger
universe can be reduced by choosing a covering member over each point of T,
so the existential `I : Type u` does not strengthen the local-existence claim.
All variables and the sole universe u are explicitly bound.

Independent searches used different wording from the first worker:

- msearch LeanSearch: "Sections of sheaf pullback are locally images of sections
  under the adjunction unit": unavailable, Internal Server Error; no negative
  mathematical result inferred.
- msearch LeanFinder: "sheafification of left Kan extension sections locally
  represented by original presheaf elements": eight hits, including
  `GrothendieckTopology.Plus.exists_rep`, `GrothendieckTopology.W_toSheafify`,
  and generic sheafification and local-injectivity declarations. These are
  construction ingredients, not this etale inverse-image section statement.
- msearch Loogle: `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`:
  four hits, the concrete pullback, adjunction, finite-limit instance, and
  comparison to the abstract pullback; no local-section theorem.
- Independent rg of Mathlib Sites, all WeilConjectures, and all lean/Sheaf for
  `locally.*(represent|lift)`, `section.*represent`, and
  `sheafPullback.*(surj|section)` found generic sheafification and local-lifting
  results, topology-basis results, and unrelated algebraic or abelian material.
  Also checked the exact declaration name and node id in the source and
  `dag/lean_names_upstream.json`; no existing declaration for this statement.
  No duplicate notion is introduced, and no module should be dropped.

H5-H9: no definition in the delivery; the sole theorem proof is `sorry`.
Both docstrings name Tag 09XN and this blueprint id. The theorem docstring
reproduces the three node proof steps: inverse-image construction, local
sheafification representatives, and colimit representatives with the required
factorization. The single import supplies the dependency and its concrete
pullback/unit notions; there are no local notations, local instances, private
copies, or hidden let/show binders. No new nodes or dependency modules occur.
No mismatch was found, so the correct Lean and node record were left unchanged;
only this independent reading was appended to the report. Checked mechanically
that `lean.statement` equals the file signature verbatim and that all Lean lines
are at most 100 characters. Server single-file compilation via scompile: exit 0,
1.9 seconds, no errors or warnings.
