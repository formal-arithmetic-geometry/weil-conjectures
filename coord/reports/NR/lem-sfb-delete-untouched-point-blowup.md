## Worker report

The module `Sheaf.AlgebraicGeometry.DeleteUntouchedPointBlowup` states
`AlgebraicGeometry.exists_delete_untouched_point_blowup`, with `sorry` as its entire
proof. It introduces no definition, helper theorem, or new node. The original
statement, dependencies, and proof plan are unchanged; only the node's `lean` field
is set. The declaration docstring gives all six steps of the node's proof, naming
their existing dependency nodes. No statement fault or dispute was found.

The original number of arrows is written `n + 1`; the shorter tower has `n` arrows.
The node's one-based index `a` is represented by `a : Fin (n + 1)`, with original
index `a.val + 1`. This represents every original `1 ≤ a ≤ length` case and does
not assume a tower of length at least two. Level indices are `Fin (n + 2)`.

Hypotheses, in the order of the node:

- The base scheme is `S : Scheme.{u}`. The family `X` and instances
  `[∀ i, (X i).Over S]` equip every level with its original structure map to `S`.
- Integrality is `[∀ i, IsIntegral (X i)]`; regularity is
  `hregular : ∀ i, IsRegularScheme (X i)`. Noetherianity is
  `[∀ i, IsNoetherian (X i)]`, which includes both local Noetherianity and
  quasi-compactness, as required. `hdim` asserts `topologicalKrullDim (X i) = 2`
  for every level, including level zero and the last level.
- The arrows are `b i : X i.succ ⟶ X i.castSucc` with
  `hbS : ∀ i, (b i).IsOver S`. The family `q` records the composites to level
  zero, determined by `hq₀ : q 0 = 𝟙 (X 0)` and
  `hq : b i ≫ q i.castSucc = q i.succ`. These are an explicit presentation of
  the original composites, not independent geometric assumptions.
- `x i` is the centre of `b i`, `hx i` states that its singleton is closed,
  and `hx_dim` asserts that its local ring has `ringKrullDim = 2`.
  `hb i` identifies the arrow, by an isomorphism over its target, with
  `(Scheme.IdealSheafData.vanishingIdeal ⟨{x i}, hx i⟩).blowupMap`.
  Mathlib's vanishing ideal supplies the reduced scheme structure, so no
  arbitrary ideal supported at the point can satisfy this presentation.
- `a : Fin (n + 1)` selects the deleted arrow. `E` is a family of ideal sheaves.
  `hEₐ` makes `E a.succ` the scheme-theoretic inverse image of the reduced
  centre under `b a`. For `a < i`, `hE` identifies `E i.succ` with the kernel
  of the existing `strictTransformMap` of `(E i.castSucc).subschemeι` along
  `b i`, on the complement of `{x i}`. Since that map is a closed immersion,
  its kernel is exactly the ideal of the strict transform as a closed
  subscheme. This uses scheme-theoretic closure, not topological closure.
  Values of `E` before `a.succ` are unrestricted and do not enter the result.
- `havoid` is `a < i → x i ∉ (E i.castSucc).support`, precisely the condition
  on every later centre and not on the deleted centre itself.
- `Z : Scheme.{u}` with `[Z.Over S]`, and `f` with `[f.IsOver S]`, give the
  stipulated target and morphism. `himage : ∃ z, f '' E_last.support = {z}`
  means that the topological image consists of exactly one point; in particular
  it excludes an empty exceptional fibre, rather than merely asserting that
  the image is subsingleton.

Conclusions, in the order of the node:

- `Y : Fin (n + 1) → Scheme.{u}`, arrows `d : ∀ j : Fin n, ...`, the
  isomorphism `e₀ : Y 0 ≅ X 0`, and the maps `p`, with
  `p 0 = e₀.hom` and `d j ≫ p j.castSucc = p j.succ`, give exactly a
  tower of `n` arrows to the original level zero. All its levels are
  integral, regular, Noetherian, and of dimension two by the displayed
  four-part conjunction for each `j`.
- Its ordered centres `y`, their closedness `hy`, and the blowup isomorphisms
  for each `d j` express that these are reduced-closed-point blowups.
  No extra local-dimension hypothesis is imposed on the new centres.
- The factor maps are `c : X_last ⟶ Y_last` and `g : Y_last ⟶ Z`.
  The equations `c ≫ p_last = q_last` and `c ≫ g = f` are exactly
  `p'c = b₁⋯b_length` and `f'c = f` in Lean's composition order.
- The structure morphism of `Y j` is explicitly `p j ≫ (X 0 ↘ S)`;
  the tower equations make each arrow an `S`-morphism. The two equations
  involving `(X 0 ↘ S)`, `(X_last ↘ S)`, and `(Z ↘ S)` assert separately
  that `c` and `g` are `S`-morphisms for this structure. Thus the result is
  over the given `S`, not just over the bottom scheme as an unbased assertion.
- `z`, `hz`, and `ec` identify `c` itself with the blowup of a reduced closed
  point. The equality `E_last = (vanishingIdeal ⟨{z}, hz⟩).comap c` identifies
  the exceptional fibre as a closed subscheme, preserving its scheme structure.
  `IsIso (c ∣_ complement {z})` is the asserted isomorphism away from that fibre.
- The last clause universally quantifies `V : (X 0).Opens` after choosing
  the shorter tower, so the result works simultaneously for every eligible
  open. The premise `∀ i, q i.castSucc (x i) ∉ V` is exactly the condition
  on every original centre. The first conclusion `∀ j, p j.castSucc (y j) ∉ V`
  is the condition on every new tower centre. The next two conclusions say
  all original and new composite maps over `V` are isomorphisms to `V`.
  The morphism `r` between the two pullbacks of `V` is constrained by both
  projections: its first-projection equation identifies it with the restriction
  of `c`, and its second-projection equation says it is the identity under
  those identifications with `V`. `IsIso r` makes the preserved-open comparison
  explicit. These witnesses cannot be arbitrary unrelated isomorphisms.

Dependency declarations used (all signatures and docstrings were opened):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  namely `IsLocallyNoetherian X ∧ IsRegular X`, with the existing stalkwise
  `IsRegular` from `WeilConjectures.AlgebraicGeometry.Regular`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  and `AlgebraicGeometry.IsNoetherian` (local Noetherianity plus `CompactSpace`).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `WeilConjectures.Compactification.StrictTransform`: `strictTransform` and
  `strictTransformMap`, with their scheme-theoretic-image definition.
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`, and
  `Scheme.Hom.isOver_iff`; this is the recorded Mathlib match of
  `def-weil-scheme-over-base`, which needs no Lean-record repair.
- The closed-point and closed-subscheme data use existing
  `Scheme.IdealSheafData.vanishingIdeal`, `subschemeι`, `comap`, and
  `Scheme.Hom.ker`; `comapIso` identifies the inverse-image ideal's subscheme
  with the fibre product. No alternate notions are defined.

Proof dependencies imported without `public`: `WeilConjectures.Blowup.Complement`
(`isIso_blowupMap_restrict_support_compl`),
`WeilConjectures.Blowup.FlatBaseChange` (`blowupFlatBaseChange` and
`blowupFlatBaseChangeIso`, the closed-upstream audit declarations of the two
flat-base-change nodes), `Mathlib.AlgebraicGeometry.Gluing`
(`Scheme.Cover.glueMorphisms`, with its restriction and uniqueness lemmas),
`Mathlib.AlgebraicGeometry.Morphisms.Proper` (`IsProper`),
`Mathlib.AlgebraicGeometry.Morphisms.Flat` (`Flat`),
`Sheaf.AlgebraicGeometry.RegularPointBlowupGeometry`
(`Scheme.regular_point_blowup_geometry`), and
`Sheaf.AlgebraicGeometry.PointBlowdownFactorization`
(`existsUnique_factor_through_point_blowup`). Strict transform and schemes over
`S` already have public statement imports. All stated proof dependencies are
therefore available to stage 3, including those with no `lean` field but a
closed upstream audit.

Edge cases checked:

- Original length one: `n = 0` and `a = 0`. `Fin n` is empty, `Y` has one
  level, its composite `p 0 = e₀.hom` is an isomorphism, and `c` is the original
  blowup up to the base identification. No shorter positive tower is required.
- Deletion of the last arrow: `a = Fin.last n`; `hE` and `havoid` have no
  later index, and no swap is required. Deletion of the first arrow is also
  included; the prefix then is empty.
- Arbitrary auxiliary `E` at earlier levels has no effect. Nonreduced
  scheme-theoretic exceptional data are retained by ideal equality and the
  strict-transform kernel, rather than replaced by their reduced supports.
- Empty exceptional image cannot satisfy `himage`. An empty original scheme
  cannot satisfy `IsIntegral`; no additional nonemptiness was inserted.
- `V = ∅` satisfies the outside condition and all restrictions/pullbacks are
  empty-scheme isomorphisms. `V = ⊤` cannot satisfy the outside condition in
  a nonempty tower. Opens disjoint from all centre images are quantified
  without quasi-compactness or affineness assumptions.
- No excellence, separatedness, base dimension, ground field, characteristic,
  or finite-type-over-`S` condition is added. One arbitrary universe `u` suffices
  for a finite diagram of schemes and all its pullbacks.

Sources opened: `literature/stacks-project/resolve.tex`, Tag 0C5J
(`lemma-factor-through-contraction`), and `divisors.tex`, Tags 0805 and 02OS
(`lemma-flat-base-change-blowing-up` and
`lemma-blowing-up-gives-effective-Cartier-divisor`). Also read the current
blueprint `latest/.../sk-thm-sf-ctf-stability/_section.md`; this auxiliary tower
lemma neither changes that unit statement nor adds its standing assumptions.
The supplied CompactObject example is now a withdrawn module with no declarations;
the delivered header follows the current module convention and nearby landed files.

Searches made on 2026-10-24 with
`python3 /home/ubuntu/weil-launcher-all/batch2/msearch.py NR
lem-sfb-delete-untouched-point-blowup ...`:

- LeanFinder query: “Delete an intermediate blowup of a regular surface when
  later centres avoid its exceptional divisor and a morphism contracts it”.
  Eight results: smooth-relative-dimension results, an ideal subscheme gluing
  immersion, a rational-map representative, normalization, and relative Proj.
  None constructs or states the deletion or its contraction comparison.
- Loogle query: `"blowupMap", "strictTransform"`. Zero results.
- Mathlib grep query: `blowup.*(commut|factor|descend)|blowdown|exceptional.*curve`,
  subdirectory `AlgebraicGeometry`. Zero results.
- LeanSearch query: “A morphism from a tower of point blowups of a regular
  surface factors after deletion of a blowup whose exceptional divisor is
  untouched by subsequent centres”. Eight results, namely over-tower instances,
  normalization factorization, properness and its base-change stability, and
  smoothness. No deletion lemma or specialization thereof.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `delete.*[Bb]lowup`, `untouched`, and tower/point-blowup terminology found no
  declaration of this statement. Related finite point-blowup presentations in
  `NodalTraitRegularization` and the surface-principalization node were read;
  they concern existence of different towers and do not delete an untouched
  exceptional curve. No existing point-blowup-tower definition was copied.
- `rg` on Mathlib, both Lean roots, and `dag/lean_names_upstream.json` for
  `exists_delete_untouched_point_blowup` found no name collision.

Validation: the module compiled with `scompile.py NR
lem-sfb-delete-untouched-point-blowup <module>` against the published live build,
both sandbox (1.9 seconds) and actual module (2.0 seconds), with no errors or
warnings. The default 60-second per-file limit was retained. Every variable and
universe is explicitly bound; `autoImplicit` is disabled. The node's `lean.statement`
is extracted verbatim from the theorem keyword up to the proof assignment.

## Second reading by NR

The dispatcher explicitly prohibits starting another agent and assigns independent
review to the maintainer. This section records the author's second pass, not an
independent approval. Reopened the node, theorem, and dependency signatures.
Checked each input and output against the mapping above, especially the `n = 0`
case, the strict inequality `a < i`, the scheme-theoretic fibre equality,
`S`-linearity of both factor maps, and the common choice of tower before `∀ V`.
The two projection conditions on `r` pin down the actual restriction of `c` and
its identity over `V`; bare existence of a pullback isomorphism would not do so.
No mismatch requiring a statement correction was found; no signature changed in
this pass. The maintainer's independent reading remains the review of this delivery.

Delivery dry run: `deliver2.py NR lem-sfb-delete-untouched-point-blowup --no-push`
printed `OK (dry run): commit a52632fbe0f passes the preflight and compiles;
nothing pushed`. The staged set was exactly the module, node record, and this report.
