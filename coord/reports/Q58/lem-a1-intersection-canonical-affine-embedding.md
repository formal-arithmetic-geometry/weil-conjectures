## Worker report

The delivery states `AlgebraicGeometry.intersection_canonical_affine_embedding` in
`Sheaf.AlgebraicGeometry.IntersectionCanonicalAffineEmbedding`. Its only theorem proof is
`sorry`. The auxiliary definition module constructs the ringed subspace using the actual
Mathlib inverse-image sheaf and its adjunction unit; no mathematical object is chosen
from an unproved existence theorem. The existing node statement is unchanged.

The source was read in `literature/stacks-project/more-groupoids.tex`, the section
“Descending ind-quasi-affine morphisms,” equation-sections-of-intersection and
lemma-sits-in-functions (Tag 0API), including the proof of the final assertion about W.

Hypothesis and conclusion correspondence:

- A scheme Y is `(Y : Scheme.{u})`.
- Every quasi-compact open is quasi-affine is `hY : ∀ U : Y.Opens,
  IsCompact (U : Set Y) → Scheme.IsQuasiAffine U.toScheme`. Mathlib's quasi-affine
  predicate includes quasi-compactness, exactly as the parenthetical definition here does.
- The family is set-indexed and nonempty: `(I : Type v) [Nonempty I]` and
  `(U : I → Y.Opens)`. Its individual quasi-compactness is `hU`.
- E is exactly the intersection: `(E : Set Y)` and `hE : E = ⋂ i, (U i : Set Y)`.
  The index universe v is arbitrary and independent of u; no small-family restriction
  has been imposed. There is no categorical limit indexed by v in the statement.
- The subspace topology is the topology on the subtype E. The structure sheaf is
  `TopCat.Sheaf.pullback CommRingCat (subspaceInclusion Y.toLocallyRingedSpace E)`
  applied to Y's sheaf. This is the recorded topological inverse image, not open
  restriction and not a sheaf inherited from a scheme structure on E.
- C is written explicitly each time as
  `(ringedSubspace Y.toLocallyRingedSpace E).presheaf.obj (op ⊤)`.
- The first existential `hlocal` supplies locality of every stalk. The definition
  `locallyRingedSubspace ... hlocal` bundles the already constructed topology and
  sheaf with this proof; it does not choose new data. This locality is a conclusion,
  not an added hypothesis on Y or E.
- `j` is a morphism of locally ringed spaces to `(Spec C).toLocallyRingedSpace`.
  `toSpecΓ C ≫ j.c.app (op ⊤) = 𝟙 _` says precisely that its section map, after
  the canonical identification C with the global sections of its spectrum, is the
  identity. The next conjunct quantifies over every normalized `j'` and states
  `j' = j`; normalization plus this conjunct is the unique-morphism claim.
- Its image is encoded by a nonempty set V of opens in Spec C, every member compact,
  with F written explicitly as `⋂₀ (SetLike.coe '' V)`. The existential `e` is an
  isomorphism of the source LRS with the inverse-image LRS on F. The equation
  `e.hom.toShHom ≫ ringedSubspaceι ... F = j.toShHom` says that this isomorphism
  identifies the actual j with inclusion of F. This asserts an isomorphism of
  structure sheaves, not just a homeomorphism. Locality `hF` is included as proof
  data for bundling the target restricted ringed space.
- For every ambient open W and `hW : (W : Set Y) ⊆ E`, the morphism l is the
  restriction/inclusion into the ringed subspace: its underlying map is explicitly
  `x ↦ ⟨x.val, hW x.property⟩`, and its ringed-space composite with the unit inclusion
  into Y equals `W.ι`. Thus its map on sections is the canonical restriction.
  The next equation identifies `l ≫ j` with the affine-adjunction morphism of
  `LocallyRingedSpace.Γ.map l.op`, exactly the homomorphism C → Γ(W,O_Y).
  Finally `IsOpenImmersion (Scheme.Hom.mk (l ≫ j))` is the node's open-immersion
  assertion. W is arbitrary and is not assumed quasi-compact. The source's L and W
  clauses are combined in this single universally quantified clause: they range over
  the same ambient opens and both conclusions are retained.
- Naturality quantifies over a scheme isomorphism `e : Y ≅ Y'` with
  `he : e.hom '' E = E'`. It asserts the existence of the induced restricted LRS
  isomorphism a, specifies its base on every point and its compatibility with the
  ringed inclusions, and gives
  `a.hom ≫ target.toΓSpec = j ≫ Spec.locallyRingedSpaceMap (Γ.map a.hom.op)`.
  This is exactly the naturality square, with contravariant section-ring map
  C' → C. The target locality proof is universally quantified proof data, so the
  equation does not depend on any choice of such a proof. No quasi-compactness or
  openness assumption is placed on E or E'.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; the scheme's underlying LRS and spectrum definitions were read.
- `Mathlib.AlgebraicGeometry.OpenImmersion`, imported publicly through QuasiAffine:
  `AlgebraicGeometry.IsOpenImmersion` is the LRS open-immersion predicate for a
  scheme morphism.
- `Mathlib.Topology.Sheaves.Functors`: `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`, their unit, and pushforward.
  The module signature and docstring were read. The abstract left adjoint is used
  consistently with its own unit; no assertion of definitional equality with
  presheaf pullback/sheafification is made.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: `LocallyRingedSpace`,
  `LocallyRingedSpace.Hom`, its sheafed-space forgetful map and global-section functor.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`:
  `ΓSpec.locallyRingedSpaceAdjunction`, `LocallyRingedSpace.toΓSpec`,
  `toSpecΓ`, and `Spec.locallyRingedSpaceMap`. The adjunction signature, its
  homEquiv formula and the left-triangle section normalization were read.
- `Mathlib.AlgebraicGeometry.QuasiAffine`: `Scheme.IsQuasiAffine` and the canonical
  affinization open-immersion instance; these do not cover nonopen E.
- The additional statement dependency `def-a1-ringed-subspace` supplies
  `LocallyRingedSpace.subspaceInclusion`, `ringedSubspace`, `ringedSubspaceι`, and
  `locallyRingedSubspace` from the delivered `Sheaf.AlgebraicGeometry.RingedSubspace`.

The module also imports the recorded, available proof infrastructure:
`Sheaf.Topology.SpectralLimitPullbackSections`, `Sheaf.Topology.SetsInverseImageComposition`,
`WeilConjectures.Topology.InverseImageStalk` (read from the published source using
`scompile.py --source`), Mathlib's sheafification comparison, filtered ring colimits,
function-field/stalk and sheaf-stalk modules. The two proof nodes
`lem-a1-filtered-spectrum-topological-limit` and
`lem-a1-quasi-affine-open-affinization-square` have no recorded declaration on the
read base; they are proof-only dependencies and are not needed to type this statement.
Their future module imports belong to maintainer bookkeeping. No statement prerequisite
is missing and no dependency interface was replaced.

Edge cases checked before writing:

- Empty Y and empty E are permitted; local-stalk conditions are vacuous on E, and
  the section ring is allowed to be the zero ring. Spec C and its intersection image
  can consequently be empty. No nontrivial-ring or nonempty-space binder was added.
- A nonempty family containing an empty open is permitted and has E empty.
- The singleton-family case covers an individual quasi-compact open.
- E can be nonopen (for example a localization-type intersection in an affine
  scheme). Neither `Opens Y` nor `Scheme` is used as its type.
- W can be empty or fail to be quasi-compact; both are included by its universal
  binder. The identity isomorphism and self-isomorphisms preserving E are included
  in naturality, and repeated members of the original family are allowed.
- An empty index family is excluded exactly by the node's explicit nonemptiness
  requirement; no ambient quasi-compactness, separatedness, or noetherian assumption
  is added.

Searches made:

- `msearch.py leanfinder`, “An intersection of quasi compact opens in an ind quasi
  affine scheme embeds in the spectrum of its global sections”: eight hits headed
  by `Scheme.instIsOpenImmersionToSpecΓOfIsQuasiAffine`; this concerns schemes and
  does not state the arbitrary-intersection theorem.
- `msearch.py loogle`, `"LocallyRingedSpace", "restrict"`: twelve hits, all open
  restriction or its stalk formulas. The full signature requires `IsOpenEmbedding`.
- `msearch.py leansearch` and `leanfinder`, “The inverse image of the structure sheaf
  on an arbitrary subspace of a locally ringed space”: eight hits each, on O, open
  restrictions and spectrum component formulas. None constructs the arbitrary subspace.
- `msearch.py grep`, `subspace|inverseImage|inverse_image`, in `Geometry/RingedSpace`:
  eight hits, all gluing or open/top restriction comments.
- Direct `rg` in Mathlib RingedSpace sources confirmed only open restriction APIs;
  direct `rg` in WeilConjectures and lean/Sheaf for
  `ringedSubspace|locallyRingedSubspace|subspaceInclusion|ringedSubspaceι|intersection_canonical_affine_embedding`
  returned no declaration. Searching the item's ID in WeilConjectures returned no hit.
  The upstream declaration index contained no corresponding name.
- DAG phrase/name search for ringed subspace: the current item and two statements
  about open restrictions of modules, neither defining this object.
  `tools/blueprint_refs.py search 'locally ringed subspace'` found zero blueprint nodes.

No STATEMENT-DISPUTED issue or statement correction was needed. The eight-step source
proof plan is retained in the theorem docstring. All mathematical definitions have real
bodies, and no theorem has been proved in this stage-2 delivery.

## New nodes

`def-a1-ringed-subspace` defines the inverse-image ringed space of an arbitrary subset
of a locally ringed space, its ringed inclusion given by the adjunction unit, and its
bundling with a supplied locality proof. The source is Tag 0API's `(E,O_X|E)` in the
statement and the first sentence of its proof. Mathlib's open restriction is inapplicable
to a general E, and the recorded sheaf inverse-image node supplies a sheaf functor but
no bundled ringed subspace. The searches above and in the new node record found no
existing definition node or declaration. All four definitions are recorded in
`lean.declarations`. The item cites this new node as an added statement dependency.

Validation: `scompile.py Q58 lem-a1-intersection-canonical-affine-embedding` compiled
both delivered files separately, in dependency order, including their library-module
checks, with exit code 0 and no warnings. The successful statement includes all
clauses above. Earlier elaboration diagnostics were repaired by opening the LRS
namespace inside AlgebraicGeometry, preserving projection syntax while wrapping long
lines, and making the ambient spectrum explicit in the compact-open coercion.

## Second reading by Q58

Independent maintainer second reading of immutable delivery
0e60a525487a5c0375396e59f86043cf62943bc0, performed on 2026-10-18.
The original heading contained only a disclaimer, not a reading (H11); this complete
replacement report supplies the actual reading. No Lean or node statement was changed.

I read the item node, all six statement dependencies, both delivered modules, their
module and declaration docstrings, and the source in more-groupoids.tex:2958–3059
(Tag 0API, including the preceding sections formula and the final W argument).
The source definition of ind-quasi-affine is in more-morphisms.tex:19522–19534.

Clause-by-clause check:

- Y is Scheme.{u}. hY says every compact ambient open is quasi-affine. The exact
  Mathlib Scheme.IsQuasiAffine predicate includes CompactSpace and immersion of
  toSpecΓ; its canonical map is an open immersion. This matches the node's
  quasi-compact quasi-affine convention and the source's ind-quasi-affine hypothesis.
- I : Type v, Nonempty I, U, hU and hE give precisely a nonempty indexed family of
  quasi-compact opens and its intersection. No compactness of E or Y is assumed.
  v is independent of u: this is a set intersection, not a large categorical limit.
  In the proof outline the family can be replaced by the set of distinct opens,
  which is small in u, before applying the small-index spectral-limit interface.
- subspaceInclusion is the continuous subtype inclusion. ringedSubspace uses the
  actual CommRingCat sheaf pullback and ringedSubspaceι its own adjunction unit.
  The abstract pullback is canonically isomorphic to sheafification of presheaf
  pullback by Sites.Pullback.sheafPullbackConstruction.sheafPullbackIso. Using its
  matching unit consistently is valid; no definitional-equality claim is needed.
- The existential hlocal proves locality rather than assuming it. The bundle
  locallyRingedSubspace changes only proof data. C is exactly its sheaf's value
  at the top open. j has the required LRS source and affine-spectrum target.
- toSpecΓ C followed by j.c.app at top equals the identity; this is exactly the
  normalization in GammaSpecAdjunction.Γ_Spec_left_triangle. Quantification over
  every normalized j' gives uniqueness of the LRS morphism, not merely its base.
- V is a nonempty set of compact opens and F is their set intersection. The LRS
  isomorphism e together with its equation against ringedSubspaceι identifies
  the actual j and both structure sheaves, not just the image topology.
  Requiring V nonempty loses no case: Spec C itself is quasi-compact.
- The W clause covers every ambient open contained in E. Its l has the subtype
  inclusion as base and its composite with the ringed inclusion equals W.ι.
  The pullback adjunction characterizes its sheaf map as canonical restriction.
  The homEquiv equation is the map corresponding to C → Γ(W,O_Y). Thus the L
  restriction clause and W open-immersion clause are both present. Scheme.Hom.mk
  wraps the LRS map between the already given schemes; it assumes no scheme
  structure on E. W need not be quasi-compact.
- Naturality uses every scheme isomorphism e carrying E onto E'. The induced a
  has the required point map and compatibility with the ringed inclusions. Its
  final equation has the contravariant section-ring map C' → C in the right
  direction. Universal hlocal' is only proof data, not a stronger scheme
  hypothesis; locality follows from the same inverse-image stalk fact.

Exact APIs read: Scheme and Scheme.Hom/Spec/Spec.map; LocallyRingedSpace and its
Hom, Γ and open restriction; IsOpenImmersion; TopCat.Sheaf.pullback and
pullbackPushforwardAdjunction; Sites.Pullback's abstract/construction comparison;
ΓSpec.locallyRingedSpaceAdjunction.homEquiv, toΓSpec and Γ_Spec_left_triangle;
Scheme.IsQuasiAffine and its canonical open-immersion instance. All six dependency
notions are used through their recorded APIs or the new node's four definitions.
The two unstated proof-only affine-limit/square nodes are not prerequisites for
typing this statement and do not require substitute definitions in this delivery.

Independent searches with rg for ringedSubspace, locallyRingedSubspace,
subspaceInclusion and intersection/affinization terminology in Mathlib RingedSpace,
WeilConjectures and the group clone's lean/Sheaf found no duplicate of these
constructions or this theorem. The existing LRS restrict API requires an open
embedding and cannot handle nonopen E. The worker's three search categories are
recorded above. The new node has the required source, ancestry, chapter/unit,
searches, definition status, empty proof fields and complete Lean record.

Edge cases: empty Y, empty E, a family containing the empty open, zero section
ring, singleton and repeated family members, nonopen E, empty/noncompact W,
identity isomorphisms and arbitrary index universe v are covered. Only the empty
index family is excluded, as required. There is no Nontrivial, Noetherian,
separatedness, or extra finiteness binder.

Both lean.statement fields were checked verbatim as substrings of the delivered
signatures. All variables/universes are bound. Both files meet the 100-character
limit. The four definitions contain real data; the sole theorem proof is sorry.
Source/blueprint docstrings and all eight proof steps are present. No route-pivot
dropped node occurs in stmt_deps or proof_deps, and no repair note for this item
exists in the inspected shared origin/newtargets-dag ref. The delivery introduces
no dropped enhancement machinery and no pro-etale replacement.

Compiler reproduction: the prescribed scompile.py was invoked on both immutable
snapshot modules together, in dependency order. The installed wrapper uses a
private server side overlay rather than the older brief's local implementation;
no direct SSH command, global build, live Lean write or project edit was used.
The wrapper returned exit code 0 with no diagnostics. RingedSubspace library check
took 23.9 seconds; IntersectionCanonicalAffineEmbedding library check took 30.8
seconds. Its private-overlay, preliminary and sandbox checks also succeeded.
The output named the private overlay /dev/shm/nt-tmp/nt-local-compile-islxia56/.lbuild.
