## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover` states
`AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_bijective_on_affine_open_cover`.
Its only theorem proof is `sorry`; no definitions, instances, or proofs are added.
The item's node is copied with only its `lean` field changed.

Clause-by-clause correspondence:

- The scheme Y is `{Y : Scheme.{u}}`.
- The O_Y-modules F and G are `{F G : Y.Modules}`. Mathlib defines `Y.Modules`
  as `SheafOfModules.{u} Y.ringCatSheaf`, the dependency's category.
- Their quasi-coherence is `[F.IsQuasicoherent] [G.IsQuasicoherent]`.
- The O_Y-linear morphism φ is `(φ : F ⟶ G)` in that module category.
- The arbitrary index set A is `{A : Type v}` and its open subschemes are
  `(W : A → Y.Opens)`; opens carry Mathlib's canonical open subscheme structure.
- The covering condition Y = union of the W_a is `(hcover : iSup W = ⊤)`:
  the supremum of opens is their union and the top open is the whole scheme.
- Every cover member is affine: `(haffine : ∀ a : A, IsAffineOpen (W a))`.
  `IsAffineOpen U` is Mathlib's `IsAffine U` for the corresponding open subscheme.
- The section map on every member is bijective:
  `(hbijective : ∀ a : A, Function.Bijective (φ.app (W a)))`.
  `Scheme.Modules.Hom.app` is the underlying abelian-group section map;
  `Hom.app_smul` says it is O_Y(W_a)-linear, so its underlying bijectivity is
  exactly the node's condition.
- The conclusion that φ is an isomorphism of O_Y-modules is `IsIso φ` in
  `Y.Modules`, and therefore requires an inverse in the module category.

Dependencies read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; full declarations and docstrings read.
- `pqf-def-coherent`: imported module `Sheaf.AlgebraicGeometry.Coherent`.
  Its recorded main declaration is `AlgebraicGeometry.RingedSpace.IsCoherent`,
  whose full definition/docstring were read. Its module docstring explicitly
  records that the quasi-coherent clause uses Mathlib's
  `SheafOfModules.IsQuasicoherent` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` (signature/docstring read),
  rather than a project definition. This is also the COHERENT SHEAVES convention
  in coord/STATE.md. The coherent clause is not a hypothesis of this item.
- `def-weil-sheaf-of-modules-category`: its `mathlib_match` is `SheafOfModules`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`; the structure, `Hom`, and category
  signatures/docstrings were read. The specialized `Scheme.Modules`, `Hom.app`,
  `Hom.app_smul`, and `Hom.isIso_iff_isIso_app` were read in
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`. These imports are supplied by
  `Sheaf.AlgebraicGeometry.Coherent`; there is no private copy of any notion.

Source check: the local literature/stacks-project files are absent on this
machine, so the cited tags were opened directly on the Stacks website:
[01IA](https://stacks.math.columbia.edu/tag/01IA),
[01IB](https://stacks.math.columbia.edu/tag/01IB),
[04TN](https://stacks.math.columbia.edu/tag/04TN), and
[01SB](https://stacks.math.columbia.edu/tag/01SB).
The first two supply the affine module equivalence; the third glues compatible
maps; the last uses affine-cover checking in its proof. The theorem docstring
includes all four proof steps of the node: transport to Spec of the section
ring, apply naturality and invertibility of the tilde/Gamma counits, transport
back to the open, and glue the local inverses. The proof's cited nodes are named
in those steps, without importing modules needed only for the future proof.

Edge cases checked mathematically before writing:

- The index set may be empty. Its supremum is the bottom open, so the cover
  condition then forces Y to be empty. On an empty scheme all module sheaves
  are zero and every module morphism is an isomorphism, as required.
- Empty cover members are allowed: the empty scheme is affine (Spec of the
  zero ring), and its section maps are between trivial modules.
- Zero modules, identity maps, redundant cover members, and an infinite affine
  cover satisfy the same formulation. No nonemptiness, finiteness, separation,
  Noetherian, or characteristic hypothesis is imposed.
- The independent index universe v does not bound the scheme or modules; this
  is a union of opens, not a limit/colimit of schemes with a smallness issue.
  Every variable and both universes are explicitly bound.

Searches (actual tool outputs, 2026-10-11):

- `msearch.py ... leansearch "A map between quasi-coherent sheaves of modules
  is an isomorphism if bijective on sections over an affine open cover"`:
  UNAVAILABLE, zero hits, Internal Server Error. No absence verdict inferred.
- `msearch.py ... leanfinder "A morphism between quasi-coherent modules on a
  scheme is an isomorphism if its sections maps on an affine open cover are
  bijective"`: eight hits, including `Scheme.Modules.Hom.isIso_iff_isIso_app`,
  `instIsIsoAbApp`, `Sheaf.isLocallyBijective_iff_isIso`,
  `PresheafOfModules.homEquivOfIsLocallyBijective`, and criteria for morphisms
  of schemes. None states this affine-cover module criterion. The all-opens
  criterion requires every open rather than only the specified affine cover.
- `msearch.py ... loogle "AlgebraicGeometry.IsAffineOpen, CategoryTheory.IsIso"`:
  seven hits for affine opens, scheme morphisms, and pushout sections, none
  concerning a morphism between quasi-coherent module sheaves on a cover.
- `msearch.py ... grep "isIso_of.*[Aa]ffine|isIso.*[Cc]over|isIso_iff_isIso_app"
  AlgebraicGeometry/Modules`: three hits, all the all-opens section criterion
  and its instance in Mathlib/AlgebraicGeometry/Modules/Sheaf.lean.
- `rg` for `isIso.*[Cc]over|isIso.*[Aa]ffine|bijective.*[Aa]ffine` in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf`: no exact
  theorem matching this node. The source includes
  `AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_app_of_isAffineOpen` in
  `WeilConjectures/AlgebraicGeometry/Modules/LocallyFreeAffine.lean:180`. Its full
  signature and docstring were read: it assumes bijectivity on EVERY affine
  open, for arbitrary modules, rather than on a specified affine cover for
  quasi-coherent modules. It therefore does not state this node. Other source
  hits concern restriction or affine morphisms. An earlier project search
  found the node's name only
  in the proof docstring of `AffineModuleCorrespondence.lean`.
- `grep -rn "lem-weil-pbc-quasi-coherent-iso-on-affine-cover"` in the source
  repository's WeilConjectures directory: no hits.
- Proposed declaration name searched with `rg` in dag/lean_names_upstream.json,
  Mathlib, WeilConjectures, and lean/Sheaf: no collision.

No statement dispute, correction, new node, or unusable dependency was found.
Server validation: `scompile.py E1 lem-weil-pbc-quasi-coherent-iso-on-affine-cover
<module>` returned exit code 0, compiled in 2.3 seconds, with no warnings.

Delivery validation: `deliver2.py E1 lem-weil-pbc-quasi-coherent-iso-on-affine-cover
--no-push` printed OK: server compile and preflight pass apart from the independent
second reading, which the second reader supplies. Nothing was pushed.

## Second reading by E1

Independent second reader, 2026-10-11. I opened the delivered node and module,
all three statement dependency nodes, their recorded declarations and module
docstrings, and the source places before judging the Lean. No mismatch found;
no Lean or node fields changed. This section is the only review change.

Objects, hypotheses, and conclusion, in the node's order:

1. An arbitrary scheme Y: `{Y : Scheme.{u}}`. PASS. The recorded
   `AlgebraicGeometry.Scheme` is a locally ringed space locally isomorphic to
   a ring spectrum; no field, finiteness, or separation condition is hidden.
2. Two O_Y-modules F and G: `{F G : Y.Modules}`. PASS. I read
   `Scheme.Modules := SheafOfModules.{u} Y.ringCatSheaf` and the latter's
   structure and category. This is exactly the module-sheaf dependency,
   specialized to the scheme's Zariski site and structure sheaf.
3. Both modules quasi-coherent: `[F.IsQuasicoherent] [G.IsQuasicoherent]`.
   PASS. The pqf-def-coherent module explicitly assigns its quasi-coherent
   clause to Mathlib's `SheafOfModules.IsQuasicoherent`. I read this class:
   local cokernel presentations by free modules. On schemes this is the
   affine-local tilde-module notion of the node by Stacks 01IA. The recorded
   `RingedSpace.IsCoherent` is a different clause of that dependency and is
   correctly not used as an extra hypothesis here.
4. An O_Y-linear morphism phi: `(φ : F ⟶ G)`. PASS. The category uses
   `SheafOfModules.Hom`, not arbitrary maps of underlying sheaves or sets.
5. An arbitrary indexed family of open subschemes: `{A : Type v}` and
   `(W : A → Y.Opens)`. PASS. I read `Scheme.Opens` and `IsAffineOpen`:
   the latter is `IsAffine` of the canonical open subscheme.
6. The union equals Y: `(hcover : iSup W = ⊤)`. PASS. Supremum of opens
   is union; top is the whole space. There is no extra covering condition.
7. Every member affine: `(haffine : ∀ a : A, IsAffineOpen (W a))`. PASS.
   This concerns precisely the open subschemes introduced in item 5.
8. Every specified section map bijective:
   `(hbijective : ∀ a : A, Function.Bijective (φ.app (W a)))`. PASS.
   I read `Hom.app`, which forgets the section module map to its underlying
   abelian-group map, and `Hom.app_smul`, which confirms O_Y(W a)-linearity.
   Thus underlying bijectivity is exactly the stated hypothesis.
9. The conclusion: `IsIso φ`. PASS. This is invertibility in Y.Modules,
   including a module-linear inverse, with no extra existential choices or
   weakened conclusion. All hypotheses precede the conclusion as in the node.

Source: local Stacks .tex files are absent. I read the official pages
[01IA](https://stacks.math.columbia.edu/tag/01IA),
[01IB](https://stacks.math.columbia.edu/tag/01IB),
[04TN](https://stacks.math.columbia.edu/tag/04TN), and
[01SB](https://stacks.math.columbia.edu/tag/01SB), and independently fetched
and read the raw official `schemes.tex` labels
`section-quasi-coherent-affine`, `lemma-quasi-coherent-affine`, and
`lemma-equivalence-quasi-coherent`, `sheaves.tex` label `lemma-glue-maps`,
and `morphisms.tex` label `lemma-affine-equivalence-modules` from
https://github.com/stacks/stacks-project. The affine section has no standing
Noetherian or field assumption. The extra affine morphism of 01SB belongs to
its application, not the module isomorphism criterion assembled from the
other tags. No source hypothesis is missing.

Edge cases: A may be empty; `iSup W = ⊤` then forces the empty scheme,
where every module sheaf has trivial sections and every morphism is invertible.
Empty members are allowed (the empty scheme is Spec of the zero ring).
Zero modules, redundant members, infinite covers, and arbitrary
characteristics are included. There is no n, degree, or finite-rank parameter.
The explicit universes u and v bind every variable. Independent v is suitable
for a union of opens, not a scheme limit, and arbitrarily larger module
carriers can be included by raising u for the scheme too. No nonempty-index
or small-index condition has slipped in.

Independent searches, with queries different from the first reader:

- `msearch.py E1 <item> leanfinder "invertibility of a quasi coherent sheaf
  homomorphism tested on a covering by affine charts"`: OK, eight hits.
  The relevant `Hom.isIso_iff_isIso_app` quantifies over all opens; I opened
  its signature. Other hits concern presentations or affine scheme maps.
- `msearch.py E1 <item> loogle
  'AlgebraicGeometry.Scheme.Modules.Hom.app, "bijective"'`: OK, zero hits.
- `msearch.py E1 <item> leansearch "sections on an affine covering detect an
  isomorphism between quasicoherent modules"`: UNAVAILABLE (Internal Server
  Error); this gives no absence verdict. LeanFinder, Loogle and grep worked.
- `rg -n 'bijective_app|isIso.*(affine|Affine)|isIso.*(cover|Cover)'` in
  source `WeilConjectures/AlgebraicGeometry/Modules`, project
  `lean/Sheaf/AlgebraicGeometry`, and Mathlib's scheme modules. I opened
  `isIso_of_bijective_app_of_isAffineOpen` in LocallyFreeAffine: it assumes
  every affine open, without quasi-coherence. I also opened
  `isIso_of_bijective_app_top` in AffineDescent: it assumes a single Spec R.
  `Hom.isIso_of_forall_bijective_app` in PullbackFreeGenerator requires all
  subopens of local neighbourhoods. None is this arbitrary affine-cover
  criterion, and none warrants replacing this delivery with existing:true.

H5/H6: the only new declaration is the named theorem with `by sorry`;
no data definitions, instances, or proved helpers are introduced.
H8: both docstrings name the sources and blueprint id. The theorem docstring
carries all four node steps: transport to Spec of sections; use counit
naturality and the affine equivalence; transport back; glue inverse maps.
H9: namespaces, topic, explicit binders, import, and 100-character line bound
are correct. I compared the node's lean.statement with the extracted signature
byte for byte: equal. There are no new nodes, dependency modules, or statement
corrections to review. No repair was necessary.

Second-reader validation: `scompile.py` with the absolute module path returned
exit code 0, compiled in 2.3 seconds, with no warnings. The initial invocation
with a relative sandbox path from the read-only repository could not find the
file; rerunning with the absolute path resolved this invocation error.
`deliver2.py E1 lem-weil-pbc-quasi-coherent-iso-on-affine-cover --no-push`
printed OK: preflight and server compilation passed.
