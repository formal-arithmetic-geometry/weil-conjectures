## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleFilteredColimitFinitePresentation` states
`AlgebraicGeometry.Scheme.Modules.exists_filteredColimit_of_isQuasicoherent` with a
`sorry` proof. It introduces no definition and proves nothing. The theorem docstring
records all seven steps of the DAG proof and names their dependency nodes.

Hypotheses and clauses matched to Lean:

- A scheme X: `(X : Scheme.{u})`.
- X quasi-compact: `[CompactSpace X]`, the compactness of its underlying space.
- X quasi-separated: `[QuasiSeparatedSpace X]`, compactness of intersections of
  quasi-compact open subsets. On a scheme this is the convention's quasi-separatedness.
- An O_X-module F: `(F : X.Modules)`. Mathlib defines this as
  `SheafOfModules.{u} X.ringCatSheaf`; it is the category of all module sheaves,
  not the quasi-coherent full subcategory.
- F quasi-coherent: `[SheafOfModules.IsQuasicoherent.{u} (R := X.ringCatSheaf) F]`.
  This is the Mathlib notion explicitly identified by the landed `pqf-def-coherent`
  module, whose main declaration `RingedSpace.IsCoherent` is not needed here.
- Small index category: `∃ (I : Type u) (_ : SmallCategory I)`.
  Its objects and hom types are sets in the scheme/module universe. No independent
  smaller universe is imposed. The representative construction in the node's proof
  fits this universe: finite local presentations are specified by finite data over
  the site's opens and rings, and morphisms to F are in Type u.
- Nonempty, common targets, and equalization of parallel arrows:
  `(_ : IsFiltered I)`. These are precisely Mathlib's three fields of filteredness.
- A diagram in Mod(O_X): `(M : I ⥤ X.Modules)`.
- Every diagram term of finite presentation:
  `∀ i : I, SheafOfModules.IsFinitePresentation.{u} (R := X.ringCatSheaf) (M.obj i)`.
  This class is existence of local finite presentations: finite generating sections
  and finite generating sections of the kernel, equivalently the stated local
  exact sequence between finite free sheaves (Mathlib `Presentation.isColimit` and
  `presentationOfIsCokernelFree` translate the two descriptions).
- Module maps φ_i: `∃ φ : M ⟶ (Functor.const I).obj F`; its components
  `φ.app i : M.obj i ⟶ F` are module morphisms.
- Compatibility for every arrow a: the naturality field of φ says
  `M.map a ≫ φ.app i' = φ.app i ≫ 𝟙 F`, equivalently the node's equation.
- The cocone with vertex F is a colimit:
  `Nonempty (IsColimit (Cocone.mk F φ))`. IsColimit is data, so Nonempty
  expresses its existence as a proposition. Its desc, fac and uniq fields are
  the required universal property in the entire module category.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules` is definitionally
  `SheafOfModules.{u} X.ringCatSheaf`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules` and its `Hom`
  (def-weil-sheaf-of-modules-category's mathlib_match; no lean record is required).
- `Sheaf.AlgebraicGeometry.Coherent`: read its complete module and
  `RingedSpace.IsCoherent` declaration. The quasi-coherent clause of
  pqf-def-coherent is explicitly Mathlib `SheafOfModules.IsQuasicoherent`, so use
  that declaration from `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`;
  the coherence definition/import itself is unused here.
- The same Mathlib module: `SheafOfModules.IsFinitePresentation`,
  `QuasicoherentData`, `Presentation`, `Presentation.IsFinite`,
  `presentationOfIsCokernelFree`, `Presentation.isColimit`. No private copy of
  the finite-presentation notion is needed. The existing DAG node
  def-weil-pbc-module-finite-type-presentation also identifies this exact Mathlib
  specialization; the item's own statement already supplies its definition.
- `Mathlib.CategoryTheory.Filtered.Basic`: `CategoryTheory.IsFiltered`;
  `Mathlib.CategoryTheory.Limits.Cones`: `Cocone`; and
  `Mathlib.CategoryTheory.Limits.IsLimit`: `IsColimit` (the declarations listed
  in def-weil-pbc-category-colimit). We use a cocone's universal property rather
  than require a separately chosen colimit object.
- `Mathlib.Topology.QuasiSeparated`: `QuasiSeparatedSpace`, implementing the
  quasi-separated scheme convention. The conventions node fixes no new notion.

Edge cases checked mathematically before writing: the empty scheme is allowed,
with all local conditions vacuous, and admits a singleton zero diagram. The zero
module on any qcqs X is allowed, again with a singleton zero diagram. The index
category cannot be empty because IsFiltered contains nonemptiness. Presentations
with zero generators or zero relations are allowed by the finite-free definition.
There is no field, characteristic, reducedness, separation, or Noetherian assumption.
The cocone is in all module sheaves, exactly as the node requires.

Searches made on 2026-10-11:

- msearch.py LeanFinder: "A quasi-coherent module on a quasi-compact quasi-separated
  scheme is a filtered colimit of modules of finite presentation". Eight hits,
  all the finite-presentation/quasi-coherence definitions and associated local
  presentation data; no theorem giving this filtered-colimit presentation.
- msearch.py Loogle: `SheafOfModules.IsFinitePresentation,
  CategoryTheory.Limits.IsColimit`. Zero hits.
- msearch.py LeanSearch: "quasi-coherent module on qcqs scheme filtered colimit of
  finitely presented sheaves of modules". Service unavailable (Internal Server
  Error), recorded without a search verdict.
- msearch.py grep: `IsFinitePresentation|filtered colimit` in
  `Algebra/Category/ModuleCat/Sheaf`. Five hits, the finite-presentation classes
  and their instances, no matching colimit theorem.
- rg in WeilConjectures/AlgebraicGeometry for `filtered.*[Cc]olimit|finite.*[Pp]resentation`:
  general unrelated ring/scheme finite-presentation results, no matching theorem.
- rg for the item id and `exists.*[Cc]olimit.*[Pp]resentation` in WeilConjectures
  and lean/Sheaf: no hits. rg for `exists_filteredColimit_of_isQuasicoherent` in
  Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no hits.
- rg in lean/Sheaf for finite-presentation and filtered-colimit statements:
  `FinitePresentationHomDirectedColimit` is about maps from a fixed finitely
  presented module, and `ConstructibleModuleSheafColimit` is about constructible
  étale module sheaves. Neither states this theorem.
- rg in dag/nodes located def-weil-pbc-module-finite-type-presentation, whose
  statement and mathlib_match were read; the needed notion already exists.

The local Stacks source is absent on this machine. Read the primary source at
[Stacks 01PJ](https://stacks.math.columbia.edu/tag/01PJ). Its hypotheses, diagram,
finite-presentation condition, and colimit agree with the DAG statement. No
statement correction, new node, dependency module, or disputed statement is needed.

Validation: server compilation via scompile.py; final dry run via
`deliver2.py C1 lem-weil-pbc-module-filtered-colimit-finite-presentation --no-push`.

## Second reading by C1

I independently read the sandbox node and module, all five statement-dependency
nodes, and the declarations below. I fetched the primary Stacks `properties.tex`
into the sandbox scratchpad, since the local literature checkout is absent, and
read `section-extending-quasi-coherent-sheaves` and
`lemma-directed-colimit-diagram-finite-presentation` (01PJ, lines 3040–3189),
including its entire proof. The section introduction imposes no standing extra
hypothesis. I also read Modules Definition 01BN at
https://stacks.math.columbia.edu/tag/01BN. The node agrees with this source;
there is no statement correction or citer review to perform.

My object/hypothesis/conclusion checklist, made from the node:

1. Scheme X: `(X : Scheme.{u})`. PASS. I read `Scheme` and `Scheme.Hom`
   in Mathlib's Scheme module: locally ringed spaces locally isomorphic to spectra,
   with locally ringed-space morphisms, as def-pc-scheme requires.
2. Quasi-compact X: `[CompactSpace X]`. PASS: compactness of the entire underlying
   space is quasi-compactness; no Hausdorff condition is included.
3. Quasi-separated X: `[QuasiSeparatedSpace X]`. PASS. Its field requires compact
   intersections of compact opens. I checked Mathlib's morphism module
   `QuasiSeparated.lean`, especially `quasiSeparatedSpace_iff_quasiSeparated`:
   this is equivalent to the scheme diagonal being quasi-compact. The convention
   dependency defines no competing notion.
4. An O_X-module F: `(F : X.Modules)`. PASS. `Scheme.Modules` in
   `Mathlib.AlgebraicGeometry.Modules.Sheaf` is `SheafOfModules.{u} X.ringCatSheaf`;
   its Hom definition is `SheafOfModules.Hom`. I opened the latter structure and
   its category instance in `ModuleCat/Sheaf.lean`: module presheaf maps with
   sheaf underlying abelian presheaves. This is def-weil-sheaf-of-modules-category,
   not a category restricted to quasi-coherent objects.
5. Quasi-coherent F: the `SheafOfModules.IsQuasicoherent` instance binder. PASS.
   I read pqf-def-coherent and the full landed Coherent module: its quasi-coherent
   clause expressly uses this Mathlib class; `RingedSpace.IsCoherent` is only the
   coherent clause and would be the wrong hypothesis. I read `QuasicoherentData`
   and `IsQuasicoherent` in Mathlib: local free presentations, equivalent on
   schemes to the node's affine-local tilde-module formulation. No coherence,
   finite type, Noetherian, separated, field, or characteristic assumption appears.
6. Small filtered category: `∃ (I : Type u) (_ : SmallCategory I)
   (_ : IsFiltered I)`. PASS. I opened `IsFilteredOrEmpty` and `IsFiltered`:
   common targets, equalization to the right, and nonemptiness are all present.
   This is a category, not a directed-poset specialization. Objects and Hom types
   lie in the same universe u as the scheme's rings, opens and module sections.
7. Diagram: `(M : I ⥤ X.Modules)` under those existential binders. PASS: one
   functor gives the objects and all transition maps with identities/composition.
8. Every term finitely presented: `∀ i : I,
   SheafOfModules.IsFinitePresentation (M.obj i)`, with the displayed explicit
   ring and universe arguments. PASS. I read `Presentation`, `Presentation.IsFinite`,
   `QuasicoherentData.IsFinitePresentation` and `IsFinitePresentation`, as well as
   `presentationOfIsCokernelFree` and `Presentation.isColimit`. These encode local
   finite generators and finite generators of their kernel, equivalently exactly
   the local finite-free cokernel sequence specified inline in the node (01BN).
   The DAG already has def-weil-pbc-module-finite-type-presentation with this
   precise Mathlib match; there is no missing notion or private definition.
9. Module maps to F and compatibility: `∃ φ : M ⟶ (Functor.const I).obj F`.
   PASS: `φ.app i` is the required module map, and naturality for `a : i ⟶ j`
   gives `M.map a ≫ φ.app j = φ.app i ≫ 𝟙 F`, the node's compatibility equation.
   The quantifier order is unchanged: X and F first, then I, its structures and M,
   termwise finite presentation, then the compatible maps.
10. The specified cocone is a colimit in all O_X-modules:
    `Nonempty (IsColimit (Cocone.mk F φ))`. PASS. I read `Cocone` and `IsColimit`
    in Mathlib: the vertex is F, and desc/fac/uniq give the universal property
    against every cocone in X.Modules. `Nonempty` makes existence of that data a
    proposition. This is equivalent to the source's comparison isomorphism and
    uses the declarations recorded by def-weil-pbc-category-colimit.

Edge cases: an empty scheme is permitted (no Nonempty X binder), and its local
conditions are vacuous; its unique module can be presented by a singleton zero
diagram. A zero F on any qcqs scheme also admits the singleton zero diagram.
An empty indexing category cannot witness the conclusion, exactly because the
source requires filteredness including nonemptiness. Zero generators and zero
relations are allowed by finite index types (so m = 0 and n = 0 are covered).
No restriction on ring characteristic or reducedness is introduced. The universe
u is bound explicitly and arbitrary. For a qcqs scheme finite local presentations
can be encoded by finite matrices of sections on finite affine covers, all data
in Type u; Hom sets to F are in Type u too. Thus choosing representatives and
shrinking their category into Type u does not exclude a case of the source's
small-category existence assertion.

Independent searches (different wording from the worker):

- msearch LeanFinder: “Every quasicoherent sheaf on a compact quasiseparated scheme
  admits a small filtered diagram of locally finite free cokernel sheaves with
  that sheaf as colimit”. Eight hits: the finite-presentation/quasi-coherence
  definitions and their accessors, no theorem of the required form.
- msearch Loogle: `"IsQuasicoherent", "IsColimit"`. Zero hits.
- msearch LeanSearch: “A quasi coherent sheaf is generated as a filtered colimit by
  sheaves with finite local generators and relations on a qcqs scheme”. Service
  unavailable (Internal Server Error); no verdict inferred from this failure.
- msearch grep: `colimit|presentable`; returned general condensed-module colimit
  declarations, not this scheme-module statement.
- Direct rg in Mathlib's module-sheaf and scheme-module directories, upstream
  WeilConjectures/AlgebraicGeometry and this project's lean/Sheaf/AlgebraicGeometry
  for `01PJ`, filtered/colimit combinations, locally presentable, and combinations
  of IsQuasicoherent/IsFinitePresentation with IsColimit: no duplicate statement.
- Full upstream/project rg for the proposed declaration and blueprint id and
  dag/lean_names_upstream.json: no declaration already recorded. I opened the two
  relevant project search hits: FinitePresentationHomDirectedColimit states
  factorization/eventual equality for maps out of a fixed finitely presented
  module; ConstructibleModuleSheafColimit is about constructible small-etale
  coefficient sheaves. Neither is this ordinary O_X-module theorem.

No mismatch was found. I changed no Lean or node fields; I added this independent
review and search evidence only. No new definition node or dependency module is
needed. The four imports supply the carrier, local-presentation predicates,
filteredness and quasi-separatedness used in the signature. There is exactly one
named theorem with `sorry`, no definitions or proved results. Both source-bearing
blueprint docstrings are present. The theorem docstring reproduces each of the
seven proof steps, including the cyclic-image/kernel extension for injectivity
and the finite-presentation extension for surjectivity. All variables/universes
are explicitly bound, and the node's lean.statement is verbatim the signature.

Second-reader validation: scompile.py compiled the module in 2.2 seconds, exit 0,
with no warnings. Explicit signature equality and the 100-character line limit
were checked mechanically.
