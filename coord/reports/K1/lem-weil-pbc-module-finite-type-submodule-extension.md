## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension` states
`AlgebraicGeometry.Scheme.Modules.exists_quasicoherent_finiteType_submodule_extension`.
Its only proof is `sorry`; no definitions or proofs were added. The node is unchanged
except for `lean`.

Hypotheses and clauses, in order:

- Scheme X: `{X : Scheme.{u}}`, the recorded `AlgebraicGeometry.Scheme`.
- X quasi-compact and quasi-separated: `[CompactSpace X] [QuasiSeparatedSpace X]`.
  These are the convention node's underlying topological properties, with no Hausdorff
  assumption. U is an open subscheme: `(U : X.Opens)`. Its quasi-compactness is
  `[CompactSpace U]`, compactness of the open subtype, equivalent to compactness of
  its underlying subset.
- O_X-module F: `(F : X.Modules)`, definitionally `SheafOfModules.{u} X.ringCatSheaf`.
  Quasi-coherence is `[F.IsQuasicoherent]`.
- Restriction means `F.over U`, the existing sectionwise restriction on `Over U`;
  objects are opens T together with T ≤ U. Its underlying sections and restrictions
  are those of F at T. This uses Mathlib's `SheafOfModules.over`, not tensor pullback
  and not a new restriction definition.
- Given G is `(G : SheafOfModules.{u} (X.ringCatSheaf.over U))` with
  `[G.IsQuasicoherent] [G.IsFiniteType]`. Its submodule inclusion is `(ι : G ⟶ F.over U)
  [Mono ι]`. A monomorphism of module sheaves is injective on sections (kernels are
  sectionwise); its component images are O(T)-submodules stable under restriction,
  and G is already a sheaf. Conversely every submodule in the node has this encoding.
- The existential G' is an O_X-module in `X.Modules`; `G'.IsQuasicoherent ∧
  G'.IsFiniteType` supplies exactly the two demanded properties. Its map `ι' : G' ⟶ F`
  with `Mono ι'` supplies the submodule.
- Equality on U AS SUBMODULES is `∃ e : G'.over U ≅ G, e.hom ≫ ι = ι'.over U`.
  Since e is bijective on sections, this equation makes both inclusions have exactly
  the same images inside F(T) for EVERY T ≤ U. Conversely equal subsheaves supply
  this unique inclusion-compatible isomorphism. Thus it states equality of subobjects,
  not just abstract isomorphism of modules; no conclusion or hypothesis changes.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-pbc-scheme-conventions` is explicitly a convention with no declaration;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` supplies the scheme's
  `QuasiSeparatedSpace` formulation.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (recorded mathlib_match for
  `def-weil-pbc-quasi-compact-scheme`).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules` and its `Hom`;
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules`.
- `Sheaf.AlgebraicGeometry.Coherent` (pqf-def-coherent) explicitly records its first
  two clauses as Mathlib's `SheafOfModules.IsQuasicoherent` and `.IsFiniteType`,
  and only defines the third, `.RingedSpace.IsCoherent`, which this lemma does not need.
  Its recorded declaration and complete docstring were read; no dependency module
  is necessary because the module already gives the exact notions and imports them.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`: `SheafOfModules.IsFiniteType`,
  local finite generating sections, recorded by def-weil-pbc-module-finite-type-presentation.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`: `over`,
  `overFunctor`, `Hom.over`; `Quasicoherent`: `IsQuasicoherent`.

Edge cases: empty X and empty U are allowed. U = top allows G' = G under the canonical
restriction identification. G = 0 has the zero submodule as extension; finite type
permits zero generators. Neither F nor X is assumed Noetherian, F need not be finite
or coherent, and there is no separatedness assumption beyond quasi-separatedness.
The arbitrary explicit universe u is shared with the usual category X.Modules;
no independent universe of tests can make a hypothesis vacuous.

Searches (2026-10-11):

- msearch.py leanfinder, "A finite type quasi-coherent submodule over a quasi-compact
  open of a qcqs scheme extends to a finite type quasi-coherent submodule on the whole
  scheme": eight hits, for qcqs structure-sheaf section localization and finite-type
  generators; no extension theorem.
- msearch.py loogle, "SheafOfModules.IsQuasicoherent, SheafOfModules.IsFiniteType":
  zero hits.
- msearch.py grep, "extend.*finite|finite.*submodule|submodule.*extend" in
  AlgebraicGeometry: Artinian comment and IsProper declaration, neither a match.
- rg over WeilConjectures for the same patterns and the item id: no item-id match;
  `Compactification/FiniteTypeExtension.lean` has finite-type IDEAL extensions.
  Read `exists_finiteType_le_comap_eq_of_le`, `exists_finiteType_le_comap_eq`, and
  `exists_finiteType_comap_eq`: these concern IdealSheafData, not arbitrary module F,
  so they do not already state this node. Other results concern blowups or scalars.
- rg over lean/Sheaf for the patterns and chosen declaration name: coherent submodules,
  ring submodules, and derivation extensions only; no matching module-extension statement.
- rg of dag/lean_names_upstream.json for the chosen full declaration suffix: no match.

The locally absent literature/stacks-project/properties.tex was checked instead at
https://stacks.math.columbia.edu/tag/01PF (Lemma 28.23.2): precisely the same hypotheses
and conclusion. Its proof uses finite affine enlargement and finite local generators;
all seven more detailed DAG steps are recorded in the theorem docstring, with nodes.
No statement faults or STATEMENT-DISPUTED concerns were found.

Validation: scompile.py on the server succeeds with no errors or warnings. The required
no-push dry run is the last validation step; the independent second reader will supply
its own section and deliver.

## Second reading by K1

I independently opened the item's node, the delivered Lean file, and all six
statement dependency nodes. I read the source's `lemma-extend` in properties.tex
at https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex,
including the introduction to its section and the preceding lemma, and checked
its tag at https://stacks.math.columbia.edu/tag/01PF. The section imposes no
additional standing hypotheses. The node and the source agree; no correction
record or citer recheck is needed.

Objects, hypotheses, and conclusion clauses matched separately:

1. A scheme X: `{X : Scheme.{u}}`. PASS. I read `Scheme` in
   Mathlib/AlgebraicGeometry/Scheme.lean:42: a locally ringed space locally
   isomorphic to spectra. This is def-pc-scheme's recorded declaration.
2. X is quasi-compact: `[CompactSpace X]`. PASS. I read `CompactSpace` in
   Mathlib/Topology/Defs/Filter.lean:283; it is compactness without Hausdorffness,
   exactly def-weil-pbc-quasi-compact-scheme's recorded match.
3. X is quasi-separated: `[QuasiSeparatedSpace X]`. PASS. I read
   `quasiSeparatedSpace_iff_forall_affineOpens` and
   `quasiSeparatedSpace_iff_quasiSeparated` in Morphisms/QuasiSeparated.lean:
   these identify the topological condition with compact intersections of affine
   opens and with quasi-separatedness of the structural morphism. The convention
   dependency fixes no additional declaration or assumption.
4. U is an open subscheme of X: `(U : X.Opens)`. PASS. Its canonical scheme
   structure is the open restriction; no unrelated morphism or base is supplied.
5. U is quasi-compact: `[CompactSpace U]`. PASS. Compactness of the open subtype
   is compactness of its underlying subset, with no closedness assumption.
6. F is an O_X-module: `(F : X.Modules)`. PASS. I read Modules.Sheaf.lean:39:
   `Modules := SheafOfModules.{u} X.ringCatSheaf`. I also read the structure and
   linear morphisms in ModuleCat/Sheaf.lean:33 and :43, the match recorded by
   def-weil-sheaf-of-modules-category.
7. F is quasi-coherent: `[F.IsQuasicoherent]`. PASS. The dependency module
   Sheaf/AlgebraicGeometry/Coherent.lean explicitly records this clause of
   pqf-def-coherent as Mathlib's existing IsQuasicoherent, and I read its
   local-presentation definition in Sheaf/Quasicoherent.lean:251. On schemes
   this is the node's affine-local quasi-coherence, without finite relations.
8. G is an O_U-module: `(G : SheafOfModules.{u} (X.ringCatSheaf.over U))`.
   PASS. I read `overFunctor`, `over`, and `Hom.over` in
   Sheaf/PushforwardContinuous.lean:59-73. They restrict sections along the
   forgetful functor from opens over U. I also read `Scheme.Modules.overEquiv`
   in Modules/Sheaf.lean:558, identifying this carrier with U.Modules.
9. G is a submodule of F restricted to U: `(ι : G ⟶ F.over U) [Mono ι]`.
   PASS. Sheaf/Limits.lean supplies sectionwise limits and evaluation preserving
   finite limits, so these monomorphisms are injective on sections. Their images
   form exactly the compatible module subsheaves specified by the node. Conversely
   any such subsheaf has this monomorphism representation. This is not an extra
   restriction on G.
10. G is quasi-coherent and finite type: `[G.IsQuasicoherent] [G.IsFiniteType]`.
    PASS. I read IsFiniteType and LocalGeneratorsData in Sheaf/Generators.lean:
    local finite generating sections, with finite index types allowed to be empty.
    This is clause (1) of def-weil-pbc-module-finite-type-presentation, not finite
    presentation or coherence.
11. There exists an O_X-submodule G' of F: `∃ (G' : X.Modules), ... ∃ (ι' : G' ⟶ F),
    Mono ι' ∧ ...`. PASS, by the same sectionwise interpretation as in item 9.
12. G' is quasi-coherent and finite type: `G'.IsQuasicoherent ∧ G'.IsFiniteType`.
    PASS; no additional property is demanded of F or G'.
13. G' restricts to G AS SUBMODULES of F|_U: `∃ (e : G'.over U ≅ G),
    e.hom ≫ ι = ι'.over U`. PASS. Componentwise, e is an invertible linear map
    and the equation identifies the two images inside F(T), for every T contained
    in U. Conversely equal sectionwise submodules give the unique compatible
    isomorphism. Omitting the equation would weaken the conclusion, but it is
    present, with the correct composition orientation and quantifier order.

Edge cases: X and U may be empty; neither has a Nonempty binder. When U is empty,
G is the zero sheaf and the zero submodule extends it. Zero F and zero G are
allowed. U = top is covered, including the source's n = 0 affine-enlargement case.
There is no index type or positive-generator requirement in the signature.
There is no base field, characteristic restriction, Noetherian hypothesis,
separatedness hypothesis, or finite-type assumption on F. The explicit arbitrary
universe u covers the usual module category over any Scheme.{u}; no independent
universe of tests creates a vacuous hypothesis. All variables and u are bound.

Independent duplicate searches, with different search words from the first reader:

- msearch leanfinder: "quasicoherent subsheaf finite generated restriction extends
  on qcqs scheme". Eight hits: local finite generators and qcqs structure-sheaf
  localization, no submodule extension theorem.
- msearch loogle: "SheafOfModules.over, CategoryTheory.Mono". Zero hits. An initial
  query using unqualified Mono was rejected as an unknown identifier and was rerun
  with the qualified name; it was not counted as evidence of absence.
- msearch grep: "subsheaf|submodule.*extension|extension.*submodule". The hits concern
  type-valued subsheaves, projective structure sheaves, ring extensions and injective
  modules; none states the required geometric extension theorem.
- rg on repository lean/Sheaf and source WeilConjectures for
  "submodule.*extend|extend.*submodule|quasicoherent.*extension|finiteType_submodule":
  no matching theorem (the coherent finite-type submodule kernel lemma is unrelated).
- I opened source WeilConjectures/Compactification/FiniteTypeExtension.lean,
  including the signatures of exists_finiteType_le_comap_eq_of_le,
  exists_finiteType_le_comap_eq and exists_finiteType_comap_eq. They quantify over
  IdealSheafData, not arbitrary F : X.Modules, so they are strictly special cases.
  The stage-1 reviewed note's reference to a "more generally" clause does not give
  an existing general module theorem in the current source file.
- rg of dag/lean_names_upstream.json for the proposed declaration found no collision.

No new nodes or dependency modules were supplied or needed. The existing Coherent
module supplies the exact dependency notions through its Mathlib imports and its
explicit documentation; it has no missing notion to repair. There are no definitions
in this delivery, hollow or otherwise. The sole theorem has exactly `by sorry`.
Both docstrings cite Stacks 01PF and the item id; the theorem's seven numbered proof
steps follow all seven node steps, including equality of inclusions after gluing.
The imports, namespace, topic path, and line lengths satisfy the conventions.
The node's lean.statement is verbatim the signature preceding `:=` in the file.

Mismatches and changes: none. I preserved the correct Lean and node record and added
only this independent second-reading section. The first explicit compile invocation
used a relative path from the read-only repository and failed to locate the sandbox
file; rerunning with its absolute sandbox path compiled cleanly on the server in
4.1 seconds, with no error or warning. No repository or source files were edited.

## Reviewer fix (R-fse1244)

Statement unchanged in content; restated in the form of the landed sibling
lem-weil-pbc-module-finite-presentation-extension (H1 ef7bad70c): explicit `X`,
quasi-compact open as `hU : IsCompact (U : Set X)` (was `[CompactSpace U]`), carriers
`SheafOfModules.{u} (moduleRings X.toRingedSpace)` and `(moduleRings X.toRingedSpace).over U`
(were `X.Modules` and `X.ringCatSheaf.over U`), and the compatibility as
`(SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).map ι' = e.hom ≫ ι`
(was `e.hom ≫ ι = ι'.over U`), so that stage 3 of the finite-presentation extension,
which uses this lemma in steps 5 and 7, applies it without conversion. Recompiled cleanly.
