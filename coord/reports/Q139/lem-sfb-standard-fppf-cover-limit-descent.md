## Worker report

The module `Sheaf.AlgebraicGeometry.StandardFppfCoverLimitDescent` states
`AlgebraicGeometry.Scheme.exists_standardFppfCover_stage`. Its only theorem proof is
`sorry`; it introduces no definitions, helper theorems, or new nodes. The original
node is unchanged except for its `lean` record.

Read the source in `literature/stacks-project/topologies.tex`,
`definition-standard-fppf` (Tag 021Q, lines 1989–1995) and
`lemma-limit-fppf-topology` (Tag 049N, clause (1) and its fppf proof, lines 4291–4351).
The source gives exactly finite affine flat finite-presentation families whose
images cover, and descent of the entire labeled family to one stage.

Hypotheses and clauses, matched to the Lean statement:

| Node text | Lean rendering |
| --- | --- |
| A scheme S and the size convention | `(S : Scheme.{u})`, explicit `universe u v`, and `set_option autoImplicit false`. The size node is a convention, with no declaration to import. |
| A small nonempty directed set I | `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`; the index is in the schemes' universe, as required for affine limits. |
| An inverse system of affine S-schemes | `(D : Iᵒᵖ ⥤ Over S)` and `(hD : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left)`. Morphisms of `Over S` include compatibility with S. Affine here describes the underlying scheme, not the structure morphism to S. |
| T is the inverse limit | `(c : Cone D) (hc : IsLimit c)` and `T = c.pt.left`. Since the index is connected, the forgetful functor preserves and creates this limit. Thus this is also the ordinary scheme limit, with the canonical compatible structure map to S; it imposes no extra limit condition. |
| A finite family, including m = 0 | `{κ : Type v} [Finite κ] (V : κ → Over c.pt.left)`. This includes `Fin m` for every m, without imposing an ordering or excluding an empty set. |
| Each component is affine | `(hV : ∀ a : κ, IsAffine (V a).left)`. |
| Each map is flat | `(hflat : ∀ a : κ, Flat (V a).hom)`. |
| Each map is locally of finite presentation | `(hlfp : ∀ a : κ, LocallyOfFinitePresentation (V a).hom)`. |
| The images cover T | `hcov : ∀ x : c.pt.left, ∃ a : κ, ∃ y : (V a).left, (V a).hom y = x`, precisely joint surjectivity on scheme points. |
| The affine maps are also qcqs and finitely presented | These are consequences, not added assumptions: an affine-source map to the affine limit is affine, hence quasi-compact and quasi-separated. Along with `hlfp` this gives finite presentation in the node's convention. The proof docstring spells out this step. |
| One stage i and a standard covering there with the original labels | `∃ (i : I) (W : κ → Over (D.obj (op i)).left)`, followed by the three componentwise properties (affine, flat, locally of finite presentation) and joint surjectivity on the stage. The same affine argument supplies quasi-compactness, quasi-separatedness, and finite presentation for these maps. |
| Its base change is isomorphic to the original family over T | For every original `a : κ`, `Nonempty ((Over.pullback (c.π.app (op i)).left).obj (W a) ≅ V a)`. This uses the canonical projection to the chosen stage and the existing pullback functor. Isomorphisms are in `Over c.pt.left`, so the maps to T commute; this is stronger data than merely an isomorphism of underlying schemes, exactly as required by the node. The same label appears on both sides. All maps to S follow by composition. |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (structure and full signatures/docstrings read).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and
  `AlgebraicGeometry.Flat.iff_flat_stalkMap`; the latter identifies the recorded
  affine-local class with the node's stalkwise condition. The same module supplies
  `Flat.isStableUnderBaseChange` for the proof dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, the recorded declaration, and its
  affine global-sections characterization `Scheme.Hom.finitePresentation_appTop`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine` (publicly
  available through the statement imports), with `Scheme.isoSpec` identifying its
  canonical-map formulation with the node's spectrum-isomorphism definition.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `CategoryTheory.Over.pullback`;
  its actual object is `Over.mk (pullback.snd g.hom f)`, not an unspecified map.
- `Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`:
  `Over.preservesLimitsOfShape_forget_of_isConnected` and
  `Over.createsLimitsOfShapeForgetOfIsConnected` justify the slice-limit encoding.
- Proof imports preserve the recorded proof plan:
  `Sheaf.AlgebraicGeometry.FinitePresentationFamilyDescent`
  (`AlgebraicGeometry.exists_finitePresentation_family_stage`),
  `WeilConjectures.AlgebraicGeometry.DescendAffine`
  (`AlgebraicGeometry.exists_isAffineHom_baseChange_of_isLimit`),
  `WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation`
  (`AlgebraicGeometry.exists_flat_stage_of_limit`),
  `WeilConjectures.AlgebraicGeometry.FiniteFamilyJointSurjectivityStage`
  (`AlgebraicGeometry.finite_family_joint_surjectivity_stage`), and
  `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`
  (`AlgebraicGeometry.exists_limit_affine_transition`). Their full statements and
  proof docstrings were read. The Mathlib leaf dependencies are supplied by
  `Morphisms.Affine`, `Morphisms.Separated`, `Morphisms.QuasiSeparated` (through
  the public finite-presentation import), `AlgebraicGeometry.Limits`,
  `Morphisms.Flat`, and `Limits.Shapes.Pullback.IsPullback.Basic`.
  These give affine permanence, affine qcqs, qcqs permanence, flat base change,
  the affine-local-target criterion, and `IsPullback.paste_vert_iff`.

Edge cases checked before writing:

- If κ is empty, `hcov` means T has no points. The output covering condition then
  means that the chosen stage has no points. This is the required eventual empty
  stage assertion, not a vacuous output or an excluded empty case. Joint-surjectivity
  descent explicitly includes this case.
- If T is empty but κ is nonempty, each component over T is empty. No nonemptiness
  requirement on components or maps was introduced.
- A constant system and a singleton index allow the given covering as a model;
  the isomorphism is over T via the canonical identity pullback.
- No affineness, quasi-compactness, or Noetherian condition on S is imposed.
  No surjectivity of an individual map is assumed: only the whole family covers.
- Preorders are allowed, including equivalent distinct indices. Only directedness,
  not linear order or antisymmetry, is required. The family universe v is arbitrary
  but the family is finite; the inverse-system index stays in universe u.

Searches actually run (all through the prescribed tool where applicable):

- `msearch.py ... leanfinder` with query
  `A finite standard fppf covering of an affine inverse limit descends to a finite stage of the inverse system`:
  8 hits, including `ExistsHomHomCompEqCompAux.exists_index`,
  `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`, and
  `exists_appTop_π_eq_of_isAffine_of_isLimit`. These concern maps, sections and
  affine open covers, not descent of the flat covering components.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation`:
  12 hits, including `UniversallyOpen.of_flat`, flat descent, and
  `Scheme.fppfPrecoverage_eq_inf`. None states inverse-limit descent of a finite
  affine covering family.
- `msearch.py ... leansearch` with query
  `Finite families of flat locally finitely presented affine schemes jointly covering an affine inverse limit descend to a common finite stage`:
  8 hits, including `Scheme.exists_isOpenCover_and_isAffine`, affine limit
  existence, and `Scheme.isAffine_of_isLimit`. Affine open-cover approximation
  does not descend an arbitrary standard fppf covering.
- `msearch.py ... grep 'fppf|Fppf' AlgebraicGeometry`: 7 hits, principally the
  fppf precoverage in `Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`. Its definition
  was read: it gives the general covering notion, not the present theorem.
- `rg -n 'StandardFppf|standardFppf|standard_fppf|standard fppf|standardFPPF'`
  over Mathlib's AlgebraicGeometry, `lean/WeilConjectures`, and `lean/Sheaf`:
  no matching declaration. A later broader fppf/limit search found
  `FppfSheafificationAffineContinuity.lean`, whose proof docstring cites this
  missing theorem; its actual declaration was read and is not a duplicate.
- The required item-id search in `lean/WeilConjectures` returned no match.
  The fresh declaration-name search `exists_standardFppfCover_stage` in
  Mathlib, both project Lean trees, and `dag/lean_names_upstream.json` returned
  no match. No second definition of a covering notion is introduced.

No statement fault or dispute was found. No statement correction, new node, or
unusable dependency interface is needed. Compilation and the delivery preflight
are performed with the prescribed `scompile.py` and `deliver2.py` wrappers only.

## Second reading by Q139

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
