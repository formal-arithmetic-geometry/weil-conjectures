## Worker report

The module `Sheaf.AlgebraicGeometry.InvariantComponentAffineDescent` states
`AlgebraicGeometry.exists_affine_open_invariant_component_descent`, with proof `sorry`.
It also constructs four canonical maps in the namespace
`AlgebraicGeometry.InvariantComponentAffineDescent`: `overlapBase`, `overlapLeft`,
`overlapRight`, and `restrictionMap`. Their data are compositions or `pullback.map`;
none uses choice, a postponed existence assertion, or sorry. These are notation-saving
specializations of the already recorded fibre-product construction, belonging to this
node's own diagram, rather than new mathematical notions.

Source read: literature/stacks-project/more-morphisms.tex,
`lemma-descent-connected-fibres` (Tag 057I), its full statement and proof, particularly
the last two paragraphs. The module docstring records this exact subargument. The
proof docstring reproduces all five DAG proof steps and their dependency references.
No statement correction, dependency repair, or disputed statement is needed.
The local example CompactObject module is withdrawn; its node points to
WeilConjectures.CategoryTheory.CompactObject, which was read for the header and conventions.

Hypotheses and constructions, clause by clause:

- Schemes and morphisms: `{X Z B : Scheme.{u}}`, `f : X ⟶ B`, `p : Z ⟶ B`,
  and `σ : Z ⟶ X`; `u` is explicit and unrestricted, and `autoImplicit` is false.
- Flatness: `[Flat f]`. Finite presentation is exactly
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`, as required
  by the scheme-conventions node and Stacks 01TP. No separatedness or Noetherian
  hypothesis is imposed.
- Geometrically reduced fibres: `[GeometricallyReduced f]`. Mathlib defines this by
  reducedness after every field-valued base change. This is equivalent to all the
  residue-field fibres being geometrically reduced, including empty fibres.
- Finite locally free multisection: `[p.IsFiniteLocallyFree]`, the recorded upstream
  class extending IsFinite, Flat and LocallyOfFinitePresentation.
- The triangle commutes: `hσ : σ ≫ f = p` (Lean composition is left to right).
- `Y` is `pullback f p`, its projection to `Z` is `pullback.snd f p`, and its induced
  section is the actual universal lift `pullback.lift σ (𝟙 Z) ...`. The proof parameter
  of this lift is exactly hσ followed by the inverse identity-composition equality.
- `C` is an open of this scheme, `(pullback f p).Opens`; thus openness is built into
  the object, with its uniquely determined restricted scheme structure. `hC` identifies
  its carrier with the points lying in `connectedComponentIn` of the topological
  fibre through the induced section. The scheme-fibre node identifies this subspace
  with the scheme-theoretic fibre. This is the precise locus used in the recorded
  section-component quasi-compactness theorem, not an arbitrary open subset.
- `b₀ : B`, `hb₀ : Nonempty (p.fiber b₀)` express the distinguished point and nonempty
  scheme-theoretic fibre.
- `R` is `pullback p p`; `overlapBase p = pullback.fst p p ≫ p` is `q`.
  `W : (pullback p p).Opens` is open, and `hW` says `q⁻¹{b₀} ⊆ W.carrier`.
- On `pullback f (overlapBase p)`, `h` is the second projection. `overlapLeft` and
  `overlapRight` are the canonical maps `1_X × pr₀`, `1_X × pr₁` to `Y`, constructed
  by `pullback.map`. For the second map, the required triangle equality is exactly
  `pullback.condition` on `R`. `hInv` equates the intersections (lattice infima of
  opens) `h⁻¹W ⊓ a₀⁻¹C` and `h⁻¹W ⊓ a₁⁻¹C`.

Conclusion, clause by clause:

- `∃ V : B.Opens, b₀ ∈ V ∧ IsAffineOpen V` gives the affine open neighbourhood.
- `(overlapBase p) ⁻¹' (V : Set B) ⊆ W.carrier` gives `q⁻¹V ⊆ W`.
- `X_V` is the chosen `pullback f V.ι`, `Z_V` is `pullback p V.ι`, and `p_V` is
  `pullback.snd p V.ι`. Its finite local freeness and surjectivity are the next two
  conjuncts, using the existing class and `Surjective`, respectively.
- `IsAffine (pullback p V.ι)` asserts that `Z_V` is affine.
- `P = X_V ×_V Z_V` is the explicit nested pullback of these two second projections.
  Its first projection is `π`.
- Both `Presieve.singleton p_V ∈ Scheme.fpqcPrecoverage V.toScheme` and the analogous
  membership for `π` are explicit conclusions: these say the singleton families are
  fpqc coverings, exactly the recorded covering notion.
- `restrictionMap f p V` is the canonical `P → Y`, using the first projections of
  `X_V`, `Z_V` and the inclusion `V.ι`. The compatibility arguments are the two
  inverse pullback-condition equalities. Hence its inverse image of `C` is precisely
  the canonical realization of `C_V = C ×_B V` on `P`.
- `IsCompact ((restrictionMap f p V) ⁻¹' C.carrier)` is quasi-compactness of `C_V`.
  Mathlib's compactness has no Hausdorff assumption.
- `∃ U : (pullback f V.ι).Opens, IsCompact U.carrier ∧ ...` gives the open `U` and
  its quasi-compactness.
- The following equality of opens is exactly `π⁻¹ᵁ U = C_V`.
- Finally `∀ U', π⁻¹ᵁ U' = C_V → U' = U` states uniqueness among ALL opens with the
  specified pullback, with `V` outside this quantifier. No uniqueness of `V` or
  additional compactness restriction on competing opens is asserted.
- There is no geometric connectedness hypothesis on `X_{b₀}`. The source uses that
  only in the preceding construction of W, supplied here as a hypothesis.

Recorded dependency declarations read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  its morphisms. Affine opens and their open subschemes are the standard Mathlib ones.
- def-weil-flat-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`.
- def-sbc-locally-finite-presentation:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- def-weil-pbc-scheme-conventions: no standalone declaration (a convention node);
  its finite-presentation convention supplies the three classes listed above.
- def-pc-geometrically-irreducible: the recorded
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` imports Reduced;
  `AlgebraicGeometry.GeometricallyReduced` is the reduced clause used here.
- def-pc-finite-locally-free:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (current source lines 895–900).
- def-pc-base-change: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`,
  the chosen `pullback`, projections and universal section conventions (in particular
  `baseChange_morphism_projections`, `baseChange_iterated`, and
  `baseChange_section_characterization` describe the same canonical constructions).
- def-pc-scheme-fibre: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`.
- def-weil-connected-scheme: `Mathlib.Topology.Connected.Basic`, `ConnectedSpace`;
  its component expression is Mathlib `connectedComponentIn`, as used by the existing
  section-component theorem. No separate connectedness predicate is defined.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; the open subschemes use Mathlib `Scheme.Opens`
  with their canonical inclusions and inverse-image opens.
- def-weil-surjective-morphism: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective`.
- def-weil-pbc-fpqc-covering: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `AlgebraicGeometry.Scheme.fpqcPrecoverage`.
- def-weil-pbc-quasi-compact-scheme: `Mathlib.Topology.Defs.Filter`, `CompactSpace`
  and `IsCompact`; a compact open carrier is exactly a quasi-compact open scheme.

The proof imports include all already-stated proof-dependency modules:
Mathlib's finite morphism, properness, quasi-finiteness, universal openness,
quasi-separatedness, finite-presentation and fpqc base-change APIs (some transitively),
`WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent` with
`AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat` with
`AlgebraicGeometry.isCompact_setOf_mem_connectedComponentIn_preimage_singleton`.
Their relevant signatures and docstrings were read. No proof import is omitted for a cycle.

Edge cases checked before writing:

- Empty B is incompatible with the supplied point; empty Z or an empty distinguished
  fibre is excluded precisely by hb₀, not by a global nonemptiness assumption.
- Empty fibres of X away from b₀ cause no problem; C_V and U may have empty fibres.
- The identity multisection and W equal to the whole overlap are included.
- A finite locally free map may miss entire components of B: it is not assumed
  surjective globally; surjectivity is concluded only after shrinking around b₀.
- Disconnected or geometrically disconnected X_{b₀} is allowed if the supplied
  invariance condition holds. Components not met by the section are not forced into U.
- Bases are allowed to be non-affine, non-quasi-compact or non-Noetherian; V is the
  affine neighbourhood provided by the conclusion. No characteristic is excluded.
- Uniqueness is for fixed V and fixed canonical pullback, including the empty open.
  The universal quantifier ranges over every competing open, not just compact ones.

Searches (using the prescribed msearch wrapper, Q77 and this item):

1. leanfinder: "An invariant section connected component along a finite locally free
   multisection descends to a quasi compact open after affine shrinking". Eight hits
   concerned affine approximation and compact-open coverings; no matching theorem.
2. loogle: `"connectedComponentIn", "IsCompact"`. Zero hits.
3. grep: `invariant.*component|component.*descent|fpqcPrecoverage`, subdirectory
   AlgebraicGeometry. Seven fpqc-precoverage references; none states this theorem.
4. leansearch: "Invariant open section component descends after affine shrinking
   finite locally free cover". Eight hits on affine covers, approximation and descent
   of morphism properties; none matches this construction and conclusion.
5. rg on lean/WeilConjectures and lean/Sheaf for `connectedComponentIn` found the
   existing SlicingFlat compactness theorem and SectionComponentPullback API, reused
   rather than duplicated. Searches for invariant component/descent and the exact
   item id found no existing declaration of this statement. The requested exact-id
   grep on WeilConjectures also had no matches.
6. rg on dag/lean_names_upstream.json and both source trees for the new full theorem
   and helper namespace found no collision. Generic words overlapLeft, overlapRight
   and restrictionMap occur in unrelated namespaces and private declarations.

Validation: scompile.py compiled the module separately both as a sandbox module and
under its actual library name, cleanly (3.8 s and 3.6 s). Initial carrier annotations
inside `Set (pullback ...)` let Lean try the category of Types; using the already
bundled opens' `.carrier` resolved this elaboration issue without changing the statement.

## Second reading by Q77

I reopened the current node and reread the final module in a separate review pass;
the maintainer supplies the independent review specified in the assignment.
The triangle, section-component identity, finite-presentation qcqs convention,
nonempty fibre, W-neighbourhood and overlap-invariance hypotheses all match their
node clauses. I checked each conclusion against the ordered conjunction: affine V,
b₀ membership, q-preimage inclusion, finite locally free and surjective p_V, affine
Z_V, both actual singleton fpqc covering memberships, compact C_V, open compact U,
pullback equality and uniqueness among all opens. The maps are canonical with the
required domains and projections, rather than existential arbitrary maps. In
particular restrictionMap has domain X_V ×_V Z_V, so the equality with π⁻¹U is typed
on the same scheme. No connectedness, global surjectivity, Noetherian assumption,
or unique-V assertion has slipped in. No mathematical mismatch was found and no
statement change was made. The only repair was the carrier elaboration described above.
