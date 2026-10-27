## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFpqcOpenImmersionDescent` states
`AlgebraicGeometry.AlgebraicSpace.exists_scheme_openImmersion_of_fpqc_cover`.
Its sole theorem has proof `sorry`; it introduces no definitions or extra nodes.
Only the item's `lean` record changes.

Source read: `literature/stacks-project/spaces-descent.tex`, Tag 041X,
`lemma-descending-property-open-immersion`, including its full proof. The argument
descends the open image and uses the fpqc sheaf property before proving schematicity.
The latest blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md` was also read;
the item's supporting role is the one recorded in its inherited source/from/via.
No blueprint unit or node statement is changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes S and P: `{S : Scheme.{u}} (P : Over S)`. The over-object records P and
  its structural morphism to S, as required to speak of the S-morphism a.
- Algebraic space Z over S: `(Z : AlgebraicSpace S)`, the recorded full subcategory
  of fppf sheaves with representable diagonal and a surjective etale scheme atlas.
- S-morphism a from Z to P: `(a : Z.obj.obj ⟶ yoneda.obj P)`. Natural transformations
  on schemes over S are precisely the morphisms in the node. The representable
  target is written directly, so no extra algebraicity proof is a hypothesis.
- Arbitrary covering family: `{I : Type v} (Pᵢ : I → Over S)` and
  `(p : ∀ i : I, Pᵢ i ⟶ P)`. Its fpqc condition is `hcover`, membership of the
  underlying scheme-arrow presieve in `Scheme.fpqcPrecoverage P.left`.
  There is no singleton-cover, quasi-compact-target or nonempty-index restriction.
- Z_i = Z ×_P P_i is a scheme: `hlocal` provides `Zᵢ : Over S` and an isomorphism
  `e : Limits.pullback a (yoneda.map (p i)) ≅ yoneda.obj Zᵢ` for every i.
  These are presheaf pullbacks. Limits of sheaves are computed as presheaf limits,
  so this expresses the sheaf fibre product without assuming Z is schematic.
- The local projection is an open immersion: `q : Zᵢ ⟶ Pᵢ i`,
  `IsOpenImmersion q.left`, and the equation
  `Limits.pullback.snd a (yoneda.map (p i)) = e.hom ≫ yoneda.map q`.
  The equation specifies the actual projection under the representing isomorphism;
  the hypothesis is not an arbitrary choice of a different open-immersion map.
- Z is identified with an open subscheme of P: the conclusion gives `U : Over S`,
  `j : U ⟶ P`, `IsOpenImmersion j.left`, and
  `e : Z.obj.obj ≅ yoneda.obj U` with `a = e.hom ≫ yoneda.map j`.
  An open immersion identifies its source with its open image equipped with the
  restricted structure sheaf, exactly the equivalent characterization in
  def-weil-open-immersion. Thus these witnesses express both schematicity of Z and
  that the original a is an open immersion. No separate open-subspace definition
  or assumed representability of a is necessary.
- No representability or quasi-compactness assumption on a: neither appears among
  the binders. In particular, the conclusion covers non-quasi-compact open images.

Recorded dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`;
  its full defining signature, IsAlgebraicSpace, representability and atlas data
  were read. Its sheaf is exposed through `Z.obj.obj`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.snd`, at the presheaf category.

The statement imports these dependency modules publicly. The two additional
non-public proof imports are
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf` (the full-family gluing and equality
statement `existsUnique_section_and_eq_of_fpqc_cover`) and
`WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent`
(`openSubscheme_existsUnique_of_fpqc`). The remaining proof dependencies are
Mathlib declarations in the public Fpqc/OpenImmersion imports, including base change,
subcanonical fpqc descent, unique open factorization and open-immersion base change.
The theorem docstring carries all five steps of the DAG proof with these node ids.

Edge cases checked before writing:

- Empty I: retained. The fpqc hypothesis then forces P to be empty; the represented
  pullbacks and sheaf condition give the empty source, matching the conclusion.
- Empty base or target, empty local schemes and empty open image: no nonemptiness
  assumptions or excluded empty opens.
- Identity singleton cover: hlocal is already the requested representation, and
  the conclusion retains the map compatibility rather than forgetting a.
- Non-quasi-compact target, covering arrows and image: only the family's genuine
  fpqc condition is imposed; no quasi-compactness of a or j is assumed.
- Non-schematic source at the outset: Z is an algebraic space, never a scheme
  binder. Its representability occurs only in the conclusion and local hypothesis.
- Universes: all schemes and their sheaf values use the recorded size u, while
  the family has arbitrary index universe v. No auto-implicit variables are allowed
  (`set_option autoImplicit false`); every universe and binder is explicit.

Searches made using the prescribed msearch.py wrapper:

- LeanFinder: "An algebraic space mapping to a scheme is an open immersion if its
  pullbacks by an fpqc covering are schemes and open immersions". Eight hits,
  including presheafed-space toSchemeHom and ordinary scheme IsOpenImmersion
  results; none states this algebraic-space descent assertion.
- Loogle: `"AlgebraicGeometry", "DescendsAlong"`. Twelve hits, including
  `descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`.
  Read FlatDescent.lean:131 onward: its source is already a scheme and its cover
  is a singleton, so it does not supply the item's schematicity conclusion.
- Grep: `open.*immersion.*descen|descen.*[Oo]penImmersion|AlgebraicSpace` in
  Mathlib/AlgebraicGeometry. Five hits, all ordinary scheme results in FlatDescent
  or FlatMono, with no algebraic-space version.
- LeanSearch: "An algebraic space mapping to a scheme is an open immersion if its
  pullbacks along an fpqc covering are schemes and open immersions". Eight hits;
  ordinary IsOpenImmersion and scheme fpqc descent, no exact statement.
- Local rg of `lean/WeilConjectures` and `lean/Sheaf` for open-immersion descent,
  fpqc/open combinations and AlgebraicSpace interfaces. The etale-local
  `SpaceOpenImmersionEtaleLocal.lean` has an etale-cover hypothesis; the scheme
  `Morphisms/FpqcOpenImmersionDescent.lean` assumes a scheme source. Neither is
  this item. Existing representability and pullback interfaces suffice.
- Local rg for the item id in `lean/WeilConjectures`: no hits. Searches for the new
  declaration name in both source trees and `dag/lean_names_upstream.json`: no hits.

No STATEMENT-DISPUTED or node fault was found. The first compile exposed namespace
shadowing: unqualified `pullback` resolved to AlgebraicSpace's module pullback.
Qualifying `Limits.pullback` and `Limits.pullback.snd` repaired the notation without
changing the mathematical statement.

## Second reading by Q47

Author's second reading; the dispatcher forbids starting another agent, and the
maintainer supplies the independent delivery review. I reopened the node and the
completed signature and checked every binder and both projection equations.
S and P are schemes with the necessary structure map; Z retains the full recorded
algebraic-space hypothesis; a is an S-map of presheaves to h_P; hcover is precisely
the fpqc family definition. The two local existential scheme/map witnesses and
the representing isomorphism encode the complete local hypothesis. Its projection
equation is essential and is present. In the conclusion the open immersion j and
representing isomorphism e commute with a, so the assertion identifies this map
with the open inclusion rather than merely showing Z is abstractly schematic.
The empty-index and non-quasi-compact cases remain included. No mismatch with the
node required a statement correction. The only correction during elaboration was
qualification of the categorical pullback, described above. All five proof steps
are in the docstring; there are no helper declarations or copied definitions.
