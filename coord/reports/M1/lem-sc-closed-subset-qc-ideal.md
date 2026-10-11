## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedSubsetQcIdeal` states
`AlgebraicGeometry.Scheme.exists_quasicoherent_ideal_stalk_vanishing_eq`, with a single
`sorry` proof and no new definitions. The node is unchanged except for its `lean` record.

Hypothesis and clause correspondence:

- A scheme Y: `(Y : Scheme.{u})`, using Mathlib's `AlgebraicGeometry.Scheme`.
- A closed subset Z of Y: `(Z : Set Y) (hZ : IsClosed Z)`. No finiteness, separation,
  reducedness, or Noetherian hypothesis is imposed.
- Existence of an ideal sheaf J inside O_Y: `∃ J : Y.IdealSheafData`. This is the standard
  affine-local encoding of a quasi-coherent ideal. The source project's `J.toModules`
  is the actual module sheaf, defined as the kernel of O_Y -> i_* O_{V(J)}, and
  `J.toModulesι` is its monomorphism into `SheafOfModules.unit Y.ringCatSheaf`.
  `range_toModulesι_app` identifies its affine sections with `J.ideal`; the module's
  `idealOfOpens` gives ideals on every open, and `injective_toModulesι_app` proves
  injectivity on every open. Thus this binder gives an actual sheaf of ideals, not merely
  an arbitrary module monomorphism. Conversely, a quasi-coherent ideal sheaf gives exactly
  this compatible affine-local data, so the encoding excludes no witnesses required by
  the statement.
- Quasi-coherence: `J.toModules.IsQuasicoherent`, the Mathlib predicate used by the recorded
  `pqf-def-coherent` module. On schemes this is equivalent to the node's affine tilde
  criterion. It is explicit in the conclusion, not assumed through a private instance.
- V(J) = {y : J_y != O_{Y,y}} = Z: the set equality
  `{y : Y | ¬ Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
  ((Modules.toPresheaf Y).map J.toModulesι))} = Z`.
  The functor first forgets to additive presheaves, then takes the stalk of the inclusion.
  Since this is an inclusion, its image is the stalk ideal J_y inside O_{Y,y}. That ideal
  is the whole local ring exactly when the inclusion is surjective. Failure of
  surjectivity therefore expresses the stipulated inequality of ideals verbatim in
  mathematical meaning. This is not the support of J as a module (which would be wrong).

Dependencies read and used:

- `def-pc-scheme`: `mathlib_match` names `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`; read the structure signatures and docstrings.
  `Scheme` is used; the statement involves no morphism between arbitrary schemes.
- `pqf-def-coherent`: recorded module `Sheaf.AlgebraicGeometry.Coherent`, declaration
  `AlgebraicGeometry.RingedSpace.IsCoherent`; read the entire file. Only the quasi-coherent
  clause is needed here. That file explicitly delegates it to Mathlib's
  `SheafOfModules.IsQuasicoherent`, imported through this dependency module. Read that
  class's signature/docstring in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`;
  no private quasi-coherence definition or unnecessary coherent hypothesis is introduced.
- Existing APIs (not new notions): `Scheme.IdealSheafData` and `support` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`; `IdealSheafData.toModules` and
  `toModulesι` in `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`;
  `Scheme.Modules.toPresheaf` in `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
  Read the full signatures, construction bodies and docstrings. In particular
  `toModulesι` is `kernel.ι`, with the existing `Mono` instance.

Source: opened https://stacks.math.columbia.edu/tag/01J3 (the local literature checkout
is absent). Its proof constructs the vanishing ideal, identifies it with a radical ideal
on each affine and with its localization on standard opens, and concludes quasi-coherence.
The theorem docstring carries the node's complete proof: apply
`lem-weil-pbc-reduced-induced-closed-subscheme`, then use I_p != R_p iff I is contained in p
on each affine chart. The proof dependency is not imported to prove anything in stage 2.

Edge cases checked mathematically before writing: the empty scheme gives equality of
empty sets; Z empty allows the unit ideal and its everywhere surjective inclusion;
Z = Y allows the zero ideal (including on nonreduced schemes), with inclusion into each
nonzero local ring not surjective. Spec R and Z = V(I) give I_p != R_p exactly when
I is contained in p. Nilpotents do not require reducedness. No bound is imposed on the
scheme universe: `u` is explicit, and the additive stalks and module sheaves use that same
universe. There are no auto-bound implicit variables.

Searches for an existing full statement:

- `msearch.py ... leansearch "closed subset of scheme quasi coherent ideal sheaf vanishing
  locus"`: unavailable, HTTP Internal Server Error. Recorded as unavailable, no verdict.
- `msearch.py ... leanfinder "Every closed subset of a scheme is the vanishing locus of a
  quasi-coherent ideal sheaf"`: eight hits, including `IdealSheafData.vanishingIdeal`,
  `coe_support_vanishingIdeal`, `support`, and closedness of zero loci. These do not state
  quasi-coherence of the actual module sheaf together with the explicit stalk condition.
  The search service descriptions of support as nonzero stalks are inaccurate; the
  source definition is the intersection of affine zero loci and was read directly.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal"`:
  twelve hits for the construction, affine ideals, support identity, and Galois connection;
  no theorem giving the full requested existential statement.
- `msearch.py ... grep "vanishingIdeal|IsQuasicoherent" AlgebraicGeometry/IdealSheaf`:
  ten hits for vanishingIdeal in Basic and Functorial; no actual module quasi-coherence
  theorem in Mathlib's IdealSheaf directory.
- `rg -n 'quasiCoherent|IsQuasiCoherent|IdealSheaf|vanishingIdeal'` over project
  `WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`: ideal-data uses,
  including Hilbert and curve APIs; no matching statement.
- Targeted `rg -n 'IsQuasicoherent|quasicoherent|stalk|Surjective'` over
  `WeilConjectures/Mathlib/AlgebraicGeometry/IdealSheaf`: the existing Module bridge and
  unrelated surjectivity results, no matching theorem.
- `rg -n 'lem-sc-closed-subset-qc-ideal'` in `WeilConjectures` and
  `dag/lean_names_upstream.json`: no declaration. Search for the proposed full name and
  `stalk_vanishing` in upstream, project modules, and the upstream-name index: no collision.

Validation: `scompile.py M1 lem-sc-closed-subset-qc-ideal` compiled the final module
on the server in 2.0 seconds, exit 0, with no errors or warnings. Delivery dry run is the
last check; the independent second reader will add their own section. No statement dispute,
correction, new definition node, or dependency replacement was necessary.

## Second reading by M1

I reread the node and the module item by item. The node introduces a scheme `Y`; Lean renders
this as `(Y : Scheme.{u})`, with the same universe and no extra structure. It introduces a
subset `Z ⊆ Y` and the hypothesis that it is closed; Lean renders these as `(Z : Set Y)` and
`(hZ : IsClosed Z)`. No Noetherian, separated, reduced, finite-type, characteristic, or
base-field hypothesis is present. The conclusion asks for one quasi-coherent sheaf of ideals
`𝒥 ⊆ 𝒪_Y`; Lean represents this existing ideal-sheaf notion by
`J : Y.IdealSheafData`, uses its actual module sheaf `J.toModules` and inclusion
`J.toModulesι`, and asserts `J.toModules.IsQuasicoherent`. The final clause is the required
equality with `Z`: the set of points where the additive stalk map induced by the ideal inclusion
is not surjective is exactly `Z`. Since `toModulesι` is the kernel inclusion supplied by the
existing IdealSheaf bridge, this is precisely the condition that the stalk ideal is proper.
The existential, conjunction, and set equality have the same quantifier order and strength as
the node. The dependency `pqf-def-coherent` supplies the quasi-coherent notion through its
Mathlib `SheafOfModules.IsQuasicoherent` clause; no finite-type or coherent hypothesis was
accidentally added.

Edge cases checked: `Y = ∅` gives the empty equality; `Z = ∅` is represented by the unit ideal
and an everywhere-surjective stalk inclusion; `Z = Set.univ` is represented by the zero ideal;
affine `Y = Spec R` reduces to `I_p ≠ R_p` iff `I ⊆ p`; nilpotents require no reducedness;
and the explicit universe `u` does not exclude any scheme. There is no index set, integer `n`,
or characteristic parameter.

I searched Mathlib and the source project with LeanSearch, LeanFinder, Loogle, and ripgrep for
closed-subset/quasi-coherent ideal and stalk-vanishing statements. The only nearby declarations
are `Scheme.IdealSheafData.vanishingIdeal`, support APIs, and the project's
`IdealSheafData.toModules` bridge; none states this existential theorem. The proposed full
name also has no collision in Mathlib, `WeilConjectures`, `lean/Sheaf`, or the upstream-name
index.

The first worker's statement and implementation match the node, so I made no semantic changes.
I only verified the declaration and retained the single named `sorry` proof required for stage 2.
