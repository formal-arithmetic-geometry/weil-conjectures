## Worker report

The module `Sheaf.AlgebraicGeometry.ConormalSurjectionUnramified` states
`AlgebraicGeometry.Scheme.Modules.isUnramified_near_of_conormal_surjective`.
Its only declaration is this theorem, with proof `sorry`. No definitions, dependency
repairs, new nodes, or changes to the mathematical statement are needed. The node copy
changes only `lean`.

The sources read were `literature/stacks-project/morphisms.tex`, at
`lemma-conormal-functorial` (01R4), `lemma-two-immersions` (067L), and
`lemma-unramified-at-point` (02GF), together with the exceptional-curve argument in
`literature/stacks-project/resolve.tex` (0C5R, lines 4945–4968).
Tag 067L gives the right-exact conormal sequence with the specified first arrow;
02GF identifies vanishing of the cotangent fibre with unramifiedness at a point.
The theorem docstring reproduces all four proof steps of the node, including the
local-ring quotient and residue-field identification.

Hypothesis and conclusion correspondence:

- The schemes and the ambient morphism are `{X Y Z : Scheme.{u}}` and `(f : X ⟶ Y)`.
  The explicitly bound universe `u` is unrestricted.
- Local finite type of `f` is `[LocallyOfFiniteType f]`; no quasi-compactness or finite
  presentation is assumed.
- The two closed immersions are `(i : Z ⟶ X) (j : Z ⟶ Y)` with
  `[IsClosedImmersion i] [IsClosedImmersion j]`.
- The equality `f ∘ i = j` is `(h : i ≫ f = j)`.
- The ideal sheaves are the recorded `i.ker` and `j.ker`, viewed as modules through
  `.toModules`. Their conormal sheaves are exactly
  `(tensorPullback i).obj i.ker.toModules` and
  `(tensorPullback j).obj j.ker.toModules`.
- The required arrow is obtained from
  `closedImmersion_conormal_functorial i j f (𝟙 Z)`.
  Its square equality is `h.trans (Category.id_comp j).symm`; this is just
  `i ≫ f = (𝟙 Z) ≫ j`, with no new assumption. The inner `Classical.choose_spec`
  extracts the property of the ideal map supplied by that theorem, and the outer
  `Classical.choose` selects its uniquely characterized conormal map. The dependency
  theorem fixes it by the adjunction equation and affine representative formula.
  This is not an arbitrary morphism or a choice from a bare `Nonempty` statement.
- That chosen map has source `id_Z^* C_{Z/Y}`. Precomposition with
  `(tensorPullbackSectionId Z).inv.app ((tensorPullback j).obj j.ker.toModules)`
  gives exactly the node's map `C_{Z/Y} ⟶ C_{Z/X}`. The identity comparison is the
  existing section-normalized comparison, not a newly chosen isomorphism.
- The hypothesis `hsurj : Epi (...)` expresses surjectivity as a morphism of sheaves
  of modules, equivalently local surjectivity (or surjectivity on stalks). It does
  not require surjectivity of sections on every open.
- Every point of `Z` is covered by `∀ z : Z`. The witness `∃ W : X.Opens` is an open
  subscheme of `X`, and `i z ∈ W` says it is a neighbourhood of the specified point.
- `IsUnramified (W.ι ≫ f)` is precisely unramifiedness of the restriction with target
  the original `Y`. Its recorded definition expands to local finite type and an
  open-immersion diagonal. No neighbourhood in `Y` is substituted.

Recorded statement-dependency declarations used, with source modules:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`, in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-sbc-closed-immersion-ideal-sheaf`: `AlgebraicGeometry.Scheme.Hom.ker`, in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`; its `.toModules` is the existing kernel
  construction from `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`,
  publicly imported by the conormal-functoriality dependency.
- `def-pc-module-pullback`: the recorded module
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, using
  `Scheme.Modules.tensorPullback` and `tensorPullbackSectionId`. The functor is the
  upstream tensor construction publicly imported there. The identity comparison is
  induced by `tensorPullbackSectionAdjunction`, whose unit is fixed on sections.
- `lem-weil-pbc-closed-immersion-conormal-functorial`:
  `Scheme.Modules.closedImmersion_conormal_functorial`, in
  `WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, in
  `Mathlib.AlgebraicGeometry.OpenImmersion`, via the definition of unramifiedness
  and the open-subscheme inclusion.
- `def-weil-unramified-morphism`: `AlgebraicGeometry.IsUnramified`, in
  `Sheaf.AlgebraicGeometry.UnramifiedMorphism`.

The recorded proof dependencies that already have modules are imported privately:
`WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk`
(`Scheme.Modules.exists_tensorPullback_stalk_iso`),
`Mathlib.AlgebraicGeometry.ResidueField` (`Scheme.residueField` and
`Scheme.Hom.residueFieldMap`), and `Mathlib.LinearAlgebra.TensorProduct.Tower`
(`LinearMap.baseChange` and the tensor constructions).
The closed-immersion proof dependency is already a public statement import.
`lem-sfb-two-closed-immersions-conormal-exact` and
`lem-sfb-unramified-cotangent-fibre-criterion` have no recorded Lean module in the
read clone, so there is no module to import for them yet. They are proof-only
prerequisites, not notions required to state this theorem; their future proof
imports can be added when their modules land.

Edge cases checked before writing: empty `Z` gives a vacuous universal conclusion;
if `X` is empty a map `Z ⟶ X` forces that case. Identity immersions are allowed:
when both are identities the morphism is an identity and the conclusion holds.
When `j` is the identity, the conormal source is zero, so surjectivity really forces
the other conormal module to vanish; it is not an automatic hypothesis. Nonreduced
closed subschemes are retained by `.ker` and tensor pullback. Arbitrary points,
including nonclosed points, and arbitrary residue fields and characteristics are
included. There is no flatness, Noetherian, smoothness, or reducedness restriction.

Searches for existing declarations (2026-10-24):

- `msearch.py ... leanfinder` with query "A morphism locally of finite type is
  unramified near a common closed subscheme when the canonical conormal map is
  surjective": eight hits, including `FormallyUnramified`, `formallyUnramified_iff`
  and `Algebra.isOpen_unramifiedLocus`; none states this theorem.
- `msearch.py ... leansearch` with query "Surjectivity of the canonical conormal
  morphism for two closed immersions implies unramifiedness near the closed
  subscheme": eight hits concerning formal unramifiedness and closed-immersion
  stalk surjectivity; no match.
- `msearch.py ... loogle '"conormal", "unramified"'`: zero hits. An earlier query
  `AlgebraicGeometry, conormal, unramified` reported an unknown namespace identifier;
  the quoted-name query repaired that search.
- `msearch.py ... grep 'conormal.*unramified|unramified.*conormal|conormalMapOfCommonClosedSubscheme'`:
  zero Mathlib hits. Direct `rg` in Mathlib's `AlgebraicGeometry` for
  `conormal.*unramified|unramified.*conormal|twoImmersions|two_immersions` also had none.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for conormal/unramified combinations found algebraic
  chart lemmas, formal-unramified conormal definitions, and the Bertini proof
  discussion, but not this theorem. Searching the exact item id upstream found none.
- Direct `rg` for `closedImmersion_conormal_functorial|conormalMap|conormalMorphism|conormalFunctorial`
  found the recorded canonical-map theorem and existing consumers that extract
  its unique map by the same nested `Classical.choose` expression. No helper
  definition is duplicated here. The new theorem name has no existing occurrence.

Validation: `scompile.py Q67 lem-sfb-conormal-surjection-unramified` compiled the
single delivered file in sandbox mode (9.1 s) and library module mode (10.6 s), with
no errors or unexpected warnings. No statement dispute or node fault was found.

## Second reading by Q67

Q67 reread the node and the completed file after compilation; independent review
of this dispatcher delivery is left to the maintainer as specified by the brief.
The signature retains exactly the locally finite type hypothesis, both closed
immersions with their common domain, and their equality over `Y`. In particular,
the map in `hsurj` is the dependency's canonical map for top `𝟙 Z`, and its source
has been explicitly identified with `j`'s conormal module using the canonical
identity-pullback comparison. This avoids silently using a different source or an
unconstrained conormal arrow. `Epi` means sheaf surjectivity, not global section
surjectivity. The conclusion quantifies over all `z : Z`, asks for an actual open
neighbourhood of `i z` in `X`, and keeps target `Y`. The definition of `IsUnramified`
was opened and checked: its two clauses match the recorded dependency. All
variables and the one scheme universe are explicitly bound. The proof is only
`sorry`; the four-step natural-language proof includes the residue-field
identification that is essential for applying 02GF. No mismatch was found and no
mathematical statement was changed.
