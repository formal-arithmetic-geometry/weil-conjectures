## Worker report

The module `Sheaf.AlgebraicGeometry.ConstantGroupScheme` defines the constant scheme,
its maps and components, the fibre square, and the operations on its `T`-valued points.
The only postponed proof is the named theorem
`AlgebraicGeometry.exists_constantGroupSchemeMultiplication`, which supplies the
multiplication morphism with its componentwise and over-base properties. Its docstring
gives the gluing argument and cites the pointer node
`lem-weil-pbc-constant-group-scheme-multiplication`. No definition contains `sorry`.

Clause mapping:

- `T : Scheme.{u}` and `E : Type v` with `[AddCommGroup E]` are the scheme and abelian
  group. `[Small.{u} E]` permits the Mathlib coproduct in the universe of schemes;
  the universe `u` is arbitrary. The group structure implies `E` is nonempty.
- `T_E = ∐ fun _ : E => T` is `constantGroupScheme T E`; the maps `ι_e` are
  `constantGroupSchemeIncl T E e = Sigma.ι (fun _ : E => T) e`.
- The codiagonal `π` is `constantGroupSchemeProjection T E = Sigma.desc (fun _ => 𝟙 T)`.
  The equality `ι_e ≫ π = 𝟙 T` is the Mathlib `Sigma.ι_desc` equation.
- `V_e` is `constantGroupSchemeComponent T E e`, the range of `ι_e`.
  Openness, closedness, disjointness and covering are the recorded Mathlib
  coproduct-family dependency, not new assertions in this definition.
- `P = T_E ×_T T_E` is `constantGroupSchemeSquare T E = pullback π π`;
  `p` and `q` are `pullback.fst π π` and `pullback.snd π π`.
  `ρ = π ∘ p` is `constantGroupSchemeSquareProjection T E`; equality with `π ∘ q`
  follows from `pullback.condition`.
- `W_{e,e'}` is `constantGroupSchemePairComponent T E e e'`, the intersection of
  the two inverse images of `V_e` and `V_e'`. Its set builder expresses both
  membership conditions. The open subscheme used for restrictions is the
  `(e,e')` member of `Scheme.Pullback.openCoverOfLeftRight` applied to the two
  `sigmaOpenCover`s; it has exactly this underlying subset.
- `m` is `constantGroupSchemeMultiplication T E`, chosen from the named existence
  theorem. That theorem states, for each pair, `cover.f (e,e') ≫ m =
  pullback.fst (ι_e ≫ π) (ι_e' ≫ π) ≫ ι_(e+e')`, and `m ≫ π = ρ`.
  Uniqueness, clopenness and the remaining image claims belong to the pointer
  node and are not asserted as part of the data definition.
- For `s : U ⟶ T`, `ConstantGroupSchemePoint T E s` is the subtype of scheme
  morphisms `f : U ⟶ T_E` with `f ≫ π = s`, hence `Mor_T(U,T_E)`.
  `constantGroupSchemePointAdd` pairs `f` and `g` with `pullback.lift`, then
  composes with `m`. Its subtype proof uses `m ≫ π = ρ`.
- `constantGroupSchemeConstantPoint T E s e` is `s ≫ ι_e`, with the subtype
  proof from `Sigma.ι_desc`. `constantGroupSchemeCanonicalMap T E s` is
  `fun e => constantGroupSchemeConstantPoint T E s e`.
- The module claims no group-scheme axioms for `m`, as the node specifies.

Statement dependencies used: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
(`Mathlib.AlgebraicGeometry.Scheme`); `Scheme.Over` and `Scheme.Hom.IsOver`
(`Mathlib.AlgebraicGeometry.Over`, represented by an equivalent explicit subtype);
`CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and
`pullback.lift` (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`);
`AlgebraicGeometry.IsOpenImmersion` (`Mathlib.AlgebraicGeometry.OpenImmersion`,
through the open cover); `AlgebraicGeometry.sigmaOpenCover`,
`disjoint_opensRange_sigmaι`, and the scheme coproduct instance
(`Mathlib.AlgebraicGeometry.Limits`); `AlgebraicGeometry.Scheme.Cover.glueMorphisms`
(`Mathlib.AlgebraicGeometry.Gluing`, named in the existence theorem's proof plan).
All these are imported transitively by the three direct Mathlib imports.

Edge cases checked: the empty scheme gives a valid (possibly empty) coproduct
and pullback; the trivial group gives one component and a single pair
component; `U` may be empty; `E` cannot be empty because it has an additive
group identity. No characteristic, finiteness, or connectedness condition is
introduced. The universe is not fixed to a particular size.

Searches for an existing notion: `msearch.py ... leanfinder` with query
"constant group scheme over a scheme coproduct of copies indexed by an
abelian group with multiplication and constant points" returned eight
unrelated preadditive/group-category declarations; `msearch.py ... loogle`
with `ConstantGroupScheme, Scheme.GrpObjAsOverPullback, Scheme.sigma` found no
`ConstantGroupScheme`; `msearch.py ... grep` with
`constant.?group.?scheme|ConstantGroupScheme|constantScheme` in
`AlgebraicGeometry` found no match. `rg` over Mathlib AlgebraicGeometry, the
source `WeilConjectures`, and the project's `lean/Sheaf` found only a prose
mention of a constant group scheme in `GroupScheme/Basic.lean`, not a
definition. `grep -rn` for the item id in `WeilConjectures` found no match.

The local Stacks `.tex` checkout is absent in this machine's read-only
`literature/`; I read the published Stacks Tag 03YW and Tag 03P5 pages.

## Second reading by F1

I read the node, its six dependency records, the Lean module, Mathlib's `Limits.lean`
and `Pullbacks.lean`, and Stacks Tags 03YW and 03P5. Tag 03YW starts with an
arbitrary abstract group and scheme base, then describes the multiplication by
pairs of components; Tag 03P5 concerns locally constant maps. The node specializes
the group to an abelian group and claims no group-object axioms here.

- Objects and hypotheses: `T : Scheme.{u}` is the arbitrary base scheme and
  `E : Type v` with `[AddCommGroup E]` is its abelian index group. There is no
  finiteness, Noetherian, connectedness, characteristic, or field hypothesis.
  `[Small.{u} E]` is Mathlib's size condition for `∐` in `Scheme.{u}`;
  it asks that the index be representable in the scheme universe. The node's
  arbitrary set can be placed in a sufficiently large scheme universe.
- `T_E = ∐_e T`: `constantGroupScheme T E := ∐ fun _ : E => T` uses the
  coproduct from the dependency `lem-weil-pbc-scheme-coproduct-family`.
  `constantGroupSchemeIncl T E e` is `Sigma.ι`, and
  `constantGroupSchemeProjection T E` is `Sigma.desc` of identity maps;
  `Sigma.ι_desc` gives the required codiagonal equation. These supply
  the object over `T` of `def-weil-scheme-over-base`.
- `V_e = ι_e(T)`: `constantGroupSchemeComponent T E e` is exactly
  `Set.range (constantGroupSchemeIncl T E e)`. The clopen, disjoint, and
  covering facts are the Mathlib coproduct-family dependency, not new data.
- `P`, `p`, `q`, and `ρ`: `constantGroupSchemeSquare T E` is `pullback π π`;
  the module uses `pullback.fst` and `pullback.snd` for its projections.
  `constantGroupSchemeSquareProjection T E` is `pullback.fst π π ≫ π`;
  `pullback.condition` identifies it with `pullback.snd π π ≫ π`. These
  match the recorded fibre-product dependency.
- `W_{e,e'}`: `constantGroupSchemePairComponent T E e e'` is the set
  of `x` whose two projection images lie in the corresponding `V` sets.
  The `openCoverOfLeftRight` member used below has the pullback of the two
  coprojections as domain and covers exactly that pair component as an
  open subscheme, matching `def-weil-open-immersion`.
- `m`: `constantGroupSchemeMultiplication T E` chooses the `m` from
  `exists_constantGroupSchemeMultiplication`. Its first conjunct is, for
  every `ij : E × E`, the equation on that cover member with target
  coprojection indexed by `ij.1 + ij.2`; the second is `m ≫ π = ρ`.
  Composing the small pullback projection with the coprojection is the
  restriction of `ρ`, so this is the node's component formula. The separate
  pointer node carries uniqueness, clopenness of the pair components,
  image containment, and the inverse-image formula; they are not data
  required to choose `m` here.
- `Mor_T(U,T_E)`: for any `s : U ⟶ T`, `ConstantGroupSchemePoint T E s`
  is the subtype of morphisms `f : U ⟶ T_E` with `f ≫ π = s`. It is the
  hom-set of schemes over `T` from the recorded `Scheme.Over` notion.
  `constantGroupSchemePointAdd` pairs two such morphisms by `pullback.lift`
  and composes with `m`; its subtype equation uses the theorem's base-map
  conjunct. `constantGroupSchemeConstantPoint T E s e` is `s ≫ ι_e`,
  and `constantGroupSchemeCanonicalMap T E s` sends `e` to that point.

Edge cases: an additive group is nonempty even when trivial; the trivial group
gives one coproduct component. Empty `T` and empty `U` remain valid schemes,
and no equation depends on them having points. There is no natural-number
parameter or characteristic restriction. The two universe parameters are
arbitrary, subject to the index being small enough for the chosen scheme
universe, as in the dependency's Mathlib coproduct instance.

Independent searches: `msearch.py` LeanFinder for "constant group object
represented by locally constant functions on a scheme" returned no
representing scheme; Loogle for `AlgebraicGeometry.sigmaOpenCover,
CategoryTheory.Limits.pullback` returned no combined declaration; `msearch.py`
grep for "locally constant maps scheme group representable" returned no
match. `rg` for `constantGroupScheme` and `ConstantGroupScheme` in Mathlib,
the source repository, and `dag/lean_names_upstream.json` found no existing
definition. A separate `rg` for disjoint unions and locally constant maps
in Mathlib AlgebraicGeometry, the source repository, and project `lean/Sheaf`
found ingredients and related finite constructions, but no constant group
scheme with this data.

The definitions and signatures match the node. I changed one misleading
docstring: the auxiliary existence theorem had said its conclusion included
uniqueness, although uniqueness belongs to the pointer node and is absent
from that theorem's type. Its docstring now describes its actual clauses and
the gluing steps. No Lean statement or node field changed.
