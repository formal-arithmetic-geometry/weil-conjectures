## Worker report

The delivery states `lem-sfb-simple-isogeny-decomposition` in
`Sheaf.AlgebraicGeometry.AbelianVariety.SimpleIsogenyDecomposition`, with three
named theorems and `sorry` proofs. It adds the missing notion of simplicity in
`Sheaf.AlgebraicGeometry.AbelianVariety.Simple`, owned by the new definition node
`def-sfb-simple-abelian-variety`. No existing statement is corrected and no
dependency interface is replaced.

Hypotheses and clauses, in the order of the node:

- The arbitrary field is `{k : Type u} [Field k]` throughout. There is no
  perfectness, algebraic-closedness, or characteristic assumption.
- An abelian variety over k is `C : Over (Spec (.of k))` with `[GrpObj C]`
  and `[IsAbelianVariety C]`. This is the dependency's existing convention.
- Positive dimension in the definition of k-simple is
  `0 < IsAbelianVariety.dim C`.
- An abelian subvariety over k is quantified as
  `B : Over (Spec (.of k))`, `[GrpObj B]`, `[IsAbelianVariety B]`,
  `i : B ⟶ C`, `[IsMonHom i]`, `[IsClosedImmersion i.left]`.
  A closed immersion is in particular a subgroup embedding when it is a
  homomorphism. Thus this uses exactly the closed abelian subgroup schemes of
  the node, without any condition on rational-point cardinalities.
- The forbidden dimensions are rendered literally by
  `¬ (0 < IsAbelianVariety.dim B ∧
  IsAbelianVariety.dim B < IsAbelianVariety.dim C)`.
- For every A, `IsAbelianVariety.exists_simple_isogeny_decomposition` produces
  `r : ℕ`, `C : Fin r → Over (Spec (.of k))`, group and abelian-variety
  instances on every factor, and `∀ i, IsSimpleAbelianVariety (C i)`.
- The product is Mathlib's actual `piObj C` in k-schemes. The existential
  `GrpObj (piObj C)` is characterized by all `Pi.π C i` being homomorphisms.
  These conditions determine its componentwise group law; this is not an
  arbitrary uncharacterized group structure. This follows the interface of
  the recorded finite-product proof dependency.
- The required k-isogeny to A is
  `∃ (f : piObj C ⟶ A), IsIsogeny f`. Morphisms in `Over` are over k.
  `r = 0` is allowed, and `piObj C` is then the terminal k-scheme, namely
  the zero abelian variety. Its group operations are unique. No nonempty
  instance on the index set is required.
- The second clause is `isIsogeny_of_nonzero_of_simple`. It binds both
  abelian group schemes, their simplicity hypotheses `hX` and `hY`, and
  `[IsMonHom f]`. Nonzero is `hf : f ≠ 1`; the scoped `MonObj` group law
  on scheme morphisms uses `1` for the constant identity-section map.
  It concludes exactly `IsIsogeny f`.
- The final clause is `IsIsogeny.exists_isogeny_quasi_inverse`. It assumes
  any isogeny f between abelian varieties, without requiring simplicity.
  It gives `g : Y ⟶ X` and `IsIsogeny g`, and one `n : ℕ` with `0 < n`.
  Positive naturals encode precisely positive integers. The two equations
  are `f ≫ g = 𝟙 X ^ n` and `g ≫ f = 𝟙 Y ^ n`, in categorical composition
  order: respectively g after f and f after g. The same n occurs in both.

Dependency declarations read and used:

- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs` (class signature
  and docstring read).
- `def-sc-abelian-variety`:
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`,
  `AlgebraicGeometry.IsAbelianVariety`, its actual proper/smooth/connected
  fields, and `AlgebraicGeometry.IsAbelianVariety.dim`. The accompanying
  `topologicalKrullDim_eq` identifies the natural-number dimension with
  the actual topological Krull dimension.
- `def-sc-group-scheme`: `Mathlib.CategoryTheory.Monoidal.Grp`,
  `CategoryTheory.GrpObj`; `Mathlib.CategoryTheory.Monoidal.Mon`,
  `CategoryTheory.IsMonHom`; and `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`,
  `CategoryTheory.GrpObj.Hom.group`. The specializations and kernel conventions
  are documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-sc-isogeny`: `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`,
  `AlgebraicGeometry.IsIsogeny`: homomorphism, surjectivity of the underlying
  map, and finiteness of the scheme-theoretic kernel, exactly as recorded.
- `def-sc-mult-n`: the same module's `torsionSubgroupScheme` and its
  docstring identify multiplication by n as `𝟙 G ^ n`. The statement needs
  the multiplication map, not a newly defined torsion scheme.
- `def-sfb-simple-abelian-variety`: the new module's
  `AlgebraicGeometry.IsSimpleAbelianVariety` is used in both relevant clauses.

All recorded proof dependencies with modules are imported without `public`,
unless already public through a statement dependency. In particular these
include `MultipleRetraction`, `HomImageDimension`, `AbelianFiniteProduct`,
`KernelAbelianPart`, `FiniteGroupSchemeOrderAnnihilator`, the upstream abelian
`Basic` and `Isogeny` modules, and Mathlib's finite/radicial base-change and
fpqc modules. The Mathlib-only representable-descent and fpqc-base-change
leaves are supplied by `Mathlib.AlgebraicGeometry.Sites.Fpqc` and its imports.
No proof-dependency import closes a cycle. The three theorem docstrings
contain the corresponding portions of all eleven proof steps, including the
scheme-theoretic image complement over imperfect fields and fpqc cancellation
for the quasi-inverse; every postponed assertion belongs to this item's node.

Source reading: read the actual Milne AV PDF using `pdftotext -layout`,
specifically §10 before Proposition 10.1, Proposition 10.1 and its imperfect-field
footnote 10 on printed p.42, the discussion and footnote 11 on p.43, and
Remark 8.6 on p.36. These agree with the accepted node and proof route.

Edge cases checked before writing:

- The zero abelian variety is excluded from simplicity by positive dimension,
  but included in the decomposition theorem via `r = 0`.
- An elliptic curve has no strictly intermediate natural-number dimension;
  its simplicity condition is therefore the intended one.
- B = 0 and B = C do not violate simplicity. A genuine intermediate closed
  abelian subgroup does violate it. No geometric simplicity is imposed.
- A zero homomorphism between simple varieties is excluded by `f ≠ 1`;
  an identity homomorphism is allowed. The notation `1` is not the categorical
  identity `𝟙`, and this distinction is explicitly documented.
- Zero-dimensional X and Y are allowed in the quasi-inverse assertion;
  n = 1 suffices there. The zero map on the zero group is an isogeny.
- In characteristic p, n divisible by p is allowed and neither separability
  nor reducedness of the kernel is required.
- All schemes and the base field use universe u, as in the dependency
  declarations. The finite indexing type `Fin r` imposes no further size
  restriction on a finite family. Closed subvarieties can be represented in
  the same scheme universe as their ambient variety.

Searches performed (also retained as exact msearch result records in the new
definition node's `mathlib_searches`):

- LeanFinder: "Every abelian variety over a field is isogenous to a finite
  product of simple abelian varieties and isogenies have quasi inverses".
  Eight hits: Schur lemmas and semisimple module/Wedderburn results, no match.
- Loogle: `"isogeny", "simple"`: zero hits.
- Mathlib grep in AlgebraicGeometry:
  `SimpleAbelian|simple.*[Aa]belian|Poincar.*reduc|isogen`: zero hits.
- LeanSearch: "Simple abelian variety has positive dimension and no proper
  positive dimensional abelian subvariety". Eight hits concerning abstract
  simple additive groups, none about abelian varieties.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for simple-abelian names and
  phrases found only unrelated constructible simple objects. The exact item
  tag in `lean/WeilConjectures` had no hits. A separate search of
  `dag/lean_names_upstream.json` found no proposed declaration-name collision.
- Search of definition-node titles and statements for "simple abelian"
  found no nodes; `tools/blueprint_refs.py search 'simple abelian'` reported
  `0 blueprint nodes match 'simple abelian'`. Existing theorem nodes mention
  the notion but do not define it separately.

No statement dispute or dependency fault was found. Both delivered files
compiled cleanly using the prescribed `scompile.py` command; the measured
library checks took 1.4 s and 2.4 s respectively. No local Lean or Lake build
was run.

## Second reading by N5

The dispatcher explicitly forbids starting other agents; this is a separate
self-review pass, with independent maintainer review to follow delivery.
Reopened the original node, both modules, and the new node record. Checked
positive dimension, the quantification over closed k-subgroups, all factor
structures, the isogeny direction, and the empty-index case against the first
clause. Checked that the second theorem has both simplicity hypotheses and
excludes exactly the constant identity-section homomorphism. Checked that the
third theorem assumes no simplicity, returns an isogeny rather than just a
morphism, and uses the same positive n in the two correctly ordered equations.
The new definition unfolds to the node's first sentence with the closed
subgroup notion supplied by a closed immersion that is a homomorphism.
The product group structure is normalized by all projections, including
the empty case, and contains no chosen or postponed data. No mathematical
mismatch was found and no statement correction was necessary.

## New nodes

`def-sfb-simple-abelian-variety` introduces k-simplicity: positive-dimensional
abelian varieties with no closed abelian k-subgroup of strictly intermediate
dimension. Its source is Milne AV I §10, p.42, immediately before Proposition
10.1, with the positive-dimension convention explicit in the owning item.
The LeanSearch, LeanFinder, Loogle, Mathlib grep, project grep, definition-node
search and blueprint search above found no existing definition. The module
defines the predicate with real data as a conjunction and a universal
quantification, importing the recorded abelian-variety and group-scheme
definitions. The item gains only this new statement dependency and its Lean
record; every other original field is preserved. The blueprint ancestry has
`node: null`, exactly as returned by `blueprint_refs.py ancestor` for this
item; its `via` prepends this item to the original ancestry chain.
